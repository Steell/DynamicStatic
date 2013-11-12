module DynamicStatic.DS

open DynamicStatic.ControlFlowTree
open DynamicStatic.Type
open DynamicStatic.ConstraintSet
open DynamicStatic.TypeExpression
open DynamicStatic.ControlTypeExpression


let guess_maker() =
    let rec numbers_from n =
        seq { yield n; yield! numbers_from (n+1) }
    seq { for n in numbers_from 0 -> sprintf "_%i_temp_" n }


let mutable private guesses = guess_maker().GetEnumerator()
let fresh_var() =
    ignore <| guesses.MoveNext();
    guesses.Current


let build_cft (id : string) 
              (expr : TypeExpression) 
              : ControlFlowTree * ControlTypeExpression =

    let cft_add_stack cft stack = List.foldBack (cft_add fresh_var) stack cft

    let rec build_cft (expr : TypeExpression) (cft : ControlFlowTree) (stack : string list) : (ControlTypeExpression * ControlFlowTree * string list) =
        let rec build_exprs cft' stack' a = function
            | expr::exprs ->
                let cte, cft'', stack'' = build_cft expr cft' stack'
                build_exprs cft'' stack'' (cte::a) exprs
            | [] ->  List.rev a, cft', stack'
        match expr with
        | Atom_E -> CAtom_E, cft, stack
        
        | Type_E(t) -> 
            let rec gather_ids stack = function 
                | TypeId(id) -> failwith <| sprintf "Not allowed to use TypeId(%s) in TypeExpression" id
                | PolyType(id) -> id::stack
                | Not(t) | List(t) -> gather_ids stack t
                | Func(overloads) -> 
                    Set.fold (fun stack' (param_type, return_type) -> 
                                 gather_ids (gather_ids stack' param_type) 
                                            return_type)
                             stack 
                             overloads
                | Union(ts) -> Set.fold gather_ids stack ts
                | _ -> stack
            CType_E(t), cft, gather_ids stack t

        | Let(ids, exprs, body_expr) ->
            let c_exprs, cft', stack' = build_exprs cft (ids @ stack) [] exprs
            let c_body, cft'', stack'' = build_cft body_expr cft' stack'
            CLet(ids, c_exprs, c_body), cft'', stack''
        
        | Fun(param_name, body_expr) ->
            let c_body, cft', stack' = build_cft body_expr cft <| param_name::stack
            let id = fresh_var()
            CFun(param_name, c_body, id), cft', id::stack'
        
        | Call(fun_expr, arg_expr) ->
            let fun_expr', cft', stack' = build_cft fun_expr cft stack
            let arg_expr', cft'', stack'' = build_cft arg_expr cft' stack'
            let return_id = fresh_var()
            CCall(fun_expr', arg_expr', return_id), cft'', return_id::stack''

        | Begin(exprs) ->
            let c_exprs, cft', stack' = build_exprs cft stack [] exprs
            CBegin(c_exprs), cft', stack'

        | If(test, t_expr, f_expr) ->
            let c_test, cft', stack' = build_cft test cft stack

            let c_t_expr, t_cft, t_stack = build_cft t_expr cft' []
            let t_cft' = cft_add_stack t_cft t_stack

            let c_f_expr, f_cft, f_stack = build_cft f_expr cft' []
            let f_cft' = cft_add_stack f_cft f_stack

            let t_idx, cft'' = cft_add_branch t_cft' cft'
            let f_idx, cft''' = cft_add_branch f_cft' cft''

            CIf(c_test, (t_idx, c_t_expr), (f_idx, c_f_expr)),  cft''', stack'

    let cte, cft, stack = build_cft expr empty_cft [id]
    cft_add_stack cft stack, cte


let rec constrain (cft : ControlFlowTree) 
                  (cset : ConstraintSet) 
                  (sub_type : Type) 
                  (super_type : Type) 
                  : UnificationResult =

    let unify' map cset' =
        match cft_map_lookup map sub_type with
        | Some(cft_subtype) ->
            match cft_map_lookup map super_type with
            | Some(cft_supertype) ->
                unify (generalize_rule fresh_var) cft_subtype cft_supertype cset'
            | None -> Failure(sub_type, super_type) // Maybe we should
        | None -> Failure(sub_type, super_type)     // succeed here?

    match cft with
    | Leaf(map) -> unify' map cset
    | Branch(trees) -> 
        let rec unify_in_all cset' = function
            | tree::trees' -> 
                match constrain tree cset' sub_type super_type with
                | Success(cset'') -> unify_in_all cset'' trees'
                | x -> x
            | [] -> Success(cset')
        unify_in_all cset trees


let overload_function cft ((param_name : string), (body_type : Type)) : Type =
    let rec define_in_leaves os = function
        | Leaf(map) -> 
            let lookup t = 
                match cft_map_lookup map t with
                | Some(x) -> x
                | None -> failwith "Overload Failure"
            Set.add (lookup <| PolyType(param_name), lookup body_type) os
        | Branch(trees) ->
            List.fold define_in_leaves os trees
    Func(define_in_leaves Set.empty cft)


type ConstructionResult =
    | Pass of Type * ConstraintSet
    | Fail of Type * Type

let rec build_cset (expected : Type) 
                   (expr : ControlTypeExpression)
                   (cft : ControlFlowTree)
                   (cset : ConstraintSet)
                   : ConstructionResult =
    match expr with
    | CAtom_E -> build_cset expected (CType_E(Atom)) cft cset

    | CType_E(t) -> 
        match constrain cft cset t expected with
        | Success(cset') -> Pass(t, cset')
        | Failure(t1, t2) -> Fail(t1, t2)

    | CLet(ids, exprs, body_expr) ->
        let rec constrain_all cset'' = function
            | (t1, t2)::xs -> 
                match build_cset t1 t2 cft cset'' with
                | Pass(_, cset''') -> constrain_all cset''' xs
                | x -> x
            | [] -> Pass(Any, cset'')
        match constrain_all cset <| List.zip (List.map PolyType ids) exprs with
        | Pass(_, cset') -> build_cset expected body_expr cft cset'
        | x -> x

    | CFun(param_name, body_expr, return_id) ->
        let rtn = PolyType(return_id)
        match build_cset rtn body_expr cft cset with
        | Pass(t, cset') ->
            let f = Func(make_oset [PolyType(param_name), t])
            match constrain cft cset' f expected with
            | Success(cset'') -> Pass(f, cset'')
            | Failure(t1, t2) -> Fail(t1, t2)
        | x -> x
        
    | CCall(func_expr, arg_expr, id) ->
        let argId = PolyType(id)
        match build_cset argId arg_expr cft cset with
        | Pass(t, cset') ->
            let f = Func(make_oset [t, expected])
            build_cset f func_expr cft cset'
        | x -> x
        
    | CBegin(exprs) ->
        let rec begin_exprs cset' = function
            | []           -> Pass(Unit, cset')
            | [expr']      -> build_cset expected expr' cft cset'
            | expr'::exprs -> 
                match build_cset Any expr' cft cset' with
                | Pass(_, cset'') -> begin_exprs cset'' exprs
                | x -> x
        begin_exprs cset exprs

    | CIf(test, (t_idx, t_expr), (f_idx, f_expr)) ->
        let t_cft = cft_branch t_idx cft
        let f_cft = cft_branch f_idx cft
        
        // constrain test to True in t_cft
        match build_cset True test t_cft cset with
        | Pass(_, cset) -> 
            // constrain test to False in f_cft
            match build_cset False test f_cft cset with
            | Pass(_, cset) ->
                // constrain if return to true branch in t_cft
                match build_cset expected t_expr t_cft cset  with
                | Pass(_, cset) -> 
                    // constrain if return to false branch in f_cft
                    match build_cset expected f_expr f_cft cset with
                    | Pass(_, cset) -> Pass(expected, cset)
                    | x -> x
                | x -> x
            | _ ->
                // constrain test to True|False in f_cft
                match build_cset (Union(Set.ofList [True; False])) test f_cft cset with
                | Pass(_, cset) ->
                    // constrain if return to true branch in t_cft
                    match build_cset expected t_expr t_cft cset with
                    | Pass(_, cset) -> 
                        // constrain if return to false branch in f_cft
                        match build_cset expected f_expr f_cft cset with
                        | Pass(_, cset) -> Pass(expected, cset)
                        | x -> x
                    | x -> x
                | _ ->
                    // constrain if return to true branch in cft
                    match build_cset expected t_expr cft cset with
                    | Pass(_, cset) -> Pass(expected, cset)
                    | x -> x
        | _ ->
            // constrain test to True|False in t_cft
            match build_cset (Union(Set.ofList [True; False])) test t_cft cset with
            | Pass(_, cset) ->
                // constrain test to False in f_cft
                match build_cset False test f_cft cset with
                | Pass(_, cset) ->
                    // constrain if return to true branch in t_cft
                    match build_cset expected t_expr t_cft cset with
                    | Pass(_, cset) -> 
                        // constrain if return to false branch in f_cft
                        match build_cset expected f_expr f_cft cset with
                        | Pass(_, cset) -> Pass(expected, cset)
                        | x -> x
                    | x -> x
                | _ ->
                    // constrain test to True|False in f_cft
                    match build_cset (Union(Set.ofList [True; False])) test f_cft cset with
                    | Pass(_, cset) ->
                        // constrain if return to true branch in t_cft
                        match build_cset expected t_expr t_cft cset with
                        | Pass(_, cset) -> 
                            // constrain if return to false branch in f_cft
                            match build_cset expected f_expr f_cft cset with
                            | Pass(_, cset) -> Pass(expected, cset)
                            | x -> x
                        | x -> x
                    | _ ->
                        // constrain if return to true branch in cft
                        match build_cset expected t_expr cft cset with
                        | Pass(_, cset) -> Pass(expected, cset)
                        | x -> x
            | _ ->
                // constrain test to False in f_cft
                match build_cset False test f_cft cset with
                | Pass(_, cset) ->
                    // constrain if return to false branch in cft
                    match build_cset expected f_expr cft cset with
                    | Pass(_, cset) -> Pass(expected, cset)
                    | x -> x
                | _ ->
                    // constrain test to True|False in f_cft
                    match build_cset (Union(Set.ofList [True; False])) f_expr f_cft cset with
                    | Pass(_, cset) ->
                        // constrain if return to false branch in cft
                        match build_cset expected f_expr cft cset with
                        | Pass(_, cset) -> Pass(expected, cset)
                        | x -> x
                    | x -> x


let fold_type_constants (cset : Map<string, Type>) : Map<string, Type> =
    
    let rec contains_vars = function
        | TypeId(id')      -> Map.containsKey id' cset
        | List(t) | Not(t) -> contains_vars t
        | Func(os)         -> Set.exists (fun (pt, ot) -> contains_vars pt || contains_vars ot) os
        | Union(ts)        -> Set.exists contains_vars ts
        | _                -> false
    
    let rec folder lookup to_fold =
    
        let rec fold_constraint lookup = function
            | TypeId(id) -> Map.tryFind id lookup
            | List(t) ->
                match fold_constraint lookup t with
                | Some(t') -> Some(List(t'))
                | None -> None
            | Not(t) ->
                match fold_constraint lookup t with
                | Some(t') -> Some(Not(t'))
                | None -> None
            | Func(os) ->
                let rec fold_os folded os' = function
                    | (param_type, body_type)::os'' ->
                        match fold_constraint lookup param_type with
                        | Some(p) ->
                            match fold_constraint lookup body_type with
                            | Some(t) -> fold_os true (oset_add (p, t) os') os''
                            | None -> fold_os true (oset_add (p, body_type) os') os''
                        | None ->
                            match fold_constraint lookup body_type with
                            | Some(t) -> fold_os true (oset_add (param_type, t) os') os''
                            | None -> fold_os false (oset_add (param_type, body_type) os') os''
                    | [] -> if folded then Some(os') else None
                match fold_os false Set.empty <| Set.toList os with
                | Some(os') -> Some(Func(os'))
                | None -> None
            | Union(ts) ->
                let ts_folder (folded, s) t =
                    match fold_constraint lookup t with
                    | Some(t') -> true, uset_add t' s
                    | None -> folded, uset_add t s
                match Set.fold ts_folder (false, Set.empty) ts with
                | true, ts' -> Some(Union(ts'))
                | false, _ -> None
            | _ -> None

        let rec fold_all again lookup a = function
            | (id, t)::cs ->
                match fold_constraint lookup t with
                | Some(t') -> fold_all true lookup (cmap_add id t' a) cs
                | None     -> fold_all again lookup (cmap_add id t a) cs
            | [] -> 
                if again then
                    let to_fold', lookup' = Map.partition (fun _ -> contains_vars) a
                    let lookup'' = Map.foldBack Map.add lookup' lookup
                    folder lookup'' <| Map.toList to_fold'
                else
                    Map.foldBack Map.add a lookup
                        
        fold_all false lookup Map.empty to_fold

    let to_fold, lookup = Map.partition (fun _ -> contains_vars) cset
    
    folder lookup <| Map.toList to_fold


let constrain_undefined_ids (cft : ControlFlowTree) (map : Map<string, Type>) : Map<string, Type> =
    let rec find_undefined_ids (undef_set, all_ids) = function
        | Leaf(leaf_map) ->
            let folder (undef_set, all_map) poly_id type_id =
                // does the current binding have a definition?
                if Map.containsKey type_id map then
                    // keep it in the cft, add it to the all_map
                    match Map.tryFind poly_id all_map with
                    | Some(ids) -> undef_set, Map.add poly_id (type_id::ids) all_map
                    | None -> undef_set, Map.add poly_id [type_id] all_map
                else
                    // remove from cft, don't add to all_map
                    Set.add type_id undef_set, all_map
            Map.fold folder (undef_set, all_ids) leaf_map
        | Branch(trees) ->
            List.fold find_undefined_ids (undef_set, all_ids) trees
    
    let undef_set, all_ids = find_undefined_ids (Set.empty, Map.empty) cft

    let rec update_cfts map = function
        | Leaf(leaf_map) ->
            let folder map' poly_id type_id =
                if Set.contains type_id undef_set then
                    match Map.tryFind poly_id all_ids with
                    | Some(ids) -> Map.add type_id (Union(Set.ofList <| List.map TypeId ids)) map'
                    | None      -> map'
                else
                    map'
            Map.fold folder map leaf_map
        | Branch(trees) ->
            List.fold update_cfts map trees

    update_cfts map cft


let rec collapse_cft (cft : ControlFlowTree) (cmap : Map<string, Type>) (t : Type) : Type =
    
    let lookup id map =
        let id' = Map.find id map
        match Map.tryFind id' cmap with
        | Some(t') -> t'
        | None -> TypeId(id')
    
    let rec cft_lookup id = function
        | Leaf(map) -> lookup id map
        | Branch(trees) -> make_union <| List.fold (fun a t -> (cft_lookup id t)::a) [] trees

    match t with
    | PolyType(id) -> cft_lookup id cft
    | List(t') -> List(collapse_cft cft cmap t')
    | Not(t') -> Not(collapse_cft cft cmap t')
    | Union(uset) -> make_union <| Seq.toList (Seq.map (fun t -> collapse_cft cft cmap t) uset)

    | Func(oset) ->
        let rec overload_func oset' = function
            | Leaf(_) as cft ->
                let rec collapse_overloads oset'' = function
                    | (arg, rtn)::oset''' -> 
                        let oset = oset_add (collapse_cft cft cmap arg, collapse_cft cft cmap rtn) oset''
                        collapse_overloads oset oset'''
                    | [] -> oset''
                collapse_overloads oset' <| Set.toList oset
            | Branch(trees) ->
                List.fold overload_func oset' trees
        Func(overload_func Set.empty cft)
    
    | x -> x


let cft2str cft =
    let i = ref -1
    let rec cft2str = function
        | Leaf(map) -> 
            i := !i + 1;
            String.concat "\n" <| Seq.map (fun (p_id, t_id) -> sprintf "%s = %s[%d]" t_id p_id !i) (Map.toSeq map)
        | Branch(trees) -> String.concat "\n\n====================\n\n" <| List.map cft2str trees
    cft2str cft


let type_check expr =
    guesses <- guess_maker().GetEnumerator();
    let result_id = fresh_var()
    let (cft, cte) = build_cft result_id expr
    let cft_str = cft2str cft
    let t = PolyType(result_id)
    match build_cset t cte cft Map.empty with
    | Pass(t', cset) ->
        let set_str = cset2str cset
        //printfn "%s" set_str;
        let merged_map = cset //merge_duplicate_rules cset
        //let set_str' = cset2str merged_map
        let unfolded_map = constrain_undefined_ids cft merged_map
        let set_set'' = cset2str unfolded_map
        let diff = cset2str <| Map.filter (fun id _ -> not <| Map.containsKey id merged_map) unfolded_map
        let map = fold_type_constants unfolded_map
        let set_str''' = cset2str map
        collapse_cft cft map t
    | Fail(t1, t2) -> failwith <| sprintf "Unification Error: %s %s" (type2str t1) (type2str t2)
