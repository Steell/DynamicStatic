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

let build_cft (expr : TypeExpression) : ControlFlowTree * ControlTypeExpression =
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
                    Set.fold (fun stack' (param_type, return_type) -> gather_ids (gather_ids stack' param_type) return_type) 
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
            CFun(param_name, c_body), cft', stack'
        
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

            let return_id = fresh_var()
            CIf(c_test, (t_idx, c_t_expr), (f_idx, c_f_expr), return_id),  cft''', return_id::stack'

    let cte, cft, stack = build_cft expr empty_cft []
    cft_add_stack cft stack, cte

let rec constrain (cft : ControlFlowTree) (cset : Set<Constraint>) (sub_type : Type) (super_type : Type) : UnificationResult =
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

let rec build_cset ((expr : ControlTypeExpression), (cft : ControlFlowTree)) (cset : Set<Constraint>) : (Type * Set<Constraint>) =
    let rec build_exprs cft' cset' a = function
        | expr::exprs ->
            let cte, cset'' = build_cset (expr, cft') cset'
            build_exprs cft' cset'' (cte::a) exprs
        | [] ->  List.rev a, cset'
    match expr with
    | CAtom_E -> Atom, cset
    | CType_E(t) -> t, cset
    | CLet(ids, exprs, body_expr) ->
        let expr_types, cset' = build_exprs cft cset [] exprs
        let rec constrain_all cset'' = function
            | (t1, t2)::xs -> 
                match constrain cft cset'' t1 t2 with
                | Success(cset''') -> constrain_all cset''' xs
                | x -> x
            | [] -> Success(cset'')
        match constrain_all cset' <| List.zip (List.map PolyType ids) expr_types with
        | Success(cset'') -> build_cset (body_expr, cft) cset''
        | Failure(t1, t2) -> failwith "Unification Failure (build_cset.Let)."
    | CFun(param_name, body_expr) ->
        let body_type, cset' = build_cset (body_expr, cft) cset
        Func(Set.ofList [PolyType(param_name), body_type]), cset'
    | CCall(func_expr, arg_expr, return_id) ->
        let func_type, cset' = build_cset (func_expr, cft) cset
        let arg_type, cset'' = build_cset (arg_expr, cft) cset'

        (*match func_type with
        | Func(os) ->
            let rec constrain_os cset''' rtn_set = function
                | (arg_type', rtn)::os' ->
                    match constrain cft cset'' arg_type arg_type' with
                    | Success(cset'''') -> constrain_os cset'''' (uset_add rtn rtn_set) os'
                    | _ -> constrain_os cset''' rtn_set os'
                | [] -> 
                    if rtn_set.IsEmpty then
                        failwith "Unification failure (build_cset.Call) Could not constrain function call types."
                    else if rtn_set.Count = 1 then
                        rtn_set.MinimumElement, cset'''
                    else
                        Union(rtn_set), cset'''
            constrain_os cset'' Set.empty <| Set.toList os
                        
        | _ ->*)

        let func = Func(*oset_add (arg_type, PolyType(return_id)) Set.empty*)(Set.ofList [arg_type, PolyType(return_id)])
        match constrain cft cset'' func func_type with
        | Success(cset''') -> PolyType(return_id), cset'''
        | Failure(t1, t2) -> failwith "Unification failure (build_cset.Call) Could not constrain function call types."

    | CBegin(exprs) ->
        let rec begin_exprs cset' = function
            | []           -> Unit, cset'
            | [expr']      -> build_cset (expr', cft) cset'
            | expr'::exprs -> 
                let _, cset'' = build_cset (expr', cft) cset'
                begin_exprs cset'' exprs
        begin_exprs cset exprs
    | CIf(test, (t_idx, t_expr), (f_idx, f_expr), return_id) ->
        let test_type, cset = build_cset (test, cft) cset
        let t_cft = cft_branch t_idx cft
        let f_cft = cft_branch f_idx cft

        // constrain test to True in t_cft
        match constrain t_cft cset test_type True with
        | Success(cset) -> 
            // constrain test to False in f_cft
            match constrain f_cft cset test_type False with
            | Success(cset) ->
                let true_type, cset = build_cset (t_expr, t_cft) cset
                let false_type, cset = build_cset (f_expr, f_cft) cset
                // constrain if return to true branch in t_cft
                match constrain t_cft cset (PolyType(return_id)) true_type with
                | Success(cset) -> 
                    // constrain if return to false branch in f_cft
                    match constrain f_cft cset (PolyType(return_id)) false_type with
                    | Success(cset) -> PolyType(return_id), cset
                    | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) False CFT could not be constrained to if return type"
                | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) True CFT could not be constrained to if return type"
            | Failure(t1, t2) ->
                // constrain test to True|False in f_cft
                match constrain f_cft cset test_type <| Union(Set.ofList [True; False]) with
                | Success(cset) ->
                    let true_type, cset = build_cset (t_expr, t_cft) cset
                    let false_type, cset = build_cset (f_expr, f_cft) cset
                    // constrain if return to true branch in t_cft
                    match constrain t_cft cset (PolyType(return_id)) true_type with
                    | Success(cset) -> 
                        // constrain if return to false branch in f_cft
                        match constrain f_cft cset (PolyType(return_id)) false_type with
                        | Success(cset) -> PolyType(return_id), cset
                        | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) False CFT could not be constrained to if return type"
                    | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) True CFT could not be constrained to if return type"
                | Failure(t1, t2) ->
                    // constrain if return to true branch in cft
                    let true_type, cset = build_cset (t_expr, t_cft) cset
                    match constrain cft cset (PolyType(return_id)) true_type with
                    | Success(cset) -> PolyType(return_id), cset
                    | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) True CFT could not be constrained to if return type"
        | Failure(t1, t2) ->
            // constrain test to True|False in t_cft
            match constrain t_cft cset test_type <| Union(Set.ofList [True; False]) with
            | Success(cset) ->
                // constrain test to False in f_cft
                match constrain f_cft cset test_type False with
                | Success(cset) ->
                    let true_type, cset = build_cset (t_expr, t_cft) cset
                    let false_type, cset = build_cset (f_expr, f_cft) cset
                    // constrain if return to true branch in t_cft
                    match constrain t_cft cset (PolyType(return_id)) true_type with
                    | Success(cset) -> 
                        // constrain if return to false branch in f_cft
                        match constrain f_cft cset (PolyType(return_id)) false_type with
                        | Success(cset) -> PolyType(return_id), cset
                        | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) False CFT could not be constrained to if return type"
                    | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) True CFT could not be constrained to if return type"
                | Failure(t1, t2) ->
                    // constrain test to True|False in f_cft
                    match constrain f_cft cset test_type <| Union(Set.ofList [True; False]) with
                    | Success(cset) ->
                        let true_type, cset = build_cset (t_expr, t_cft) cset
                        let false_type, cset = build_cset (f_expr, f_cft) cset
                        // constrain if return to true branch in t_cft
                        match constrain t_cft cset (PolyType(return_id)) true_type with
                        | Success(cset) -> 
                            // constrain if return to false branch in f_cft
                            match constrain f_cft cset (PolyType(return_id)) false_type with
                            | Success(cset) -> PolyType(return_id), cset
                            | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) False CFT could not be constrained to if return type"
                        | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) True CFT could not be constrained to if return type"
                    | Failure(t1, t2) ->
                        // constrain if return to true branch in cft
                        let true_type, cset = build_cset (t_expr, t_cft) cset
                        match constrain cft cset (PolyType(return_id)) true_type with
                        | Success(cset) -> PolyType(return_id), cset
                        | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) True CFT could not be constrained to if return type"
            | Failure(t1, t2) ->
                // constrain test to False in f_cft
                match constrain f_cft cset test_type False with
                | Success(cset) ->
                    // constrain if return to false branch in cft
                    let false_type, cset = build_cset (f_expr, f_cft) cset
                    match constrain cft cset (PolyType(return_id)) false_type with
                    | Success(cset) -> PolyType(return_id), cset
                    | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) False CFT could not be constrained to if return type"
                | Failure(t1, t2) ->
                    // constrain test to True|False in f_cft
                    match constrain f_cft cset test_type <| Union(Set.ofList [True; False]) with
                    | Success(cset) ->
                        // constrain if return to false branch in cft
                        let false_type, cset = build_cset (f_expr, f_cft) cset
                        match constrain cft cset (PolyType(return_id)) false_type with
                        | Success(cset) -> PolyType(return_id), cset
                        | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) False CFT could not be constrained to if return type"
                    | Failure(t1, t2) -> failwith "Unification Failure (build_vset.If) Test could not be constrained to True|False"

let merge_duplicate_rules (cset : Set<Constraint>) : Map<string, Type> =
    let merge_types cset' t1 t2 =
        let unify' = unify <| fun cset'' id t -> Failure(TypeId(id), t) //Success(cset_add (id, t) cset'')
        let merge_types' cset' t1 t2 =
            let cset' = Set.ofList cset'
            match unify' t1 t2 cset' with
            | Success(cset'') -> Some(t1, Set.toList cset'')
            | Failure(_, _) ->
                match unify' t2 t1 cset' with
                | Success(cset'') -> Some(t2, Set.toList cset'')
                | Failure(_, _) -> None
        match (t1, t2) with
        | TypeId(id1), TypeId(id2) when id1 <> id2 -> Some(t1, (id2, t1)::cset')
        | _, TypeId(_) -> merge_types' cset' t2 t1
        | _            -> merge_types' cset' t1 t2
        
    let rec merge_all map = function
        | (id, t)::cset' ->
            match Map.tryFind id map with
            | Some(t') ->
                match merge_types cset' t' t with
                | Some(t'', cset'') -> merge_all (cmap_add id t'' map) cset''
                | None -> failwith "Could not merge types."
            | None -> merge_all (cmap_add id t map) cset'
        | [] -> map
    merge_all Map.empty <| Set.toList cset


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
    let (cft, cte) = build_cft expr
    let cft_str = cft2str cft
    let t, cset = build_cset (cte, cft) Set.empty
    let set_str = cset2str cset
    //printfn "%s" set_str;
    let merged_map = merge_duplicate_rules cset
    let set_str' = cset2str <| Map.toSeq merged_map
    let unfolded_map = constrain_undefined_ids cft merged_map
    let set_set'' = cset2str <| Map.toSeq unfolded_map
    let diff = cset2str (Map.toSeq <| Map.filter (fun id _ -> not <| Map.containsKey id merged_map) unfolded_map)
    let map = fold_type_constants unfolded_map
    let set_str''' = cset2str <| Map.toSeq map
    collapse_cft cft map t
