module DynamicStatic.DS

open DynamicStatic.Type
open DynamicStatic.ConstraintSet
open DynamicStatic.Expression


let guess_maker() =
    let rec numbers_from n =
        seq { yield n; yield! numbers_from (n+1) }
    seq { for n in numbers_from 0 -> sprintf "_%i_temp_" n }


let mutable private guesses = guess_maker().GetEnumerator()
let fresh_var() =
    ignore <| guesses.MoveNext();
    guesses.Current


type ConstructionResult =
    | Pass of (Type * ConstraintSet) list
    | Fail of Type * Type

let rec build_cset (expected : Type) 
                   (env : Environment)
                   (cset : ConstraintSet)
                   (expr : Expression)
                   : ConstructionResult =
    
    let constrain t =
        match unify generalize_rule t expected Map.empty with
        | Success(cset) -> Pass([t, cset])
        | Failure(t1, t2) -> Fail(t1, t2)
    
    match expr with

    | Number(_) | String(_) -> constrain Atom

    | Bool(b) -> constrain <| if b then True else False

    | Id(id) -> 
        match Map.tryFind id env with
        | Some(t) -> constrain t
        | None -> failwith "Unbound identifier"

    | Let(id, expr, body_expr) -> build_cset expected env cset <| Call(Fun(id, body_expr), expr) 

    | Fun(param_name, body_expr) ->
        let param_tvar = TypeId(fresh_var())
        let rtn_tvar = TypeId(fresh_var())
        match build_cset rtn_tvar (Map.add param_name param_tvar env) cset body_expr with
        | Pass(branches) ->
            // X = lookup param_name in all csets
            // Y = return type for each branch
            // (X1 -> Y1, X2 -> Y2, etc.)
            // constrain that against expected
            failwith "TODO: build_cset.Fun"
        | x -> x
        
    | Call(func_expr, arg_expr) ->
        
        let arg_tvar = TypeId(fresh_var())

        // step 1: build func_expr cset
        //      expected' = arg_tvar -> expected

        // step 2: for each result of the func building...
        //      confirm it's either a TypeId or a Func, since those are the only things that are callable
        //      turn into a single overloaded function
        //          TypeIds should be replaced with expected'(?)

        // step 3: build arg_expr cset
        //      expected'' = arg_tvar

        // step 4: 
        //  for each result of the arg building...
        //      constrain against all funcs separately
        //          skip failures
        //          if there are no successes, then fail

        failwith "TODO: build_cset.Call"

        (*
        match build_cset arg_tvar env arg_expr with
        | Pass(branches) ->
            // merge all branches(?)
            //   branches = [(X1, cset1); (X2, cset2); ...]
            //   merged = ({X1|X2|...|Xn}, same for cset rules)

            let func_expected = Func(Set.ofList [ arg_tvar, expected ])


        | x -> x
        *)

    | Begin(exprs) ->
        let rec begin_exprs cset' = function
            | []           -> Pass([ Unit, cset' ])
            | [expr']      -> build_cset expected env cset' expr'
            | expr'::exprs -> 
                match build_cset Any env cset' expr' with
                | Pass(branches) -> 
                    //TODO: drop return types, merge all branches
                    let cset'' = failwith "TODO: build_cset.Begin"
                    begin_exprs cset'' exprs
                | x -> x
        begin_exprs cset exprs

    | If(test, t_expr, f_expr) ->
        
        // constrain test to True in t_cft
            // constrain test to False in f_cft
                // constrain if return to true branch in t_cft
                    // constrain if return to false branch in f_cft
                // constrain test to True|False in f_cft
                    // constrain if return to true branch in t_cft
                        // constrain if return to false branch in f_cft
                    // constrain if return to true branch in cft
            // constrain test to True|False in t_cft
                // constrain test to False in f_cft
                    // constrain if return to true branch in t_cft
                        // constrain if return to false branch in f_cft
                    // constrain test to True|False in f_cft
                        // constrain if return to true branch in t_cft
                            // constrain if return to false branch in f_cft
                        // constrain if return to true branch in cft
                // constrain test to False in f_cft
                    // constrain if return to false branch in cft
                    // constrain test to True|False in f_cft
                        // constrain if return to false branch in cft
        
        failwith "TODO: build_cset.If"

///Replaces all instances of type variables with their constraints
let fold_type_constants (cset : Map<string, Type>) : Map<string, Type> =
    
    ///Does the given type contain constrained type variables?
    let rec contains_vars id = function
        | TypeId(id') when id <> id' -> 
            match Map.tryFind id' cset with
            | None -> false
            | Some(t) -> not <| contains_id id' t
        | List(t) | Not(t) -> contains_vars id t
        | Func(os)         -> Set.exists (fun (pt, ot) -> contains_vars id pt || contains_vars id ot) os
        | Union(ts)        -> Set.exists (contains_vars id) ts
        | _                -> false
    
    let rec folder lookup to_fold =
    
        ///Given a type and a lookup map, replaces all type variables with value stored in lookup
        let rec fold_constraint lookup = function
            | TypeId(id) -> 
                match Map.tryFind id lookup with
                | Some(t') -> 
                    if contains_id id t' then 
                        None 
                    else 
                        Some(t')
                | None -> None
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
                            | None -> fold_os folded (oset_add (param_type, body_type) os') os''
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
                    let to_fold', lookup' = Map.partition contains_vars a
                    let lookup'' = Map.foldBack Map.add lookup lookup'
                    folder lookup'' <| Map.toList to_fold'
                else
                    Map.foldBack Map.add a lookup
                        
        fold_all false lookup Map.empty to_fold

    let to_fold, lookup = Map.partition contains_vars cset
    folder lookup <| Map.toList to_fold


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
