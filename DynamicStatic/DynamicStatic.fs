module DynamicStatic

let guess_maker() =
    let rec numbers_from n =
        seq { yield n; yield! numbers_from (n+1) }
    seq { for n in numbers_from 0 -> sprintf "%i_temp_" n }

let guesses = guess_maker().GetEnumerator()
let fresh_var() =
    ignore <| guesses.MoveNext();
    guesses.Current


type Type =
    | Any
    | Atom 
    | Unit
    | True | False 
    | TypeId of string   // only used in CFT and CSet
    | PolyType of string // one can map to several TypeIds, each in a different execution path
    | List of Type
    | Func of Set<Overload>
    | Union of Set<Type>

and Overload = Type * Type
       
let rec type2str = function
    | Any -> "Any"
    | Atom -> "Atom"
    | Unit -> "IO"
    | True -> "True"
    | False -> "False"
    | TypeId(id) -> sprintf "'%s" id
    | PolyType(id) -> sprintf "Poly(%s)" id
    | List(t) -> sprintf "List<%s>" <| type2str t
    | Func(os) when os.Count = 1 -> overload2str os.MinimumElement
    | Func(os) -> sprintf "(%s)" <| String.concat "+" (Seq.map overload2str os)
    | Union(ts) -> String.concat "|" <| Seq.map type2str ts

and overload2str (ps, r) = 
    sprintf "(%s -> %s)" (type2str ps) (type2str r)

type Constraint = string * Type

let constraint_is_reflexive (id, rule) =
    match rule with
    | TypeId(id') when id = id' -> true
    | _ -> false

let cset_add constrnt cset =
    if constraint_is_reflexive constrnt then
        cset
    else
        Set.add constrnt cset

let cmap_add id rule cmap =
    if constraint_is_reflexive (id, rule) then
        cmap
    else
        Map.add id rule cmap

let rec union sub super =
    let rec all_union super = function
        | sub::ts -> union sub super && all_union super ts
        | [] -> true
    let rec unions_with_any sub = function
        | super::ts -> union sub super || unions_with_any sub ts
        | [] -> false
    match sub, super with
    | _, Any | Func(_), Atom -> true

    | PolyType(id), _ | _, PolyType(id) -> failwith "Illegal PolyType(%s) found in constraint set." id

    | TypeId(id), _          -> false
    | _,          TypeId(id) -> true

    | List(sub'), List(super') -> union sub' super'
    
    //A|B := A|B|C
    | Union(subs), _             -> all_union super <| Set.toList subs
    | _,           Union(supers) -> unions_with_any sub <| Set.toList supers
    
    | Func(sub_os'), Func(super_os') -> 
        // Unification successful if everything in super_os' unifies with something in sub_os'
        let rec any_union super' = function
            | sub'::os -> union_overload sub' super' || any_union super' os
            | [] -> false
        let rec unions_with_all sub_os'' = function
            | super'::os -> any_union super' sub_os'' && unions_with_all sub_os'' os
            | [] -> true
        unions_with_all (Set.toList sub_os') (Set.toList super_os')
    
    | sub', super' when sub' = super' -> true
    | _,    _                         -> false

and union_overload (sub_arg, sub_return) (super_arg, super_return) =
    union super_arg sub_arg && union sub_return super_return

let rec uset_add t uset = 
    
    let rec add set t = function
        | t'::ts -> 
            match t, t' with
            | Func(os1), Func(os2) -> 
                let t'' = Func(Set.foldBack oset_add os1 os2)
                Set.union set <| Set.ofList (t''::ts)
            | _ ->
                if union t' t then
                    Set.union set <| Set.ofList (t'::ts)
                else if union t t' then
                    add (Set.add t set) t ts
                else
                    add (Set.add t' set) t ts
        | [] -> set
    match t with
    | Union(ts) -> Seq.fold (fun a t -> uset_add t a) uset ts
    | _ -> add Set.empty t <| Set.toList uset

and oset_add overload oset : Set<Overload> =
    
    let combine_overloads o1 o2 =
        let sub_param, sub_return = o1
        let super_param, super_return = o2
        let make_union t1 t2 = Union(uset_add t2 <| uset_add t1 Set.empty)
        if sub_param = super_param then
             // if returns are functions make sure they are combined into a single overloaded function
            Some(sub_param, make_union sub_return super_return)
        else if sub_return = super_return then
            Some(make_union sub_param super_param, sub_return)
        else if union_overload o1 o2 then
            Some(o1)
        else if union_overload o2 o1 then
            Some(o2)
        else
            None

    let rec add set o = function
        | o' :: os ->
            match combine_overloads o o' with
            | Some(o'') -> Set.add o'' set
            | None -> add (Set.add o' set) o os
        | [] -> Set.add o set

    add Set.empty overload <| Set.toList oset

type ControlFlowTree = 
    | Leaf of Map<string, string> 
    | Branch of ControlFlowTree list

let rec cft_add (id : string) = function
    | Leaf(map) -> Leaf(Map.add id (fresh_var()) map)
    | Branch(trees) -> Branch(List.map (cft_add id) trees)

let cft_add_branch (to_add : ControlFlowTree) = function
    | Leaf(_) -> 0, Branch([to_add])
    | Branch(trees) -> trees.Length, Branch(trees@[to_add])

let cft_branch idx = function
    | Leaf(_) -> failwith "Can't get a branch from a leaf."
    | Branch(trees) -> trees.Item idx

let empty_cft = Leaf(Map.empty)

let cft_map_lookup map =
    let rec lookup = function
        | PolyType(id) -> 
            match Map.tryFind id map with
            | Some(id') -> Some(TypeId(id'))
            | None -> None
        | List(t) -> 
            match lookup t with
            | Some(t') -> Some(List(t'))
            | None -> None
        | Func(os) ->
            let overload_lookup (parameter, return_type) = function
                | Some(os) -> 
                    match lookup parameter with
                    | Some(ps) ->
                        match lookup return_type with
                        | Some(r) -> Some(oset_add (ps, r) os)
                        | None -> None
                    | None -> None
                | None -> None               
            match Set.foldBack overload_lookup os <| Some(Set.empty) with
            | Some(os) -> Some(Func(os))
            | None -> None
        | Union(ts) ->
            match lookup_all <| Set.toList ts with
            | Some(ts') -> Some(Union(Set.ofList ts'))
            | None -> None
        | x -> Some(x)
    and lookup_all ts =
        List.foldBack 
            (fun t -> function 
                | Some(ts) -> 
                    match lookup t with
                    | Some(t') -> Some(t'::ts)
                    | None -> None
                | None -> None)
            ts
            (Some([]))
    lookup

type ControlTypeExpression = (int * CTE)
and CTE =
    | CAtom_E
    | CType_E of Type
    | CLet of string list * CTE list * CTE
    | CFun of string * CTE
    | CCall of CTE * CTE * string
    | CIf of CTE * ControlTypeExpression * ControlTypeExpression * string
    | CBegin of CTE list

///AST for FScheme expressions
type TypeExpression =
    | Atom_E
    | Type_E of Type
    | Let of string list * TypeExpression list * TypeExpression
    | Fun of string * TypeExpression
    | Call of TypeExpression * TypeExpression
    | If of TypeExpression * TypeExpression * TypeExpression
    | Begin of TypeExpression list

let generalize_rule cset id t =
    let rec generalize_type cset = function
        | PolyType(id) -> failwith "Illegal PolyType(%s) found in constraint set." id

        | TypeId(id') ->
            let id'' = fresh_var()
            let t' = TypeId(id'')
            t', cset_add (id', t') cset

        | List(t) ->
            let t', cset' = generalize_type cset t
            List(t'), cset'

        | Union(ts) ->
            let union_folder (ts', cset') t =
                let t', cset'' = generalize_type cset' t
                Set.add t' ts', cset''
            let ts', cset' = Set.fold union_folder (Set.empty, cset) ts
            Union(ts'), cset'

        | Func(os) ->
            let overload_folder (os', cset') (param_type, return_type) =
                let param_type', cset'' = generalize_type cset' param_type
                let return_type', cset''' = generalize_type cset'' return_type
                Set.add (param_type', return_type) os', cset'''
            let os', cset' = Set.fold overload_folder (Set.empty, cset) os
            Func(os'), cset'

        | t -> t, cset

    let t', cset' = generalize_type cset t
    cset_add (id, t') cset'
    
type UnificationResult =
    | Success of Set<Constraint>
    | Failure of Type * Type

let rec unify (sub : Type) (super : Type) (cset: Set<Constraint>) : UnificationResult = 
    let rec all_unify cset' super = function
        | sub::ts -> 
            match unify sub super cset' with
            | Success(cset'') -> all_unify cset'' super ts
            | failure -> Some(failure), cset'
        | [] -> None, cset'
    let rec unifies_with_any cset' sub = function
        | super::ts ->
            match unify sub super cset' with
            | Success(_) as s -> Some(s)
            | Failure(_, _) -> unifies_with_any cset' sub ts
        | [] -> None
    match sub, super with
    | _, Any | Func(_), Atom -> Success(cset)

    | PolyType(id), _ | _, PolyType(id) -> failwith "Illegal PolyType(%s) found in constraint set." id

    | TypeId(id), _          -> Success(cset_add (id, super) cset)
    | _,          TypeId(id) -> Success(generalize_rule cset id sub)

    | List(sub'), List(super') -> unify sub' super' cset
    
    | Union(subs), _ -> 
        match all_unify cset super <| Set.toList subs with 
        | Some(failure), _ -> failure 
        | None, cset'      -> Success(cset')

    | _, Union(supers) -> 
        match unifies_with_any cset sub <| Set.toList supers with
        | Some(success) -> success
        | None          -> Failure(sub, super)
    
    | Func(sub_os'), Func(super_os') -> 
        // Unification successful if everything in super_os' unifies with something in sub_os'
        let unify_overload (sub_arg, sub_return) (super_arg, super_return) cset' =
            match unify super_arg sub_arg cset' with
            | Success(cset'') ->
                match unify sub_return super_return cset'' with
                | Success(cset''') -> Some(cset''')
                | _ -> None
            | _ -> None
        ///all super overloads are satisfied by some sub overload?
        let rec unify_subs_against_supers cset' sub_os'' (super_os'' : Set<Type * Type>) =
            match sub_os'' with
            | sub'::os when super_os''.Count > 0 ->
                ///collect all super overloads that the sub overload unifies with
                let rec unify_with_all (cset'', a) sub' = function
                    | super'::os ->
                        match unify_overload sub' super' cset'' with
                        | None -> unify_with_all (cset'', a) super' os
                        | Some(cset''') -> unify_with_all (cset''', Set.add super' a)  super' os
                    | [] -> (cset'', a)
                let cset'', unified = unify_with_all (cset', Set.empty) sub' <| Set.toList super_os''
                let remaining_supers = Set.difference super_os'' unified
                unify_subs_against_supers cset'' os remaining_supers
            | _ -> Success(cset')
        unify_subs_against_supers cset (Set.toList sub_os') super_os'
    
    | sub', super' when sub' = super' -> Success(cset)
    | _,    _                         -> Failure(sub, super)

let build_cft (expr : TypeExpression) : ControlFlowTree * CTE =
    let cft_add_stack cft stack = List.foldBack cft_add stack cft
    let rec build_cft (expr : TypeExpression) (cft : ControlFlowTree) (stack : string list) : (CTE * ControlFlowTree * string list) =
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
                | List(t) -> gather_ids stack t
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
                unify cft_subtype cft_supertype cset'
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

let rec build_cset ((expr : CTE), (cft : ControlFlowTree)) (cset : Set<Constraint>) : (Type * Set<Constraint>) =
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
        overload_function cft (param_name, body_type), cset'
    | CCall(func_expr, arg_expr, return_id) ->
        let func_type, cset' = build_cset (func_expr, cft) cset
        let arg_type, cset'' = build_cset (arg_expr, cft) cset'
        let func = Func(Set.ofList [arg_type, PolyType(return_id)])
        match constrain cft cset'' func func_type with
        | Success(cset''') -> PolyType(return_id), cset'''
        | Failure(t1, t2) -> failwith "Unification Failure (build_cset.Call) Could not constrain function call types."
    | CBegin(exprs) ->
        let rec begin_exprs cset' = function
            | []           -> Unit, cset'
            | [expr']      -> build_cset (expr', cft) cset'
            | expr'::exprs -> 
                let _, cset'' = build_cset (expr', cft) cset'
                begin_exprs cset'' exprs
        begin_exprs cset exprs
    | CIf(test, (t_idx, t_expr), (f_idx, f_expr), return_id) ->
        let test_type, cset' = build_cset (test, cft) cset
        let t_cft = cft_branch t_idx cft
        let f_cft = cft_branch f_idx cft
        match constrain t_cft cset' test_type True with
        // test type is True
        | Success(cset'') -> 
            let true_type, cset''' = build_cset (t_expr, t_cft) cset''
            match constrain t_cft cset''' true_type <| PolyType(return_id) with
            // true type unified with return type
            | Success(cset'''') -> 
                match constrain cft cset''' test_type <| Union(Set.ofList [True; False]) with
                // test type is True|False
                | Success(cset''''') -> 
                    let false_type, cset'''''' = build_cset (f_expr, f_cft) cset'''''
                    match constrain f_cft cset'''''' false_type <| PolyType(return_id) with
                    // false type unified with return type
                    | Success(cset''''''') -> PolyType(return_id), cset'''''''
                    // error
                    | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) False CFT could not be constrained to if return type"
                // test type is ONLY True
                | Failure(t1, t2) -> true_type, cset''''
            // error
            | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) True CFT could not be constrained to if return type"
        // test type is not True
        | Failure(t1, t2) ->
            match constrain f_cft cset' test_type False with
            // test type is False
            | Success(cset'') -> 
                let false_type, cset''' = build_cset (f_expr, f_cft) cset''
                match constrain f_cft cset''' false_type <| PolyType(return_id) with
                // false type unified with return type
                | Success(cset'''') -> 
                    match constrain cft cset'''' test_type <| Union(Set.ofList [True; False]) with
                    // Test type is True|False
                    | Success(cset'') -> 
                        let true_type, cset''' = build_cset (t_expr, t_cft) cset''
                        match constrain t_cft cset''' true_type <| PolyType(return_id) with
                        // true type unified with return type
                        | Success(cset'''') -> PolyType(return_id), cset''''
                        // error
                        | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) True CFT could not be constrained to if return type"
                    // test type is ONLY False
                    | Failure(t1, t2) -> false_type, cset''''
                // error
                | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) False CFT could not be constrained to if return type"
            // test type can only be True|False
            | Failure(t1, t2) ->
                match constrain cft cset' test_type <| Union(Set.ofList [True; False]) with
                // Test type is True|False
                | Success(cset'') -> 
                    let true_type, cset''' = build_cset (t_expr, t_cft) cset''
                    match constrain t_cft cset''' true_type <| PolyType(return_id) with
                    // true type unified with return type
                    | Success(cset'''') ->
                        let false_type, cset'''''' = build_cset (f_expr, f_cft) cset''''
                        match constrain f_cft cset'''''' false_type <| PolyType(return_id) with
                        // false type unified with return type
                        | Success(cset''''''') -> PolyType(return_id), cset'''''''
                        // error
                        | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) False CFT could not be constrained to if return type"
                    // error
                    | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) True CFT could not be constrained to if return type"
                // test type is ONLY False
                | Failure(t1, t2) -> failwith "Unification Failure (build_vset.If) Test could not be constrained to True|False"

let merge_duplicate_rules (cset : Set<Constraint>) : Map<string, Type> =
    let merge_types cset' t1 t2 =
        let cset' = Set.ofList cset'
        match unify t1 t2 cset' with
        | Success(cset'') -> Some(t1, Set.toList cset'')
        | Failure(_, _) ->
            match unify t2 t1 cset' with
            | Success(cset'') -> Some(t2, Set.toList cset'')
            | Failure(_, _) -> None
    let rec merge_all map = function
        | (id, t)::cset' ->
            match Map.tryFind id map with
            | Some(t') ->
                match merge_types cset' t t' with
                | Some(t'', cset'') -> merge_all (cmap_add id t'' map) cset''
                | None -> failwith "Could not merge types."
            | None -> merge_all (cmap_add id t map) cset'
        | [] -> map
    merge_all Map.empty <| Set.toList cset

let rec fold_type_constants (cset : Map<string, Type>) : Map<string, Type> =
    let rec is_recursive id type_constraint =
        match type_constraint with
        | TypeId(id') when id = id -> true
        | List(t) -> is_recursive id t
        | Func(os) -> Set.exists (fun (pt, ot) -> is_recursive id pt || is_recursive id ot) os
        | Union(ts) -> Set.exists (is_recursive id) ts
        | _ -> false
    let lookup = Map.filter (fun id t -> not <| is_recursive id t) cset
    let rec fold_constraint id type_constraint = 
        match type_constraint with
        | TypeId(id') when id' <> id -> Map.tryFind id' lookup
        | List(t) ->
            match fold_constraint id t with
            | Some(t') -> Some(List(t'))
            | None -> None
        | Func(os) ->
            let rec fold_os os' = function
                | (param_type, body_type)::os'' ->
                    match fold_constraint id param_type with
                    | Some(p) ->
                        match fold_constraint id body_type with
                        | Some(t) -> fold_os (Set.add (p, t) os') os''
                        | None -> None
                    | None -> None
                | [] -> Some(os')
            match fold_os Set.empty <| Set.toList os with
            | Some(os') -> Some(Func(os'))
            | None -> None
        | Union(ts) ->
            let ts_folder s t =
                match s with
                | Some(ts') ->
                    match fold_constraint id t with
                    | Some(t') -> Some(Set.add t' ts')
                    | None -> None
                | None -> None
            match Set.fold ts_folder (Some(Set.empty)) ts with
            | Some(ts') -> Some(Union(ts'))
            | None -> None
        | _ -> None
    let rec fold_all again cset' = function
        | (id, t)::cs ->
            match fold_constraint id t with
            | Some(t') -> fold_all true cset' <| (id, t')::cs
            | None -> fold_all again (cmap_add id t cset') cs
        | [] -> 
            if again then
                fold_type_constants cset'
            else
                cset'
    fold_all false Map.empty <| Map.toList cset

let collapse_cft (cft : ControlFlowTree) (cset : Map<string, Type>) : Map<string, Type> =
    let rec collapse_map map = function
        | (poly_id, id)::cs -> 
            let t =
                match Map.tryFind id cset with
                | Some(t) -> t
                | None -> TypeId(id)
            let t' =
                match Map.tryFind poly_id map with
                | Some(t') -> Union(List.foldBack uset_add [t; t'] Set.empty)
                | None -> t
            collapse_map (Map.add poly_id t' map) cs
        | [] -> map
        
    let rec collapse map = function
        | Leaf(map') -> collapse_map map <| Map.toList map'
        | Branch(trees) -> List.fold collapse map trees
    collapse Map.empty cft

let type_check expr =
    let (cft, cte) = build_cft expr
    let t, cset = build_cset (cte, cft) Set.empty
    let map = merge_duplicate_rules cset |> fold_type_constants
    let lookup = collapse_cft cft map
    let rec update_type = function
        | PolyType(id) -> Map.find id lookup
        | List(t) -> List(update_type t)
        | Func(os) -> Func(Set.map (fun (p, r) -> update_type p, update_type r) os)
        | Union(ts) -> Union(Set.map update_type ts)
        | x -> x
    update_type t

(*  ;; filter :: A B -> Z
    (define (filter l p)
      (if (empty? l)
          <1> empty
          ;; x :: F
          <2> (let ((x (first l)))
            (if (p x)
                <3> (cons x (filter (rest l) p))
                <4> (filter (rest l) p)))))

    ;; filter :: List<A|B> ((A -> True)+(B -> False)) -> List<A>
*)
let filter = 
    Let(["filter"], 
        [Fun("l", Fun("p", If(Call(Type_E(Func(Set.ofList [List(PolyType("A")), Union(Set.ofList [True; False])])), Type_E(PolyType("l"))), 
                              Type_E(PolyType("M")), 
                              Let(["x"], [Call(Type_E(Func(Set.ofList [List(PolyType("B")), PolyType("B")])), 
                                               Type_E(PolyType("l")))], 
                                If(Call(Type_E(PolyType("p")), 
                                        Type_E(PolyType("x"))), 
                                    Call(Call(Type_E(Func(Set.ofList [PolyType("C"), Func(Set.ofList [List(PolyType("C")), List(PolyType("C"))])])), 
                                              Type_E(PolyType("x"))),
                                        Call(Call(Type_E(PolyType("filter")), 
                                                  Call(Type_E(Func(Set.ofList [List(PolyType("K")), List(PolyType("K"))])),Type_E(PolyType("l")))), 
                                             Type_E(PolyType("p")))),
                                    Call(Call(Type_E(PolyType("filter")), 
                                              Call(Type_E(Func(Set.ofList [List(PolyType("L")), List(PolyType("L"))])), 
                                                   Type_E(PolyType("l")))),
                                         Type_E(PolyType("p"))))))))], 
        Type_E(PolyType("filter")))

let id = Let(["id"], [Fun("x", Type_E(PolyType("x")))], Type_E(PolyType("id")))

let trueFalse = If(Type_E(True), Type_E(True), Type_E(False))

let overloadCall = Call(Type_E(Func(Set.ofList [True, False; False, True])), Type_E(True))

let omega = Let(["omega"], [Fun("x", Call(Type_E(PolyType("x")), Type_E(PolyType("x"))))], Type_E(PolyType("omega")))

let fact = Let(["fact"], [Fun("n", 
                              If(Call(Call(Type_E(Func(Set.ofList [Atom, Func(Set.ofList [Atom, Union(Set.ofList [True; False])])])), Type_E(PolyType("n"))), Type_E(Atom)), 
                                 Type_E(Atom), 
                                 Call(Type_E(PolyType("fact")), Call(Call(Type_E(Func(Set.ofList [Atom, Func(Set.ofList [Atom, Atom])])), Type_E(PolyType("n"))), Type_E(Atom)))))], 
               Type_E(PolyType("fact")))

let Test() =
    let test = type_check >> type2str >> printfn "%s"
    //test id;
    test trueFalse;
    //test omega;
    //test fact;
    //test overloadCall;
    //test filter;

(*  ;; flatten :: A -> Z
    (define (flatten l)
        (if (not (list? l))
            (list l)
            (if (empty? l)
                empty
                (append (flatten (first l))
                        (flatten (rest l))))))

    ;; flatten :: A -> List<Atom>
    ;;   where A = Atom|List<A>
*)

(*  ;; omega :: A -> Z
    (define (omega x) (x x))

    ;; omega :: (A -> B) -> B
    ;;   where A = A -> B
*)

(*  ;; Y :: A -> Z
    (define (Y f)
        ((lambda (x) (x x))
         (lambda (x) (f (lambda (v) ((x x) v))))))

    ;; Y :: ((A -> B) C -> D) -> (C -> D)
    ;;   where A = A -> B
*)