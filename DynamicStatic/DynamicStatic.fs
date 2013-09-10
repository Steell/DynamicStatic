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
    | Nil
    | Unit
    | True | False 
    | TypeId of string   // only used in CFT and CSet
    | PolyType of string // one can map to several TypeIds, each in a different execution path
    | List of Type
    | Func of (Type list * Type) list
    | Union of Set<Type>
       
let rec type2str = function
    | Any -> "Any"
    | Atom -> "Atom"
    | Nil -> "Nil"
    | Unit -> "IO"
    | True -> "True"
    | False -> "False"
    | TypeId(id) -> sprintf "'%s" id
    | PolyType(id) -> sprintf "Poly(%s)" id
    | List(t) -> sprintf "List<%s>" <| type2str t
    | Func([o]) -> overload2str o
    | Func(os) -> sprintf "(%s)" <| String.concat "+" (Seq.map overload2str os)
    | Union(ts) -> String.concat "|" <| Seq.map type2str ts

and overload2str (ps, r) = 
    sprintf "(%s -> %s)" (String.concat " " <| List.map type2str ps) (type2str r)

type Constraint = string * Type

let cset_add (id, rule) cset =
    match rule with
    | TypeId(id') when id = id' -> cset
    | _ -> Set.add (id, rule) cset

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
            let overload_lookup (parameters, return_type) = function
                | Some(os) -> 
                    match lookup_all parameters with
                    | Some(ps) ->
                        match lookup return_type with
                        | Some(r) -> Some((ps, r)::os)
                        | None -> None
                    | None -> None
                | None -> None               
            match List.foldBack overload_lookup os <| Some([]) with
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
    | CFun of string list * CTE
    | CCall of CTE * CTE list * string
    | CIf of CTE * ControlTypeExpression * ControlTypeExpression * string
    | CBegin of CTE list

///AST for FScheme expressions
type TypeExpression =
    | Atom_E
    | Type_E of Type
    | Let of string list * TypeExpression list * TypeExpression
    | Fun of string list * TypeExpression
    | Call of TypeExpression list
    | If of TypeExpression * TypeExpression * TypeExpression
    | Begin of TypeExpression list

(*
type TypeEnv = Map<string, Type>

let base_env : TypeEnv list = 
    [ 
        Map.ofSeq [ 
            "empty",  Nil
            "empty?", Func([[Nil], True; [List(PolyType("A"))], False])
            "first",  Func([[List(PolyType("B"))], PolyType("B")])
            "cons",   Func([[PolyType("C"); List(PolyType("C"))], List(PolyType("C"))])
            "rest",   Funv([[List(PolyType("K"))], List(PolyType("K"))])
        ]
    ]

let env_lookup (env : TypeEnv list) (id : string) =
    let fresh_guess = guess_maker()
    let rec replace_all_ids (var_env : Map<string, string>) = function
        | PolyType(userid) -> 
            match var_env.TryFind userid with
            | Some(id) -> env, PolyType(id)
            | None ->
                let id = fresh_guess()
                Map.add userid id, PolyType(id)
        | TypeId(x) -> failwith <| sprintf "Not allowed to use TypeId(%s) in TypeEnv"
        | List(t) -> 
            let (var_env', t') = replace_all_ids var_env t
            var_env', List(t')
        | Union(ts) ->
            let union_fldr (var_env', ts') t =
                let (var_env'', t') = replace_all_ids var_env' t
                var_env'', Set.add t' ts'
            Union(Set.fold union_fldr (var_env, Set.empty) ts)
        | Func(os) ->
            let overload_fldr (param_types, return_type)  (var_env', os') =
                let (var_env'', param_types') =
                    let param_fldr t (var_env', al') =
                        let (var_env'', t') = replace_all_ids var_env' t
                        var_env'', t'::al
                    List.foldBack param_fldr param_types (var_env', [])
                let (var_env''', return_type') = replace_all_ids var_env'' return_type
                var_env''', (param_types', return_type')::os
            List.foldBack overload_fldr os []
    let rec try_find id = function
        | h::t ->
            match h.TryFind id with
            | Some(t) -> t
            | None -> try_find id t
        | [] -> None
    match try_find id env with
    | Some(t) -> 
        let (_, t') = replace_all_ids Map.empty t
        Some(t')
    | None -> None
*)

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
            let overload_folder (os', cset') (ts, t) =
                let input_folder (ts', cset') t' =
                    let t'', cset'' = generalize_type cset' t'
                    t''::ts', cset''
                let ts', cset'' = List.fold input_folder ([], cset') ts
                let t', cset''' = generalize_type cset'' t
                (ts', t)::os', cset'''
            let os', cset' = List.fold overload_folder ([], cset) os
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
    | _, Any | Nil, List(_) | Func(_), Atom -> Success(cset)

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
        let unify_overload sub' super' cset' =
            let sub_args, sub_return = sub'
            let super_args, super_return = super'
            if List.length sub_args <> List.length super_args then
                None
            else
                let rec arg_folder cset'' sub_args' super_args' =
                    match sub_args', super_args' with
                    | sub_arg::sub_args'', super_arg::super_args'' ->
                        match unify super_arg sub_arg cset'' with
                        | Success(cset''') -> arg_folder cset''' sub_args'' super_args''
                        | _ -> None
                    | _ -> Some(cset'')
                match arg_folder cset' sub_args super_args with
                | Some(cset'') ->
                    match unify sub_return super_return cset'' with
                    | Success(cset''') -> Some(cset''')
                    | _ -> None
                | None -> None
        let rec any_unify cset' super' = function
            | sub'::os ->
                match unify_overload sub' super' cset' with
                | None -> any_unify cset' super' os
                | x -> x
            | [] -> None
        let rec unifies_with_all cset' sub_os'' = function
            | super'::os ->
                match any_unify cset super' sub_os'' with
                | None -> Failure(sub, super)
                | Some(cset'') -> unifies_with_all cset'' sub_os'' os
            | [] -> Success(cset')
        unifies_with_all cset sub_os' super_os'
    
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
                    List.fold (fun stack' (param_types, return_type) -> gather_ids (List.fold gather_ids stack' param_types) return_type) 
                              stack 
                              overloads
                | Union(ts) -> Set.fold gather_ids stack ts
                | _ -> stack
            CType_E(t), cft, gather_ids stack t

        | Let(ids, exprs, body_expr) ->
            let c_exprs, cft', stack' = build_exprs cft (ids @ stack) [] exprs
            let c_body, cft'', stack'' = build_cft body_expr cft' stack'
            CLet(ids, c_exprs, c_body), cft'', stack''
        
        | Fun(param_names, body_expr) ->
            let c_body, cft', stack' = build_cft body_expr cft <| param_names @ stack
            CFun(param_names, c_body), cft', stack'
        
        | Call(exprs) ->
            let c_exprs, cft', stack' = build_exprs cft stack [] exprs
            let return_id = fresh_var()
            CCall(c_exprs.Head, c_exprs.Tail, return_id), cft', return_id::stack'

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
            | None -> Failure(sub_type, super_type)
        | None -> Failure(sub_type, super_type)
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

let overload_function cft ((param_names : string list), (body_type : Type)) : Type =
    let rec define_in_leaves os = function
        | Leaf(map) -> 
            let lookup t = 
                match cft_map_lookup map t with
                | Some(x) -> x
                | None -> failwith "Overload Failure"
            (List.map (PolyType >> lookup) param_names, lookup body_type)::os
        | Branch(trees) ->
            List.fold define_in_leaves os trees
    Func(define_in_leaves [] cft)

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
    | CFun(param_names, body_expr) ->
        let body_type, cset' = build_cset (body_expr, cft) cset
        overload_function cft (param_names, body_type), cset'
    | CCall(func_expr, arg_exprs, return_id) ->
        let func_type, cset' = build_cset (func_expr, cft) cset
        let arg_types, cset'' = build_exprs cft cset' [] arg_exprs
        match constrain cft cset'' func_type <| Func([arg_types, PolyType(return_id)]) with
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
        let cset'' = 
            match constrain t_cft cset' test_type True with
            | Success(cset'') -> cset''
            | Failure(t1, t2) -> cset'
        let cset''' =
            match constrain f_cft cset'' test_type False with
            | Success(cset''') -> cset'''
            | Failure(t1, t2) -> cset''
        let cset'''' = 
            match constrain cft cset''' test_type <| Union(Set.ofList [True; False]) with
            | Success(cset'''') -> cset''''
            | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) Test CFT could not be constrained to True|False"
        let true_type, cset''''' = build_cset (t_expr, t_cft) cset''(*''*)
        match constrain t_cft cset''''' true_type <| PolyType(return_id) with
        | Success(cset'''''') ->
            let false_type, cset''''''' = build_cset (f_expr, f_cft) cset''''''
            match constrain f_cft cset''''''' false_type <| PolyType(return_id) with
            | Success(cset'''''''') -> PolyType(return_id), cset''''''''
            | Failure(t1, t2) -> failwith "Unification Failure (build_cset.If) False CFT could not be constrained to if return type"
        | Failure(t, t2) -> failwith "Unification Failure (build_cset.If) True CFT could not be constrained to if return type"

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
                | Some(t'', cset'') -> merge_all (Map.add id t'' map) cset''
                | None -> failwith "Could not merge types."
            | None -> merge_all (Map.add id t map) cset'
        | [] -> map
    merge_all Map.empty <| Set.toList cset

let rec fold_type_constants (cset : Map<string, Type>) : Map<string, Type> =
    let rec is_recursive id type_constraint =
        match type_constraint with
        | TypeId(id') when id = id -> true
        | List(t) -> is_recursive id t
        | Func(os) -> List.exists (fun (pt, ot) -> List.exists (is_recursive id) pt || is_recursive id ot) os
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
                | (param_types, body_type)::os'' ->
                    let rec fold_ps ps = function
                        | p::ps' -> 
                            match fold_constraint id p with
                            | Some(t) -> fold_ps (t::ps) ps'
                            | None -> None
                        | [] -> Some(List.rev ps)
                    match fold_ps [] param_types with
                    | Some(ps) ->
                        match fold_constraint id body_type with
                        | Some(t) -> fold_os ((ps, t)::os') os''
                        | None -> None
                    | None -> None
                | [] -> Some(os')
            match fold_os [] os with
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
            | None -> fold_all again (Map.add id t cset') cs
        | [] -> 
            if again then
                fold_type_constants cset'
            else
                cset'
    fold_all false Map.empty <| Map.toList cset

let rec collapse_types t1 t2 =
    match (t1, t2) with
    | Any, x | x, Any
    | Atom, (Func(_) as x) | (Func(_) as x), Atom
    | Nil, (List(_) as x) | (List(_) as x), Nil    -> x
    | PolyType(id), _ | _, PolyType(id) -> failwith "Impossible"
    | List(t1'), List(t2') -> List(collapse_types t1 t2)
    | Func(os1), Func(os2) -> Func(os1 @ os2)
    | Union(ts), x | x, Union(ts) -> Union(Set.add x ts)
    | _, _ -> Union(Set.ofList [t1; t2])

let collapse_cft (cft : ControlFlowTree) (cset : Map<string, Type>) : Map<string, Type> =
    let rec collapse_map map = function
        | (poly_id, id)::cs -> 
            let t =
                match Map.tryFind id cset with
                | Some(t) -> t
                | None -> TypeId(id)
            let t' =
                match Map.tryFind poly_id map with
                | Some(t') -> collapse_types t t'
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
        | Func(os) -> Func(List.map (fun (ps, r) -> List.map update_type ps, update_type r) os)
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
let filter = Let(["filter"], [Fun(["l"; "p"], 
                                  If(Call([Type_E(Func([[Nil], True; [List(PolyType("A"))], False])); Type_E(PolyType("l"))]), 
                                     Type_E(Nil), 
                                     Let(["x"], [Call([Type_E(Func([[List(PolyType("B"))], PolyType("B")])); Type_E(PolyType("l"))])], 
                                         If(Call([Type_E(PolyType("p")); Type_E(PolyType("x"))]), 
                                            Call([Type_E(Func([[PolyType("C"); List(PolyType("C"))], List(PolyType("C"))])); Type_E(PolyType("x")); Call([Type_E(PolyType("filter")); Call([Type_E(Func([[List(PolyType("K"))], List(PolyType("K"))])); Type_E(PolyType("l"))]); Type_E(PolyType("p"))])]),
                                            Call([Type_E(PolyType("filter")); Call([Type_E(Func([[List(PolyType("L"))], List(PolyType("L"))])); Type_E(PolyType("l"))]); Type_E(PolyType("p"))])))))],
                 Type_E(PolyType("filter")))

let id = Let(["id"], [Fun(["x"], Type_E(PolyType("x")))], Type_E(PolyType("id")))

let trueFalse = If(Type_E(True), Type_E(True), Type_E(False))

let overloadCall = Call([Type_E(Func([[True], False; [False], True])); Type_E(True)])

let omega = Let(["omega"], [Fun(["x"], Call([Type_E(PolyType("x")); Type_E(PolyType("x"))]))], Type_E(PolyType("omega")))

let fact = Let(["fact"], [Fun(["n"], 
                              If(Call([Type_E(Func([[Atom; Atom], Union(Set.ofList [True; False])])); Type_E(PolyType("n")); Type_E(Atom)]), 
                                 Type_E(Atom), 
                                 Call([Type_E(PolyType("fact")); Call([Type_E(Func([[Atom; Atom], Atom])); Type_E(PolyType("n")); Type_E(Atom)])])))], 
               Type_E(PolyType("fact")))

let Test() =
    let test = type_check >> type2str >> printfn "%s"
    //test id;
    //test trueFalse;
    //test omega;
    //test fact;
    //test overloadCall;
    test filter;

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