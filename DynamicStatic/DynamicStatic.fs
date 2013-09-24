module DynamicStatic.DS

let guess_maker() =
    let rec numbers_from n =
        seq { yield n; yield! numbers_from (n+1) }
    seq { for n in numbers_from 0 -> sprintf "_%i_temp_" n }

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
       
let type2str t =
    let rec infinite_letters =
        let a2z = "abcdefghijklmnopqrstuvwxyz"
        seq { yield! a2z; yield! infinite_letters }
    let letters = infinite_letters.GetEnumerator()
    let fresh_letter() =
        ignore <| letters.MoveNext();
        letters.Current
    let lookup = ref Map.empty
    let rec type2str = function
        | Any -> "Any"
        | Atom -> "Atom"
        | Unit -> "IO"
        | True -> "True"
        | False -> "False"
        | TypeId(id) -> 
            match Map.tryFind id !lookup with
            | Some(id') -> sprintf "'%c" id'
            | None ->
                let new_var = fresh_letter()
                lookup := Map.add id new_var !lookup;
                sprintf "'%c" new_var
        | PolyType(id) -> sprintf "Poly(%s)" id
        | List(t) -> sprintf "List<%s>" <| type2str t
        | Func(os) when os.Count = 1 -> overload2str os.MinimumElement
        | Func(os) -> sprintf "(%s)" <| String.concat "+" (Seq.map overload2str os)
        | Union(ts) -> sprintf "{%s}" <| String.concat "|" (Seq.map type2str ts)

    and overload2str (ps, r) = 
        sprintf "(%s -> %s)" (type2str ps) (type2str r)
    
    type2str t

let rec type_2_str t =
    let overload2str (ps, r) = 
        sprintf "(%s -> %s)" (type_2_str ps) (type_2_str r)
    match t with
    | Any -> "Any"
    | Atom -> "Atom"
    | Unit -> "IO"
    | True -> "True"
    | False -> "False"
    | TypeId(id) -> id
    | PolyType(id) -> sprintf "Poly(%s)" id
    | List(t) -> sprintf "List<%s>" <| type_2_str t
    | Func(os) when os.Count = 1 -> overload2str os.MinimumElement
    | Func(os) -> sprintf "(%s)" <| String.concat "+" (Seq.map overload2str os)
    | Union(ts) -> sprintf "{%s}" <| String.concat "|" (Seq.map type_2_str ts)

type Constraint = string * Type

let cset2str cs =
    String.concat "\n" <| Seq.map (fun (id, rule) -> sprintf "%-10s := %s" id <| type_2_str rule) cs

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
        | [] -> Set.add t set

    match t with
    | Union(ts) -> Seq.fold (fun a t -> uset_add t a) uset ts
    | _ -> add Set.empty t <| Set.toList uset

and oset_add overload oset : Set<Overload> =
    
    let combine_overloads o1 o2 =
        let sub_param, sub_return = o1
        let super_param, super_return = o2
        let make_union t1 t2 = make_union [t1; t2]
        if sub_param = super_param then
             // if returns are functions make sure they are combined into a single overloaded function
            Some(sub_param, make_union sub_return super_return)
        (*else if sub_return = super_return then
            Some(make_union sub_param super_param, sub_return)*)
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

    match overload with
    | Union(uset), rtn ->
        let os = Set.map (fun t -> t, rtn) uset
        Set.foldBack oset_add os oset
    | _ ->
        add Set.empty overload <| Set.toList oset

and make_union types =
    let uset = List.foldBack uset_add types Set.empty
    if uset.Count = 1 then
        uset.MinimumElement
    else
        Union(uset)


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
                        | Some(r) -> Some((*oset_add*)Set.add (ps, r) os)
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
    
type UnificationResult =
    | Success of Set<Constraint>
    | Failure of Type * Type

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
                uset_add t' ts', cset''
            let ts', cset' = Set.fold union_folder (Set.empty, cset) ts
            if ts'.Count = 1 then
                ts'.MinimumElement, cset'
            else
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
    Success(cset_add (id, t') cset')

let rec unify generalize (sub : Type) (super : Type) (cset: Set<Constraint>) : UnificationResult = 
    let rec all_unify cset' super = function
        | sub::ts -> 
            match unify generalize sub super cset' with
            | Success(cset'') -> all_unify cset'' super ts
            | failure -> Some(failure), cset'
        | [] -> None, cset'
    let rec unifies_with_any cset' sub = function
        | super::ts ->
            match unify generalize sub super cset' with
            | Success(_) as s -> Some(s)
            | Failure(_, _) -> unifies_with_any cset' sub ts
        | [] -> None
    match sub, super with
    | PolyType(id), _ | _, PolyType(id) -> failwith "Illegal PolyType(%s) found in constraint set." id

    //don't add reflexive rules
    | TypeId(id1), TypeId(id2) when id1 = id2 -> Success(cset)
    
    | TypeId(id), _          -> Success(cset_add (id, super) cset)
    | _,          TypeId(id) -> (*Success(cset_add (id, sub) cset)*)generalize cset id sub

    | _, Any | Func(_), Atom -> Success(cset)

    | List(sub'), List(super') -> unify generalize sub' super' cset
    
    | Union(subs), _ -> 
        match all_unify  cset super <| Set.toList subs with 
        | Some(failure), _ -> failure 
        | None, cset'      -> Success(cset')

    | _, Union(supers) -> 
        match unifies_with_any cset sub <| Set.toList supers with
        | Some(success) -> success
        | None          -> Failure(sub, super)
    
    | Func(sub_os'), Func(super_os') -> 
        // Unification successful if everything in super_os' unifies with something in sub_os'
        let unify_overload (sub_arg, sub_return) (super_arg, super_return) cset' =
            match unify generalize super_arg sub_arg cset' with
            | Success(cset'') ->
                match unify generalize sub_return super_return cset'' with
                | Success(cset''') -> Some(cset''')
                | _ -> None
            | _ -> None
        ///all super overloads are satisfied by some sub overload?
        let rec unify_subs_against_supers cset' sub_os'' (super_os'' : Set<Type * Type>) =
            match sub_os'' with
            | sub'::os when super_os''.Count > 0 ->
                ///collect all super overloads that the sub overload unifies with
                let rec unify_with_all unified_supers = function
                    | super'::os ->
                        match unify_overload sub' super' Set.empty with
                        | Some(_) -> unify_with_all (Set.add super' unified_supers) os
                        | None -> unify_with_all unified_supers os
                    | [] ->
                        let super' =
                            Set.fold 
                                (fun (arg, rtn) (arg', rtn') -> make_union [arg; arg'], make_union [rtn; rtn']) 
                                (Union(Set.empty), Union(Set.empty))
                                unified_supers
                        match unify_overload sub' super' cset' with
                        | Some(cset'') -> cset'', unified_supers
                        | None -> cset', Set.empty
                let cset'', unified = unify_with_all Set.empty <| Set.toList super_os''
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
                unify generalize_rule cft_subtype cft_supertype cset'
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
        | TypeId(id') -> Map.containsKey id' cset
        | List(t)     -> contains_vars t
        | Func(os)    -> Set.exists (fun (pt, ot) -> contains_vars pt || contains_vars ot) os
        | Union(ts)   -> Set.exists contains_vars ts
        | _           -> false
    
    let rec folder lookup to_fold =
    
        let rec fold_constraint lookup = function
            | TypeId(id) -> Map.tryFind id lookup
            | List(t) ->
                match fold_constraint lookup t with
                | Some(t') -> Some(List(t'))
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
                                    Call(Call(Type_E(Func(Set.ofList [PolyType("C"), Func(Set.ofList [List(PolyType("D")), List(Union(Set.ofList [PolyType("C"); PolyType("D")]))])])), 
                                              Type_E(PolyType("x"))),
                                        Call(Call(Type_E(PolyType("filter")), 
                                                  Call(Type_E(Func(Set.ofList [List(PolyType("K")), List(PolyType("K"))])),Type_E(PolyType("l")))), 
                                             Type_E(PolyType("p")))),
                                    Call(Call(Type_E(PolyType("filter")), 
                                              Call(Type_E(Func(Set.ofList [List(PolyType("L")), List(PolyType("L"))])), 
                                                   Type_E(PolyType("l")))),
                                         Type_E(PolyType("p"))))))))], 
        Type_E(PolyType("filter")))

let id = (*Let(["id"], [*)Fun("x", Type_E(PolyType("x")))(*], Type_E(PolyType("id")))*)

let trueFalse = If(Type_E(Union(Set.ofList [True; False])), Type_E(True), Type_E(False))

let notExpr = Fun("x", If(Type_E(PolyType("x")), Type_E(False), Type_E(True)))

let notType = Func(Set.ofList [True, False; False, True])

let omega = Fun("x", Call(Type_E(PolyType("x")), Type_E(PolyType("x"))))

let fact = Let(["fact"], [Fun("n", 
                              If(Call(Call(Type_E(Func(Set.ofList [Atom, Func(Set.ofList [Atom, Union(Set.ofList [True; False])])])), Type_E(PolyType("n"))), Type_E(Atom)), 
                                 Type_E(Atom), 
                                 Call(Type_E(PolyType("fact")), Call(Call(Type_E(Func(Set.ofList [Atom, Func(Set.ofList [Atom, Atom])])), Type_E(PolyType("n"))), Type_E(Atom)))))], 
               Type_E(PolyType("fact")))

let map = Let(["map"], [Fun("l",
                            Fun("f",
                                If(Call(Type_E(Func(Set.ofList [List(PolyType("A")), Union(Set.ofList [True; False])])),
                                        Type_E(PolyType("l"))),
                                   Type_E(List(PolyType("B"))),
                                   Call(Call(Type_E(Func(Set.ofList [PolyType("C"), Func(Set.ofList [List(PolyType("D")), List(Union(Set.ofList [PolyType("C"); PolyType("D")]))])])), 
                                             Call(Type_E(PolyType("f")),
                                                  Call(Type_E(Func(Set.ofList [List(PolyType("E")), PolyType("E")])), 
                                                       Type_E(PolyType("l"))))),
                                        Call(Call(Type_E(PolyType("map")),
                                                  Call(Type_E(Func(Set.ofList [List(PolyType("F")), List(PolyType("F"))])),
                                                       Type_E(PolyType("l")))), 
                                             Type_E(PolyType("f")))))))],
             Type_E(PolyType("map")))

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

let yComb = Fun("f",
                Call(omega, 
                     Fun("w", 
                         Call(Type_E(PolyType("f")), 
                              Fun("v", 
                                  Call(Call(Type_E(PolyType("w")), 
                                            Type_E(PolyType("w"))), 
                                       Type_E(PolyType("v"))))))))

let factY =
    Call(yComb,
         Fun("fact",
             Fun("n", 
                 If(Call(Call(Type_E(Func(Set.ofList [Atom, Func(Set.ofList [Atom, Union(Set.ofList [True; False])])])), Type_E(PolyType("n"))), Type_E(Atom)), 
                    Type_E(Atom), 
                    Call(Type_E(PolyType("fact")), Call(Call(Type_E(Func(Set.ofList [Atom, Func(Set.ofList [Atom, Atom])])), Type_E(PolyType("n"))), Type_E(Atom)))))))