module DynamicStatic.ConstraintSet

open Type


type Constraint = string * Type
type ConstraintSet = Set<Constraint>

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

type UnificationResult =
    | Success of ConstraintSet
    | Failure of Type * Type

let generalize_rule fresh_var cset id t =
    let rec generalize_type cset = function
        | PolyType(id) -> failwith "Illegal PolyType(%s) found in constraint set." id

        | TypeId(id') ->
            let id'' = fresh_var()
            let t' = TypeId(id'')
            t', cset_add (id', t') cset

        | List(t) ->
            let t', cset' = generalize_type cset t
            List(t'), cset'

        | Not(t) ->
            let t', cset'  = generalize_type cset t
            Not(t'), cset'

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

let rec unify generalize (sub : Type) (super : Type) (cset: ConstraintSet) : UnificationResult = 
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

    | Not(sub'), Not(super') -> unify generalize sub' super' cset

    | Not(sub'), super'  | sub', Not(super') ->
        match unify generalize sub' super' cset with
        | Success(_)    -> Failure(sub', super')
        | Failure(_, _) -> Success(cset)

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