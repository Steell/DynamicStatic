module DynamicStatic.ConstraintSet

open Type


type Constraint = string * Type
type ConstraintSet = Map<string, Type>

let cset2str (cs : ConstraintSet) =
    String.concat "\n" (Seq.map (fun (id, rule) -> sprintf "%-10s := %s" id 
                                                        <| type_2_str rule) 
                             <| Map.toSeq cs)

let constraint_is_reflexive (id, rule) =
    match rule with
    | TypeId(id') when id = id' -> true
    | _ -> false

let cmap_add id rule cmap =
    if constraint_is_reflexive (id, rule) then
        cmap
    else
        Map.add id rule cmap

let cset_add (i, c) (cset : ConstraintSet) = cmap_add i c cset

type UnificationResult =
    | Success of ConstraintSet
    | Failure of Type * Type

let rec unify generalize (sub : Type) 
                         (super : Type) 
                         (cset: ConstraintSet) 
                         : UnificationResult = 
    
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
    
    | TypeId(id), _          -> merge_types cset id super
    | _,          TypeId(id) -> (*generalize*) merge_types cset id sub

    | _, Any | Func(_), Atom -> Success(cset)

    | Not(sub'), Not(super') -> unify generalize super' sub' cset

    | sub', Not(super') ->
        match unify generalize sub' super' cset with
        | Success(_)    -> Failure(sub', super')
        | Failure(_, _) -> Success(cset)

    | List(sub'), List(super') -> unify generalize sub' super' cset
    
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
            match unify generalize super_arg sub_arg cset' with
            | Success(cset'') ->
                match unify generalize sub_return super_return cset'' with
                | Success(cset''') -> Some(cset''')
                | _ -> None
            | _ -> None
        ///all super overloads are satisfied by some sub overload?
        let rec unify_subs_against_supers sub_os'' (super_os'' : Set<Type * Type>) o_csets =
            match sub_os'' with
            | sub'::os when super_os''.Count > 0 ->
                ///collect all super overloads that the sub overload unifies with
                let rec unify_with_all unified_supers = function
                    | super'::os ->
                        match unify_overload sub' super' Map.empty with
                        | Some(_) -> unify_with_all (Set.add super' unified_supers) os
                        | None -> unify_with_all unified_supers os
                    | [] ->
                        let super' =
                            Set.fold 
                                (fun (arg, rtn) (arg', rtn') -> make_union [arg; arg'], make_union [rtn; rtn']) 
                                (Union(Set.empty), Union(Set.empty))
                                unified_supers
                        match unify_overload sub' super' cset with
                        | Some(cset') -> cset', unified_supers
                        | None -> cset, Set.empty
                
                let cset', unified = unify_with_all Set.empty <| Set.toList super_os''
                let remaining_supers = Set.difference super_os'' unified
                
                unify_subs_against_supers os remaining_supers (cset'::o_csets)
            | _ -> 
                let merge_types (cset' : ConstraintSet) id t =
                    match Map.tryFind id cset' with
                    | Some(t') ->  Map.add id (make_union [t'; t]) cset'
                    | None -> Map.add id t cset'
    
                let cset' = List.fold (Map.fold merge_types) Map.empty o_csets

                Success(cset')

        unify_subs_against_supers (Set.toList sub_os') super_os' []
    
    | sub', super' when sub' = super' -> Success(cset)
    | _,    _                         -> Failure(sub, super)

and generalize_rule fresh_var (cset : ConstraintSet) id t =
    let rec generalize_type cset = function
        | PolyType(id) -> failwith "Illegal PolyType(%s) found in constraint set." id

        | TypeId(id') ->
            let id'' = fresh_var()
            let t' = TypeId(id'')
            match merge_types cset id' t' with
            | Success(cset') -> Some(t', cset')
            | _ -> None

        | List(t) ->
            match generalize_type cset t with
            | Some(t', cset') -> Some(List(t'), cset')
            | x -> x

        | Not(t) ->
            match generalize_type cset t with
            | Some(t', cset') -> Some(Not(t'), cset')
            | x -> x

        | Union(ts) ->
            let union_folder a t =
                match a with
                | Some(ts', cset') ->
                    match generalize_type cset' t with
                    | Some(t', cset'') -> Some(uset_add t' ts', cset'')
                    | None             -> None
                | x -> x
            match Set.fold union_folder (Some(Set.empty, cset)) ts with
            | Some(ts', cset') ->
                if ts'.Count = 1 then
                    Some(ts'.MinimumElement, cset')
                else
                    Some(Union(ts'), cset')
            | None -> None

        | Func(os) ->
            let overload_folder a (param_type, return_type) =
                match a with
                | Some(os', cset') ->
                    match generalize_type cset' param_type with
                    | Some(param_type', cset'') ->
                        match generalize_type cset'' return_type with
                        | Some(return_type', cset''') ->
                            Some(Set.add (param_type', return_type) os', cset''')
                        | None -> None
                    | None -> None
                | None -> None
            match Set.fold overload_folder (Some(Set.empty, cset)) os with
            | Some(os', cset') -> Some(Func(os'), cset')
            | None -> None

        | t -> Some(t, cset)

    match generalize_type cset t with
    | Some(t', cset') -> merge_types cset' id t'
    | None -> Failure(PolyType(id), t)

and merge_types (cset' : ConstraintSet) id t =
    let unify' = unify <| fun cset'' id t -> Failure(TypeId(id), t) //Success(cset_add (id, t) cset'')
    let merge_types' t1 t2 =
        match unify' t1 t2 cset' with
        | Success(cset'') -> Success(Map.add id t1 cset'')
        | Failure(_, _) -> 
            match unify' t2 t1 cset' with
            | Success(cset'') -> Success(Map.add id t2 cset'')
            | _ -> Failure(t1, t2)
    match Map.tryFind id cset' with
    | Some(t') ->  
        match (t', t) with
        | TypeId(id1), TypeId(id2) when id1 <> id2 -> merge_types cset' id2 t'
        | _, TypeId(_) -> merge_types' t t'
        | _            -> merge_types' t' t
    | None -> Success(Map.add id t cset')
    