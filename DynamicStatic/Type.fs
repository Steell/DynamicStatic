module DynamicStatic.Type

#nowarn "40"

open NUnit.Framework
open NUnit.FSharp.TestUtils

type Type =
    | Any
    | Atom 
    | Unit
    | True | False 
    | TypeId of string   // only used in CFT and CSet
    | PolyType of string // one can map to several TypeIds, each in a different execution path
    | List of Type
    | Func of OverloadSet
    | Union of UnionSet
    | Not of Type

and OverloadSet = Set<Type * Type>
and UnionSet = Set<Type>
       
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
        | Not(t) -> sprintf "Not<%s>" <| type2str t

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
    | Not(t) -> sprintf "Not<%s>" <| type_2_str t


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

    | Not(sub'), Not(super') | List(sub'), List(super') -> union sub' super'

    | sub', Not(super') | Not(sub'), super' -> not <| union sub' super'
    
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

and oset_add overload oset : OverloadSet =
    
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
