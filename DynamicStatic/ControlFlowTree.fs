module DynamicStatic.ControlFlowTree

open Type


type ControlFlowTree = 
    | Leaf of Map<string, string> 
    | Branch of ControlFlowTree list

let cft_add fresh_var = 
    let rec cft_add id = function
        | Leaf(map) -> Leaf(Map.add id (fresh_var()) map)
        | Branch(trees) -> Branch(List.map (cft_add id) trees)
    cft_add

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