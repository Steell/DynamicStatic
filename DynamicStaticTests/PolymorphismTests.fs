module DynamicStatic.Tests.PolymorphismTests

open NUnit.Framework
open NUnit.FSharp.TestUtils

open DynamicStatic.DS
open DynamicStatic.Type
open DynamicStatic.TypeExpression

let typecheck = type_check >> type2str


let id = Fun("x", Type_E(PolyType("x")))

[<Test>]
let ``id == ('a -> 'a)``() = typecheck id == "('a -> 'a)"

let id_call arg = Call(id, Type_E(arg))

[<Test>]
let ``(id Atom) == Atom``() = typecheck (id_call Atom) == "Atom"

[<Test>]
let ``(id Any) == Any``() = typecheck (id_call Any) == "Any"

[<Test>]
let ``(id {True|False}) == {True|False}``() = 
    typecheck (id_call <| Union(Set.ofList [True; False])) == "{True|False}"

[<Test>]
let ``(id id) == id``() = 
    typecheck (Call(id, Fun("y", Type_E(PolyType("y"))))) == "('a -> 'a)"

[<Test>]
let ``(id List<Atom>) == List<Atom>``() = typecheck (id_call <| List(Atom)) == "List<Atom>"

[<Test>]
let ``(id 'a) == 'a``() = typecheck (id_call <| PolyType("a")) == "'a"


let empty = Type_E(List(PolyType("empty")))

let isEmpty = Type_E(Func(Set.ofList [List(PolyType("empty?A")), Bool]))

// cons :: A -> List<B> -> List<{A|B}>
let cons = Type_E(Func(Set.ofList [PolyType("consA"), 
                                   Func(Set.ofList [List(PolyType("consB")), 
                                                    List(Union(Set.ofList [PolyType("consA"); PolyType("consB")]))])]))

[<Test>]
let ``(cons Atom List<Atom>) == List<Atom>``() =
    let call = Call(Call(cons, Atom_E), Type_E(List(Atom)))
    typecheck call == "List<Atom>"

[<Test>]
let ``(cons Atom List<True>) == List<{Atom|True}>``() =
    let call = Call(Call(cons, Atom_E), Type_E(List(True)))
    typecheck call == "List<{Atom|True}>"

[<Test>]
let ``(cons Atom empty) == List<Atom>``() =
    let call = Call(Call(cons, Atom_E), empty)
    typecheck call == "List<Atom>"


let first = Type_E(Func(Set.ofList [List(PolyType("firstA")), PolyType("firstA")]))

[<Test>]
let ``(first List<Atom>) == Atom``() =
    let call = Call(first, Type_E(List(Atom)))
    typecheck call == "Atom"

[<Test>]
let ``(first List<'a>) == 'a``() =
    let call = Call(first, Type_E(PolyType("A")))
    typecheck call == "'a"


let rest = Type_E(Func(Set.ofList [List(PolyType("restA")), List(PolyType("restA"))]))

[<Test>]
let ``(rest List<Atom>) == List<Atom>``() =
    let call = Call(rest, Type_E(List(Atom)))
    typecheck call == "List<Atom>"
    
[<Test>]
let ``(rest List<'a>) == List<'a>``() =
    let call = Call(rest, Type_E(PolyType("A")))
    typecheck call == "List<'a>"



[<Test>]
let ``(if (empty? List<Atom>) empty Atom) == {Atom|List<'a>}``() =
    let expr = If(Call(isEmpty, Type_E(List(Atom))), empty, Atom_E)
    typecheck expr == "{Atom|List<'a>}"

[<Test>]
let ``(if (empty? List<Atom>) Atom empty) == {Atom|List<'a>}``() =
    let expr = If(Call(isEmpty, Type_E(List(Atom))), Atom_E, empty)
    typecheck expr == "{Atom|List<'a>}"


(*  ;; map :: List<A> -> (A -> B) -> List<B>
    (define (map l f)
        (if (empty? l)
            empty
            (cons (f (first l)) (map (rest l) f))))
*)
let map = Let(["map"], [Fun("mapl",
                            Fun("mapf",
                                If(Call(isEmpty, Type_E(PolyType("mapl"))),
                                   empty,
                                   Call(Call(cons, Call(Type_E(PolyType("mapf")), 
                                                        Call(first, Type_E(PolyType("mapl"))))),
                                        Call(Call(Type_E(PolyType("map")),
                                                  Call(rest, Type_E(PolyType("mapl")))), 
                                             Type_E(PolyType("mapf")))))))],
             Type_E(PolyType("map")))

[<Test>]
let ``map == (List<'a> -> (('a -> 'b) -> List<'b>))``() = 
    let maptype = typecheck map
    maptype == "(List<'a> -> (('a -> 'b) -> List<'b>))"