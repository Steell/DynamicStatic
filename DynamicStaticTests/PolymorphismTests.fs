module DynamicStatic.Tests.PolymorphismTests

open NUnit.Framework
open NUnit.FSharp.TestUtils

open DynamicStatic.DS
open DynamicStatic.Type
open DynamicStatic.TypeExpression

let typecheck = type_check >> type2str


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

[<Test>]
let ``map == (List<'a> -> (('a -> 'b) -> List<'b>))``() = typecheck map == "(List<'a> -> (('a -> 'b) -> List<'b>))"


let id = Fun("x", Type_E(PolyType("x")))

[<Test>]
let ``id == ('a -> 'a)``() = typecheck id == "('a -> 'a)"

let id_call arg = Call(id, Type_E(arg))

[<Test>]
let ``(id Atom) == Atom``() = typecheck (id_call Atom) == "Atom"

[<Test>]
let ``(id Any) == Any``() = typecheck (id_call Any) == "Any"

[<Test>]
let ``(id {True|False}) == {True|False}``() = typecheck (id_call <| Union(Set.ofList [True; False])) == "{True|False}"

[<Test>]
let ``(id id) == id``() = typecheck (Call(id, Fun("y", Type_E(PolyType("y"))))) == "('a -> 'a)"

[<Test>]
let ``(id List<Atom>) == List<Atom>``() = typecheck (id_call <| List(Atom)) == "List<Atom>"

[<Test>]
let ``(id 'a) == 'a``() = typecheck (id_call <| PolyType("a")) == "'a"