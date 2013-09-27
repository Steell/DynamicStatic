module PolymorphismTests

open NUnit.Framework
open DynamicStatic
open TestUtils

let type_check = type_check >> type2str


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
let ``Map Definition``() = type_check map == "List<'a> -> (('a -> 'b) -> List<'b>))"


let id = Fun("x", Type_E(PolyType("x")))

[<Test>]
let ``Identity Definition``() = type_check id == "('a -> 'a)"


let id_call arg = Call(id, Type_E(arg))

[<Test>]
let ``Call Identity With Atom``() = type_check (id_call Atom) == "Atom"

[<Test>]
let ``Call Identity With Any``() = type_check (id_call Any) == "Any"

[<Test>]
let ``Call Identity With Union``() = type_check (id_call <| Union(Set.ofList [True; False])) == "{True|False}"

[<Test>]
let ``Call Identity With Itself``() = type_check (Call(id, Fun("y", Type_E(PolyType("y"))))) == "('a -> 'a)"

[<Test>]
let ``Call Identity With List``() = type_check (id_call <| List(Atom)) == "List<Atom>"

[<Test>]
let ``Call Identity With Polymorphic Type``() = type_check (id_call <| PolyType("a")) == "'a"