module DynamicStatic.Tests.BasicTests

open NUnit.Framework
open NUnit.FSharp.TestUtils

open DynamicStatic.DS
open DynamicStatic.Type
open DynamicStatic.TypeExpression

let typecheck = type_check >> type2str


let basic_check = Type_E >> typecheck

[<Test>]
let ``Any == Any``() = basic_check Any == "Any"

[<Test>]
let ``Atom == Atom``() = basic_check Atom == "Atom"

[<Test>]
let ``Unit == Unit``() = basic_check Unit == "IO"

[<Test>]
let ``True == True``() = basic_check True == "True"

[<Test>]
let ``False == False``() = basic_check False == "False"

[<Test>]
let ``TypeId error``() =
    let test() = basic_check (TypeId("x"))
    test |> ``fails with`` "Not allowed to use TypeId(x) in TypeExpression"

[<Test>]
let ``PolyType == PolyType``() = basic_check (PolyType("x")) == "'a"

[<Test>]
let ``List<Atom> == List<Atom>``() = basic_check (List(Atom)) == "List<Atom>"


let fact = Let(["fact"], [Fun("n", 
                              If(Call(Call(Type_E(Func(Set.ofList [Atom, Func(Set.ofList [Atom, Union(Set.ofList [True; False])])])), Type_E(PolyType("n"))), Type_E(Atom)), 
                                 Type_E(Atom), 
                                 Call(Type_E(PolyType("fact")), Call(Call(Type_E(Func(Set.ofList [Atom, Func(Set.ofList [Atom, Atom])])), Type_E(PolyType("n"))), Type_E(Atom)))))], 
               Type_E(PolyType("fact")))

[<Test>]
let ``factorial == (Atom -> Atom)``() = typecheck fact == "(Atom -> Atom)"

[<Test>]
let ``((Not<List<'a>> -> Unit) Atom)``() =
    let call = Call(Type_E(Func(Set.ofList [Not(List(Atom)), Unit])), Type_E(Atom))
    typecheck call == "IO"


[<Test>]
let ``x == Atom in: (begin ((Not<List<'a>> -> Unit) x) ((Atom -> Unit) x) x)``() =
    let call = Begin([Call(Type_E(Func(Set.ofList [Not(List(Atom)), Unit])), Type_E(PolyType("x"))); 
                      Call(Type_E(Func(Set.ofList [Atom, Unit])), Type_E(PolyType("x")));
                      Type_E(PolyType("x"))])
    typecheck call == "Atom"


[<Test>]
let ``make_union [Atom; Atom] == Atom``() =
    make_union [Atom; Atom] == Atom

[<Test>]
let ``make_union ['a; 'b] == {'a|'b}``() =
    let letters = ["A"; "B"]
    let poly_sets = List.map PolyType letters
    make_union poly_sets == Union(Set.ofList poly_sets)

    let id_sets = List.map TypeId letters
    make_union id_sets == Union(Set.ofList id_sets)


let compose = Fun("f", 
                  Fun("g", 
                      Fun("x", 
                          Call(Type_E(PolyType("g")), 
                               Call(Type_E(PolyType("f")), Type_E(PolyType("x")))))))

[<Test>]
let ``compose == (('a -> 'b) -> (('b -> 'c) -> ('a -> 'c)))``() =
    let result = typecheck compose
    result == "(('a -> 'b) -> (('b -> 'c) -> ('a -> 'c)))"