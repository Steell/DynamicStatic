﻿module DynamicStatic.Tests.BasicTests

open NUnit.Framework
open DynamicStatic.DS
open DynamicStatic.Type
open DynamicStatic.TypeExpression
open TestUtils

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