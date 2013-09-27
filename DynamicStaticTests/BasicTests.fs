module BasicTests

open NUnit.Framework
open DynamicStatic
open TestUtils

let type_check = type_check >> type2str


let basic_check = Type_E >> type_check

[<Test>]
let ``Only Any``() = basic_check Any == "Any"

[<Test>]
let ``Only Atom``() = basic_check Atom == "Atom"

[<Test>]
let ``Only Unit``() = basic_check Unit == "IO"

[<Test>]
let ``Only True``() = basic_check True == "True"

[<Test>]
let ``Only False``() = basic_check False == "False"

[<Test>]
let ``Only TypeId``() =
    let test() = basic_check (TypeId("x"))
    test |> ``fails with`` "Not allowed to use TypeId(x) in TypeExpression"

[<Test>]
let ``Only PolyType``() = basic_check (PolyType("x")) == "'a"

[<Test>]
let ``Only List With No Variables``() = basic_check (List(Atom)) == "List<Atom>"


let fact = Let(["fact"], [Fun("n", 
                              If(Call(Call(Type_E(Func(Set.ofList [Atom, Func(Set.ofList [Atom, Union(Set.ofList [True; False])])])), Type_E(PolyType("n"))), Type_E(Atom)), 
                                 Type_E(Atom), 
                                 Call(Type_E(PolyType("fact")), Call(Call(Type_E(Func(Set.ofList [Atom, Func(Set.ofList [Atom, Atom])])), Type_E(PolyType("n"))), Type_E(Atom)))))], 
               Type_E(PolyType("fact")))

[<Test>]
let ``Factorial Definition``() = type_check fact == "(Atom -> Atom)"