module OverloadTests

open NUnit.Framework
open DynamicStatic
open TestUtils

let typecheck = type_check >> type2str

let notExpr = Fun("x", If(Type_E(PolyType("x")), Type_E(False), Type_E(True)))
let notType = Func(Set.ofList [True, False; False, True])

[<Test>]
let ``Not Definition``() = type_check notExpr == notType

[<Test>]
let ``Call Not: 1 Overload Match``() =
    typecheck (Call(Type_E(notType), Type_E(True))) == "False";
    typecheck (Call(Type_E(notType), Type_E(False))) == "True";

[<Test>]
let ``Call Not: 2 Overload Match``() =
    typecheck (Call(Type_E(notType), Type_E(Union(Set.ofList [True; False])))) == "{True|False}"



(*  ;; filter :: A B -> Z
    (define (filter l p)
      (if (empty? l)
          <1> empty
          ;; x :: F
          <2> (let ((x (first l)))
            (if (p x)
                <3> (cons x (filter (rest l) p))
                <4> (filter (rest l) p)))))

    ;; filter :: List<A|B> ((A -> True)+(B -> False)) -> List<A>
*)
let filter = 
    Let(["filter"], 
        [Fun("l", Fun("p", If(Call(Type_E(Func(Set.ofList [List(PolyType("A")), Union(Set.ofList [True; False])])), Type_E(PolyType("l"))), 
                              Type_E(PolyType("M")), 
                              Let(["x"], [Call(Type_E(Func(Set.ofList [List(PolyType("B")), PolyType("B")])), 
                                               Type_E(PolyType("l")))], 
                                If(Call(Type_E(PolyType("p")), 
                                        Type_E(PolyType("x"))), 
                                    Call(Call(Type_E(Func(Set.ofList [PolyType("C"), Func(Set.ofList [List(PolyType("D")), List(Union(Set.ofList [PolyType("C"); PolyType("D")]))])])), 
                                              Type_E(PolyType("x"))),
                                        Call(Call(Type_E(PolyType("filter")), 
                                                  Call(Type_E(Func(Set.ofList [List(PolyType("K")), List(PolyType("K"))])),Type_E(PolyType("l")))), 
                                             Type_E(PolyType("p")))),
                                    Call(Call(Type_E(PolyType("filter")), 
                                              Call(Type_E(Func(Set.ofList [List(PolyType("L")), List(PolyType("L"))])), 
                                                   Type_E(PolyType("l")))),
                                         Type_E(PolyType("p"))))))))], 
        Type_E(PolyType("filter")))

[<Test>]
let ``Filter Definition``() = 
    typecheck filter == "(List<{'a|'b}> -> ((('a -> True)+('b -> False)) -> List<'a>))"