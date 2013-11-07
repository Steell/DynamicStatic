module DynamicStatic.Tests.OverloadTests

open NUnit.Framework
open DynamicStatic.DS
open DynamicStatic.Type
open DynamicStatic.TypeExpression
open TestUtils

let typecheck = type_check >> type2str

let notExpr = Fun("x", If(Type_E(PolyType("x")), Type_E(False), Type_E(True)))
let notType = Func(Set.ofList [True, False; False, True])

[<Test>]
let ``not == ((True -> False) + (False -> True))``() = type_check notExpr == notType

[<Test>]
let ``(not True) == False and (not False) == True``() =
    typecheck (Call(Type_E(notType), Type_E(True))) == "False";
    typecheck (Call(Type_E(notType), Type_E(False))) == "True";

[<Test>]
let ``(not {True|False}) == {True|False}``() =
    typecheck (Call(Type_E(notType), Type_E(Union(Set.ofList [True; False])))) == "{True|False}"


let overloadedType = Func(Set.ofList [True, Atom; False, Atom; Atom, Atom])

[<Test>]
let ``Arbitrary Overload Call: 1 Match``() =
    typecheck (Call(Type_E(overloadedType), Type_E(True))) == "Atom";
    typecheck (Call(Type_E(overloadedType), Type_E(False))) == "Atom";
    typecheck (Call(Type_E(overloadedType), Type_E(Atom))) == "Atom";

[<Test>]
let ``Arbitrary Overload Call: 2 Match``() =
    typecheck (Call(Type_E(overloadedType), Type_E(Union(Set.ofList [True; False])))) == "Atom";
    typecheck (Call(Type_E(overloadedType), Type_E(Union(Set.ofList [True; Atom])))) == "Atom";
    typecheck (Call(Type_E(overloadedType), Type_E(Union(Set.ofList [False; Atom])))) == "Atom";

[<Test>]
let ``Arbitrary Overload Call: 3 Match``() =
    typecheck (Call(Type_E(overloadedType), Type_E(Union(Set.ofList [True; False; Atom])))) == "Atom";


[<Test>]
let ``Overload Definition: ((List<'a> -> Atom) -> (Atom -> List<Atom>))``() =
    let overloadedFunction =
        Fun("x", If(Call(Type_E(Func(Set.ofList [List(PolyType("A")), True; Not(List(PolyType("A"))), False])),
                         Type_E(PolyType("x"))),
                    Type_E(Atom),
                    Call(Type_E(Func(Set.ofList [Atom, List(Atom)])),
                         Type_E(PolyType("x")))))
    typecheck overloadedFunction == "((List<'a> -> Atom) -> (Atom -> List<Atom>))"




(*  ;; filter :: A B -> Z
    (define (filter l p)
      (if (empty? l)
          empty
          (let ((x (first l)))
            (if (p x)
                (cons x (filter (rest l) p))
                (filter (rest l) p)))))

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
let ``filter == (List<{'a|'b}> -> ((('a -> True)+('b -> False)) -> List<'a>))``() = 
    let t = typecheck filter
    t == "(List<{'a|'b}> -> ((('a -> True)+('b -> False)) -> List<'a>))"

(*  ;; filter :: A B -> Z
    (define (filter l p)
      (if (empty? l)
          empty
          (let ((x (first l))
                (r (filter (rest l) p)))
            (if (p x)
                (cons x r)
                r))))

    ;; filter :: List<A|B> ((A -> True)+(B -> False)) -> List<A>
*)
let filter2 = 
    Let(["filter"], 
        [Fun("l", Fun("p", If(Call(Type_E(Func(Set.ofList [List(PolyType("A")), Union(Set.ofList [True; False])])), Type_E(PolyType("l"))), 
                              Type_E(PolyType("M")), 
                              Let(["x"; "r"], [Call(Type_E(Func(Set.ofList [List(PolyType("B")), PolyType("B")])), 
                                                    Type_E(PolyType("l")));
                                               Call(Call(Type_E(PolyType("filter")), 
                                                         Call(Type_E(Func(Set.ofList [List(PolyType("L")), List(PolyType("L"))])), 
                                                              Type_E(PolyType("l")))),
                                                    Type_E(PolyType("p")))], 
                                If(Call(Type_E(PolyType("p")), 
                                        Type_E(PolyType("x"))), 
                                    Call(Call(Type_E(Func(Set.ofList [PolyType("C"), Func(Set.ofList [List(PolyType("D")), List(Union(Set.ofList [PolyType("C"); PolyType("D")]))])])), 
                                              Type_E(PolyType("x"))),
                                        Type_E(PolyType("r"))),
                                    Type_E(PolyType("r")))))))], 
        Type_E(PolyType("filter")))


[<Test>]
let ``filter2 == (List<{'a|'b}> -> ((('a -> True)+('b -> False)) -> List<'a>))``() = 
    let t = typecheck filter2
    t == "(List<{'a|'b}> -> ((('a -> True)+('b -> False)) -> List<'a>))"