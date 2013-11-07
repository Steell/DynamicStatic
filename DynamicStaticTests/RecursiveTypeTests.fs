module DynamicStatic.Tests.RecursiveTypeTests

open NUnit.Framework
open NUnit.FSharp.TestUtils

open DynamicStatic.DS
open DynamicStatic.Type
open DynamicStatic.TypeExpression

let typecheck = type_check >> type2str


(*  ;; omega :: A -> Z
    (define (omega x) (x x))

    ;; omega :: (A -> B) -> B
    ;;   where A = A -> B
*)
let omega = Fun("x", Call(Type_E(PolyType("x")), Type_E(PolyType("x"))))

[<Test>]
let ``omega == 'a where 'a = ('a -> 'b)``() = typecheck omega == "'a where 'a = ('a -> 'b)"


(*  ;; Y :: A -> Z
    (define (Y f)
        ((lambda (x) (x x))
         (lambda (x) (f (lambda (v) ((x x) v))))))

    ;; Y :: ((A -> B) C -> D) -> (C -> D)
    ;;   where A = A -> B
*)
let yComb = Fun("f",
                Call(omega, 
                     Fun("w", 
                         Call(Type_E(PolyType("f")), 
                              Fun("v", 
                                  Call(Call(Type_E(PolyType("w")), 
                                            Type_E(PolyType("w"))), 
                                       Type_E(PolyType("v"))))))))

[<Test; Timeout(2000)>]
let ``Y == ((('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b))``() = typecheck yComb == "((('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b))"


let factY =
    Call(yComb,
         Fun("fact",
             Fun("n", 
                 If(Call(Call(Type_E(Func(Set.ofList [Atom, Func(Set.ofList [Atom, Union(Set.ofList [True; False])])])), Type_E(PolyType("n"))), Type_E(Atom)), 
                    Type_E(Atom), 
                    Call(Type_E(PolyType("fact")), Call(Call(Type_E(Func(Set.ofList [Atom, Func(Set.ofList [Atom, Atom])])), Type_E(PolyType("n"))), Type_E(Atom)))))))

[<Test; Timeout(2000)>]
let ``(Y fact/Y) == (Atom -> Atom)``() = typecheck factY == "(Atom -> Atom)"


(*  ;; flatten :: A -> Z
    (define (flatten l)
        (if (not (list? l))
            (list l)
            (if (empty? l)
                empty
                (append (flatten (first l))
                        (flatten (rest l))))))

    ;; flatten :: A -> List<Atom>
    ;;   where A = Atom|List<A>
*)
