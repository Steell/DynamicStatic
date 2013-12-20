DynamicStatic
=============

Work in progress type inference prototype. Supports subtypes, type unions, function overloads, and recursive types.


The following Scheme program for filtering a list:

```scheme
(define filter 
  (lambda (l) (lambda (p)
    (if (empty? l)
        empty
        (let ([x (first l)]
              [r (filter (rest l))])
          (if (p x) (cons x r) r))))
```

is inferred to have the following type:

```scheme
;; filter :: Listof({'a|'b}) -> (('a -> True)+('b -> False)) -> Listof('a)
```

given the following built-in function type information:

```scheme
;; Bool = {True|False}

;; empty? :: Listof(Any) -> Bool
;; empty :: Listof('a)
;; first :: Listof('a) -> 'a
;; rest :: Listof('a) -> Listof('a)
;; cons :: 'a -> Listof('b) -> Listof({'a|'b})
```

The main idea is that Hindley-Milner type inference correctly represents how we reason about types, but can be expanded to include more concepts. By introducing function overloads, union types, and recursive types, the Hindley-Milner algorithm can resolve types for many programs that previously required explicit type annotations.

In the `filter` example, by inferring the type of parameter `p` to be an overloaded function, the type of `x` can be inferred in two separate branches. References to `x` outside the conditional branches see the type of `x` as `{'a|'b}`, but in the branches the type is seen as `'a` or `'b` (depending on the branch).

All of the following uses of `filter` correctly resolve:

```scheme
;; filter :: Listof(Listof(Integer)) -> (Listof(Integer) -> {True|False}) -> Listof(Integer)
(filter '(() (1) (2) ()) (lambda (x) (not (empty? x))))

;; filter :: Listof({String|Integer}) -> ((String -> True)+(Integer->False)) -> Listof(String)
(filter '("foo" 0 "bar" 1) string?) ; string? :: (String -> True)+(~String -> False)
```


## Let-bound polymorphism


```scheme
((lambda (f) (f "string!") (f 1)) (lambda (x) x))

;; DynamicStatic can resolve the type using an overload:

;; ((String -> Any)+(Integer -> 'b)) -> 'b
(lambda (f) (f "string!") (f 1))
```

## Not implemented

### Recursive Types

Typing the Y-Combinator using recursive types:

```scheme
;; omega :: (R -> 'b)
;;   where R = (R -> 'b)
(define omega (lambda (x) (x x)))

;; Y :: (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
(define Y 
  (lambda (f) 
    (omega (lambda (x) (f (lambda (v) ((x x) v)))))))

;; fact/Y :: Integer -> Integer
(define fact/Y
  (Y (lambda (fact)
       (lambda (n)
         (if (<= 0 n) 
             1 
             (* n (fact (sub1 n))))))))
```

Flattening a list:

```scheme
;; flatten :: (R -> List<Atom>)
;;    where R = {Atom|List<R>}
(define flatten
  (lambda (x)
    (if (list? x)
        (if (empty? x)
            empty
            (append (flatten (first x))
                    (flatten (rest x))))
        (list x))))
```
