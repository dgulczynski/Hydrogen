# Hydrogen
Type inference playground.

# Calculus' syntax
<img src="https://render.githubusercontent.com/render/math?math=\text{var} \ni x,\dots">

<img src="https://render.githubusercontent.com/render/math?math=\text{tvar} \ni \alpha,\dots">

<img src="https://render.githubusercontent.com/render/math?math=\text{type} \ni \tau \Coloneqq \alpha \mid \text{Int} \mid \tau \rightarrow \tau">

<img src="https://render.githubusercontent.com/render/math?math=\text{expr} \ni e \Coloneqq x \mid n \mid \lambda x . e \mid \text{fun} f x . e \mid e \: e \mid \text{let} x = e \: \text{in} \: e">

# Usage
Simply running `ocaml examples.ml` should result in output like:
```
Simple examples:
Type of λx. x is _a -> _a
Type of λx. x 2 is (Int -> _b) -> _b
Type of λy. (λx. x) 1 is _a -> Int
Type of λx. λy. x is _a -> _b -> _a
Type of λy. (λx. y x) 1 is (Int -> _d) -> _d
Type of λx. (λx. x) (x 42) is (Int -> _d) -> _d
Type of λx. λy. λz. (x z) (y z) is (_c -> _e -> _f) -> (_c -> _e) -> _c -> _f

Let bindings:
Type of let f = λx. x 1 in λy. f (λx. y x) is (Int -> _g) -> _g with env: (f : (Int -> 'a) -> 'a)
Type of let g = λx. x (x 1) in let f = λx. x 1 in λy. g (f (λx. y x)) is (Int -> Int -> Int) -> Int with env: (f : (Int -> 'a) -> 'a) (g : (Int -> Int) -> Int)

Ill-typed example:
Type inference error: The type variable _a occurs inside _a -> _b
Type of λx. x x is ILL-TYPED

Recursive functions:
Type of fun f x. f (f 1) is Int -> Int
Type of let fix = fun fix f. f (fix f) in fix (λx. λy. λz. 2) is _g -> _h -> Int with env: (fix : ('a -> 'a) -> 'a)

Parametric polymorphism:
Type of let id = λx. x in id id is _c -> _c with env: (id : 'a -> 'a)
Type of λx. (λy. y) (x 1) is (Int -> _d) -> _d
Type of λx. let y = x 1 in y is (Int -> _b) -> _b
```
