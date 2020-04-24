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
Type of λx. x is a -> a
Type of λx. x 2 is (Int -> b) -> b
Type of λy. (λx. x) 1 is a -> Int
Type of λx. λy. x is a -> b -> a
Type of λy. (λx. y x) 1 is (Int -> d) -> d
Type of λx. (λx. x) (x 42) is (Int -> d) -> d
Type of λx. λy. λz. (x z) (y z) is (c -> e -> f) -> (c -> e) -> c -> f

Let bindings:
Type of let f = λx. x 1 in λy. f (λx. y x) is (Int -> g) -> g with env: (f : (Int -> 'b) -> 'b)
Type of let g = λx. x (x 1) in let f = λx. x 1 in λy. g (f (λx. y x)) is (Int -> Int -> Int) -> Int with env: (f : (Int -> 'e) -> 'e) (g : (Int -> Int) -> Int)

Ill-typed example:
Type inference error: The type variable a occurs inside a -> b
Type of λx. x x is ILL-TYPED

Recursive functions:
Type of fun f x. f (f 1) is Int -> Int
Type of let fix = fun fix f. f (fix f) in fix (λx. λy. λz. 2) is g -> h -> Int with env: (fix : ('c -> 'c) -> 'c)

Parametric polymorphism:
Type of let id = λx. x in id id is c -> c with env: (id : 'a -> 'a)
Type of λx. (λy. y) (x 1) is (Int -> d) -> d
Type of λx. let y = x 1 in y is (Int -> b) -> b
```
