# Hydrogen
Type inference playground.

# Calculus' syntax
<img src="https://render.githubusercontent.com/render/math?math=\text{var} \ni x,\dots">

<img src="https://render.githubusercontent.com/render/math?math=\text{tvar} \ni \alpha,\dots">

<img src="https://render.githubusercontent.com/render/math?math=\text{type} \ni \tau \Coloneqq \alpha \mid \text{Int} \mid \tau \rightarrow \tau">

<img src="https://render.githubusercontent.com/render/math?math=\text{expr} \ni e \Coloneqq x \mid n \mid \lambda x . e \mid \text{fun} f x . e \mid e \: e \mid \text{let} x = e \: \text{in} \: e">

# Usage
Simply running `ocaml hydrogen.ml` should result in output like:
```
Type of λx. x is 't0 -> 't0
Type of λx. x 2 is (Int -> 't1) -> 't1
ERROR: Cannot construct infinite type t0 ~ t0 -> t1
Type of λx. x x is ILL-TYPED
Type of λy. (λx. x) 1 is 't0 -> Int
Type of λx. λy. x is 't0 -> 't1 -> 't0
Type of λy. (λx. y x) 1 is (Int -> 't3) -> 't3
Type of λx. (λy. y) (x 42) is (Int -> 't3) -> 't3
Type of λx. λy. λz. (x z) (y z) is ('t2 -> 't4 -> 't5) -> ('t2 -> 't4) -> 't2 -> 't5
Type of let f = λx. x 1 in λy. f (λx. y x) is (Int -> 't6) -> 't6 with env: (f : (Int -> 't1) -> 't1)
Type of let g = λx. x (x 1) in let f = λx. x 1 in λy. g (f (λx. y x)) is (Int -> Int -> Int) -> Int with env: (f : (Int -> 't4) -> 't4) (g : (Int -> Int) -> Int)
Type of fun f x. f (f 1) is Int -> Int
Type of fun fix f. f (fix f) is ('t2 -> 't2) -> 't2
Type of (fun fix f. f (fix f)) (λx. λy. λz. 2) is 't5 -> 't6 -> Int
Type of let id = λx. x in id id is 't2 -> 't2 with env: (id : 't0 -> 't0)
```