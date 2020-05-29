# Hydrogen
Type inference playground.

# Calculus' syntax
<img src="https://render.githubusercontent.com/render/math?math=\text{var} \ni x,\dots">

<img src="https://render.githubusercontent.com/render/math?math=\text{tvar} \ni \alpha,\dots">

<img src="https://render.githubusercontent.com/render/math?math=\text{type} \ni \tau \Coloneqq \alpha \mid \text{Int} \mid \tau \rightarrow \tau">

<img src="https://render.githubusercontent.com/render/math?math=\text{expr} \ni e \Coloneqq x \mid n \mid \lambda x . e \mid \text{fun} f x . e \mid e \: e \mid \text{let} x = e \: \text{in} \: e">

# Usage
Simply running `ocaml effect_examples.ml` should result in output like:
```
Simple effects:
Type / effect of λe:Error. λx. raise_e x is ∀e:Error. b -{e:Error}-> a / i
Type / effect of handle_a:State(Int) put_a 21 {put v k. k () | get () k. k 37 | return x. λy. x} is d -> Unit / {a:State(Int)}

Nested effects:
Type / effect of λy. handle_a:State(Int) handle_b:State(Int -> Int) put_a ((get_b ()) y) {get () k. k (λx. x) | return x. x} {put v k. k () | return x. x} is Int -{b:State(Int -> Int) a:State(Int)}-> Unit / i

Instance application:
Type / effect of let putx = λs:State(Int). λx. put_s x in handle_a:State(Int) ((putx)<a>) 1 {put v k. k () | get () k. k 1 | return x. 2} is Int / {a:State(Int)} with env: (putx : ∀s:State(Int). Int -{s:State(Int)}-> Unit)
```
