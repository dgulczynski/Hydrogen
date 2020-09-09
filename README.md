# Hydrogen
Bachelor thesis project regarding type inference in presence of algebraic effects.

# Usage
To build the project along with examples use `ocamlbuild examples.byte`.

To try your own examples, you can use functions `print_inferred_type` or `print_examples` from README.md.

To start repl session use `ocaml` or `utop` with `-init print_examples.ml`.

Running `./examples.byte` (alternatively `ocaml print_examples.ml`) should result in output like:
```
Simple effects:
⊢ λe:Error. λx. raise_e x : ∀e:Error. Unit -{e}-> ?τ1 / ι
⊢ handle put 21 {put v k. k () | get () k. k 37 | return x. x} : Unit / ι

Nested effects:
⊢ λy. handle_a handle_b put_a ((get_b ()) y) {get () k. k (λx. x) | put v k. k () | return x. x} {get () k. k 42 | put v k. k () | return x. x} : Int -> Unit / ι

Effect generalization:
⊢ let apply = λf. λx. f x in apply (λx. x) : ?τ4 -> ?τ4 / ι
  (apply : ('τa -{'εb}-> 'τc) -> 'τa -{'εb}-> 'τc)
⊢ let update = λs:State 'a. λf. put_s (f (get_s ())) in update : ∀s:State ?τ9. (?τ9 -{s,?ε5}-> ?τ9) -{s,?ε5}-> Unit / ι
  (update : ∀s:State 'a. ('a -{s,'εa}-> 'a) -{s,'εa}-> Unit)
⊢ let move_map = λfrom:State a. λto:State b. λf. put_to (f (get_from ())) in 1 : Int / ι
  (move_map : ∀from:State a. ∀to:State b. (a -{from,'εa}-> b) -{from,to,'εa}-> Unit)

Instance application:
⊢ let putx = λs:State Int. λx. put_s x in handle_a (putx<a>) 1 {put v k. k () | get () k. k 1 | return x. 2} : Int / ι
  (putx : ∀s:State Int. Int -{s}-> Unit)
⊢ let update = λs:State a. λf. put_s (f (get_s ())) in handle_b (λ(). get_b ()) ((update<b>) (λx. x)) {get () k. λc. (k c) c | put v k. λc. (k ()) v | return x. λc. x} : ?τ21 -> ?τ21 / ι
  (update : ∀s:State a. (a -{s,'εa}-> a) -{s,'εa}-> Unit)

Simple examples:
⊢ λx. x : ?τ0 -> ?τ0 / ι
⊢ λg. λf. λx. g (f x) : (?τ4 -{?ε1}-> ?τ5) -> (?τ3 -{?ε1}-> ?τ4) -> ?τ3 -{?ε1}-> ?τ5 / ι
⊢ λx. x 2 : (Int -{?ε2}-> ?τ7) -{?ε2}-> ?τ7 / ι
⊢ λy. (λx. x) 1 : ?τ8 -> Int / ι
⊢ λx. λy. x : ?τ11 -> ?τ12 -> ?τ11 / ι
⊢ λy. (λx. y x) 1 : (Int -{?ε5}-> ?τ16) -{?ε5}-> ?τ16 / ι
⊢ λx. (λx. x) (x 42) : (Int -{?ε7}-> ?τ20) -{?ε7}-> ?τ20 / ι
⊢ λx. λy. λz. (x z) (y z) : (?τ23 -{?ε10}-> ?τ25 -{?ε10}-> ?τ26) -> (?τ23 -{?ε10}-> ?τ25) -> ?τ23 -{?ε10}-> ?τ26 / ι

Let bindings:
⊢ let f = λx. x 1 in λy. f (λx. y x) : (Int -{?ε3}-> ?τ6) -{?ε3}-> ?τ6 / ι
  (f : (Int -{'εa}-> 'τb) -{'εa}-> 'τb)
⊢ let g = λx. x (x 1) in let f = λx. x 1 in λy. g (f (λx. y x)) : (Int -{?ε11}-> Int -{?ε11}-> Int) -{?ε11}-> Int / ι
  (f : (Int -{'εa}-> 'τb) -{'εa}-> 'τb)
  (g : (Int -{'εa}-> Int) -{'εa}-> Int)

Recursive functions:
⊢ fun f x. f (f 1) : Int -> Int / ι
⊢ let fix = fun fix f. f (fix f) in fix (λx. λy. λz. 2) : ?τ10 -> ?τ11 -> Int / ι
  (fix : ('τa -{'εb}-> 'τa) -{'εb}-> 'τa)

Parametric polymorphism:
⊢ let id = λx. x in id id : ?τ2 -> ?τ2 / ι
  (id : 'τa -> 'τa)
⊢ λx. (λy. y) (x 1) : (Int -{?ε2}-> ?τ7) -{?ε2}-> ?τ7 / ι
⊢ λx. let y = x 1 in y : (Int -{?ε4}-> ?τ9) -{?ε4}-> ?τ9 / ι
  (y : ?τ9)

Ill-typed examples:
Type inference error: The type variable ?τ0 occurs inside ?τ0 -{?ε0}-> ?τ1
⊢ λx. x x : ILL-TYPED / ι
Type inference error: Instance (e : Error) application to (λx. x : ?τ2 -> ?τ2 / ι) which does not reduce to instance lambda
⊢ λe:Error. (λx. x)<e> : ILL-TYPED / ι
Type inference error: Nested unnamed handlers
⊢ handle handle put ((get ()) y) {get () k. k (λx. x) | return x. x} {put v k. k () | return x. x} : ILL-TYPED / ι

```
