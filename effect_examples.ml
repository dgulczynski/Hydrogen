#use "effects.ml"

let print_inferred_type (expr : expr) : unit =
  let strexpr = "Type of " ^ string_of_expr expr ^ " is "
  and gamma, t = infer_type expr in
  if gamma = [] then print_string (strexpr ^ string_of_type t ^ "\n")
  else (
    print_string (strexpr ^ string_of_type t ^ " with env:") ;
    List.iter
      (fun (x, t) -> print_string (" (" ^ x ^ " : " ^ string_of_type t ^ ")"))
      gamma ;
    print_newline () )

let print_examples (name : string) (es : expr list) =
  print_string (name ^ ":\n") ;
  List.iter print_inferred_type es ;
  print_newline ()

(* Infix alternative constructors *)
let ( @: ) e1 e2 = App (e1, e2)

let ( ->: ) t1 t2 = Arrow (t1, t2)

let _ =
  print_examples "Simple effects"
    [ ILam ("a", State Int, Lam ("x", Op ("a", Put) @: V "x"))
    ; Op ("e", Throw) @: I 1 ]
