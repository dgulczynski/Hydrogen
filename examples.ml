#use "hydrogen.ml"

let print_inferred_type (expr : expr) : unit =
  let gamma, t = infer_type expr in
  print_string ("Type of " ^ string_of_expr expr ^ " is " ^ string_of_type t) ;
  if gamma = [] then print_newline ()
  else (
    print_string " with env:" ;
    List.iter (fun (x, t) -> print_string (" (" ^ x ^ " : " ^ string_of_type t ^ ")")) gamma ;
    print_newline () )

let print_examples (name : string) (es : expr list) =
  print_string (name ^ ":\n") ;
  List.iter print_inferred_type es ;
  print_newline ()

(* Infix alternatives consructors *)
let ( @: ) e1 e2 = App (e1, e2)

let _ =
  print_examples "Simple examples"
    [ Lam ("x", V "x")
    ; Lam ("x", V "x" @: I 2)
    ; Lam ("y", Lam ("x", V "x") @: I 1)
    ; Lam ("x", Lam ("y", V "x"))
    ; Lam ("y", Lam ("x", V "y" @: V "x") @: I 1)
    ; Lam ("x", Lam ("x", V "x") @: V "x" @: I 42)
    ; Lam ("x", Lam ("y", Lam ("z", (V "x" @: V "z") @: V "y" @: V "z"))) ]

let _ =
  print_examples "Let bindings"
    [ Let ("f", Lam ("x", V "x" @: I 1), Lam ("y", V "f" @: Lam ("x", V "y" @: V "x")))
    ; Let
        ( "g"
        , Lam ("x", V "x" @: V "x" @: I 1)
        , Let
            ( "f"
            , Lam ("x", V "x" @: I 1)
            , Lam ("y", V "g" @: V "f" @: Lam ("x", V "y" @: V "x")) ) ) ]

let _ = print_examples "Ill-typed example" [Lam ("x", V "x" @: V "x")]

let _ =
  print_examples "Recursive functions"
    [ Fun ("f", "x", V "f" @: V "f" @: I 1)
    ; Let
        ( "fix"
        , Fun ("fix", "f", V "f" @: V "fix" @: V "f")
        , V "fix" @: Lam ("x", Lam ("y", Lam ("z", I 2))) ) ]

let _ =
  print_examples "Parametric polymorphism"
    [ Let ("id", Lam ("x", V "x"), V "id" @: V "id")
    ; Lam ("x", Lam ("y", V "y") @: V "x" @: I 1)
    ; Lam ("x", Let ("y", V "x" @: I 1, V "y")) ]

let _ =
  print_examples "Annotations"
    [ Let
        ( "id"
        , Lam ("x", V "x")
        , Annoted (V "id", Arrow (GV "b", GV "b"))
          @: Annoted (V "id", Arrow (GV "c", GV "c")) ) ]
