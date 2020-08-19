;;
#use "hydrogen.ml"

let print_inferred_type (expr : expr) : unit =
  let strexpr = "Type of " ^ string_of_expr expr ^ " is " and gamma, t = infer_type expr in
  if gamma = [] then print_string (strexpr ^ string_of_type t ^ "\n")
  else (
    print_string (strexpr ^ string_of_type t ^ " with env:") ;
    List.iter (fun (x, t) -> print_string (" (" ^ x ^ " : " ^ string_of_type t ^ ")")) gamma ;
    print_newline () )

let print_examples (name : string) (es : expr list) =
  print_string (name ^ ":\n") ;
  List.iter print_inferred_type es ;
  print_newline ()

(* Infix alternative constructors *)
let ( @: ) e1 e2 = App (e1, e2)

let ( ->: ) t1 t2 = Arrow (t1, t2)

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
  print_examples "Type annotations"
    [ Let
        ( "id"
        , Annoted
            ( Lam ("x", V "x")
            , let a = TV (ref (Free "a")) in
              a ->: a )
        , Annoted
            ( V "id"
            , let b = TV (ref (Free "b")) in
              b ->: b )
          @: Annoted (V "id", Int ->: Int) )
    ; (let a = TV (ref (Free "a")) and b = TV (ref (Free "b")) and c = TV (ref (Free "c")) in
       TLam
         ( "x"
         , Arrow (a, Arrow (b, c))
         , Lam ("y", TLam ("z", Int, Annoted ((V "x" @: V "z") @: V "y" @: V "z", c))) )) ]
