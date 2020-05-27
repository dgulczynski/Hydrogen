#use "effects.ml"

let print_inferred_type (expr : expr) : unit =
  let strexpr = "Type / effect of " ^ string_of_expr expr ^ " is "
  and gamma, t, e = infer_type expr in
  if gamma = [] then
    print_string
      (strexpr ^ string_of_type t ^ " / " ^ string_of_effect e ^ "\n")
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

let ( ->: ) t1 t2 eff = Arrow (t1, t2, eff)

let _ =
  print_examples "Simple effects"
    [ ILam ("e", Error, Lam("x", Op ("e", Throw) @: V "x"))
    ; Handle
        ( "a"
        , State Int
        , Op ("a", Put) @: I 21
        , ( [(Put, "v", "k", V "k" @: Nil); (Get, "()", "k", V "k" @: I 37)]
          , "x"
          , Lam ("y", V "x") ) ) ]

let _ =
  print_examples "Nested effects"
    [ Lam
        ( "y"
        , Handle
            ( "a"
            , State Int
            , Handle
                ( "b"
                , State ((Int ->: Int) Pure)
                , Op ("a", Put) @: (Op ("b", Get) @: Nil) @: V "y"
                , ([(Get, "()", "k", V "k" @: Lam ("x", V "x"))], "x", V "x")
                )
            , ([(Put, "v", "k", V "k" @: Nil)], "x", V "x") ) ) ]
