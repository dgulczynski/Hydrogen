#use "hydrogen.ml"

let print_inferred_type (expr : expr) : unit =
  let gamma, t = infer_type expr in
  Printf.printf "Type of %s is %s" (string_of_expr expr) (string_of_type t);
  if gamma = [] then Printf.printf "\n"
  else (
    Printf.printf " with env:";
    List.iter
      (fun (x, t) -> Printf.printf " (%s : %s)" x (string_of_type t))
      gamma;
    Printf.printf "\n" )

let some_terms =
  [
    Lam ("x", V "x");
    Lam ("x", App (V "x", I 2));
    Lam ("x", App (V "x", V "x"));
    Lam ("y", App (Lam ("x", V "x"), I 1));
    Lam ("x", Lam ("y", V "x"));
    Lam ("y", App (Lam ("x", App (V "y", V "x")), I 1));
    Lam ("x", App (Lam ("y", V "y"), App (V "x", I 42)));
    Lam ("x", Lam ("y", Lam ("z", App (App (V "x", V "z"), App (V "y", V "z")))));
    Let
      ( "f",
        Lam ("x", App (V "x", I 1)),
        Lam ("y", App (V "f", Lam ("x", App (V "y", V "x")))) );
    Let
      ( "g",
        Lam ("x", App (V "x", App (V "x", I 1))),
        Let
          ( "f",
            Lam ("x", App (V "x", I 1)),
            Lam ("y", App (V "g", App (V "f", Lam ("x", App (V "y", V "x")))))
          ) );
    Fun ("f", "x", App (V "f", App (V "f", I 1)));
    Fun ("fix", "f", App (V "f", App (V "fix", V "f")));
    App
      ( Fun ("fix", "f", App (V "f", App (V "fix", V "f"))),
        Lam ("x", Lam ("y", Lam ("z", I 2))) );
    Let ("id", Lam ("x", V "x"), App (V "id", V "id"));
  ]

let _ = List.iter print_inferred_type some_terms