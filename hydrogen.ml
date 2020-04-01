type var = string

type tvar = string

type expr = App of expr * expr | Lam of var * expr | I of int | V of var

type t = Int | Arrow of t * t | TV of tvar | Bad

let rec string_of_type (t : t) : string =
  match t with
  | Int -> "Int"
  | Arrow (t1, t2) -> (
      match t1 with
      | Arrow _ -> "(" ^ string_of_type t1 ^ ") -> " ^ string_of_type t2
      | _ -> string_of_type t1 ^ " -> " ^ string_of_type t2 )
  | TV tv -> tv
  | Bad -> "ILL-TYPED"

let rec string_of_expr (e : expr) : string =
  match e with
  | I i -> string_of_int i
  | V v -> v
  | Lam (var, e') -> "λ" ^ var ^ ". " ^ string_of_expr e'
  | App (e', e'') -> (
      ( match e' with
        | I i -> string_of_int i
        | V v -> v
        | _ -> "(" ^ string_of_expr e' ^ ")" )
      ^ " "
      ^
      match e'' with
      | I i -> string_of_int i
      | V v -> v
      | _ -> "(" ^ string_of_expr e'' ^ ")" )

let infer_type (expr : expr) =
  let rec gather_constraints (gamma : (var * t) list) (expr : expr) (cs : (t * t) list) :
    (var * t) list * t * (t * t) list =
    match expr with
    | I _ -> (gamma, Int, cs)
    | App (f, x) ->
      let fgamma, tf, csf = gather_constraints gamma f cs in
      let xgamma, tx, csx = gather_constraints fgamma x csf in
      let tfx = newTV () in
      (xgamma, tfx, (tf, Arrow (tx, tfx)) :: csx)
    | Lam (x, e) ->
      let tx = newTV () in
      let egamma, te, cse = gather_constraints ((x, tx) :: gamma) e cs in
      (egamma, Arrow (tx, te), cse)
    | V v -> (gamma, snd (List.find (fun (v', t') -> v' = v) gamma), cs)
  and unify_types (t : t) (cs : (t * t) list) =
    match cs with
    | [] -> t
    | (Arrow (t1, t2), Arrow (t1', t2')) :: cs ->
      unify_types t ((t1, t1') :: (t2, t2') :: cs)
    | (TV a, t2) :: cs ->
      if TV a = t2 then unify_types t cs
      else if occurs (TV a) t2 then (
        Printf.printf "ERROR: Cannot construct infinite type %s ~> %s\n" a (string_of_type t2);
        Bad )
      else
        let substitute = subst (TV a) t2 in 
        unify_types (substitute t)
          (List.map
             (fun (c1, c2) -> (substitute c1, substitute c2))
             cs)
    | (t1, TV t2) :: cs -> unify_types t ((TV t2, t1) :: cs)
    | (t1, t2) :: cs ->
      Printf.printf "This probably shouldn't happen: unification of %s and %s\n" (string_of_type t1) (string_of_type t2);
      unify_types t cs
  and subst x v t =
    match t with
    | Arrow (t1, t2) -> Arrow (subst x v t1, subst x v t2)
    | _ -> if t = x then v else t
  and occurs (x : t) (t : t) =
    match t with
    | Arrow (t1, t2) -> occurs x t1 || occurs x t2
    | _ -> t = x
  and newTV : unit -> t =
    let counter = ref (-1) in
    (fun _ ->  counter := !counter + 1; 
      TV ("t" ^ string_of_int !counter))
  in
  let gamma, t, cs = gather_constraints [] expr [] in
  let t' = unify_types t cs in
  Printf.printf "Type of %-24s\tis %s\n" (string_of_expr expr) (string_of_type t');
  t'

let some_terms =
  [
    Lam ("x", V "x");
    Lam ("x", App (V "x", I 2));
    Lam ("x", App (V "x", V "x"));
    Lam ("y", App (Lam ("x", V "x"), I 1));
    Lam ("y", App (Lam ("x", App (V "y", V "x")), I 1));
    Lam ("x", Lam ("y", V "x"));
    Lam ("x", App (Lam ("y", V "y"), App (V "x", I 42)));
    Lam ("x", Lam ("y", Lam ("z", App (App (V "x", V "z"), App (V "y", V "z")))));
    Lam ("y", App (Lam ("x", App (V "y", V "x")), I 1));
  ]

let _ = List.map infer_type some_terms
