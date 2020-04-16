type var = string

type tvar = string

type expr =
  | App of expr * expr
  | Lam of var * expr
  | I of int
  | V of var
  | Let of var * expr * expr
  | Fun of var * var * expr

type t = Int | Arrow of t * t | TV of tvar | GV of tvar | Bad

let rec string_of_type (t : t) : string =
  match t with
  | Int -> "Int"
  | Arrow (t1, t2) -> (
      match t1 with
      | Arrow _ -> "(" ^ string_of_type t1 ^ ") -> " ^ string_of_type t2
      | _ -> string_of_type t1 ^ " -> " ^ string_of_type t2 )
  | TV tv -> tv
  | GV tv -> "'" ^ tv
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
      ^ " " ^
      match e'' with
      | I i -> string_of_int i
      | V v -> v
      | _ -> "(" ^ string_of_expr e'' ^ ")" )
  | Let (var, body, expr) ->
      "let " ^ var ^ " = " ^ string_of_expr body ^ " in " ^ string_of_expr expr
  | Fun (f, x, body) -> "fun " ^ f ^ " " ^ x ^ ". " ^ string_of_expr body

let infer_type (expr : expr) =
  let rec gather_constraints (gamma : (var * t) list) (expr : expr) (cs : (t * t) list) 
  : (var * t) list * t * (t * t) list =
    match expr with
    | I _ -> (gamma, Int, cs)
    | V v -> (gamma, instantiate (snd (List.find (fun (v', t') -> v' = v) gamma)), cs)
    | Lam (x, e) ->
        let tx = newTV () in
        let _, te, cse = gather_constraints ((x, tx) :: gamma) e cs in
        (gamma, Arrow (tx, te), cse)
    | Fun (f, x, e) ->
        let tx = newTV () and tfx = newTV () in
        let tf = Arrow (tx, tfx) in
        let _, te, cse =
          gather_constraints ((f, tf) :: (x, tx) :: gamma) e cs
        in
        (gamma, Arrow (tx, te), (tf, Arrow (tx, te)) :: cse)
    | App (f, x) ->
        let _, tf, csf = gather_constraints gamma f cs in
        let _, tx, csx = gather_constraints gamma x csf in
        let tfx = newTV () in
        (gamma, tfx, (tf, Arrow (tx, tfx)) :: csx)
    | Let (x, e, e') ->
        let _, te, cse = gather_constraints gamma e cs in
        gather_constraints
          ( ( x,
              generalize
                (free_type_variables (List.map snd gamma))
                (unify_types te cse) )
          :: gamma )
          e' cs
  
  and unify_types (t : t) (cs : (t * t) list) : t =
    match cs with
    | [] -> t
    | (Arrow (t1, t2), Arrow (t1', t2')) :: cs ->
        unify_types t ((t1, t1') :: (t2, t2') :: cs)
    | (TV a, t2) :: cs ->
        if TV a = t2 then unify_types t cs
        else if occurs (TV a) t2 then (
          Printf.printf "ERROR: Cannot construct infinite type %s ~ %s\n" a
            (string_of_type t2);
          Bad )
        else
          let substitute = subst a t2 in
          unify_types (substitute t)
            (List.map (fun (c1, c2) -> (substitute c1, substitute c2)) cs)
    | (t1, TV a) :: cs -> unify_types t ((TV a, t1) :: cs)
    | (t1, t2) :: cs ->
        if t1 = t2 then unify_types t cs
        else (
          Printf.printf
            "This probably shouldn't happen: constraint of type %s ~ %s\n"
            (string_of_type t1) (string_of_type t2);
          unify_types t cs )
  
  and subst (x : tvar) (v : t) (t : t) : t =
    match t with
    | Arrow (t1, t2) -> Arrow (subst x v t1, subst x v t2)
    | TV tv -> if x = tv then v else t
    | _ -> t
  
  and occurs (x : t) (t : t) : bool =
    match t with Arrow (t1, t2) -> occurs x t1 || occurs x t2 | _ -> t = x
  
  and newTV : unit -> t =
    let counter = ref (-1) in
    fun _ ->
      counter := !counter + 1;
      TV ("t" ^ string_of_int !counter)

  and generalize (ftv : tvar list) (t : t) : t =
    match t with
    | Arrow (t1, t2) -> Arrow (generalize ftv t1, generalize ftv t2)
    | TV tv -> if List.mem tv ftv then TV tv else GV tv
    | _ -> t

  and free_type_variables (ts : t list) =
    match ts with
    | [] -> []
    | Arrow (t1, t2) :: ts' -> free_type_variables (t1 :: t2 :: ts')
    | TV tv :: ts' -> tv :: free_type_variables ts'
    | _ :: ts' -> free_type_variables ts'
  
  and instantiate (t : t) =
    let rec aux t instd =
      match t with
      | Arrow (t1, t2) ->
          let t1', instd' = aux t1 instd in
          let t2', instd'' = aux t2 instd' in
          (Arrow (t1', t2'), instd'')
      | GV gv -> handle gv instd instd
      | _ -> (t, instd)
    and handle gv instd original =
      match instd with
      | [] ->
          let ntv = newTV () in
          (ntv, (gv, ntv) :: original)
      | (gv', tv') :: instd' ->
          if gv' = gv then (tv', original) else handle gv instd' original
    in
    fst (aux t [])
  
  in
  let gamma, t, cs = gather_constraints [] expr [] in
  let t' = generalize (free_type_variables (List.map snd gamma)) (unify_types t cs) in
  Printf.printf "Type of %s is %s" (string_of_expr expr) (string_of_type t');
  if gamma = [] then Printf.printf "\n"
  else (
    Printf.printf " with env:";
    List.iter
      (fun (x, t) -> Printf.printf " (%s : %s)" x (string_of_type t))
      gamma;
    Printf.printf "\n" );
  t'

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

let _ = List.map infer_type some_terms
