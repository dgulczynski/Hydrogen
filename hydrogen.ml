type identifier = string

type var = identifier

type typ = Int | Arrow of typ * typ | TV of tvar ref | GV of identifier | Bad

and tvar = Free of identifier | Bound of typ

type expr =
  | I       of int
  | V       of var
  | Lam     of var * expr
  | Fun     of var * var * expr
  | Let     of var * expr * expr
  | App     of expr * expr
  | Annoted of expr * typ
  | TLam    of var * typ * expr

type env = (var * typ) list

exception IllTyped of string

let rec string_of_type : typ -> string = function
  | Int                    -> "Int"
  | Arrow (t1, t2)         -> (
    match t1 with
    | Arrow _ -> "(" ^ string_of_type t1 ^ ") -> " ^ string_of_type t2
    | _       -> string_of_type t1 ^ " -> " ^ string_of_type t2 )
  | TV {contents= Free a}  -> a
  | TV {contents= Bound t} -> string_of_type t
  | GV v                   -> "'" ^ v
  | Bad                    -> "ILL-TYPED"

let rec string_of_expr : expr -> string = function
  | I i            -> string_of_int i
  | V v            -> v
  | Lam (x, e)     -> "λ" ^ x ^ ". " ^ string_of_expr e
  | TLam (x, t, e) -> "λ(" ^ x ^ " : " ^ string_of_type t ^ "). " ^ string_of_expr e
  | Fun (f, x, e)  -> "fun " ^ f ^ " " ^ x ^ ". " ^ string_of_expr e
  | Let (x, e, e') -> "let " ^ x ^ " = " ^ string_of_expr e ^ " in " ^ string_of_expr e'
  | App (e1, e2)   ->
      let aux = function
        | I i            -> string_of_int i
        | V v            -> v
        | Annoted _ as e -> string_of_expr e
        | e              -> "(" ^ string_of_expr e ^ ")"
      in
      aux e1 ^ " " ^ aux e2
  | Annoted (e, t) -> "(" ^ string_of_expr e ^ " : " ^ string_of_type t ^ ")"

let infer_type (expr : expr) =
  let rec m (gamma : env) (t : typ) : expr -> env = function
    | I _             ->
        union (t, Int) ;
        gamma
    | V v             ->
        union (t, instantiate (type_of_var gamma v)) ;
        gamma
    | Lam (x, e)      -> m gamma t (TLam (x, freshTV (), e))
    | TLam (x, tx, e) ->
        let te = freshTV () in
        union (t, Arrow (tx, te)) ;
        let _ = m ((x, tx) :: gamma) te e in
        gamma
    | Fun (f, x, e)   ->
        let _ = m ((f, t) :: gamma) t (Lam (x, e)) in
        gamma
    | Let (x, e, e')  ->
        let te = freshTV () in
        let _ = m gamma te e in
        m ((x, generalize gamma (find te)) :: gamma) t e'
    | App (e1, e2)    ->
        let t2 = freshTV () in
        let _ = m gamma (Arrow (t2, t)) e1 in
        m gamma t2 e2
    | Annoted (e, t') ->
        let _ = m gamma t' e in
        union (t, t') ;
        gamma
  
  and type_of_var (gamma : env) (v : var) : typ =
    match List.assoc_opt v gamma with
    | None   -> raise (IllTyped ("Free variable " ^ v))
    | Some t -> find t
  
  and find : typ -> typ = function
    | Arrow (t1, t2)                 -> Arrow (find t1, find t2)
    | TV ({contents= Bound t} as tv) ->
        let t' = find t in
        tv := Bound t' ;
        t'
    | t                              -> t
  
  and union ((t1, t2) : typ * typ) : unit =
    match (find t1, find t2) with
    | t1', t2' when t1' = t2' -> ()
    | Arrow (a1, b1), Arrow (a2, b2) ->
        union (a1, a2) ;
        union (b1, b2)
    | TV {contents= Bound t}, t' | t', TV {contents= Bound t} -> union (t, t')
    | TV ({contents= Free a} as tv), t' | t', TV ({contents= Free a} as tv) ->
        if occurs a t' then
          raise (IllTyped ("The type variable " ^ a ^ " occurs inside " ^ string_of_type t'))
        else tv := Bound t'
    | t1', t2' ->
        raise
          (IllTyped ("Cannot unify " ^ string_of_type t1' ^ " with " ^ string_of_type t2'))
  
  and occurs (x : identifier) : typ -> bool = function
    | Arrow (t1, t2)        -> occurs x t1 || occurs x t2
    | TV {contents= Free a} -> x = a
    | _                     -> false
  
  and freshTV : unit -> typ =
    let counter = ref (int_of_char 'a' - 1) in
    fun _ ->
      counter := !counter + 1 ;
      TV (ref (Free (Printf.sprintf "_%c" (char_of_int !counter))))
  
  and unify_types (t : typ) (cs : (typ * typ) list) : typ = List.iter union cs ; find t
  
  and generalize (gamma : env) (t : typ) : typ =
    let rec generalize' ftv = function
      | Arrow (t1, t2) -> Arrow (generalize' ftv t1, generalize' ftv t2)
      | TV ({contents= Free a} as tv) as t ->
          if List.mem a ftv then t
          else (
            tv := Bound (freshGV ()) ;
            t )
      | TV {contents= Bound t} -> generalize' ftv t
      | t -> t
    and free_type_variables = function
      | []      -> []
      | t :: ts ->
      match find t with
      | Arrow (t1, t2)        -> free_type_variables (t1 :: t2 :: ts)
      | TV {contents= Free a} -> a :: free_type_variables ts
      | _                     -> free_type_variables ts
    and freshGV =
      let counter = ref (int_of_char 'a' - 1) in
      fun _ ->
        counter := !counter + 1 ;
        GV (Printf.sprintf "%c" (char_of_int !counter))
    in
    generalize' (free_type_variables (List.map snd gamma)) t
  
  and instantiate (t : typ) : typ =
    let rec instantiate' t instd =
      match t with
      | Arrow (t1, t2) ->
          let t1', instd' = instantiate' t1 instd in
          let t2', instd'' = instantiate' t2 instd' in
          (Arrow (t1', t2'), instd'')
      | GV gv          -> (
        match List.assoc_opt gv instd with
        | Some t -> (t, instd)
        | None   ->
            let ntv = freshTV () in
            (ntv, (gv, ntv) :: instd) )
      | _              -> (t, instd)
    in
    fst (instantiate' t [])
  
  in
  try
    let t = TV (ref (Free "_")) in
    let gamma = m [] t expr in
    (gamma, find t)
  with IllTyped e ->
    print_string ("Type inference error: " ^ e ^ "\n") ;
    ([], Bad)
