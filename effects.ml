type identifier = string

type var = identifier

type instance = identifier

type 'a environment = (identifier * 'a) list

type 'a univar = Free of identifier | Bound of 'a

type 'a set = 'a list

type 'a constraints = ('a * 'a) list

type typ =
  | Unit
  | Int
  | Arrow  of typ * typ * effect
  | TV     of typ univar ref
  | GV     of identifier
  | Forall of instance * signature * typ
  | Bad

and signature = Error | State of typ

and effect = Fixed of instance set | Flexible of instance set * effect univar ref

type type_effect = typ * effect

type expr =
  | Nil
  | I      of int
  | V      of var
  | Lam    of var * expr
  | Let    of var * expr * expr
  | App    of expr * expr
  | Op     of instance * op * expr
  | Handle of instance * signature * expr * handler
  | ILam   of instance * signature * expr
  | IApp   of expr * instance

and op = Raise | Get | Put

and handler = (op * var * var * expr) list * var * expr

type op_type = typ * typ * effect

type env = typ environment

type ienv = signature environment

exception IllTyped of string

let empty : 'a set = []

let singleton (x : 'a) : 'a set = [x]

let rec diff (xs : 'a set) (ys : 'a set) : 'a set =
  match (xs, ys) with
  | [], _ -> []
  | xs, [] -> xs
  | (x :: xs' as xs), (y :: ys' as ys) ->
      if x < y then x :: diff xs' ys else if x = y then diff xs' ys' else diff xs ys'

let rec merge (xs : 'a set) (ys : 'a set) : 'a set =
  match (xs, ys) with
  | [], ys -> ys
  | xs, [] -> xs
  | (x :: xs' as xs), (y :: ys' as ys) ->
      if x < y then x :: merge xs' ys
      else if x = y then x :: merge xs' ys'
      else y :: merge xs ys'

let pure : effect = Fixed empty

let rec string_of_type : typ -> string = function
  | Unit                   -> "Unit"
  | Int                    -> "Int"
  | Arrow (t1, t2, eff)    ->
      ( match t1 with
      | Arrow _ -> "(" ^ string_of_type t1 ^ ") "
      | _       -> string_of_type t1 ^ " " )
      ^ "-" ^ string_of_effect eff ^ "-> " ^ string_of_type t2
  | TV {contents= Free a}  -> a
  | TV {contents= Bound t} -> string_of_type t
  | GV v                   -> "'" ^ v
  | Forall (a, s, t)       -> "∀" ^ a ^ ":" ^ string_of_signature s ^ ". " ^ string_of_type t
  | Bad                    -> "ILL-TYPED"

and string_of_signature : signature -> string = function
  | Error   -> "Error"
  | State t -> "State(" ^ string_of_type t ^ ")"

and string_of_effect : effect -> string =
  let aux = function
    | []      -> "ι"
    | i :: is -> List.fold_right (fun i acc -> i ^ " " ^ acc) is i
  in
  function
  | Fixed is -> aux is
  | Flexible (is, {contents= Free a}) -> aux is ^ a
  | Flexible (is, {contents= Bound e}) -> aux is ^ string_of_effect e

let string_of_op : op -> string = function Raise -> "raise" | Put -> "put" | Get -> "get"

let rec string_of_expr : expr -> string =
  let aux = function
    | Nil -> "()"
    | I i -> string_of_int i
    | V v -> v
    | e   -> "(" ^ string_of_expr e ^ ")"
  in
  function
  | Lam (x, e)          -> "λ" ^ x ^ ". " ^ string_of_expr e
  | Let (x, e, e')      -> "let " ^ x ^ " = " ^ string_of_expr e ^ " in " ^ string_of_expr e'
  | App (e1, e2)        -> aux e1 ^ " " ^ aux e2
  | Op (a, op, e)       -> string_of_op op ^ "_" ^ a ^ " " ^ aux e
  | Handle (a, s, e, h) ->
      "handle_" ^ a ^ ":" ^ string_of_signature s ^ " " ^ string_of_expr e ^ " "
      ^ string_of_handler h
  | ILam (a, s, e)      -> "λ" ^ a ^ ":" ^ string_of_signature s ^ ". " ^ string_of_expr e
  | IApp (e, a)         -> aux e ^ "<" ^ a ^ ">"
  | e'                  -> aux e'

and string_of_handler : handler -> string = function
  | hs, x, ret ->
      "{"
      ^ List.fold_right
          (fun (op, x, k, e) acc ->
            string_of_op op ^ " " ^ x ^ " " ^ k ^ ". " ^ string_of_expr e ^ " | " ^ acc)
          hs
          ("return " ^ x ^ ". " ^ string_of_expr ret ^ "}")

let string_of_type_effect : type_effect -> string = function
  | t, e -> string_of_type t ^ " / " ^ string_of_effect e

let (freshTV : unit -> typ), (refreshTV : unit -> unit) =
  let counter = ref (int_of_char 'a' - 1) in
  ( (fun () ->
      incr counter ;
      TV (ref (Free (Printf.sprintf "%c" (char_of_int !counter)))))
  , fun () -> counter := int_of_char 'a' - 1 )

let (freshEV : unit -> effect), (refreshEV : unit -> unit) =
  let counter = ref (-1) in
  ( (fun () ->
      incr counter ;
      Flexible (empty, ref (Free (Printf.sprintf "%c" (char_of_int !counter)))))
  , fun () -> counter := -1 )

let signature_of_instance (theta : ienv) (a : instance) : signature =
  match List.assoc_opt a theta with
  | None   -> raise (IllTyped ("Free instance " ^ a))
  | Some s -> s

let type_of_op (s : signature) (a : instance) (op : op) : op_type =
  let eff = Fixed (singleton a) in
  match (s, op) with
  | Error, Raise -> (Unit, freshTV (), eff)
  | State t, Put -> (t, Unit, eff)
  | State t, Get -> (Unit, t, eff)
  | s, op        ->
      raise
        (IllTyped
           ( "Instance " ^ a ^ ":" ^ string_of_signature s ^ " doesn't define operator "
           ^ string_of_op op ))

let type_of_op_in_env (theta : ienv) (a : instance) (op : op) : op_type =
  type_of_op (signature_of_instance theta a) a op

let rec occurs (x : identifier) : typ -> bool = function
  | Arrow (t1, t2, _)     -> occurs x t1 || occurs x t2
  | TV {contents= Free a} -> x = a
  | _                     -> false

let rec find : typ -> typ = function
  | Arrow (t1, t2, eff)            -> Arrow (find t1, find t2, eff)
  | TV ({contents= Bound t} as tv) ->
      let t' = find t in
      tv := Bound t' ;
      t'
  | t                              -> t

let rec union ((t1, t2) : typ * typ) : unit =
  match (find t1, find t2) with
  | t1', t2' when t1' = t2' -> ()
  | Arrow (a1, b1, _), Arrow (a2, b2, _) ->
      union (a1, a2) ;
      union (b1, b2)
  | TV {contents= Bound t}, t' | t', TV {contents= Bound t} -> union (t, t')
  | TV ({contents= Free a} as tv), t' | t', TV ({contents= Free a} as tv) ->
      if occurs a t' then
        raise (IllTyped ("The type variable " ^ a ^ " occurs inside " ^ string_of_type t'))
      else tv := Bound t'
  | t1', t2' ->
      raise (IllTyped ("Cannot unify " ^ string_of_type t1' ^ " with " ^ string_of_type t2'))

let rec find_e : effect -> effect = function
  | Flexible (is, {contents= Bound e}) -> (
    match find_e e with
    | Fixed is'          -> Fixed (merge is is')
    | Flexible (is', e') -> Flexible (merge is is', e') )
  | e -> e

let rec union_e ((e1, e2) : effect * effect) (ecs : effect constraints) : effect constraints =
  let expand v = function
    | [] -> ()
    | is ->
        let u = ref (Free "u") in
        v := Bound (Flexible (is, u))
  in
  match (find_e e1, find_e e2) with
  | Fixed i1, Flexible (i2, v2) ->
      expand v2 (diff i1 i2) ;
      ecs
  | Flexible (i1, v1), Flexible (i2, v2) ->
      expand v2 (diff i1 i2) ;
      (Flexible (empty, v1), Flexible (empty, v2)) :: ecs
  | Flexible (i1, _), Fixed i2 | Fixed i1, Fixed i2 ->
  match diff i1 i2 with
  | [] -> ecs
  | _  ->
      raise
        (IllTyped
           ("Effect " ^ string_of_effect e1 ^ " does not subtype " ^ string_of_effect e2))

let type_of_var (gamma : env) (v : var) : typ =
  match List.assoc_opt v gamma with
  | None   -> raise (IllTyped ("Free variable " ^ v))
  | Some t -> find t

let unify_types (t : typ) (cs : typ constraints) : typ = List.iter union cs ; find t

let generalize (gamma : env) (t : typ) : typ =
  let rec generalize' ftv = function
    | Arrow (t1, t2, eff) -> Arrow (generalize' ftv t1, generalize' ftv t2, eff)
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
    | Arrow (t1, t2, _)     -> free_type_variables (t1 :: t2 :: ts)
    | TV {contents= Free a} -> a :: free_type_variables ts
    | _                     -> free_type_variables ts
  and freshGV =
    let counter = ref (int_of_char 'a' - 1) in
    fun _ ->
      counter := !counter + 1 ;
      GV (Printf.sprintf "%c" (char_of_int !counter))
  in
  generalize' (free_type_variables (List.map snd gamma)) t

let instantiate (t : typ) : typ =
  let rec instantiate' t instd =
    match t with
    | Arrow (t1, t2, eff) ->
        let t1', instd' = instantiate' t1 instd in
        let t2', instd'' = instantiate' t2 instd' in
        (Arrow (t1', t2', eff), instd'')
    | GV gv               -> (
      match List.assoc_opt gv instd with
      | Some t -> (t, instd)
      | None   ->
          let ntv = freshTV () in
          (ntv, (gv, ntv) :: instd) )
    | _                   -> (t, instd)
  in
  fst (instantiate' t [])

let subst_instance (a : instance) (b : instance) : type_effect -> type_effect =
  let rec aux_eff =
    let f = List.map (fun a' -> if a' = a then b else a') in
    function Fixed is -> Fixed (f is) | Flexible (is, e) -> Flexible (f is, e)
  and aux_type = function
    | Forall (a', s', t') when a' != a -> Forall (a', s', aux_type t')
    | Arrow (t1, t2, eff) -> Arrow (t1, t2, aux_eff eff)
    | t -> t
  in
  function t, e -> (aux_type (find t), aux_eff (find_e e))

let rec infer (gamma : env) (theta : ienv) (expr : expr) (cs : typ constraints)
    (ecs : effect constraints) : env * type_effect * typ constraints * effect constraints =
  match expr with
  | Nil                            -> (gamma, (Unit, pure), cs, ecs)
  | I _                            -> (gamma, (Int, pure), cs, ecs)
  | V v                            -> ( gamma
                                      , (instantiate (type_of_var gamma v), pure)
                                      , cs
                                      , ecs )
  | Lam (x, e)                     ->
      let tx = freshTV () in
      let _, (te, eff), cs', ecs' = infer ((x, tx) :: gamma) theta e cs ecs in
      (gamma, (Arrow (tx, te, eff), pure), cs', ecs')
  | Let (x, e, e')                 ->
      let _, (te, eff), cs', ecs' = infer gamma theta e cs ecs in
      if eff = pure then
        infer ((x, generalize gamma (unify_types te cs')) :: gamma) theta e' [] ecs'
      else infer ((x, unify_types te cs') :: gamma) theta e' [] ecs'
  | App (e1, e2)                   -> (
      let _, (t1, ef1), cs1, ecs1 = infer gamma theta e1 cs ecs in
      let _, (t2, ef2), cs2, ecs2 = infer gamma theta e2 cs1 ecs1 in
      let t = freshTV () in
      match unify_types t1 ((t1, Arrow (t2, t, pure)) :: cs2) with
      | Arrow (t1', t1'', eff) -> (gamma, (t, eff), [], ecs2)
      | _                      ->
          raise
            (IllTyped
               ( string_of_expr e1 ^ " should have type " ^ string_of_type t2 ^ " -> "
               ^ string_of_type t ^ "instead of " ^ string_of_type t1 )) )
  | Op (a, op, e)                  ->
      let t1, t2, op_eff = type_of_op_in_env theta a op in
      let _, (e_t, e_eff), e_cs, e_ecs = infer gamma theta e cs ecs in
      (gamma, (t2, e_eff), (e_t, t1) :: e_cs, e_ecs)
  | Handle (a, s, e, (hs, x, ret)) ->
      (* raise (IllTyped ("not implemented")) *)
      let t = freshTV () and eff = freshEV () in
      let infer_handler (op, x, r, e) (cs, ecs) =
        let t1, t2, eff = type_of_op s a op in
        let _, (th, eh), cs', ecs' =
          infer ((x, t1) :: (r, Arrow (t2, t, eff)) :: gamma) theta e cs ecs
        in
        ((th, t) :: cs', (eh, eff) :: ecs')
      in
      let cs', ecs' = List.fold_right infer_handler hs (cs, ecs) in
      let _, (e_t, e_eff), e_cs, e_ecs = infer gamma ((a, s) :: theta) e cs' ecs' in
      let _, (ret_t, ret_eff), ret_cs, ret_ecs =
        infer ((x, e_t) :: gamma) theta ret e_cs e_ecs
      in
      (gamma, (ret_t, ret_eff), (ret_t, t) :: ret_cs, (ret_eff, eff) :: ret_ecs)
  | ILam (a, s, e)                 ->
      let _, (t', eff'), cs', ecs' = infer gamma ((a, s) :: theta) e cs ecs in
      (gamma, (Forall (a, s, t'), eff'), cs', ecs')
  | IApp (e, a)                    -> (
      let _, (t', eff'), cs', ecs' = infer gamma theta e cs ecs in
      match (find t', signature_of_instance theta a) with
      | Forall (a', s', t'), s when s = s' ->
          (gamma, subst_instance a' a (t', eff'), cs', ecs')
      | t', s ->
          raise
            (IllTyped
               ( "Instance " ^ a ^ ":" ^ string_of_signature s ^ " application to "
               ^ string_of_type_effect (t', eff') )) )

let infer_type (expr : expr) : env * typ * effect =
  try
    refreshTV () ;
    let gamma, (t, e), cs, ecs = infer [] [] expr [] [] in
    (gamma, unify_types t cs, e)
  with IllTyped e ->
    print_string ("Type inference error: " ^ e ^ "\n") ;
    ([], Bad, pure)
