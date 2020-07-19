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

type op_type = typ * typ

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
    | []      -> ""
    | i :: is -> "{" ^ List.fold_left (fun i acc -> i ^ " " ^ acc) i is ^ "}"
  in
  function
  | Fixed [] -> "ι"
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

let (freshEV : instance set -> effect), (refreshEV : unit -> unit) =
  let counter = ref (-1) in
  ( (fun is ->
      incr counter ;
      Flexible (is, ref (Free (Printf.sprintf "?e%d" !counter))))
  , fun () -> counter := -1 )

let signature_of_instance (theta : ienv) (a : instance) : signature =
  match List.assoc_opt a theta with
  | None   -> raise (IllTyped ("Free instance " ^ a))
  | Some s -> s

let type_of_op (s : signature) (a : instance) (op : op) : op_type =
  match (s, op) with
  | Error, Raise -> (Unit, freshTV ())
  | State t, Put -> (t, Unit)
  | State t, Get -> (Unit, t)
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

let rec find_t : typ -> typ = function
  | Arrow (t1, t2, eff)            -> Arrow (find_t t1, find_t t2, find_e eff)
  | TV ({contents= Bound t} as tv) ->
      let t' = find_t t in
      tv := Bound t' ;
      t'
  | t                              -> t

and find_e : effect -> effect = function
  | Flexible (is, {contents= Bound e}) -> (
    match find_e e with
    | Fixed is'          -> Fixed (merge is is')
    | Flexible (is', e') -> Flexible (merge is is', e') )
  | e -> e

let rec union_t ((t1, t2) : typ * typ) (ecs : effect constraints) : effect constraints =
  match (find_t t1, find_t t2) with
  | t1', t2' when t1' = t2' -> ecs
  | Arrow (a1, b1, e1), Arrow (a2, b2, e2) ->
      union_t (b1, b2) (union_e (e1, e2) (union_t (a1, a2) ecs))
  | TV {contents= Bound t}, t' | t', TV {contents= Bound t} -> union_t (t, t') ecs
  | TV ({contents= Free a} as tv), t' | t', TV ({contents= Free a} as tv) ->
      if occurs a t' then
        raise (IllTyped ("The type variable " ^ a ^ " occurs inside " ^ string_of_type t'))
      else tv := Bound t' ;
      ecs
  | t1', t2' ->
      raise (IllTyped ("Cannot unify " ^ string_of_type t1' ^ " with " ^ string_of_type t2'))

and union_e ((e1, e2) : effect * effect) (ecs : effect constraints) : effect constraints =
  let expand v = function [] -> () | is -> v := Bound (freshEV is) in
  let on_failed_subtyping e1 e2 =
    raise
      (IllTyped ("Effect " ^ string_of_effect e1 ^ " does not subtype " ^ string_of_effect e2))
  in
  let e1' = find_e e1 and e2' = find_e e2 in
  match (e1', e2') with
  | Fixed i1, Flexible (i2, v2) ->
      expand v2 (diff i1 i2) ;
      ecs
  | Flexible (i1, v1), (Flexible (i2, v2) as e2') ->
      expand v2 (diff i1 i2) ;
      (Flexible (empty, v1), e2') :: ecs
  | Flexible (i1, v1), Fixed [] ->
      v1 := Bound pure ;
      ecs
  | Flexible (i1, v1), (Fixed i2 as e2') -> (
    match diff i1 i2 with
    | [] -> (Flexible ([], v1), e2') :: ecs
    | _  -> on_failed_subtyping e1' e2' )
  | Fixed i1, Fixed i2 -> match diff i1 i2 with [] -> ecs | _ -> on_failed_subtyping e1' e2'

let solve_e (ecs : effect constraints) : effect constraints = List.fold_right union_e ecs []

let simplify_e (ecs : effect constraints) : unit =
  let aux = function
    (* | Flexible (_, v1), Flexible (_, v2) -> v1 := Bound pure ; v2 := Bound pure *)
    | Flexible (_, v1), _ -> v1 := Bound pure
    | _ -> ()
  in
  List.iter aux ecs

let type_of_var (gamma : env) (v : var) : typ =
  match List.assoc_opt v gamma with
  | None   -> raise (IllTyped ("Free variable " ^ v))
  | Some t -> find_t t

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
    match find_t t with
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
  function t, e -> (aux_type (find_t t), aux_eff (find_e e))

let infer_type_with_constraints (gamma : env) (theta : ienv) (expr : expr)
    (type_cs : typ constraints) (effect_cs : effect constraints) :
    env * type_effect * typ constraints * effect constraints =
  let tcs = ref type_cs and ecs = ref effect_cs in
  let constrain_typ tc = tcs := tc :: !tcs
  and constrain_eff ec = ecs := ec :: !ecs
  and solve_typ_constraints () =
    ecs := List.fold_right union_t !tcs !ecs ;
    tcs := []
  and solve_eff_constraints () = ecs := List.fold_right union_e !ecs [] in
  let rec infer gamma theta = function
    | Nil                            -> (gamma, (Unit, pure))
    | I _                            -> (gamma, (Int, pure))
    | V v                            -> (gamma, (instantiate (type_of_var gamma v), pure))
    | Lam (x, e)                     ->
        let tx = freshTV () in
        let _, (te, eff) = infer ((x, tx) :: gamma) theta e in
        (gamma, (Arrow (tx, te, eff), pure))
    | Let (x, e, e')                 ->
        let _, (te, eff) = infer gamma theta e in
        solve_typ_constraints () ;
        let tx = find_t te in
        let x_tx = (x, if find_e eff = pure then generalize gamma tx else tx) in
        infer (x_tx :: gamma) theta e'
    | App (e1, e2)                   ->
        let _, (t1, ef1) = infer gamma theta e1 in
        let _, (t2, ef2) = infer gamma theta e2 in
        let t = freshTV () and eff_arr = freshEV empty and eff = freshEV empty in
        constrain_typ (t1, Arrow (t2, t, eff_arr)) ;
        constrain_eff (eff_arr, eff) ;
        constrain_eff (ef1, eff) ;
        constrain_eff (ef2, eff) ;
        (gamma, (t, eff))
    | Op (a, op, e)                  ->
        let t1, t2 = type_of_op_in_env theta a op in
        let _, (e_t, e_eff) = infer gamma theta e in
        let eff = freshEV [a] in
        constrain_typ (e_t, t1) ;
        constrain_eff (e_eff, eff) ;
        (gamma, (t2, eff))
    | Handle (a, s, e, (hs, x, ret)) ->
        let t = freshTV () and eff = freshEV empty in
        let infer_handler (op, x, r, e) =
          let t1, t2 = type_of_op s a op in
          let _, (th, eh) = infer ((x, t1) :: (r, Arrow (t2, t, eff)) :: gamma) theta e in
          constrain_typ (th, t) ;
          constrain_eff (eh, eff)
        in
        List.iter infer_handler hs ;
        let _, (e_t, e_eff) = infer gamma ((a, s) :: theta) e in
        let _, (ret_t, ret_eff) = infer ((x, e_t) :: gamma) theta ret in
        (* all a occurences should be found at this point??? *)
        constrain_typ (ret_t, t) ;
        constrain_eff (ret_eff, eff) ;
        (gamma, (t, eff))
    | ILam (a, s, e)                 ->
        let _, (t', eff') = infer gamma ((a, s) :: theta) e in
        constrain_eff (eff', pure) ;
        (gamma, (Forall (a, s, t'), pure))
    | IApp (e, a)                    -> (
        let _, (t', eff') = infer gamma theta e in
        match (find_t t', signature_of_instance theta a) with
        | Forall (a', s', t'), s when s = s' -> (gamma, subst_instance a' a (t', eff'))
        | t', s ->
            raise
              (IllTyped
                 ( "Instance " ^ a ^ ":" ^ string_of_signature s ^ " application to "
                 ^ string_of_type_effect (t', eff') )) )
  in
  let gamma', (typ, eff) = infer gamma theta expr in
  solve_typ_constraints () ;
  solve_eff_constraints () ;
  (gamma', (find_t typ, find_e eff), !tcs, !ecs)

let infer_type (expr : expr) : env * typ * effect =
  try
    refreshTV () ;
    refreshEV () ;
    let gamma, (typ, eff), cs, ecs = infer_type_with_constraints [] [] expr [] [] in
    (gamma, typ, eff)
  with IllTyped e ->
    print_string ("Type inference error: " ^ e ^ "\n") ;
    ([], Bad, pure)
