type identifier = string

type var = identifier

type instance = identifier

type typ =
  | Unit
  | Int
  | Arrow of typ * typ * effect
  | TV of tvar ref
  | GV of identifier
  | Forall of instance * signature * typ
  | Bad

and tvar = Free of identifier | Bound of typ

and signature = Error | State of typ

and effect = Pure | Effect of instance * signature

type type_effect = typ * effect

type expr =
  | Nil
  | I of int
  | V of var
  | Lam of var * expr
  | Let of var * expr * expr
  | App of expr * expr
  | ILam of instance * signature * expr
  | Op of instance * op
  | Handle of instance * signature * expr * handler

and op = Throw | Get | Put

and handler = (op * var * var * expr) list * var * expr

type env = (var * typ) list

type ienv = (instance * signature) list

exception IllTyped of string

let rec string_of_type : typ -> string = function
  | Unit -> "Unit"
  | Int -> "Int"
  | Arrow (t1, t2, eff) ->
      ( match t1 with
      | Arrow _ -> "(" ^ string_of_type t1 ^ ") -"
      | _ -> string_of_type t1 ^ " -" )
      ^ string_of_effect eff ^ "-> " ^ string_of_type t2
  | TV {contents= Free a} -> a
  | TV {contents= Bound t} -> string_of_type t
  | GV v -> "'" ^ v
  | Forall(a,s,t) -> "∀" ^ a ^ ":" ^ string_of_signature s ^ ". " ^ string_of_type t 
  | Bad -> "ILL-TYPED"

and string_of_signature : signature -> string = function
  | Error -> "Error"
  | State t -> "State(" ^ string_of_type t ^ ")"

and string_of_effect : effect -> string = function
  | Pure -> "i"
  | Effect (a, s) ->  a ^ ":" ^ string_of_signature s

let string_of_op : op -> string = function
  | Throw -> "throw"
  | Put -> "put"
  | Get -> "get"

let rec string_of_expr : expr -> string = function
  | Nil -> "()"
  | I i -> string_of_int i
  | V v -> v
  | Lam (x, e) -> "λ" ^ x ^ ". " ^ string_of_expr e
  | Let (x, e, e') ->
      "let " ^ x ^ " = " ^ string_of_expr e ^ " in " ^ string_of_expr e'
  | App (e1, e2) ->
      let aux = function
        | Nil -> "()"
        | I i -> string_of_int i
        | V v -> v
        | Op _ as e -> string_of_expr e
        | e -> "(" ^ string_of_expr e ^ ")"
      in
      aux e1 ^ " " ^ aux e2
  | Op (a, op) -> string_of_op op ^ "_" ^ a
  | ILam (a, s, e) ->
      "λ" ^ a ^ ":" ^ string_of_signature s ^ ". " ^ string_of_expr e
  | Handle (a, s, e, h) ->
      "handle_" ^ a ^ ":" ^ string_of_signature s ^ " " ^ string_of_expr e
      ^ " " ^ string_of_handler h

and string_of_handler : handler -> string = function
  | hs, x, ret ->
      "{"
      ^ List.fold_right
          (fun (op, x, k, e) acc ->
            string_of_op op ^ " " ^ x ^ " " ^ k ^ ". " ^ string_of_expr e
            ^ " | " ^ acc )
          hs ""
      ^ "return " ^ x ^ ". " ^ string_of_expr ret ^ "}"

let signature_of_instance (chi : ienv) (a : instance) : signature =
  match List.assoc_opt a chi with
  | None -> raise (IllTyped ("Free instance " ^ a))
  | Some s -> s

let rec occurs (x : identifier) : typ -> bool = function
  | Arrow (t1, t2, _) -> occurs x t1 || occurs x t2
  | TV {contents= Free a} -> x = a
  | _ -> false

let rec find : typ -> typ = function
  | Arrow (t1, t2, eff) -> Arrow (find t1, find t2, eff)
  | TV ({contents= Bound t} as tv) ->
      let t' = find t in
      tv := Bound t' ;
      t'
  | t -> t

let rec union ((t1, t2) : typ * typ) : unit =
  match (find t1, find t2) with
  | t1', t2' when t1' = t2' -> ()
  | Arrow (a1, b1, _), Arrow (a2, b2, _) ->
      union (a1, a2) ;
      union (b1, b2)
  | TV {contents= Bound t}, t' | t', TV {contents= Bound t} -> union (t, t')
  | TV ({contents= Free a} as tv), t' | t', TV ({contents= Free a} as tv) ->
      if occurs a t' then
        raise
          (IllTyped
             ("The type variable " ^ a ^ " occurs inside " ^ string_of_type t'))
      else tv := Bound t'
  | t1', t2' ->
      raise
        (IllTyped
           ( "Cannot unify " ^ string_of_type t1' ^ " with "
           ^ string_of_type t2' ))

let type_of_var (gamma : env) (v : var) : typ =
  match List.assoc_opt v gamma with
  | None -> raise (IllTyped ("Free variable " ^ v))
  | Some t -> find t

let (freshTV : unit -> typ), (refreshTV : unit -> unit) =
  let counter = ref (int_of_char 'a' - 1) in
  ( (fun () ->
      incr counter ;
      TV (ref (Free (Printf.sprintf "%c" (char_of_int !counter)))) )
  , fun () -> counter := int_of_char 'a' - 1 )

let unify_types (t : typ) (cs : (typ * typ) list) : typ =
  List.iter union cs ; find t

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
    | [] -> []
    | t :: ts -> (
      match find t with
      | Arrow (t1, t2, _) -> free_type_variables (t1 :: t2 :: ts)
      | TV {contents= Free a} -> a :: free_type_variables ts
      | _ -> free_type_variables ts )
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
    | GV gv -> (
      match List.assoc_opt gv instd with
      | Some t -> (t, instd)
      | None ->
          let ntv = freshTV () in
          (ntv, (gv, ntv) :: instd) )
    | _ -> (t, instd)
  in
  fst (instantiate' t [])

let rec infer (gamma : env) (chi : ienv) (expr : expr) (cs : (typ * typ) list)
    : env * type_effect * (typ * typ) list =
  match expr with
  | Nil -> (gamma, (Unit, Pure), cs)
  | I _ -> (gamma, (Int, Pure), cs)
  | V v -> (gamma, (instantiate (type_of_var gamma v), Pure), cs)
  | Lam (x, e) ->
      let tx = freshTV () in
      let _, (te, eff), cse = infer ((x, tx) :: gamma) chi e cs in
      (gamma, (Arrow (tx, te, eff), Pure), cse)
  | Let (x, e, e') ->
      let _, (te, _), cse = infer gamma chi e cs in
      infer ((x, generalize gamma (unify_types te cse)) :: gamma) chi e' []
  | App (e1, e2) -> (
      let _, (t1, ef1), cs1 = infer gamma chi e1 cs in
      let _, (t2, ef2), cs2 = infer gamma chi e2 cs1 in
      let t = freshTV () in
      match unify_types t1 ((t1, Arrow (t2, t, Pure)) :: cs2) with
      | Arrow (t1', t1'', eff) -> (gamma, (t, eff), [])
      | _ ->
          raise
            (IllTyped
               ( string_of_expr e1 ^ " should have type " ^ string_of_type t2
               ^ " -> " ^ string_of_type t ^ "instead of " ^ string_of_type t1
               )) )
  | Op (a, op) ->
      ( gamma
      , ( match (op, signature_of_instance chi a) with
        | Throw, Error -> (Arrow (freshTV (), freshTV (), Effect (a, Error)), Pure)
        | Put, State t -> (Arrow (t, Unit, Effect (a,(State t))), Pure)
        | Get, State t -> (Arrow (Unit, t, Effect (a,(State t))), Pure)
        | _, s ->
            raise
              (IllTyped
                 ( "Instance " ^ a ^ ":" ^ string_of_signature s
                 ^ " used with operator " ^ string_of_op op )) )
      , cs )
  | ILam (a, s, e) -> 
  let gamma', (t', e'), cs' = infer gamma ((a, s) :: chi) e cs in
  gamma', (Forall(a,s,t'), e') , cs'
  | Handle (a, s, e, h) -> (* placeholder *)
                           infer gamma ((a, s) :: chi) e cs

let infer_type (expr : expr) : env * typ * effect =
  try
    refreshTV () ;
    let gamma, (t, e), cs = infer [] [] expr [] in
    (gamma, unify_types t cs, e)
  with IllTyped e ->
    print_string ("Type inference error: " ^ e ^ "\n") ;
    ([], Bad, Pure)
