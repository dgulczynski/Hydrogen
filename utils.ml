open Calculus

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

let sig_map (f : typ -> typ) : signature -> signature = function
  | Error   -> Error
  | State t -> State (f t)

let pure : effect = Fixed empty

let ( *** ) (is : instance set) : effect -> effect = function
  | Fixed is'          -> Fixed (merge is is')
  | Flexible (is', e') -> Flexible (merge is is', e')
  | GenEff (is', gv)   -> GenEff (merge is is', gv)

let ( <-: ) (r : 'a univar ref) (x : 'a) : unit = r := Bound x

let ( @: ) (e1 : expr) (e2 : expr) : expr = App (e1, e2)

let ( ->: ) (t1 : typ) _ (t2 : typ) (eff : effect) : typ = Arrow (t1, eff, t2)


let rec find_e : effect -> effect = function
  | Flexible ([], {contents= Bound e}) -> find_e e
  | Flexible (is, {contents= Bound e}) -> is *** find_e e
  | e -> e

let rec find_t : typ -> typ = function
  | Arrow (t1, eff, t2) -> Arrow (find_t t1, find_e eff, find_t t2)
  | TypVar ({contents= Bound t} as tv) ->
      let t' = find_t t in
      tv <-: t' ; t'
  | Forall (a, s, t) -> Forall (a, sig_map find_t s, find_t t)
  | t -> t

let rec string_of_type : typ -> string = function
  | Unit                       -> "Unit"
  | Int                        -> "Int"
  | Arrow (t1, eff, t2)        ->
      ( match find_t t1 with
      | Arrow _ -> "(" ^ string_of_type t1 ^ ") "
      | _       -> string_of_type t1 ^ " " )
      ^ (match find_e eff with Fixed [] -> "" | eff' -> "-{" ^ string_of_effect eff' ^ "}")
      ^ "-> " ^ string_of_type t2
  | TypVar {contents= Free a}  -> a
  | TypVar {contents= Bound t} -> string_of_type t
  | GenTyp v                   -> v
  | Forall (a, s, t)           -> "∀" ^ a ^ ":" ^ string_of_signature s ^ ". "
                                  ^ string_of_type t
  | IllTyped                   -> "ILL-TYPED"

and string_of_signature : signature -> string = function
  | Error   -> "Error"
  | State t -> "State " ^ string_of_type t

and string_of_effect (e : effect) : string =
  let aux = List.fold_right (fun i acc -> i ^ "," ^ acc) in
  match find_e e with
  | Fixed [] -> "ι"
  | Fixed [i] -> i
  | Fixed is -> aux is ""
  | Flexible ([], {contents= Free a}) | GenEff ([], a) -> a
  | Flexible (is, {contents= Free a}) | GenEff (is, a) -> aux is a
  | Flexible (is, {contents= Bound e}) -> aux is (string_of_effect e)

let string_of_op : op -> string = function Raise -> "raise" | Put -> "put" | Get -> "get"

let rec string_of_expr : expr -> string =
  let aux = function
    | Nil -> "()"
    | I i -> string_of_int i
    | V v -> v
    | e   -> "(" ^ string_of_expr e ^ ")"
  in
  function
  | Lam (x, e)       -> "λ" ^ x ^ ". " ^ string_of_expr e
  | Fun (f, x, e)    -> "fun " ^ f ^ " " ^ x ^ ". " ^ string_of_expr e
  | Let (x, e, e')   -> "let " ^ x ^ " = " ^ string_of_expr e ^ " in " ^ string_of_expr e'
  | App (e1, e2)     -> aux e1 ^ " " ^ aux e2
  | Op (a, op, e)    -> string_of_op op ^ "_" ^ a ^ " " ^ aux e
  | Handle (a, e, h) -> "handle_" ^ a ^ " " ^ string_of_expr e ^ " " ^ string_of_handler h
  | ILam (a, s, e)   -> "λ" ^ a ^ ":" ^ string_of_signature s ^ ". " ^ string_of_expr e
  | IApp (e, a)      -> aux e ^ "<" ^ a ^ ">"
  | UOp (op, e)      -> string_of_op op ^ " " ^ aux e
  | UHandle (e, h)   -> "handle " ^ string_of_expr e ^ " " ^ string_of_handler h
  | e'               -> aux e'

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
