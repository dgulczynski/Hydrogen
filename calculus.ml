type identifier = string

type var = identifier

type instance = identifier

type 'a environment = (identifier * 'a) list

type 'a univar = Free of identifier | Bound of 'a

type 'a set = 'a list

type typ =
  | Unit
  | Int
  | Arrow    of typ * effect * typ
  | TypVar   of typ univar ref
  | GenTyp   of identifier
  | Forall   of instance * signature * typ
  | IllTyped

and signature = Error | State of typ

and effect =
  | Fixed    of instance set
  | Flexible of instance set * effect univar ref
  | GenEff   of instance set * identifier

type type_effect = typ * effect

type expr =
  | Nil
  | I       of int
  | V       of var
  | Lam     of var * expr
  | Fun     of var * var * expr
  | Let     of var * expr * expr
  | App     of expr * expr
  | Op      of instance * op * expr
  | Handle  of instance * expr * handler
  | ILam    of instance * signature * expr
  | IApp    of expr * instance
  | UHandle of expr * handler
  | UOp     of op * expr

and op = Raise | Get | Put

and handler = (op * var * var * expr) list * var * expr

type op_type = typ * typ
