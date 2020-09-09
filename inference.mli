type 'a constraints = ('a * 'a) list
type env = Calculus.typ Calculus.environment
type ienv = Calculus.signature Calculus.environment
exception IllTypedExn of string
val freshTV : unit -> Calculus.typ
val refreshTV : unit -> unit
val fresh_effect_univar : unit -> Calculus.effect Calculus.univar ref
val refresh_univars : unit -> unit
val infer_type_with_env :
  env ->
  ienv ->
  Calculus.expr ->
  env * Calculus.type_effect
val infer_type : Calculus.expr -> env * Calculus.type_effect
