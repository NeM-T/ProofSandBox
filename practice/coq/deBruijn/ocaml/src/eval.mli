
type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None



module Nat :
 sig
  val pred : nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool
 end

val eqb0 :
  char list -> char list -> bool

type deBruijn =
| Var of nat
| Abs of char list * deBruijn
| App of deBruijn * deBruijn

val shift :
  nat -> deBruijn -> deBruijn

val subst :
  nat -> deBruijn -> deBruijn ->
  deBruijn

type namelambda =
| Var0 of char list
| Abs0 of char list * namelambda
| App0 of namelambda * namelambda

val in_list :
  char list -> char list list ->
  nat -> nat option

val inb :
  char list -> char list list ->
  bool

val free_list :
  char list list -> char list list
  -> namelambda -> char list list

val removenames :
  char list list -> namelambda ->
  deBruijn option

val lambda_to_debruijn :
  namelambda -> deBruijn option

val nth :
  'a1 list -> nat -> 'a1 option

val debruijn_to_lambda :
  char list list -> deBruijn ->
  namelambda option

val left_eval :
  deBruijn -> deBruijn option

val result_lambda :
  deBruijn -> char list list ->
  namelambda option
