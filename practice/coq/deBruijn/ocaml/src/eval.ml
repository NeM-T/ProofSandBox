
type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None



(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

module Nat =
 struct
  (** val pred : nat -> nat **)

  let pred n = match n with
  | O -> n
  | S u -> u

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n' -> (match m with
               | O -> false
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> true
    | S n' -> (match m with
               | O -> false
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m
 end

(** val eqb0 : char list -> char list -> bool **)

let rec eqb0 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' -> (match s2 with
                | [] -> false
                | c2::s2' -> if (=) c1 c2 then eqb0 s1' s2' else false)

type deBruijn =
| Var of nat
| App of deBruijn * deBruijn
| Abs of char list * deBruijn

(** val shift : nat -> nat -> deBruijn -> deBruijn **)

let rec shift k n = function
| Var x -> Var (if Nat.leb k x then add x n else x)
| App (t1, t2) -> App ((shift k n t1), (shift k n t2))
| Abs (x, t') -> Abs (x, (shift (S k) n t'))

(** val subst : nat -> deBruijn -> deBruijn -> deBruijn **)

let rec subst d s = function
| Var x -> if Nat.eqb d x then shift O x s else if Nat.ltb d x then Var (Nat.pred x) else Var x
| App (t1, t2) -> App ((subst d s t1), (subst d s t2))
| Abs (x, t') -> Abs (x, (subst (S d) s t'))

type namelambda =
| Var0 of char list
| Abs0 of char list * namelambda
| App0 of namelambda * namelambda

(** val in_list : char list -> char list list -> nat -> nat option **)

let rec in_list x l n =
  match l with
  | [] -> None
  | h::t -> if eqb0 h x then Some n else in_list x t (S n)

(** val inb : char list -> char list list -> bool **)

let rec inb x = function
| [] -> false
| h::t -> if eqb0 h x then true else inb x t

(** val free_list : char list list -> char list list -> namelambda -> char list list **)

let rec free_list l1 l2 = function
| Var0 x -> if if inb x l1 then true else inb x l2 then l2 else x::l2
| Abs0 (x, t1) -> free_list (x::l1) l2 t1
| App0 (t1, t2) -> free_list l1 (free_list l1 l2 t1) t2

(** val removenames : char list list -> namelambda -> deBruijn option **)

let rec removenames l = function
| Var0 x -> (match in_list x l O with
             | Some n -> Some (Var n)
             | None -> None)
| Abs0 (x, t') -> (match removenames (x::l) t' with
                   | Some t1 -> Some (Abs (x, t1))
                   | None -> None)
| App0 (t1, t2) ->
  let o = removenames l t1 in
  let o0 = removenames l t2 in
  (match o with
   | Some t1' -> (match o0 with
                  | Some t2' -> Some (App (t1', t2'))
                  | None -> None)
   | None -> None)

(** val lambda_to_debruijn : namelambda -> deBruijn option **)

let lambda_to_debruijn t =
  removenames (free_list [] [] t) t

(** val nth : 'a1 list -> nat -> 'a1 option **)

let rec nth l = function
| O -> (match l with
        | [] -> None
        | h::_ -> Some h)
| S n' -> (match l with
           | [] -> None
           | _::t -> nth t n')

(** val debruijn_to_lambda : char list list -> deBruijn -> namelambda option **)

let rec debruijn_to_lambda l = function
| Var n -> (match nth l n with
            | Some x -> Some (Var0 x)
            | None -> None)
| App (t1, t2) ->
  let o = debruijn_to_lambda l t1 in
  let o0 = debruijn_to_lambda l t2 in
  (match o with
   | Some t1' -> (match o0 with
                  | Some t2' -> Some (App0 (t1', t2'))
                  | None -> None)
   | None -> None)
| Abs (x, t1) -> (match debruijn_to_lambda (x::l) t1 with
                  | Some t' -> Some (Abs0 (x, t'))
                  | None -> None)

(** val left_eval : deBruijn -> deBruijn option **)

let rec left_eval = function
| Var _ -> None
| App (t1, t2) ->
  (match t1 with
   | Abs (_, t1') -> Some (subst O t2 t1')
   | _ ->
     (match left_eval t1 with
      | Some t1' -> Some (App (t1', t2))
      | None -> (match left_eval t2 with
                 | Some t2' -> Some (App (t1, t2'))
                 | None -> None)))
| Abs (x, t1) -> (match left_eval t1 with
                  | Some t1' -> Some (Abs (x, t1'))
                  | None -> None)

(** val result_lambda : deBruijn -> char list list -> namelambda option **)

let result_lambda t l =
  match left_eval t with
  | Some t' -> debruijn_to_lambda l t'
  | None -> None
