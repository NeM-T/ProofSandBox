Require Import Nat.
Require Import List.
Import ListNotations.

Inductive constant := | T | F | Zero | Suc | Pred | Zerop | Fst | Snd.

Inductive term : Type :=
| const : constant -> term
| var : nat -> term
| abs : list term -> term -> term
| pair : term -> term -> term
| app : term -> term -> term
| If : term -> term -> term -> term.

Notation "x '||' y" := (orb x y).

Fixpoint free_value t l :=
  match t with
  | const _ => false
  | var n => length l <? n
  | abs l1 t1 => free_value t1 (l1 ++ l)
  | pair t1 t2 => (free_value t1 l) || (free_value t2 l)
  | app t1 t2 => (free_value t1 l) || (free_value t2 l)
  | If t1 t2 t3 => (free_value t1 l) || (free_value t2 l) || (free_value t3 l)
  end.

Notation " 'λ' l ';' t " := (abs l t)(at level 50).
Notation " e1 '-->>' e2 ';' e3" := (If e1 e2 e3) (at level 50).
Notation " '<<' e1 ',' e2 '>>' " := (pair e1 e2) (at level 50).

Fixpoint shift n t :=
  match t with
  | const c => const c
  | var x => var (if leb n x then (S x) else x)
  | λ l; e1 =>
     λ (map (shift n) l); (shift (S n) e1)
  | <<e1, e2>> => << (shift n e1) , (shift n e2) >>
  | app t1 t2 => app (shift n t1) (shift n t2)
  | If e1 e2 e3 =>
    If (shift n e1) (shift n e2) (shift n e3)
  end.

Fixpoint subst n t l :=
  match t with
  | const c => const c
  | var n1 =>
    if n1 <? n then (var n1)
    else (nth (n1 - n) l (var n1))
  | λ l1 ; t1 =>
    λ (map (fun t' => subst n t' l) l1) ; (subst n t1 l)
  | << t1 , t2 >> =>
    << (subst n t1 l) , (subst n t2 l)>>
  | app t1 t2 =>
    app (subst n t1 l) (subst n t2 l)
  | t1 -->> t2; t3 =>
     (subst n t1 l) -->> (subst n t2 l); (subst n t3 l)
  end.

Inductive FUN : Set :=
  | Lambda : term -> FUN | PRED | ZEROP | FST | SND.

Inductive Data : Set :=
| NatData : nat -> Data
| BoolData : bool -> Data
| FuncData : FUN -> Data
| PairData : Data -> Data -> Data.

Fixpoint Nat_to_term n :=
  match n with
  | 0 => (const Zero)
  | S n' =>
    app (const Suc) (Nat_to_term n')
  end.

Fixpoint Data_to_term d :=
  match d with
  | NatData n => Nat_to_term n
  | BoolData b =>
    match b with
    | true => (const T)
    | false => (const F)
    end
  | FuncData f =>
    match f with
    | Lambda e1 => (λ nil; e1)
    | PRED => (const Pred)
    | ZEROP => (const Zerop)
    | FST => (const Fst)
    | SND => (const Snd)
    end
  | PairData d1 d2 => << (Data_to_term d1), (Data_to_term d2) >>
  end.

Inductive NatValue : term -> Prop :=
| ZeroValue : NatValue (const Zero)
| SucValue :forall t1, NatValue t1 -> NatValue (app (const Suc) t1).

Fixpoint mynth {A: Type} n (l: list A) :=
  match n with
  | 0 => match l with
         | [] => None
         | h :: _ => Some h
         end
  | S m => match l with
           | [] => None
           | _ :: t => mynth m t
           end
  end.

Inductive EvalTerm : term -> (list Data) -> term -> Prop :=
| ConstE: forall c E, EvalTerm (const c) E (const c)
| VarE: forall n E d, mynth n E = Some d -> EvalTerm (var n) E (Data_to_term d)
| PairE: forall e1 e2 E v1 v2, EvalTerm e1 E v1 -> EvalTerm e2 E v2 -> EvalTerm (<<e1, e2>>) E (<<v1, v2>>)
| IfTE: forall e1 E e2 e3 v, EvalTerm e1 E (const T) -> EvalTerm e2 E v -> EvalTerm (If e1 e2 e3) E v
| IfFE: forall e1 E e2 e3 v, EvalTerm e1 E (const F) -> EvalTerm e3 E v -> EvalTerm (If e1 e2 e3) E v
| LambdaNilE: forall e E, EvalTerm (λ []; e) E (λ[];e)
| LambdaConE: forall (e: term) E v e h t, EvalTerm h E v -> EvalTerm (λ (h::t);e) E (λ t; (subst 0 e [v])) .

Reserved Notation " t1 '->>' t2" (at level 20).
Inductive ValueEval : term -> term -> Prop :=
| ZeropT : (app (const Zerop) (const Zero)) ->> (const T)
| ZeropF : forall v, v <> (const Zero) -> (app (const Zerop) v) ->> (const F)
| SucVE : forall t1, NatValue t1 -> (app (const Suc) t1) ->> (app (const Suc) t1)
| FstVE : forall t1 t2, (app (const Fst) (<< t1, t2 >>))  ->> t1
| SndVE : forall t1 t2, (app (const Snd) (<< t1, t2 >>))  ->> t2
| LambdaVE : forall t1 d v,
    (EvalTerm t1 [d] v) -> app(λ nil; t1) (Data_to_term d) ->> v
where "t1 ->> t2" := (ValueEval t1 t2).
