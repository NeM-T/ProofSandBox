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

Fixpoint shift n up t :=
  match t with
  | const c => const c
  | var x => var (if leb n x then (x + up) else x)
  | λ l; e1 => λ (map (shift n up) l); (shift (n + length l) up e1)
  | <<e1, e2>> => << (shift n up e1) , (shift n up e2) >>
  | app t1 t2 => app (shift n up t1) (shift n up t2)
  | If e1 e2 e3 =>
    If (shift n up e1) (shift n up e2) (shift n up e3)
  end.

Fixpoint subst n t l :=
  match t with
  | const c => const c
  | var n1 => if n1 <? n then (var n1) else (nth (n1 - n) l (var n1))
  | λ l1 ; t1 => λ (map (fun t' => subst n t' l) l1) ; (subst (n + length l1) t1 (map (shift 0 (length l1)) l ))
  | << t1 , t2 >> => << (subst n t1 l) , (subst n t2 l)>>
  | app t1 t2 => app (subst n t1 l) (subst n t2 l)
  | t1 -->> t2; t3 => (subst n t1 l) -->> (subst n t2 l); (subst n t3 l)
  end.

Inductive FUN : Set := | Lambda : term -> FUN | SUC | PRED | ZEROP | FST | SND.

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
    | SUC => (const Suc)
    end
  | PairData d1 d2 => << (Data_to_term d1), (Data_to_term d2) >>
  end.

Inductive NatValue : term -> Prop :=
| ZeroValue : NatValue (const Zero)
| SucValue :forall t1, NatValue t1 -> NatValue (app (const Suc) t1).

Fixpoint optnth {A: Type} n (l: list A) :=
  match n with
  | 0 => match l with
         | [] => None
         | h :: _ => Some h
         end
  | S m => match l with
           | [] => None
           | _ :: t => optnth m t
           end
  end.

Definition optcons {A: Type} (x: A) (l: option (list A)) :=
  match l with
  | Some l' => Some (x :: l')
  | None => None
  end.

Fixpoint optlist {A: Type} (l: list (option A)) : option (list A) :=
  match l with
  | nil => (Some nil)
  | (Some h) :: t =>
    optcons h (optlist t)
  | None :: t => None
  end.

Fixpoint NatValueBool t :=
  match t with
  | const Zero => true
  | app (const Suc) e2 => NatValueBool e2
  | _ => false
  end.

Fixpoint EvalTerm_fix (E: list Data) t :=
  match t with
  | const c => Some (const c)
  | var n =>
    match optnth n E with
    | Some d => Some (Data_to_term d)
    | None => None
    end
  | pair e1 e2 =>
    match (EvalTerm_fix E e1, EvalTerm_fix E e2) with
    | (Some v1, Some v2) => Some (pair v1 v2)
    | _ => None
    end
  | If e1 e2 e3 =>
    match EvalTerm_fix E e1 with
    | Some (const T) => EvalTerm_fix E e2
    | Some (const F) => EvalTerm_fix E e3
    | _ => None
    end
  | abs l e =>
    match optlist (map (EvalTerm_fix E) l) with
    | Some vl => Some (abs [] (subst 0 e vl))
    | None => None
    end
  | app e1 e2 =>
    match e1 with
    | const Zerop => match e2 with
                     | const Zero => Some (const T)
                     | _ => Some (const F)
                     end
    | const Suc => if NatValueBool e2 then Some t else None
    | const Pred => match e2 with
                    | app (const Suc) v => if NatValueBool v then Some v else None
                    | _ => None
                    end
    | const Fst => match EvalTerm_fix E e2 with
                   | Some (pair v _) => Some v
                   | _ => None
                   end
    | const Snd => match EvalTerm_fix E e2 with
                   | Some (pair _ v) => Some v
                   | _ => None
                   end
    | _ => None
    end
  end.

Lemma NatValueData : forall t,
    NatValueBool t = true ->
    exists n,t = (Data_to_term((NatData n))).
Proof.
  induction t; simpl; intros; try discriminate.
  destruct c; try discriminate.
  exists 0. reflexivity.
  destruct t1; try discriminate.
  destruct c; try discriminate. apply IHt2 in H. destruct H.
  exists (S x). simpl in H. subst. simpl. reflexivity.
Qed.

Lemma PairDataEx : forall t1 t2 x,
    pair t1 t2 = Data_to_term x ->
    exists v1 v2, x = PairData v1 v2.
Proof.
  intros.
  induction x.
  destruct n; simpl in H; try discriminate.
  destruct b; simpl in H; try discriminate.
  destruct f; simpl in H; try discriminate.
  inversion H; subst. exists x1, x2; reflexivity.
Qed.

Theorem EvalIsData : forall t E v,
    EvalTerm_fix E t = Some v ->
    exists d, v = (Data_to_term d).
Proof.
  induction t; simpl; intros.
  -
    inversion H; subst. destruct c.
    exists (BoolData true); reflexivity.
    exists (BoolData false); reflexivity.
    exists (NatData 0); reflexivity.
    exists (FuncData SUC); reflexivity.
    exists (FuncData PRED); reflexivity.
    exists (FuncData ZEROP); reflexivity.
    exists (FuncData FST); reflexivity.
    exists (FuncData SND); reflexivity.
  -
    destruct optnth eqn:IH; try discriminate.
    inversion H; subst. eexists; eauto.
  -
    destruct optlist eqn:IH; try discriminate.
    inversion H; subst.
    exists (FuncData (Lambda (subst 0 t l0))); reflexivity.
  -
    destruct EvalTerm_fix eqn:IH1; try discriminate.
    destruct (EvalTerm_fix E t2) eqn:IH2; try discriminate.
    apply IHt1 in IH1. apply IHt2 in IH2. destruct IH1. destruct IH2.
    inversion H; subst. exists (PairData x x0); reflexivity.
  -
    destruct t1; try discriminate.
    destruct c; try discriminate.
    +
      destruct NatValueBool eqn:IH; try discriminate.
      inversion H; subst.
      apply NatValueData in IH. destruct IH. subst. exists (NatData (S x)). reflexivity.
    +
      destruct t2; try discriminate.
      destruct t2_1; try discriminate.
      destruct c; try discriminate.
      destruct NatValueBool eqn:IH; try discriminate.
      inversion H; subst. apply NatValueData in IH. destruct IH.
      exists (NatData x). subst. reflexivity.
    +
      destruct t2; try solve [inversion H; subst; exists (BoolData false); reflexivity].
      destruct c; inversion H; subst; try solve [exists (BoolData false); reflexivity].
      exists (BoolData true). reflexivity.
    +
      destruct EvalTerm_fix eqn:IH1; try discriminate.
      destruct t; try discriminate.
      apply IHt2 in IH1. destruct IH1. inversion H0; subst.
      apply PairDataEx in H2. destruct H2. destruct H1. subst.
      inversion H0; subst. inversion H; subst. exists x0. reflexivity.
    +
      destruct EvalTerm_fix eqn:IH1; try discriminate.
      destruct t; try discriminate.
      apply IHt2 in IH1. destruct IH1. inversion H0; subst.
      apply PairDataEx in H2. destruct H2. destruct H1. subst.
      inversion H0; subst. inversion H; subst. exists x1. reflexivity.
  -
    destruct EvalTerm_fix; try discriminate.
    destruct t; try discriminate.
    destruct c; try discriminate.
    eapply IHt2; eauto.
    eapply IHt3; eauto.
Qed.






Inductive EvalTerm : term -> (list Data) -> term -> Prop :=
| ConstE: forall c E, EvalTerm (const c) E (const c)
| VarE: forall n E d, optnth n E = Some d -> EvalTerm (var n) E (Data_to_term d)
| PairE: forall e1 e2 E v1 v2, EvalTerm e1 E v1 -> EvalTerm e2 E v2 -> EvalTerm (<<e1, e2>>) E (<<v1, v2>>)
| IfTE: forall e1 E e2 e3 v, EvalTerm e1 E (const T) -> EvalTerm e2 E v -> EvalTerm (If e1 e2 e3) E v
| IfFE: forall e1 E e2 e3 v, EvalTerm e1 E (const F) -> EvalTerm e3 E v -> EvalTerm (If e1 e2 e3) E v
| LambdaE: forall e v E l, ListEval l E v -> EvalTerm (λ l; e) E (λ[]; (subst 0 e v))

with ListEval : (list term) -> (list Data) -> (list term) -> Prop :=
   | NilEval : forall E, ListEval nil E nil
   | ConsEval : forall l1 l2 e E v, EvalTerm e E v -> ListEval l1 E l2 -> ListEval (e :: l1) E (v :: l2).

Scheme EvalTerm_mut := Induction for EvalTerm Sort Prop
with ListEval_mut := Induction for ListEval Sort Prop.

Reserved Notation " t1 '->>' t2" (at level 20).
Inductive ValueEval : term -> term -> Prop :=
| ZeropT : (app (const Zerop) (const Zero)) ->> (const T)
| ZeropF : forall v, v <> (const Zero) -> (app (const Zerop) v) ->> (const F)
| SucVE : forall t1, NatValue t1 -> (app (const Suc) t1) ->> (app (const Suc) t1)
| FstVE : forall t1 t2, (app (const Fst) (<< t1, t2 >>))  ->> t1
| SndVE : forall t1 t2, (app (const Snd) (<< t1, t2 >>))  ->> t2
| LambdaVE : forall t1 d v, (EvalTerm t1 [d] v) -> app(λ nil; t1) (Data_to_term d) ->> v
where "t1 ->> t2" := (ValueEval t1 t2).
