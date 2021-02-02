Require Import Nat.
Require Import List.
Import ListNotations.
Set Implicit Arguments.
Set Asymmetric Patterns.

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

Section term_ind'.

Variable P : term -> Prop.

Fixpoint All (ls : list term) : Prop :=
match ls with
| [] => True
| h :: t => P h /\ All t
end.

Hypothesis const_case : forall c: constant,  P (const c).
Hypothesis var_case : forall n: nat,  P (var n).
Hypothesis abs_case : forall (l: list term) (t: term), All l -> P t -> P (abs l t).
Hypothesis app_case : forall t1 t2: term, P t1 -> P t2 -> P (app t1 t2).
Hypothesis pair_case : forall t1 t2: term, P t1 -> P t2 -> P (pair t1 t2).
Hypothesis if_case : forall t1 t2 t3: term, P t1 -> P t2 -> P t3 -> P (If t1 t2 t3).

Fixpoint term_ind' (t: term) : P t :=
  match t with
  | const c => (const_case c)
  | var n => (var_case n)
  | app t1 t2 => app_case (term_ind' t1) (term_ind' t2)
  | pair t1 t2 => pair_case (term_ind' t1) (term_ind' t2)
  | If t1 t2 t3 => if_case (term_ind' t1) (term_ind' t2) (term_ind' t3)
  | abs l e =>
    abs_case l
      ((fix map_ind ls : All ls :=
          match ls with
          | [] => I
          | h :: tl => conj (term_ind' h) (map_ind tl)
          end)l) (term_ind' e)
  end.

End term_ind'.

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

Fixpoint eqb_const c1 c2 :=
  match (c1, c2) with
  | (T, T) => true
  | (F, F) => true
  | (Zero, Zero) => true
  | (Suc, Suc) => true
  | (Pred, Pred) => true
  | (Zerop, Zerop) => true
  | (Fst, Fst) => true
  | (Snd, Snd) => true
  | _ => false
  end.

Fixpoint Term_to_Nat t :=
  match t with
  | const Zero => Some 0
  | app (const Suc) e =>
    match Term_to_Nat e with
    | Some n => Some (S n)
    | None => None
    end
  | _ => None
  end.

Fixpoint Term_to_Data t :=
  match t with
  | (const c) =>
    match c with
    | T => Some (BoolData true)
    | F => Some (BoolData false)
    | Zero => Some (NatData 0)
    | Suc => Some (FuncData SUC)
    | Pred => Some (FuncData PRED)
    | Zerop => Some (FuncData ZEROP)
    | Fst => Some (FuncData FST)
    | Snd => Some (FuncData SND)
    end
  | pair e1 e2 =>
    match (Term_to_Data e1, Term_to_Data e2) with
    | (Some d1, Some d2) => Some (PairData d1 d2)
    | _ => None
    end
  | abs [] e => Some (FuncData (Lambda e))
  | app (const Suc) e =>
    match Term_to_Nat e with
    | Some n => Some (NatData (S n))
    | None => None
    end
  | _ => None
  end.

Fixpoint isval t :=
  match t with
  | const _ => true
  | pair t1 t2 => andb (isval t1) (isval t2)
  | abs [] _ => true
  | app (const Suc) n => if NatValueBool n then true else false
  | _ => false
  end.

Fixpoint boolList {A: Type} (F: A -> bool) (l: list A) :=
  match l with
  | [] => true
  | h :: t => andb (F h) (boolList F t)
  end.

Fixpoint EvalTerm_fix (E: list Data) t :=
  match t with
  | const c => Some (const c)
  | var n => match optnth n E with
             | Some d => Some (Data_to_term d)
             | None => None
             end
  | pair e1 e2 =>
    match (isval e1, isval e2) with
    | (false, _) => match EvalTerm_fix E e1 with
                    | Some v1 => Some (pair v1 e2)
                    | None => None
                    end
    | (true, false) => match EvalTerm_fix E e2 with
                       | Some v2 => Some (pair e1 v2)
                       | None => None
                       end
    | (true, true) => Some (pair e1 e2)
    end
  | If e1 e2 e3 =>
    if isval e1 then
      match e1 with
      | const T => EvalTerm_fix E e2
      | const F => EvalTerm_fix E e3
      | _ => None
      end
    else EvalTerm_fix E e1
  | abs l e =>
    match optlist (map (EvalTerm_fix E) l) with
    | Some vl =>
      if boolList isval vl then Some (abs [] (subst 1 e vl)) else Some (abs vl e)
    | None => None
    end
  | app t1 t2 =>
    match (isval t1, isval t2) with
    | (false, _) => match EvalTerm_fix E t1 with
                    | Some v1 => Some (app v1 t2)
                    | None => None
                    end
    | (true, false) => match EvalTerm_fix E t2 with
                       | Some v2 => Some (app t1 v2)
                       | None => None
                       end
    | (true, true) =>
      match (t1, t2) with
      | (const Zerop, v2)=> match v2 with
                              | const Zero => Some (const T)
                              | _ => Some (const F)
                            end
      | (const Suc, v2) => if NatValueBool v2 then Some (app t1 t2) else None
      | (const Fst, pair v1 v2) => Some v1
      | (const Snd, pair v1 v2) => Some v2
      | (abs [] e, v2) =>
        match Term_to_Data v2 with
        | Some v => EvalTerm_fix [v] e
        | None => None
        end
      | _ => None
      end
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

Lemma NatValue_to_Term : forall n,
    NatValueBool (Nat_to_term n) = true.
Proof.
  induction n; simpl; intros; auto.
Qed.

Lemma substnil : forall t n,
    subst n t nil = t.
Proof.
  induction t using term_ind'; simpl; intros; auto.
  -
    destruct ltb; auto.
    destruct (n - n0); auto.
  -
    rewrite IHt. clear IHt.
    induction l; auto.
    rewrite map_cons. simpl in H. destruct H. rewrite H. apply IHl in H0. inversion H0; subst.
    repeat rewrite H2. reflexivity.
  -
    rewrite IHt1, IHt2. reflexivity.
  -
    rewrite IHt1, IHt2. reflexivity.
  -
    rewrite IHt1, IHt2, IHt3; reflexivity.
Qed.

Lemma NatTerm_is_value : forall n,
    NatValueBool n = true -> isval n = true.
Proof.
  induction n; simpl; intros; try discriminate; auto.
  destruct n1; try discriminate.
  destruct c; try discriminate. rewrite H; auto.
Qed.

Lemma Data_to_term_is_value : forall d,
    isval (Data_to_term d) =  true.
Proof.
  induction d; simpl; auto.
  -
    rewrite NatTerm_is_value; auto. apply NatValue_to_Term.
  -
    destruct b; auto.
  -
    destruct f; auto.
  -
    rewrite IHd1, IHd2. reflexivity.
Qed.

Theorem DataEvalRefl : forall d E,
    EvalTerm_fix E (Data_to_term d) = Some (Data_to_term d).
Proof.
  induction d; simpl; intros; auto.
  -
    induction n; simpl; auto.
    rewrite NatTerm_is_value; rewrite NatValue_to_Term; reflexivity.
  -
    destruct b; simpl; auto.
  -
    induction f; simpl; auto.
    rewrite substnil. reflexivity.
  -
    rewrite IHd1, IHd2.
    repeat rewrite Data_to_term_is_value.
    reflexivity.
Qed.

(*
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
    | Some vl => Some (abs [] (subst 1 e vl))
    | None => None
    end
  | app t1 t2 =>
    match (EvalTerm_fix E t1, EvalTerm_fix E t2) with
    | (Some e1, Some e2) =>
      match e1 with
      | const Zerop => match e2 with
                       | const Zero => Some (const T)
                       | _ => Some (const F)
                       end
      | const Suc => if NatValueBool e2 then Some (app e1 e2) else None
      | const Pred => match e2 with
                      | app (const Suc) v => if NatValueBool v then Some v else None
                      | _ => None
                      end
      | const Fst => match e2 with
                     | pair v _ => Some v
                     | _ => None
                     end
      | const Snd => match e2 with
                     | pair _ v => Some v
                     | _ => None
                     end
      (*
      | abs [] e => 
        match Term_to_Data t2 with
        | Some v => EvalTerm_fix [v] e
        | None => None
        end
       *)
      | _ => None
      end
    | _ => None
    end
  end.


Theorem DataEvalRefl : forall d E,
    EvalTerm_fix E (Data_to_term d) = Some (Data_to_term d).
Proof.
  induction d; simpl; intros; auto.
  -
    induction n; simpl; auto.
    rewrite IHn. rewrite NatValue_to_Term. reflexivity.
  -
    destruct b; simpl; auto.
  -
    induction f; simpl; auto.
    rewrite substnil. reflexivity.
  -
    rewrite IHd1, IHd2. reflexivity.
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
    exists (FuncData (Lambda (subst 1 t l0))); reflexivity.
  -
    destruct EvalTerm_fix eqn:IH1; try discriminate.
    destruct (EvalTerm_fix E t2) eqn:IH2; try discriminate.
    apply IHt1 in IH1. apply IHt2 in IH2. destruct IH1. destruct IH2.
    inversion H; subst. exists (PairData x x0); reflexivity.
  -
    destruct EvalTerm_fix eqn:IH1; try discriminate.
    destruct (EvalTerm_fix E t2) eqn:IH2; try discriminate.
    destruct t; try discriminate.
    destruct c; try discriminate.
    +
      destruct NatValueBool eqn:IH; try discriminate.
      inversion H; subst.
      generalize IH1; generalize IH2; intros.
      apply IHt1 in IH1; destruct IH1. apply IHt2 in IH2; destruct IH2.
      inversion H1; subst.
      apply NatValueData in IH. destruct IH. exists (NatData (S x1)). simpl. inversion H1; subst. reflexivity.
    +
      destruct t0; try discriminate.
      destruct t0_1; try discriminate.
      destruct c; try discriminate.
      destruct NatValueBool eqn:IH; try discriminate.
      inversion H; subst. apply NatValueData in IH. destruct IH.
      exists (NatData x). subst. reflexivity.
    +
      destruct t0; try solve [inversion H; subst; exists (BoolData false); reflexivity].
      destruct c; inversion H; subst; try solve [exists (BoolData false); reflexivity].
      exists (BoolData true). reflexivity.
    +
      destruct t0; try discriminate.
      apply IHt1 in IH1. apply IHt2 in IH2. destruct IH1. destruct IH2.
      generalize H1; intros. inversion H; subst. apply PairDataEx in H1. destruct H1. destruct H1. subst.
      inversion H2; subst. exists x1; reflexivity.
    +
      destruct t0; try discriminate.
      apply IHt1 in IH1. apply IHt2 in IH2. destruct IH1. destruct IH2.
      generalize H1; intros. inversion H; subst. apply PairDataEx in H1. destruct H1. destruct H1. subst.
      inversion H2; subst. exists x2; reflexivity.
    (*
    +
      admit.
     *)
  -
    destruct EvalTerm_fix; try discriminate.
    destruct t; try discriminate.
    destruct c; try discriminate.
    eapply IHt2; eauto.
    eapply IHt3; eauto.
Qed.
 *)

Inductive EvalTerm : term -> (list Data) -> term -> Prop :=
| ConstE: forall c E, EvalTerm (const c) E (const c)
| VarE: forall n E d, optnth n E = Some d -> EvalTerm (var n) E (Data_to_term d)
| PairE: forall e1 e2 E v1 v2, EvalTerm e1 E v1 -> EvalTerm e2 E v2 -> EvalTerm (<<e1, e2>>) E (<<v1, v2>>)
| IfTE: forall e1 E e2 e3 v, EvalTerm e1 E (const T) -> EvalTerm e2 E v -> EvalTerm (If e1 e2 e3) E v
| IfFE: forall e1 E e2 e3 v, EvalTerm e1 E (const F) -> EvalTerm e3 E v -> EvalTerm (If e1 e2 e3) E v
| LambdaE: forall e v E l, ListEval l E v -> EvalTerm (λ l; e) E (λ[]; (subst 0 e v))
| app_ZeopT : forall e1 e2 E,
    EvalTerm e1 E (const Zerop) -> EvalTerm e2 E (const Zero) -> EvalTerm (app e1 e2) E (const T)
| app_ZeropF : forall e1 e2 v E,
    EvalTerm e1 E (const Zerop) -> EvalTerm e2 E v -> v <> (const Zero) -> EvalTerm (app e1 e2) E (const F)
| app_Suc : forall e1 e2 E v,
    EvalTerm e1 E (const Suc) -> EvalTerm e2 E v -> NatValue v ->
    EvalTerm (app e1 e2) E (app (const Suc) v)
| app_Fst : forall e1 e2 v1 v2 E,
    EvalTerm e1 E (const Fst) -> EvalTerm e2 E (pair v1 v2) -> EvalTerm (app e1 e2) E v1
| app_Snd : forall e1 e2 v1 v2 E,
    EvalTerm e1 E (const Snd) -> EvalTerm e2 E (pair v1 v2) -> EvalTerm (app e1 e2) E v2
| app_abs : forall e1 e2 e v0 d E v,
    EvalTerm e1 E (abs [] e) -> EvalTerm e2 E v0 ->
    Term_to_Data v0 = Some d -> EvalTerm e [d] v -> EvalTerm (app e1 e2) E v
with ListEval : (list term) -> (list Data) -> (list term) -> Prop :=
   | NilEval : forall E, ListEval nil E nil
   | ConsEval : forall l1 l2 e E v, EvalTerm e E v -> ListEval l1 E l2 -> ListEval (e :: l1) E (v :: l2).

Scheme EvalTerm_mut := Induction for EvalTerm Sort Prop
with ListEval_mut := Induction for ListEval Sort Prop.

Theorem TermEvalUnique : forall t E v1 v2,
    EvalTerm t E v1 -> EvalTerm t E v2 -> v1 = v2.
Proof.
Abort.
