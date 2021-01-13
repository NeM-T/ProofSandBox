Require Coq.extraction.Extraction.
Require Import Ascii String Coq.Strings.Byte.
Require Import PeanoNat.
Require Export ExtrOcamlChar.
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive string => "char list" [ "[]" "(::)" ].
From Coq Require Import Lists.List.
Extract Inductive list => "list" [ "[]" "(::)" ].
Extraction Language OCaml.
Import ListNotations.
Import Nat.

Inductive deBruijn : Type :=
| var : nat -> deBruijn
| app : deBruijn -> deBruijn -> deBruijn
| abs : string -> deBruijn -> deBruijn.

Fixpoint shift k t :=
match t with
| var x => var (if leb k x then (S x) else x)
| abs x t' => abs x (shift (S k) t')
| app t1 t2 => app (shift k t1) (shift k t2)
end.

Reserved Notation "t '[[' x '\' s ']]'" (at level 20).
Fixpoint subst (d : nat) s t :=
match t with
| var x =>
  if eqb d x then s
  else if ltb d x then var (pred x) else var x
| abs x t' => abs x  (t' [[ (S d) \ (shift 0 s) ]])
| app t1 t2 => app (t1[[d\ s]]) (t2[[d \ s]])
end
where "t '[[' x '\' s ']]'" := (subst x s t).

Inductive namelambda : Type :=
| Var (name: string)
| Abs (name: string) (t: namelambda)
| App (t1 t2: namelambda).

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst_name (x : string) s t :=
  match t with
  | Var x' => if String.eqb x x' then s else t
  | Abs x' t1 => Abs x' (if String.eqb x x' then t1 else ([x:=s] t1))
  | App t1 t2 => App ([x:=s] t1) ([x:=s] t2)
  end
where "'[' x ':=' s ']' t" := (subst_name x s t).


Fixpoint in_list x l n :=
  match l with
  | nil => None
  | h :: t => if String.eqb h x then Some n else in_list x t (S n)
  end.

Fixpoint inb x l :=
  match l with
  | nil => false
  | h :: t => if String.eqb h x then true else (inb x t)
  end.

Fixpoint free_list l1 l2 t :=
  match t with
  | Var x =>
    if orb (inb x l1) (inb x l2) then l2 else (x :: l2)
  | Abs x t1 => (free_list (x :: l1) l2 t1)
  | App t1 t2 =>
    free_list l1 (free_list l1 l2 t1) t2
  end.

Fixpoint removenames l t :=
  match t with
  | Var x =>
    match in_list x l 0 with
    | Some n => Some (var n)
    | None => None
    end
  | Abs x t' =>
    match (removenames (x :: l) t') with
    | Some t1 => Some (abs x t1)
    | None => None
    end
  | App t1 t2 =>
    match ((removenames l t1) ,(removenames l t2)) with
      | (Some t1', Some t2') => Some (app t1' t2')
      | _ => None
    end
  end.

Definition lambda_to_debruijn t := removenames (free_list [] [] t) t.

Fixpoint nth {A: Type} (l: list A) n :=
  match n with
  | 0 =>
    match l with
    | nil => None
    | h :: t => Some h
    end
  | S n' =>
    match l with
    | nil => None
    | h :: t => nth t n'
    end
  end.

Fixpoint debruijn_to_lambda l t:=
  match t with
  | var n =>
    match nth l n with
    | Some x => Some (Var x)
    | None => None
    end
  | abs x t1 =>
    match debruijn_to_lambda (x :: l) t1 with
    | Some t' => Some (Abs x t')
    | None => None
    end
  | app t1 t2 =>
    match (debruijn_to_lambda l t1, debruijn_to_lambda l t2) with
    | (Some t1', Some t2') => Some (App t1' t2')
    | _ => None
    end
  end.

Lemma in_list_plus : forall l n1 n2 s,
    n2 <= n1 ->
    in_list s l n1 =
    (fun x => match x with | None => None | Some x' => Some  (x' + (n1 - n2)) end) (in_list s l n2).
Proof.
  induction l; simpl; intros; auto.
  destruct String.eqb. rewrite add_sub_assoc; auto. rewrite Minus.minus_plus. reflexivity.
  rewrite IHl with (n2:= S n2). reflexivity. apply le_n_S. apply H.
Qed.

Lemma in_nth : forall l n s,
    in_list s l 0 = Some n ->
    nth l n = Some s.
Proof.
  induction l; simpl; intros.
  inversion H.
  destruct String.eqb eqn:IH1. inversion H; subst. apply String.eqb_eq in IH1; subst. reflexivity.
  rewrite in_list_plus with (n2:= 0) in H; auto. simpl in H. destruct (in_list s l 0) eqn:IH2. rewrite add_1_r in H.
  inversion H; subst. apply IHl in IH2. apply IH2. inversion H.
Qed.


Lemma n_to_n : forall t1 t1' l,
    removenames l t1 = Some t1' ->
    debruijn_to_lambda l t1' = Some t1.
Proof.
  induction t1; simpl; intros; auto.
  -
    destruct in_list eqn:IH1. inversion H; subst. simpl.
    apply in_nth in IH1. rewrite IH1. reflexivity.
    inversion H.
  -
    destruct removenames eqn:IH1. inversion H; subst. apply IHt1 in IH1.
    simpl. rewrite IH1. reflexivity. inversion H.
  -
    destruct removenames eqn:IH1. destruct (removenames l t1_2) eqn:IH2.
    inversion H; subst; simpl.
    apply IHt1_1 in IH1. apply IHt1_2 in IH2. rewrite IH1, IH2. reflexivity.
    inversion H. inversion H.
Qed.


Fixpoint left_eval t :=
  match t with
  | app t1 t2 =>
    match t1 with
    | abs x t1' => Some (subst 0 t2 t1')
    | _ =>
      match left_eval t1 with
      | Some t1' => Some (app t1' t2)
      | _ =>
        match left_eval t2 with
        | Some t2' => Some (app t1 t2')
        | None => None
        end
      end
    end
  | abs x t1 =>
    match left_eval t1 with
    | Some t1' => Some (abs x t1')
    | None => None
    end
  | _ => None
  end.

Definition result_lambda t l :=
  match left_eval t with
  | Some t' => debruijn_to_lambda l t'
  | None => None
  end.

Extraction "ocaml/src/eval.ml" lambda_to_debruijn left_eval debruijn_to_lambda result_lambda.

Reserved Notation " t '-->' t' " (at level 40).
Inductive eval : deBruijn -> deBruijn -> Prop :=
| E_Abs : forall x t1 t1',
    t1 --> t1' ->
    abs x t1 --> abs x t1'
| E_App1 : forall t1 t1' t2,
    t1 --> t1' ->
    app t1 t2 --> app t1' t2
| E_App2 : forall t1 t2 t2',
    t2 --> t2' ->
    app t1 t2 --> app t1 t2'
| E_AppAbs : forall t1 t2 x,
    app (abs x t1) t2 -->  t1 [[0 \ t2]]

  where " t '-->' t' " := (eval t t').

Reserved Notation " t '-->>' t' " (at level 40).
Inductive many_eval : deBruijn -> deBruijn -> Prop :=
| eval_refl : forall t, t -->> t
| eval_trans : forall t1 t2 t3,
    t1 --> t2 -> t2 -->> t3 -> t1 -->> t3

  where " t '-->>' t' " := (many_eval t t').


Reserved Notation " t '==>' t' " (at level 40).
Inductive par_eval : deBruijn -> deBruijn -> Prop :=
| PE_Var : forall n, var n ==> var n
| PE_Abs : forall x t1 t1',
    t1 ==> t1' ->
    abs x t1 ==> abs x t1'
| PE_App : forall t1 t1' t2 t2',
    t1 ==> t1' ->
    t2 ==> t2' ->
    app t1 t2 ==> app t1' t2'
| PE_AppAbs : forall t1 t2 t1' t2' x,
    t1 ==> t1' -> t2 ==> t2' ->
    app (abs x t1) t2 ==>  t1' [[0 \ t2']]

  where " t '==>' t' " := (par_eval t t').

Lemma app_bigstep : forall t1 t2 t1' t2',
    t1 -->> t1' -> t2 -->> t2' ->
    app t1 t2 -->> app t1' t2'.
Proof.
  intros.
  generalize dependent t2. generalize dependent t2'.
  induction H; intros. induction H0. constructor.
  econstructor. solve [constructor; eauto].
  auto.
  apply IHmany_eval in H1. econstructor. constructor; eauto. auto.
Qed.

Lemma abs_bigstep : forall t1 t1' x,
    t1 -->> t1' ->
    abs x t1 -->> abs x t1'.
Proof.
  intros. induction H; try econstructor; eauto.
  constructor; auto.
Qed.

Lemma bigstep_trans : forall t1 t2 t3,
    t1 -->> t2 -> t2 -->> t3 ->
    t1 -->> t3.
Proof.
  intros. generalize dependent t3. induction H; intros; auto.
  apply IHmany_eval in H1. econstructor; eauto.
Qed.

Lemma par_bigstep : forall t1 t1',
    t1 ==> t1' -> t1 -->> t1'.
Proof.
  induction t1; intros.
  -
    inversion H; subst. constructor.
  -
    inversion H; subst.
    apply IHt1_1 in H2. apply IHt1_2 in H4. apply app_bigstep; auto.
    apply bigstep_trans with (app (abs x t1'0) t2'). apply app_bigstep; auto.
    apply IHt1_1. constructor; auto. econstructor. apply E_AppAbs. constructor.
  -
    inversion H; subst. apply IHt1 in H3. eapply abs_bigstep in H3. eapply bigstep_trans; eauto.
    constructor.
Qed.

Lemma par_refl : forall t1,
    t1 ==> t1.
Proof.
  induction t1; try constructor; auto.
Qed.

Lemma par_onestep : forall t t',
    t --> t' -> t ==> t'.
Proof.
  intros. induction H; try (constructor; auto); try apply par_refl.
Qed.

Lemma leb_S : forall n1 n2,
    n1 <=? n2 = true -> n1 <=? (S n2) = true.
Proof.
  intros.
  apply leb_le. apply leb_le in H.
  induction H; constructor; auto.
Qed.

Lemma shift_shift : forall t1 i k,
    i < (S k) ->
    shift (S k) (shift i t1 ) = shift i (shift k t1).
Proof.
  induction t1; simpl; intros.
  -
    destruct leb eqn:IH1; destruct (leb k n) eqn:IH2.
    apply leb_S in IH1. rewrite IH1. reflexivity. rewrite IH1. reflexivity.
    apply Lt.lt_n_Sm_le in H. apply leb_le in IH2. apply le_trans with (p := n) in H; auto.
    apply leb_le in H. rewrite H in IH1. inversion IH1.
    rewrite IH1. destruct n. reflexivity.
    destruct (k <=? n) eqn:IH3; auto.
    apply leb_le in IH3. apply le_n_S in IH3. apply lt_le_incl in H. apply le_trans with (p:= (S n)) in H; auto.
    apply leb_le in H. rewrite H in IH1. inversion IH1.
  -
    rewrite IHt1_1; auto. rewrite IHt1_2; auto.
  -
    rewrite IHt1; auto. apply Lt.lt_n_S in H. apply H.
Qed.

Lemma shift_sub : forall t1 i j s,
    j < (S i) ->
    shift i (t1 [[ j \ s]] ) = (shift (i + 1 ) t1) [[j \ (shift i s) ]].
Proof.
  induction t1; simpl; intros.
  -
    rewrite add_1_r.
    destruct eqb eqn:IH1.
    +
      apply eqb_eq in IH1; subst.
      destruct leb eqn:IH2.
      *
        apply leb_le in IH2. apply Lt.lt_not_le in H. induction H; auto.
      *
        rewrite eqb_refl. reflexivity.
    +
      destruct ltb eqn:IH2.
      *
        destruct leb eqn:IH3.
        **
          destruct (j =? S n) eqn:IH4.
          ***
            apply eqb_eq in IH4; subst. apply leb_le in IH3. apply nlt_ge in IH3. compute in IH3. apply lt_le_incl in H. induction IH3; auto.
          ***
            simpl.
            destruct n. inversion IH2. simpl.
            apply ltb_lt in IH3. compute in IH3. apply le_S_n in IH3. apply leb_le in IH3. rewrite IH3.
            apply ltb_lt in IH2. apply lt_lt_succ_r in IH2. apply ltb_lt in IH2. rewrite IH2. reflexivity.
        **
          rewrite IH1. rewrite IH2. simpl. destruct n. inversion IH2.
          simpl. apply leb_nle in IH3. apply nle_gt in IH3. apply Lt.lt_S_n in IH3. apply nle_gt in IH3.
          apply leb_nle in IH3. rewrite IH3. reflexivity.
      *
        destruct leb eqn:IH3.
        **
          destruct (j =? S n) eqn:IH4.
          ***
            apply eqb_eq in IH4; subst. compute in H. apply le_S_n in H. apply nlt_ge in H. apply leb_le in IH3.
            apply Lt.le_lt_n_Sm in IH3. apply lt_succ_l in IH3. induction H; apply IH3.
          ***
            simpl.
            apply leb_le in IH3. apply Le.le_Sn_le in IH3. apply leb_le in IH3. rewrite IH3.
            assert (j <? S n = false).
            apply ltb_nlt in IH2. apply nle_gt in IH2. apply (lt_succ_r n j) in IH2.
            apply ltb_nlt. apply Lt.le_not_lt. apply le_succ_l.
            apply Lt.le_lt_or_eq in IH2. destruct IH2; auto. subst. rewrite eqb_refl in IH1. inversion IH1.
            rewrite H0. reflexivity.
        **
          rewrite IH1. rewrite IH2. simpl.
          apply leb_nle in IH2. apply nle_gt in IH2.
          apply leb_nle in IH3. apply nle_gt in IH3. apply Lt.lt_n_Sm_le in IH3.
          apply Lt.le_lt_or_eq in IH3. destruct IH3. apply nle_gt in H0. apply leb_nle in H0. rewrite H0.
          reflexivity.
          subst.
          compute in H. compute in IH2. apply le_antisymm in H; auto. inversion H; subst. rewrite eqb_refl in IH1.
          inversion IH1.
  -
    rewrite IHt1_1; try rewrite IHt1_2; auto.
  -
    rewrite IHt1. rewrite shift_shift; auto.
    apply lt_0_succ.
    apply Lt.lt_n_S; auto.
Qed.

Lemma shift_sub_lt : forall t1 s i j,
    i < (S j) ->
    shift i (t1 [[j \ s]]) = (shift i t1) [[(S j) \ shift i s]].
Proof.
  induction t1; simpl; intros.
  -
    destruct eqb eqn:IH1.
    +
      apply eqb_eq in IH1; subst.
      destruct leb eqn:IH2.
      *
        simpl. rewrite eqb_refl. reflexivity.
      *
        apply leb_nle in IH2. compute in H. apply le_S_n in H. induction IH2; auto.
    +
      destruct (j <? n) eqn:IH2.
      *
        destruct (i <=? n) eqn:IH3.
        **
          rewrite IH1. apply ltb_lt in IH2. apply Lt.lt_n_S in IH2. apply ltb_lt in IH2.
          rewrite IH2. simpl. destruct n; try discriminate; simpl.
          apply leb_le in IH3. apply Lt.le_lt_or_eq in IH3. destruct IH3; subst.
          compute in H0. apply le_S_n in H0. apply leb_le in H0; rewrite H0. reflexivity.
          apply ltb_lt in IH2. apply Lt.lt_S_n in IH2. apply Lt.lt_S_n in H.
          apply nle_gt in IH2. compute in H. induction IH2. apply H.
        **
          destruct n; try discriminate; simpl.
          apply leb_nle in IH3. apply nle_gt in IH3. apply lt_succ_l in IH3. apply nle_gt in IH3. apply leb_nle in IH3. rewrite IH3.
          destruct (j =? n) eqn:IH4. apply eqb_eq in IH4; subst. compute in H. apply leb_nle in IH3. apply le_S_n in H. induction IH3; apply H.
          destruct (S j <? S n) eqn:IH5; auto.
          apply ltb_lt in IH2. compute in IH2. apply Lt.le_lt_or_eq in IH2. destruct IH2; subst; try discriminate.
          apply ltb_lt in H0. rewrite H0 in IH5. inversion IH5. inversion H0; subst. rewrite eqb_refl in IH4. inversion IH4.
      *
        destruct leb eqn:IH3.
        **
          rewrite IH1. simpl. rewrite IH3. destruct (S j <? S n) eqn:IH4; auto.
          apply ltb_lt in IH4. apply Lt.lt_S_n in IH4. apply ltb_lt in IH4. rewrite IH4 in IH2. inversion IH2.
        **
          destruct n; simpl. rewrite IH3. reflexivity.
          rewrite IH3. destruct (j =? n) eqn:IH4.
          apply eqb_eq in IH4; subst. apply ltb_nlt in IH2. apply nlt_ge in IH2. einduction nle_succ_diag_l. apply IH2.
          destruct (S j <? S n) eqn:IH5; auto.
          apply ltb_lt in IH5. compute in IH5. repeat apply Le.le_Sn_le in IH5.
          apply Lt.le_lt_or_eq in IH5; destruct IH5; subst. apply ltb_lt in H0. rewrite H0 in IH2. inversion IH2.
          rewrite eqb_refl in IH1. inversion IH1.
  -
    rewrite IHt1_1; try rewrite IHt1_2; auto.
  -
    rewrite IHt1; auto. rewrite shift_shift; auto.
    apply lt_0_succ.
    apply Lt.lt_n_S; auto.
Qed.

Lemma sub_shift : forall t1 k s,
  (shift k t1)[[k \ s]] = t1.
Proof.
  induction t1; simpl; intros.
  -
    destruct (k <=? n) eqn:IH1.
    +
      destruct eqb eqn:IH2.
      *
        apply eqb_eq in IH2; subst. apply leb_le in IH1. einduction nle_succ_diag_l; eauto.
      *
        simpl.
        assert (k <? S n = true).
        apply leb_le in IH1. apply le_n_S in IH1. unfold ltb. apply leb_le. apply IH1.
        rewrite H; reflexivity.
    +
      destruct eqb eqn:IH2.
      *
        apply eqb_eq in IH2; subst. rewrite leb_refl in IH1. inversion IH1.
      *
        destruct ltb eqn:IH3.
        **
          apply ltb_lt in IH3. apply lt_le_incl in IH3. apply leb_le in IH3. rewrite IH3 in IH1. inversion IH1.
        **
          reflexivity.
  -
    rewrite IHt1_1, IHt1_2; reflexivity.
  -
    rewrite IHt1. reflexivity.
Qed.

Lemma shift_preserve_beta : forall t1 t1' n,
    t1 --> t1' -> shift n t1 --> shift n t1'.
Proof.
  induction t1; simpl; intros; inversion H; subst.
  -
    constructor. apply IHt1_1. apply H3.
  -
    constructor. apply IHt1_2; apply H3.
  -
    simpl.
    rewrite shift_sub. rewrite add_1_r. constructor.
    apply lt_0_succ.
  -
    constructor. apply IHt1. apply H3.
Qed.

Lemma subsub :forall t1 j i v u,
    i < (S j) ->
    t1[[ S j \ shift i v ]] [[i \ u[[j\ v ]] ]] = t1 [[i \ u ]] [[j \ v]].
Proof.
  induction t1; simpl; intros.
  -
    destruct n.
    +
      destruct ltb eqn:IH1. inversion IH1.
      simpl. destruct i. reflexivity.
      simpl. apply Lt.lt_S_n in H. destruct j. inversion H. simpl. reflexivity.
    +
      simpl.
      destruct eqb eqn:IH1.
      ++
        apply eqb_eq in IH1; subst. generalize H; intros. compute in H. destruct eqb eqn:IH1; try apply eqb_eq in IH1; subst.
        einduction nle_succ_diag_l; eauto. apply ltb_lt in H0. rewrite H0. simpl. rewrite eqb_refl.
        rewrite sub_shift. reflexivity.
      ++
        destruct ltb eqn:IH2; simpl.
        destruct (eqb i n) eqn:IH3. apply eqb_eq in IH3; subst.
        apply ltb_lt in IH2.
        apply nle_gt in IH2. compute in H. induction IH2. apply H.
      --
        destruct (ltb i n) eqn:IH4.
        destruct (i =? S n) eqn:IH5; try apply eqb_eq in IH5; subst. apply ltb_lt in IH4.
        induction (nlt_succ_diag_l n); apply IH4.
        apply ltb_lt in IH2. apply lt_trans with (p:= S n) in H; auto. apply ltb_lt in H. rewrite H.
        simpl. rewrite IH1. apply Lt.lt_S_n in IH2. apply ltb_lt in IH2. rewrite IH2. reflexivity.
        destruct (i =? S n) eqn:IH5; try apply eqb_eq in IH5; subst.
        apply ltb_lt in IH2. apply nle_gt in IH2. apply lt_le_incl in H. induction IH2. apply H.
        apply ltb_lt in IH2. apply lt_trans with (p:= S n) in H; auto. compute in H.
        apply le_S_n in H. apply Lt.le_lt_or_eq in H. destruct H.
        apply ltb_lt in H. rewrite H in IH4. inversion IH4.
        subst. rewrite eqb_refl in IH3. inversion IH3.
      --
        destruct (i =? S n) eqn:IH3; try apply eqb_eq in IH3; subst; auto.
        apply ltb_nlt in IH2. apply nlt_ge in IH2.
        destruct (i <? S n) eqn:IH4. simpl.
        rewrite IH1. apply le_S_n in IH2. apply nlt_ge in IH2. apply ltb_nlt in IH2. rewrite IH2. reflexivity.
        simpl.
        destruct (eqb j (S n)) eqn:IH5; try apply eqb_eq in IH5; subst.
        ***
          compute in H. apply le_S_n in H. apply Lt.le_lt_or_eq in H. destruct H; subst.
          apply ltb_nlt in IH4. induction IH4; apply H.
          rewrite eqb_refl in IH3. inversion IH3.
        ***
          destruct (ltb j (S n)) eqn:IH6; auto.
          apply ltb_lt in IH6. compute in IH6.
          apply lt_le_trans with (p:= S n) in H; auto. apply ltb_lt in H. rewrite H in IH4.
          inversion IH4.
  -
    rewrite IHt1_2, IHt1_1; auto.
  -
    generalize lt_0_succ; intros.
    generalize H; intros.
    apply Lt.lt_n_S in H. apply IHt1 with (v:= v) (u:= u) in H.
    rewrite shift_sub_lt; auto. rewrite <- shift_shift; auto. rewrite IHt1. reflexivity. apply Lt.lt_n_S.
    apply H1.
Qed.

Lemma sub_preserve_beta : forall t1 t1' i s,
    t1 --> t1' ->
    t1[[i \ s]] --> t1' [[i \ s]].
Proof.
  induction t1; simpl; intros.
  inversion H.
  -
    inversion H; subst.
    *
      apply E_App1. apply IHt1_1. apply H3.
    *
      apply E_App2. apply IHt1_2; apply H3.
    *
      simpl. rewrite <- subsub. constructor.
      apply lt_0_succ.
  -
    inversion H; subst.
    constructor. apply IHt1. apply H3.
Qed.

Lemma par_shift : forall t1 t1' n,
    t1 ==> t1' -> shift n t1 ==> shift n t1'.
Proof.
  induction t1; intros; simpl; inversion H; subst; simpl.
  -
    apply par_refl.
  -
    constructor; auto.
  -
    rewrite shift_sub. constructor; auto. rewrite add_1_r.
    apply PE_Abs with (x:= x) in H2. apply IHt1_1 with (n:= n) in H2. simpl in H2. inversion H2; subst. apply H1.
    apply lt_0_succ.
  -
    constructor; auto.
Qed.

Lemma par_subst : forall t1 t2 t1' t2' n,
    t1 ==> t1' -> t2 ==> t2' ->
    t1[[n \ t2]] ==> t1' [[n \ t2']].
Proof.
  induction t1; simpl; intros; inversion H; subst; simpl.
  -
    destruct eqb. apply H0. apply par_refl.
  -
    constructor; auto.
  -
    rewrite <- subsub. constructor; auto.
    generalize H3; intros.
    apply PE_Abs with (x:= x) in H3.
    specialize (IHt1_1 t2 (abs x t1'0) t2' n). apply IHt1_1 in H3. simpl in H3. inversion H3; subst.
    apply H4. apply H0. apply lt_0_succ.
  -
    constructor; auto. apply par_shift with (n:= 0) in H0. apply IHt1; auto.
Qed.

Theorem ChurchRosser : forall M,
    exists N, (forall M', M ==> M' -> M' ==> N).
Proof.
  induction M.
  -
    exists (var n); intros. inversion H; subst; constructor.
  -
    destruct M1; inversion IHM1; clear IHM1; inversion IHM2; clear IHM2.
    +
      exists (app (var n) x0); intros. inversion H1; subst. inversion H4; subst. constructor; auto.
    +
      exists (app x x0). intros. inversion H1; subst. constructor; auto.
    +
      generalize H; intros. specialize (H1 (abs s M1)). generalize (par_refl (abs s M1)); intros.
      apply H1 in H2. inversion H2; subst.
      exists (subst 0 x0 t1'). intros. inversion H3; subst.
      *
        inversion H7; subst. apply H in H7. inversion H7; subst. constructor; auto.
      *
        apply PE_Abs with (x:= s) in H9. apply H in H9. inversion H9; subst. apply H0 in H10.
        apply par_subst; auto.
  -
    inversion IHM; clear IHM.
    exists (abs s x). intros. inversion H0; subst. constructor; auto.
Qed.

Inductive multi_par : deBruijn -> deBruijn -> Prop :=
| para_refl : forall d, multi_par d d
| para_trans : forall d1 d2 d3, d1 ==> d2 -> multi_par d2 d3 -> multi_par d1 d3.
Notation "d1 '==>>' d2" := (multi_par d1 d2) (at level 60).

Lemma many_par : forall t1 t2,
    t1 -->> t2 <-> t1 ==>> t2.
Proof.
  split; intros.

  induction H. constructor.
  econstructor; eauto. apply par_onestep. apply H.

  induction H.
  constructor. apply par_bigstep in H. eapply bigstep_trans; eauto.
Qed.

Lemma multi_par_trans : forall t1 t2 t3,
    t1 ==>> t2 -> t2 ==>> t3 ->
    t1 ==>> t3.
Proof.
  intros. generalize dependent t3.
  induction H; intros; auto.
  apply IHmulti_par in H1. econstructor; eauto.
Qed.

Lemma ChurchRosser2 : forall M M1 M2,
    M ==> M1 -> M ==> M2 ->
    exists N, M1 ==> N /\ M2 ==> N.
Proof.
  intros. generalize ChurchRosser.
  intros. specialize (H1 M). destruct H1. exists x.
  split; auto.
Qed.

Lemma par_multitrans : forall t1 t2 t3,
    t1 ==> t2 -> t2 ==> t3 ->
    t1 ==>> t3.
Proof.
  intros. apply para_trans with t2; auto. econstructor; eauto. constructor.
Qed.

Lemma chur : forall M,
    exists N, (forall M1, M --> M1 -> M1 -->> N).
Proof.
  generalize ChurchRosser; intros. specialize (H M); destruct H.
  exists x; intros. apply par_onestep in H0. apply H in H0.
  apply par_bigstep. apply H0.
Qed.

Lemma chh : forall t1 t2 t3,
    t1 ==> t2 -> t1 ==>> t3 ->
    exists N, t2 ==>> N /\ t3 ==>> N.
Proof.
  intros. generalize dependent t2. induction H0; intros.
  exists t2; split; try solve [econstructor; eauto; constructor].
  generalize ChurchRosser; intros. specialize (H2 d1). destruct H2.
  apply H2 in H. apply H2 in H1. apply IHmulti_par in H. destruct H. destruct H.
  exists x0; split; auto. econstructor; eauto.
Qed.

Lemma chhh : forall t1 t2 t3,
    t1 --> t2 -> t1 -->> t3 ->
    exists N, t2 -->> N /\ t3 -->> N.
Proof.
  intros. apply par_onestep in H. apply many_par in H0.
  eapply chh in H; eauto. destruct H. destruct H.
  apply many_par in H. apply many_par in H1.
  exists x; split; auto.
Qed.

Lemma ChurchRosser_many : forall M M1 M2,
    M -->> M1 -> M -->> M2 ->
    exists N, M1 -->> N /\ M2 -->> N.
Proof.
  intros.
  generalize dependent M2. induction H; intros.
  exists M2. split; auto; constructor.
  apply chhh with (t3:= M2) in H; auto.
  destruct H; destruct H.
  apply IHmany_eval in H. destruct H; destruct H.
  exists x0. split; auto. apply bigstep_trans with (t2:= x); auto.
Qed.

Definition eq_beta M N := (M -->> N) \/ (N -->> M).
Notation "M '=β' N" := (eq_beta M N) (at level 60).


Lemma K225 : forall M1 M2,
    M1 =β M2 -> exists N, M1 -->> N /\ M2 -->> N.
Proof.
  intros. compute in H. destruct H.
  -
    induction H. exists t0; split; constructor.
    inversion IHmany_eval. destruct H1.
    exists x. split; auto; try solve [econstructor; eauto].
  -
    induction H. exists t0; split; constructor.
    inversion IHmany_eval. destruct H1.
    exists x. split; auto; econstructor; eauto.
Qed.

Inductive in_beta : deBruijn -> Prop :=
| App_Abs_in : forall t1 t2 x, in_beta (app (abs x t1) t2)
| App_in1 : forall t1 t2, in_beta t1 -> in_beta (app t1 t2)
| App_in2 : forall t1 t2, in_beta t2 -> in_beta (app t1 t2)
| Abs_in : forall t1 x, in_beta t1 -> in_beta (abs x t1).

Definition βNF t := not (in_beta t).

Fixpoint beta_nfb t :=
  match t with
  | var _ => true
  | abs _ t1 => beta_nfb t1
  | app t1 t2 =>
    match t1 with
    | abs _ _ => false
    | _ => andb (beta_nfb t1) (beta_nfb t2)
    end
  end.

Lemma beta_nfb_βNF : forall t1,
    βNF t1 <-> beta_nfb t1 = true.
Proof.
  unfold βNF, not ; split.
  -
    induction t1; intros; simpl; auto.
    +
      destruct t1_1; simpl in IHt1_1; simpl in IHt1_2; auto. apply IHt1_2. intros.
      apply H. apply App_in2. apply H0.
      apply andb_true_intro. split.
      apply IHt1_1. intros. apply H. constructor; auto.
      apply IHt1_2. intros. apply H. solve [constructor; auto].
      induction H. constructor; constructor.
    +
      apply IHt1. intros. apply H. constructor; auto.
  -
    induction t1; intros.
    +
      inversion H0.
    +
      simpl in H.
      inversion H0; subst.
      discriminate H.
      destruct t1_1; try discriminate. inversion H2.
      apply andb_prop in H. destruct H. apply IHt1_1; auto.
      apply IHt1_2; auto. destruct t1_1; try discriminate; apply andb_prop in H; destruct H; auto.
    +
      inversion H0; subst; auto.
Qed.

Lemma beta_nfb_inβ : forall t1,
    in_beta t1 <-> beta_nfb t1 = false.
Proof.
  split.
  -
    induction t1; simpl; intros; auto; inversion H; subst; auto.
    +
      apply IHt1_1 in H1. rewrite H1. simpl.
      destruct t1_1; reflexivity.
    +
      apply IHt1_2 in H1. rewrite H1; simpl. rewrite Bool.andb_false_r. destruct t1_1; reflexivity.
  -
    induction t1; simpl; intros; try discriminate.
    +
      destruct t1_1.
      simpl in H. apply IHt1_2 in H. solve [constructor; auto].
      apply Bool.andb_false_iff in H. destruct H.
      apply IHt1_1 in H. constructor; auto. apply IHt1_2 in H; solve [constructor; auto].
      constructor; constructor.
    +
      constructor; auto.
Qed.
