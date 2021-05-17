Require Import List.
Import ListNotations.
Import Nat.

Inductive prop : Set :=
| top
| bot
| atom (x: nat)
| land (p q: prop)
| lor (p q : prop)
| lnot (p: prop)
| to (p q: prop).

Section Natural_Deduction.
  Reserved Notation "Γ ⊢ P" (no associativity, at level 61).

  Inductive ND : (list prop) -> prop -> Prop :=
  | ND_exfalso_quodlibet : forall Γ P,
      Γ ⊢ bot ->
      Γ ⊢ P
  | ND_True_intro : forall Γ,
      Γ ⊢ top
  | ND_or_introl : forall Γ P Q,
      Γ ⊢ P ->
      Γ ⊢ lor P Q
  | ND_or_intror : forall Γ P Q,
      Γ ⊢ Q ->
      Γ ⊢ lor P Q
  | ND_or_elim : forall Γ P Q R,
      Γ ⊢ lor P Q ->
      P :: Γ ⊢ R ->
      Q :: Γ ⊢ R ->
      Γ ⊢ R
  | ND_and_intro : forall Γ P Q,
      Γ ⊢ P ->
      Γ ⊢ Q ->
      Γ ⊢ land P  Q
  | ND_and_elim : forall Γ P Q R,
      Γ ⊢ land P Q ->
      P :: Q :: Γ ⊢ R ->
      Γ ⊢ R
  | ND_to_intro : forall Γ P Q,
      P :: Γ ⊢ Q ->
      Γ ⊢ to P Q
  | ND_to_elim : forall Γ P Q,
      Γ ⊢ to P Q ->
      Γ ⊢ P ->
      Γ ⊢ Q
  | ND_assumption : forall Γ P,
      In P Γ ->
      Γ ⊢ P
  | ND_not_intro : forall Γ P,
      P :: Γ ⊢ bot ->
      Γ ⊢ lnot P
  | ND_not_elim : forall Γ P,
      Γ ⊢ lnot P ->
      Γ ⊢ P ->
      Γ ⊢ bot
  where "Γ ⊢ P" := (ND Γ P).

  Example vdash1 : forall P, [] ⊢ (to P P).
  Proof.
    intros. apply ND_to_intro.
    apply ND_assumption. apply in_eq.
  Qed.

  Example vdash2 : forall P Q,
      [] ⊢ (to P (to Q P)).
  Proof.
    intros. apply ND_to_intro. apply ND_to_intro. apply ND_assumption.
    apply in_cons. apply in_eq.
  Qed.
  
End Natural_Deduction.

Section Semantics.

  Fixpoint InListB (x: nat) l :=
    match l with
    | [] => false
    | h :: t => if Nat.eqb x h then true else InListB x t
    end.

  Fixpoint valfix p l :=
    match p with
    | top => true
    | bot => false
    | atom n => InListB n l
    | land p1 p2 => andb (valfix p1 l) (valfix p2 l)
    | lor p1 p2 => orb (valfix p1 l) (valfix p2 l)
    | lnot p1 => if valfix p1 l then false else true
    | to p1 p2 => if valfix p1 l then valfix p2 l else true
    end.

  Fixpoint andl Γ :=
    match Γ with
    | nil => top
    | h::t => land h (andl t)
    end.

  Definition vDash Γ p :=
    (forall v, valfix (to (andl Γ) p) v = true).
             
End Semantics.

Section soundness.

  Notation "Γ ⊨ p" := (vDash Γ p) (at level 60).

  Notation "Γ ⊢ p" := (ND Γ p) (at level 60).

  
  Lemma InT : forall Γ P v,
      In P Γ ->
      valfix (andl Γ) v = true ->
      valfix P v = true.
  Proof.
    induction Γ; intros; auto.
    simpl in H, H0.
    apply andb_prop in H0.
    destruct H0.
    destruct H; subst.
    -
      apply H0.
    -
      apply IHΓ; auto.
  Qed.
  
  Theorem Sound : forall Γ p,
      Γ ⊢ p -> Γ ⊨ p.
  Proof.
    unfold vDash; intros; induction H; simpl.
    -
      simpl in IHND.
      destruct valfix; try discriminate; reflexivity.
    -
      destruct valfix; reflexivity.
    -
      simpl in IHND.
      destruct (valfix (andl Γ)) eqn:IH; try reflexivity.
      rewrite IHND. reflexivity.
    -
      simpl in IHND.
      destruct (valfix (andl Γ)) eqn:IH; try reflexivity.
      rewrite IHND. destruct (valfix P v); reflexivity.
    -
      simpl in IHND1, IHND2, IHND3.
      destruct (valfix (andl Γ)) eqn:IH; try reflexivity.
      destruct (valfix P v); simpl in IHND2. apply IHND2.
      destruct (valfix Q v); simpl in IHND3. apply IHND3.
      discriminate IHND1.
    -
      simpl in IHND1, IHND2.
      destruct (valfix (andl Γ)); try reflexivity.
      rewrite IHND1, IHND2.
      reflexivity.
    -
      simpl in IHND1, IHND2.
      destruct (valfix (andl Γ)); try reflexivity.
      apply andb_prop in IHND1. destruct IHND1.
      rewrite H1, H2 in IHND2.
      simpl in IHND2. rewrite IHND2.
      reflexivity.
    -
      simpl in IHND.
      destruct (valfix (andl Γ)); try reflexivity.
      destruct valfix; try reflexivity.
      simpl in IHND. apply IHND.
    -
      simpl in IHND1, IHND2.
      destruct (valfix (andl Γ)v); try reflexivity.
      rewrite IHND2 in IHND1. apply IHND1.
    -
      destruct (valfix (andl Γ)v) eqn:IH; try reflexivity.
      eapply InT; eauto.
    -
      simpl in IHND.
      destruct (valfix (andl Γ)v); try reflexivity.
      destruct valfix; try reflexivity; try discriminate.
    -
      simpl in IHND1, IHND2.
      destruct (valfix (andl Γ)v); try reflexivity.
      rewrite IHND2 in IHND1. discriminate.
  Qed.

End soundness.
