Set Implicit Arguments.
Set Asymmetric Patterns.
CoInductive InNat : Set := | Z | S : InNat -> InNat.
CoFixpoint infinite := S infinite.

Definition Pred x :=
  match x with
  | Z => Z
  | S x => x end.

Goal Pred infinite = infinite.
  unfold infinite. simpl. reflexivity.
Qed. 

CoInductive eqNat : InNat -> InNat -> Prop :=
| ZeroEq : eqNat Z Z
| SucEq : forall n1 n2, eqNat n1 n2 -> eqNat (S n1) (S n2).
(* | NatEq : forall n, eqNat n n. *)


CoFixpoint add n1 n2 :=
  match n2 with
  | Z => n1
  | S n => S (add n1 n)
  end.

Definition idnat n :=
  match n with
  | Z => Z
  | S n' => S n'
  end.
  
Theorem idcore : forall n,
    n = idnat n.
Proof.
  destruct n; reflexivity.
Qed.


Theorem S_infinite :
  S infinite = infinite.
  rewrite idcore.
  unfold infinite. simpl. reflexivity.
Qed.

Section Nateq_ind.

Variable R : InNat -> InNat -> Prop.
Hypothesis R_Zero_S : forall n, R Z (S n) -> False.
Hypothesis R_S_Zero : forall n, R (S n) Z -> False.
Hypothesis S_n_case : forall n1 n2, R (S n1) (n2) -> R n1 n2.
Hypothesis n_S_case : forall n1 n2, R n1 (S n2) -> R n1 n2.

Theorem Nateq_ind : forall n1 n2,
    R n1 n2 -> eqNat n1 n2.
Proof.
  cofix Nateq_ind.
  destruct n1; destruct n2; intros.
  apply ZeroEq.
  generalize (R_Zero_S H); intro H0; inversion H0.
  generalize (R_S_Zero H); intro H0; inversion H0.
  apply SucEq. apply Nateq_ind. apply S_n_case. apply n_S_case. apply H.
Qed.

End Nateq_ind.

Lemma eqNatrefl : forall n,
    eqNat n n.
Proof.
  cofix refl.
  intros; destruct n; constructor.
  apply refl.
Qed.

Lemma add_S_n : forall n1 n2,
    eqNat (add (S n1) n2) (S (add n1 n2)).
Proof.
  cofix add_S_n.
  intros. rewrite idcore.
  destruct n2; simpl.
  rewrite (idcore (add n1 Z)); simpl. rewrite (idcore (add (S n1) Z)). simpl. destruct n1.
  repeat constructor.
  repeat constructor. apply eqNatrefl.
  rewrite (idcore (add n1 (S n2))). simpl. rewrite (idcore (add (S n1) (S n2))). simpl.
  constructor. apply add_S_n.
Qed.

Theorem add_infinite : forall n,
  eqNat (add infinite n) infinite.
Proof.
  cofix add_infinite.
  intros.
  rewrite (idcore (add infinite n)).
  destruct n; simpl. rewrite S_infinite. apply eqNatrefl.
  rewrite <- S_infinite. constructor.
  rewrite S_infinite.
  apply add_infinite.
Qed.

Theorem n_eq_Sn_is_infinite : forall x, eqNat x (S x) -> eqNat x infinite.
Proof.
  cofix L. intros. destruct x.
  -
    inversion H.
  -
    rewrite idcore. simpl.
    apply SucEq.
    inversion H; subst.
    apply L. apply H2.
Qed.
