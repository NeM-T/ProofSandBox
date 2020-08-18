Variable U : Type.
Definition set := U -> Prop.

Definition In (s: set) (x: U) := s x.
Notation "x ∈ A" := (In A x) (at level 50).
Axiom set_axio :
  forall (S: set), (forall x, In S x \/ ~ (In S x)).

Definition Empty_set : set :=  fun _ => False.
Notation "∅" := Empty_set.

Definition eq_set (A B: set) :=
  forall x, x ∈ A <-> x ∈ B.
Notation "A ⩵ B" := (eq_set A B) (at level 80).


Definition subset (A B: set) :=
  forall x, x ∈ A -> x ∈ B.
Notation "A ⊂ B":= (subset A B) (at level 50).

Definition subseteq (A B: set) :=
  A ⊂ B /\ not (A ⩵ B).
Notation "A ⊆ B" := (subseteq A B) (at level 70).

Lemma L1_1_4 : forall A B C,
    A ⊂ B -> B ⊂ C -> A ⊂ C.
Proof.
  unfold subset, In.
  intros. specialize (H x). specialize (H0 x). apply H in H1. apply H0 in H1. apply H1.
Qed.

Lemma L1_1_5 : forall A,
    ∅ ⊂ A.
Proof.
  unfold subset. intros. inversion H.
Qed.

(*1S2*)
Definition cup (A B: set) : set :=
  fun x => x ∈ A \/ x ∈ B.
Notation "A ∪ B" := (cup A B) (at level 60).

Example L1_2_2 : forall A B,
    A ⊂ (A ∪ B).
Proof.
  unfold subset, cup, In. intros. left; auto.
Qed.

Example L1_2_3 : forall A B C,
    A ⊂ C -> B ⊂ C -> (A ∪ B) ⊂ C.
Proof.
  unfold subset, cup, In; intros. destruct H1; auto.
Qed.

Example L1_2_4 : forall A,
    A ∪ A ⩵ A.
Proof.
  unfold eq_set, cup, In; split; intros; auto. destruct H; auto.
Qed.

Example L1_2_5 : forall A B,
    (A ∪ B) ⩵ (B ∪ A).
Proof.
  unfold eq_set, cup, In; split; intros; destruct H; auto.
Qed.

Example L1_2_6 : forall A B C,
    ((A ∪ B) ∪ C) ⩵ (A ∪ (B ∪ C)).
Proof.
  unfold eq_set, cup, In; split; intros; destruct H; try destruct H; auto.
Qed.

Example L1_2_7 : forall A B,
    A ⊂ B <-> (A ∪ B) ⩵ B.
Proof.
  unfold eq_set, cup, subset, In; split; intros. split; intros; auto. destruct H0; auto. apply H. left; apply H0.
Qed.

Example L1_2_8 : forall A B C,
    A ⊂ B ->  (A ∪ C) ⊂ (B ∪ C).
Proof.
  unfold cup, subset, In; intros. unfold subset, In in H. destruct H0; auto.
Qed.

Example L1_2_9 : forall A,
    (∅ ∪ A) ⩵ A.
Proof.
  unfold eq_set, Empty_set, cup, In; split; intros; auto.
  destruct H; try solve [inversion H]; auto.
Qed.

Definition cap A B : set :=
  fun x => x ∈ A /\ x ∈ B.
Notation "A ∩ B" := (cap A B) (at level 60).

Example L1_2_2' : forall A B,
    (A ∩ B) ⊂ A.
Proof.
  unfold subset, cap, In; intros. destruct H. apply H.
Qed.

Example L1_2_3' : forall A B C,
    C ⊂ A -> C ⊂ B -> C ⊂ (A ∩ B).
Proof.
  unfold subset, cap, In; intros. split; auto.
Qed.

Example L1_2_4' : forall A,
    A ∩ A ⩵ A.
Proof.
  unfold eq_set, cap, In; split; intros; auto. destruct H; auto.
Qed.

Example L1_2_5' : forall A B,
    A ∩ B ⩵ B ∩ A.
Proof.
  unfold eq_set, cap, In. split; intros; destruct H; split; auto.
Qed.

Example L1_2_6' : forall A B C,
    (A ∩ B) ∩ C ⩵ A ∩ (B ∩ C).
Proof.
  unfold eq_set, cap, In; split; intros; destruct H; try destruct H; try destruct H0; split; try split; auto.
Qed.

Example L1_2_7' : forall A B,
    A ⊂ B <-> A ∩ B ⩵ A.
Proof.
  unfold eq_set, cap, subset, In; split; try split; intros; auto.
  destruct H0; auto. apply H in H0. destruct H0; auto.
Qed.

Example L1_2_8' : forall A B C,
    A ⊂ B -> (A ∩ C) ⊂ (B ∩ C).
Proof.
  unfold subset, cap, In; intros. destruct H0. split; auto.
Qed.

Example L1_2_9' : forall A,
    ∅ ∩ A ⩵ ∅.
Proof.
  unfold eq_set, cap, In. split; intros. destruct H. auto. inversion H.
Qed.

Example L1_2_10 : forall A B C,
    (A ∪ B) ∩ C ⩵ (A ∩ C) ∪ (B ∩ C).
Proof.
  unfold eq_set, cup, cap, In; split; intros.
  destruct H. destruct H; auto.
  destruct H; destruct H; split; auto.
Qed.

Example L1_2_10' : forall A B C,
    (A ∩ B) ∪ C ⩵ (A ∪ C) ∩ (B ∪ C).
Proof.
  unfold eq_set, cup, cap, In; split; intros; repeat destruct H; auto.
  destruct H0; auto.
Qed.

Example L1_2_11 : forall A B,
    (A ∪ B) ∩ A ⩵ A.
Proof.
  unfold eq_set, cup, cap, In; split; intros; repeat destruct H; auto.
Qed.

Example L1_2_11' : forall A B,
    (A ∩ B) ∪ A ⩵ A.
Proof.
  unfold eq_set, cup, cap, In; split; intros; repeat destruct H; auto.
Qed.

Definition sub (A B: set) : set :=
  fun x => x ∈ A /\ not (x ∈ B).
Notation "A '--' B" := (sub A B) (at level 40).

Definition universal_set : set :=  fun _ => True.
Notation "A ^c" := (universal_set -- A) (at level 50).

Example L1_2_12 : forall A,
    A ∪ (A ^c) ⩵ universal_set.
Proof.
  unfold eq_set, cup, sub, In; split; intros; unfold universal_set; auto.
  generalize set_axio. unfold In. intros. specialize (H0 A). specialize (H0 x). destruct H0; auto.
Qed.

Example L1_2_13 : forall A,
    (A ^c)^c ⩵ A.
Proof.
  unfold sub, eq_set, In; split; intros.
  destruct H. generalize set_axio. unfold In. intros. specialize (H1 A). specialize (H1 x). destruct H1; auto.
  destruct H0. unfold universal_set. split; auto.
  unfold universal_set, not. split; intros; auto. destruct H0; auto.
Qed.

Example L1_2_14 :
  ∅ ^c ⩵ universal_set.
Proof.
  unfold eq_set, sub, universal_set, In; split; intros; auto.
Qed.

Example L1_2_15 : forall A B,
    A ⊂ B <-> (B^c) ⊂ (A^c).
Proof.
  unfold sub, subset, In, universal_set. split; intros; try (destruct H0; split); auto.
  generalize set_axio; unfold In; intros. specialize (H1 B). specialize (H1 x). destruct H1; auto.
  apply conj with (A:= True) in H1; auto. apply H in H1. destruct H1. induction H2. apply H0.
Qed.

Ltac ufold := unfold eq_set, sub, universal_set, cup, cap, In.
Ltac set_axio_gen := generalize set_axio; unfold In; intros.

Example L1_2_16 : forall A B,
    (A ∪ B)^c ⩵ (A^c) ∩ (B^c).
Proof.
  ufold; split; intros; auto.
  destruct H. set_axio_gen. specialize (H1 A). specialize (H1 x).
  split; split; auto.
  destruct H. destruct H, H0. split; auto. intro. destruct H3; auto.
Qed.

Example L1_2_16' : forall A B,
    (A ∩ B)^c ⩵ (A^c) ∪ (B^c).
Proof.
  ufold; split; intros.
  destruct H.
  set_axio_gen. specialize (H1 A). specialize (H1 x). set_axio_gen. specialize (H2 B). specialize (H2 x).
  destruct H1; destruct H2; auto. destruct H0; auto.

  split; auto. intro. destruct H0. destruct H; destruct H; auto.
Qed.

