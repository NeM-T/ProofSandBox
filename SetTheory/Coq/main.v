Variable U : Type.
Definition set := U -> Prop.

Definition In (s: set) (x: U) := s x.
Notation "x ∈ A" := (In A x) (at level 50).
Axiom set_axio :
  forall (S: set), (forall x, In S x \/ ~ (In S x)).

Definition Empty_set : set :=  fun _ => False.
Notation "∅" := Empty_set.

Definition Full_set : set :=  fun _ => True.

Definition eq_set (A B: set) :=
  forall x, x ∈ A <-> x ∈ B.


Definition subset (A B: set) :=
  forall x, x ∈ A -> x ∈ B.
Notation "A ⊂ B":= (subset A B) (at level 50).

Definition subseteq (A B: set) :=
  A ⊂ B /\ not (eq_set A B).
Notation "A ⊆ B" := (subseteq A B) (at level 50).

Lemma L1_4 : forall A B C,
    A ⊂ B -> B ⊂ C -> A ⊂ C.
Proof.
  unfold subset, In.
  intros. specialize (H x). specialize (H0 x). apply H in H1. apply H0 in H1. apply H1.
Qed.

Lemma L1_5 : forall A,
    ∅ ⊂ A.
Proof.
  unfold subset. intros. inversion H.
Qed.
