Definition set (U: Type):= U -> Prop.

Definition In {U: Type} (s: set U) (x: U) := s x.
Notation "x ∈ A" := (In A x) (at level 50).
Axiom set_axio :
  forall (U: Type) (S: set U), (forall x, In S x \/ ~ (In S x)).

Definition Empty_set {U: Type} : set U :=  fun _ => False.
Notation "∅" := Empty_set.

Definition eq_set {U: Type} (A B: set U) :=
  forall x, x ∈ A <-> x ∈ B.
Notation "A ⩵ B" := (eq_set A B) (at level 80).


Definition subset {U: Type} (A B: set U) :=
  forall x, x ∈ A -> x ∈ B.
Notation "A ⊂ B":= (subset A B) (at level 50).

Definition subseteq {U: Type} (A B: set U) :=
  A ⊂ B /\ not (A ⩵ B).
Notation "A ⊆ B" := (subseteq A B) (at level 70).

Lemma L1_1_4 : forall U (A B C: set U),
    A ⊂ B -> B ⊂ C -> A ⊂ C.
Proof.
  unfold subset, In.
  intros. specialize (H x). specialize (H0 x). apply H in H1. apply H0 in H1. apply H1.
Qed.

Lemma L1_1_5 : forall U (A: set U),
    ∅ ⊂ A.
Proof.
  unfold subset. intros. inversion H.
Qed.

(*1S2*)
Definition cup {U: Type} (A B: set U) : set U :=
  fun x => x ∈ A \/ x ∈ B.
Notation "A ∪ B" := (cup A B) (at level 60).

Example L1_2_2 : forall (U: Type) (A B: set U),
    A ⊂ (A ∪ B).
Proof.
  unfold subset, cup, In. intros. left; auto.
Qed.

Example L1_2_3 : forall U (A B C: set U),
    A ⊂ C -> B ⊂ C -> (A ∪ B) ⊂ C.
Proof.
  unfold subset, cup, In; intros. destruct H1; auto.
Qed.

Example L1_2_4 : forall U (A: set U),
    A ∪ A ⩵ A.
Proof.
  unfold eq_set, cup, In; split; intros; auto. destruct H; auto.
Qed.

Example L1_2_5 : forall U (A B: set U),
    (A ∪ B) ⩵ (B ∪ A).
Proof.
  unfold eq_set, cup, In; split; intros; destruct H; auto.
Qed.

Example L1_2_6 : forall U (A B C: set U),
    ((A ∪ B) ∪ C) ⩵ (A ∪ (B ∪ C)).
Proof.
  unfold eq_set, cup, In; split; intros; destruct H; try destruct H; auto.
Qed.

Example L1_2_7 : forall U (A B: set U),
    A ⊂ B <-> (A ∪ B) ⩵ B.
Proof.
  unfold eq_set, cup, subset, In; split; intros. split; intros; auto. destruct H0; auto. apply H. left; apply H0.
Qed.

Example L1_2_8 : forall U (A B C: set U),
    A ⊂ B ->  (A ∪ C) ⊂ (B ∪ C).
Proof.
  unfold cup, subset, In; intros. unfold subset, In in H. destruct H0; auto.
Qed.

Example L1_2_9 : forall U (A: set U),
    (∅ ∪ A) ⩵ A.
Proof.
  unfold eq_set, Empty_set, cup, In; split; intros; auto.
  destruct H; try solve [inversion H]; auto.
Qed.

Definition cap {U: Type} A B : set U :=
  fun x => x ∈ A /\ x ∈ B.
Notation "A ∩ B" := (cap A B) (at level 60).

Example L1_2_2' : forall U (A B: set U),
    (A ∩ B) ⊂ A.
Proof.
  unfold subset, cap, In; intros. destruct H. apply H.
Qed.

Example L1_2_3' : forall (U: Type) (A B C: set U),
    C ⊂ A -> C ⊂ B -> C ⊂ (A ∩ B).
Proof.
  unfold subset, cap, In; intros. split; auto.
Qed.

Example L1_2_4' : forall U (A: set U),
    A ∩ A ⩵ A.
Proof.
  unfold eq_set, cap, In; split; intros; auto. destruct H; auto.
Qed.

Example L1_2_5' : forall U (A B: set U),
    A ∩ B ⩵ B ∩ A.
Proof.
  unfold eq_set, cap, In. split; intros; destruct H; split; auto.
Qed.

Example L1_2_6' : forall U (A B C: set U),
    (A ∩ B) ∩ C ⩵ A ∩ (B ∩ C).
Proof.
  unfold eq_set, cap, In; split; intros; destruct H; try destruct H; try destruct H0; split; try split; auto.
Qed.

Example L1_2_7' : forall U (A B: set U),
    A ⊂ B <-> A ∩ B ⩵ A.
Proof.
  unfold eq_set, cap, subset, In; split; try split; intros; auto.
  destruct H0; auto. apply H in H0. destruct H0; auto.
Qed.

Example L1_2_8' : forall U (A B C: set U),
    A ⊂ B -> (A ∩ C) ⊂ (B ∩ C).
Proof.
  unfold subset, cap, In; intros. destruct H0. split; auto.
Qed.

Example L1_2_9' : forall U (A: set U),
    ∅ ∩ A ⩵ ∅.
Proof.
  unfold eq_set, cap, In. split; intros. destruct H. auto. inversion H.
Qed.

Example L1_2_10 : forall U (A B C: set U),
    (A ∪ B) ∩ C ⩵ (A ∩ C) ∪ (B ∩ C).
Proof.
  unfold eq_set, cup, cap, In; split; intros.
  destruct H. destruct H; auto.
  destruct H; destruct H; split; auto.
Qed.

Example L1_2_10' : forall U (A B C: set U),
    (A ∩ B) ∪ C ⩵ (A ∪ C) ∩ (B ∪ C).
Proof.
  unfold eq_set, cup, cap, In; split; intros; repeat destruct H; auto.
  destruct H0; auto.
Qed.

Example L1_2_11 : forall U (A B: set U),
    (A ∪ B) ∩ A ⩵ A.
Proof.
  unfold eq_set, cup, cap, In; split; intros; repeat destruct H; auto.
Qed.

Example L1_2_11' : forall U (A B: set U),
    (A ∩ B) ∪ A ⩵ A.
Proof.
  unfold eq_set, cup, cap, In; split; intros; repeat destruct H; auto.
Qed.

Definition sub {U} (A B: set U) : set U :=
  fun x => x ∈ A /\ not (x ∈ B).
Notation "A '--' B" := (sub A B) (at level 40).

Definition universal_set {U} : set U :=  fun _ => True.
Notation "A ^c" := (universal_set -- A) (at level 50).

Example L1_2_12 : forall U (A: set U),
    A ∪ (A ^c) ⩵ universal_set.
Proof.
  unfold eq_set, cup, sub, In; split; intros; unfold universal_set; auto.
  generalize set_axio. unfold In. intros. specialize (H0 U A x). destruct H0; auto.
Qed.

Example L1_2_13 : forall U (A: set U),
    (A ^c)^c ⩵ A.
Proof.
  unfold sub, eq_set, In; split; intros.
  destruct H. generalize set_axio. unfold In. intros. specialize (H1 U A x). destruct H1; auto.
  destruct H0. unfold universal_set. split; auto.
  unfold universal_set, not. split; intros; auto. destruct H0; auto.
Qed.

Definition universal_set_type U : set U := fun _ => True.

Example L1_2_14 : forall U,
  ∅ ^c ⩵ universal_set_type U.
Proof.
  unfold eq_set, sub, universal_set_type, In; split; intros; auto.
Qed.

Example L1_2_15 : forall U (A B: set U),
    A ⊂ B <-> (B^c) ⊂ (A^c).
Proof.
  unfold sub, subset, In, universal_set. split; intros; try (destruct H0; split); auto.
  generalize set_axio; unfold In; intros. specialize (H1 U B x). destruct H1; auto.
  apply conj with (A:= True) in H1; auto. apply H in H1. destruct H1. induction H2. apply H0.
Qed.

Ltac ufold := unfold eq_set, sub, Empty_set, universal_set, subset, cup, cap, In.
Ltac set_axio_gen HH U S x := generalize set_axio; unfold In; intros HH; specialize (HH U S x).

Example L1_2_16 : forall U (A B: set U),
    (A ∪ B)^c ⩵ (A^c) ∩ (B^c).
Proof.
  ufold; split; intros; auto.
  destruct H. set_axio_gen H1 U A x.
  split; split; auto.
  destruct H. destruct H, H0. split; auto. intro. destruct H3; auto.
Qed.

Example L1_2_16' : forall U (A B: set U),
    (A ∩ B)^c ⩵ (A^c) ∪ (B^c).
Proof.
  ufold; split; intros.
  destruct H.
  set_axio_gen H1 U A x. set_axio_gen H2 U B x.
  destruct H1; destruct H2; auto. destruct H0; auto.

  split; auto. intro. destruct H0. destruct H; destruct H; auto.
Qed.

Definition Family (K U: Type) := K -> set U.

Definition bigcup  {K U: Type} (F: Family K U) : set U :=
  fun x => (exists n, x ∈ (F n)).
Notation "⋃ F" := (bigcup F) (at level 65).

Definition bigcap {K U: Type} (F: Family K U) : set U :=
  fun x => (forall n, x ∈ (F n)).
Notation "⋂ F" := (bigcap F) (at level 65).

Example L1_2_17: forall K U (F: Family K U) n,
    (F n) ⊂  ⋃ F.
Proof.
  unfold bigcup; ufold; intros; eauto.
Qed.

Lemma L1_2_18 : forall K U (F: Family K U) C,
    (forall n, (F n) ⊂ C) -> (⋃ F) ⊂ C.
Proof.
  unfold bigcup; ufold; intros.
  inversion H0. apply H in H1. apply H1.
Qed.

Lemma L1_2_17' : forall K U (F: Family K U) n,
    (⋂ F) ⊂ F n.
Proof.
  unfold bigcap; ufold; intros; auto.
Qed.

Lemma L1_2_18' : forall K U (F: Family K U) C,
    (forall n, C ⊂ (F n)) -> C ⊂ (⋂ F).
Proof.
  unfold bigcap; ufold; intros. apply H. apply H0.
Qed.

Example E1_2_2_1 : forall U (A B: set U),
    A ∩ B ⩵ ∅ <-> B ⊂ (A^c).
Proof.
  ufold; split; intros; split; auto. intro. assert (A x /\ B x); auto. apply H in H2.
  apply H2.

  intros. destruct H0. apply H in H1. destruct H1. apply H2; auto.
  intros. inversion H0.
Qed.

Example E1_2_2_2 : forall U (A B: set U),
    B ⊂ (A^c) <-> A ⊂ (B^c).
Proof.
  ufold; split; intros. split; auto. set_axio_gen H1 U B x. destruct H1.
  apply H in H1. destruct H1. destruct H2; auto. apply H1.
  split; auto. set_axio_gen H1 U A x. destruct H1. apply H in H1. destruct H1; destruct H2; auto. apply H1.
Qed.

Example E1_2_3a_1 : forall U (A B: set U),
    A -- B ⩵ (A ∪ B) -- B.
Proof.
  ufold; split; intros. destruct H. split; auto.
  destruct H. destruct H; auto. destruct H0; auto.
Qed.

Example E1_2_3a_2 : forall U (A B: set U),
    (A ∪ B) -- B ⩵ A -- (A ∩ B).
Proof.
  ufold; split; intros. destruct H. destruct H. split; auto. intro. destruct H1; apply H0; auto.
  destruct H0; apply H.
  destruct H. split; auto.
Qed.

Example E1_2_3a_3 : forall U (A B: set U),
    A -- (A ∩ B) ⩵ A ∩ (B^c).
Proof.
  ufold; split; intros; destruct H; split; auto.
  destruct H0. intro. destruct H2. apply H1 in H3. apply H3.
Qed.

Example E1_2_4a : forall U (A B C: set U),
    A -- (B ∪ C) ⩵ (A -- B) ∩ (A -- C).
Proof.
  ufold; split; intros; destruct H; split; auto. destruct H. apply H.
  intro. destruct H, H0. destruct H1; auto.
Qed.

Example E1_2_4b : forall U (A B C: set U),
    A -- (B ∩ C) ⩵ (A -- B) ∪ (A -- C).
Proof.
  ufold; split; intros.
  destruct H. set_axio_gen H1 U B x. set_axio_gen H2 U C x.
  destruct H1. destruct H2. left. split; auto.
  right; auto. left; auto.
  destruct H; destruct H. split; auto. intro. destruct H1; auto.
  split; try (intro H1; destruct H1); auto.
Qed.

Example E1_2_4c : forall U (A B C: set U),
    (A ∪ B) -- C ⩵ (A -- C) ∪ (B -- C).
Proof.
  ufold; split; intros; destruct H; auto.
  destruct H; auto. destruct H; auto. destruct H. split; auto.
Qed.

Example E1_2_4d : forall U (A B C: set U),
    (A ∩ B) -- C ⩵ (A -- C) ∩ (B -- C).
Proof.
  ufold; split; intros; destruct H; destruct H; split; auto.
  destruct H0; split; auto.
Qed.

Example E1_2_4e : forall U (A B C: set U),
    A ∩ (B -- C) ⩵ (A ∩ B) -- (A ∩ C).
Proof.
  ufold; split; intros; destruct H.
  destruct H0. split. split; auto. intro. destruct H2; auto.
  destruct H. set_axio_gen H2 U C x. destruct H2; split; try split; auto.
Qed.

Example E1_2_5a : forall U (A B C: set U),
    (A -- B) -- C ⩵ A -- (B ∪ C).
Proof.
  ufold; split; intros; destruct H; split; auto.
  destruct H; apply H. intro. destruct H. destruct H1; auto.
Qed.

Example E1_2_5b : forall U (A B C: set U),
    A -- (B -- C) ⩵ (A -- B) ∪ (A ∩ C).
Proof.
  ufold; split; intros.
  destruct H. set_axio_gen H1 U B x. set_axio_gen H2 U C x.
  destruct H1. destruct H2; auto. left. split; auto. left; auto.
  destruct H; destruct H. split; auto. intro. destruct H1; auto.
  split; auto. intro. destruct H1; auto.
Qed.

Example E1_2_6 : forall U (A C: set U),
    A ⊂ C ->
    forall B, A ∪ (B ∩ C) ⩵ (A ∪ B) ∩ C.
Proof.
  ufold; split; intros. destruct H0. split; auto. destruct H0. split; auto.
  destruct H0. destruct H0; auto.
Qed.

(*symmetric difference*)
Definition sym_diff {U: Type} (A B: set U) := (A -- B) ∪ (B -- A).
Notation "A △ B" := (sym_diff A B) (at level 60).

Example E1_2_7a : forall U (A B: set U),
    (A △ B) ⩵ (B △ A).
Proof.
  unfold sym_diff; ufold; split; intros; destruct H; destruct H; auto.
Qed.

Example E1_2_7b : forall U (A B: set U),
    (A △ B) ⩵ ((A ∪ B) -- (A ∩ B)).
Proof.
  unfold sym_diff; ufold; split; intros; destruct H; destruct H; auto.
  split; auto. intro. destruct H1; auto. split; auto. intro. destruct H1; auto.
  set_axio_gen H1 U B x. destruct H1; left; split; auto.
  set_axio_gen H1 U A x; destruct H1; right; split; auto.
Qed.

Example E1_2_7c : forall U (A B C: set U),
    (A △ B) △ C ⩵ A △ (B △ C).
Proof.
  unfold sym_diff; ufold; split; intros; destruct H; destruct H; auto.
  destruct H; destruct H. left; split; try intro; auto. destruct H2; destruct H2; auto. right. split; auto.
  set_axio_gen H1 U A x. destruct H1. left; split; auto; intro. destruct H2; destruct H2; auto.
  right; split; auto. set_axio_gen H2 U C x; destruct H2; auto. right. split; auto.
  set_axio_gen H1 U C x; destruct H1; auto. right; split; auto. intro. destruct H2; destruct H2; apply H0; auto.
  left; split; auto. left; split; auto.
  destruct H; destruct H. left. split; auto. right; split; auto. intro. destruct H2; destruct H2; auto.
Qed.

Example E1_2_7d :forall U (A B C: set U),
    A ∩ (B △ C) ⩵ (A ∩ B) △ (A ∩ C).
Proof.
  unfold sym_diff; ufold; split; intros; destruct H.
  destruct H0; destruct H0. left. split; auto. intro. destruct H2; auto.
  right. split; auto. intro. destruct H2; auto.
  destruct H; destruct H. split; auto. left. split; auto.
  destruct H; destruct H. split; auto. right. split; auto.
Qed.

Example E1_2_8a : forall U (A: set U),
    A △ ∅ ⩵ A.
Proof.
  unfold sym_diff; ufold ; split; intros.
  destruct H; destruct H; auto. inversion H.
  left; split; auto.
Qed.

Example E1_2_8b : forall U (A: set U),
    A △ universal_set ⩵ A^c.
Proof.
  unfold sym_diff; ufold; split; intros.
  destruct H; destruct H; split; auto.
  destruct H; auto.
Qed.

Example E1_2_8c : forall U (A: set U),
    A △ A ⩵ ∅.
Proof.
  unfold sym_diff; ufold; split; intros; auto.
  destruct H; destruct H; auto. inversion H.
Qed.

Example E1_2_8d : forall U (A: set U),
    (A △ A^c) ⩵ universal_set.
Proof.
  unfold sym_diff; ufold; split; intros; auto.
  set_axio_gen H1 U A x; destruct H1; auto. left. split; auto.
  intro. destruct H1; auto.
Qed.

Example E1_2_9 : forall U (A1 A2 B1 B2: set U),
    A1 △ A2 ⩵ B1 △ B2 ->
    A1 △ B1 ⩵ A2 △ B2.
Proof.
  unfold sym_diff; ufold; split; intros.
  destruct H0; destruct H0. set_axio_gen H2 U A2 x. set_axio_gen H3 U B2 x.
  destruct H2. destruct H3; auto. assert (B2 x /\ ~ B1 x); auto. eapply or_intror in H4. apply H in H4.
  destruct H4; destruct H4; auto.
  destruct H3; auto. assert (A1 x /\ not (A2 x)); auto. eapply or_introl in H4. apply H in H4.
  destruct H4; destruct H4; auto. destruct H1; auto.
  set_axio_gen H2 U A2 x. set_axio_gen H3 U B2 x.
  destruct H2; destruct H3; auto. assert (A2 x /\ not (A1 x)); auto. eapply or_intror in H4. apply H in H4.
  destruct H4; destruct H4; auto.
  assert (B1 x /\ not (B2 x)); auto. eapply or_introl in H4. apply H in H4. destruct H4; destruct H4; auto.
  destruct H1; auto.
  destruct H0; destruct H0.
  set_axio_gen H2 U A1 x. set_axio_gen H3 U B1 x.
  destruct H2; destruct H3; auto. assert (B1 x /\ not (B2 x)); auto. eapply or_introl in H4. apply H in H4.
  destruct H4; destruct H4; auto.
  assert (A2 x /\ not (A1 x)); auto. eapply or_intror in H4. apply H in H4. destruct H4; destruct H4; auto.
  destruct H1; auto.
  set_axio_gen H2 U A1 x. set_axio_gen H3 U B1 x.
  destruct H2; destruct H3; auto. assert (A1 x /\ not (A2 x)); auto. eapply or_introl in H4. apply H in H4.
  destruct H4; destruct H4; auto.
  assert (B2 x /\ not (B1 x)); auto. eapply or_intror in H4. apply H in H4. destruct H4; destruct H4; auto.
  destruct H1; auto.
Qed.

(*1-3*)
Definition Map {U V: Type} (A: set U) (B: set V) (f: U -> V) :=
  forall (x: U), x ∈ A -> (f x) ∈ B.
