Definition L_eq {A: Type} (x y: A) :=
   forall (P: A -> Set), P x -> P y.

Variable A : Type.

Lemma L_refl : forall (A: Type) (x: A),
    L_eq x x.
Proof.
  intros. unfold L_eq. intros. apply H.
Qed.

Lemma L_sym : forall (A: Type) (x y: Type),
    L_eq x y -> L_eq y x.
Proof.
  unfold L_eq; intros.
  specialize (X (fun z => P z -> P x)).
  simpl in X.
  apply X; intros.
  apply H0.
  apply H.
Qed.

Lemma L_eq_eq : forall (x y: A),
    L_eq x y -> x = y.
Proof.
  unfold L_eq; intros.
  specialize (X (fun z => x = z)).
  simpl in X. apply X. reflexivity.
Qed.
