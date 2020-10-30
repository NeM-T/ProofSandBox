
Inductive nat : Type :=
  O | S (n: nat).

Fixpoint add n m :=
  match m with
  | O => n
  | S m' => S (add n m')
  end.

Lemma add_0_l : forall n,
    add O n = n.
Proof.
  induction n. reflexivity.
  simpl.
  rewrite <- IHn. rewrite IHn. rewrite IHn. reflexivity.
Qed.

Lemma add_S_l : forall n m,
    add (S n) m = S (add n m).
Proof.
  induction m; intros. reflexivity.
  simpl. rewrite IHm. reflexivity.
Qed.

Theorem add_kan : forall n m,
    add n m = add m n.
Proof.
  induction n; intros. simpl. rewrite add_0_l. reflexivity.
  rewrite add_S_l. simpl. rewrite IHn. reflexivity.
Qed.
