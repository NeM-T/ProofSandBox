Inductive N : Set :=
    Z
  | S (n : N).

Inductive equal {A : Type} : A -> A -> Prop :=
  equal_refl : forall x, equal x x.

Check N_ind.
  
Theorem Axiom_S_not_zero : forall n, not (equal (S n) Z).
Proof.
  intro. intro. inversion H.
Qed.


Theorem Axiom_S_eq_nm : forall n m,
    equal (S n) (S m) ->
    equal n  m.
Proof.
  intros.
  inversion H. apply equal_refl.
Qed.

Fixpoint add n m :=
  match n with
  | Z => m
  | S x => S (add x m)
  end.

Print add.

Fixpoint mul n m :=
  match n with
  | Z => Z
  | S x => add m (mul x m)
  end.

Lemma equal_eq : forall (A : Type) (x y : A),
    equal x y <-> x = y.
Proof.
  split.
  -
    intros.
    inversion H. reflexivity.
  -
    intros. rewrite H.
    apply equal_refl.
Qed.    
  
Theorem Arith_add_com : forall l n m,
    add l (add n m) = add (add l n) m.
Proof.
  induction l.
  -
    intros. simpl. reflexivity.
  -
    intros. simpl. rewrite IHl. reflexivity.
Qed.

Print N_ind.
Print Arith_add_com.

