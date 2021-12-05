(*
雪江代数学１を形式化する
命題の名前はこれに沿っている
命題~~はp~~にしている
*)

Section Group.

  Variable A : Set.

  Variable f : A -> A -> A.

  Definition id_el e :=
    forall (a : A), f e a = f a e /\ f a e = a.

  Definition in_el a b :=
    forall e , f a b = f b a /\ (id_el e -> f b a = e).

  Definition asoc :=
    forall a b c, f a (f b c) = f (f a b) c.

  Definition group :=
    (exists e, id_el e) /\ (forall a, exists b, in_el a b) /\ asoc.

  Lemma p2_1_8_1 : forall a b c,
      group -> f a b = f a c -> b = c.
  Proof.
    unfold group.
    intros.
    destruct H. destruct H. destruct H1.
    generalize H. intro.
    unfold id_el in H, H1.
    unfold asoc in H2.
    specialize (H1 a). destruct H1. specialize (H1 x).
    destruct H1. 
    generalize H. intro.
    apply H4 in H3.
    specialize (H b).
    destruct H.
    rewrite <- H6. rewrite <- H. rewrite <- H3.
    rewrite <- H2.
    specialize (H5 c); destruct H5.
    rewrite <- H7, <- H5, <- H3, H0, H2. reflexivity.
  Qed.

  Lemma p2_1_8_2 : forall a b c a1 b1,
      group ->
      f a b = c ->
      in_el a a1 -> in_el b b1 ->
      b = f a1 c /\ a = f c b1.
  Proof.
    unfold group.
    intros.
    destruct H. destruct H. destruct H3.
    generalize H; intro.
    unfold id_el in H.
    unfold in_el in H1, H2, H3.
    unfold asoc in H4. destruct (H1 x), (H2 x).
    split.
    -
      destruct (H c).
      destruct (H b).
      rewrite <- H0.
      rewrite H4. rewrite H7; auto.
      symmetry. rewrite H12. apply H13.
    -
      rewrite <- H0. rewrite <- H4.
      rewrite H8. rewrite H9; auto.
      destruct (H a).
      auto.
  Qed.

  Lemma p2_1_10_1 : forall e1 e2,
      id_el e1 -> id_el e2 ->
      e1 = e2.
  Proof.
    unfold id_el; intros.
    destruct (H e2), (H0 e1).
    rewrite <- H4, H1, H2. reflexivity.
  Qed.

  Lemma p2_1_10_2 : forall e a x y,
      id_el e -> asoc ->
      in_el a x -> in_el a y ->
      x = y.
  Proof.
    unfold in_el, asoc.
    intros.
    destruct (H1 e), (H2 e).
    destruct (H x), (H y).
    rewrite <- H8.
    rewrite <- H6; auto.
    rewrite <- H5.
    rewrite H0.
    rewrite H4; auto.
    rewrite H9, H10.
    reflexivity.
  Qed.
  
  Lemma p2_1_10_3 : forall a b ab1 b1 a1,
      group ->
      in_el a a1 -> in_el b b1 -> in_el (f a b) ab1 ->
      ab1 = f b1 a1.
  Proof.
    unfold group; intros.
    destruct H. destruct H, H3.
    destruct (H0 x), (H1 x), (H2 x).
    destruct (H a1), (H b1), (H ab1), (H a), (H b).
  Abort.

  Lemma p2_1_10_4 : forall a a1 aa,
      group ->
      in_el a a1 ->
      in_el a1 aa ->
      a = aa.
  Proof.
    unfold group; intros.
    destruct H. destruct H.
    destruct H2.
    destruct (H a).
    destruct (H aa).
    destruct (H0 x), (H1 x).
    rewrite <- H5.
    rewrite <- H11; auto.
    rewrite <- H10.
    rewrite H3.
    rewrite H8. rewrite H9; auto.
    rewrite H6.
    rewrite H7.
    reflexivity.
  Qed.
  

End Group.
