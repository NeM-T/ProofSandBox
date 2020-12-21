Definition AtMostTwoElement(A:Type):Prop:=
  (forall (x y z:A),x=y \/ y=z \/ x = z).

Theorem p1:AtMostTwoElement bool.
Proof.
  compute.
  destruct x; destruct y; destruct z; auto.
Qed.

Theorem NatIsNotTwoElement : 
  not(AtMostTwoElement nat).
Proof.
  compute. intros. specialize (H 0 1 2). inversion H; try inversion H0; discriminate.
Qed.
Theorem NatIsNotBool :
  nat <> bool.
Proof.
  compute. intros. generalize p1. intros. rewrite <- H in H0. apply NatIsNotTwoElement. apply H0.
Qed.
