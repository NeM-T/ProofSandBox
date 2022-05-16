Section SetOp.
    Variable X : Type.

    Definition Sets := X -> Prop.

    Definition In (a : X) (A : Sets) := A a.

    Definition subset (A B : Sets) := forall x, A x -> B x.

End SetOp.

Section Relation.
    Variable U : Type. 

    Definition Relation := U -> U -> Prop.

    Record partial_order :=
      po_def
        { carrier : Sets U;
          Rel : Relation;
          Refl := forall x, Rel x x;
          AnSym := forall x y, Rel x y -> Rel y x -> x = y;
          Trans := forall x y z, Rel x y -> Rel y z -> Rel x z
        }.

End Relation.


Section defs.
  Variable U : Type.
  Variable D : partial_order U.
  Let R := @Rel U D.
  Let C := @carrier U D.
  
  Notation "a ⊑ b" := (R a b) (at level 60). 
  Notation "x ∈ A" := (In U x A) (at level 50).
  Notation "A ⊂ B" := (subset U A B) (at level 70).

  Inductive bottom bot : Prop :=
    bot_def : bot ∈ C -> (forall a,(a ∈ C -> bot ⊑ a)) -> bottom bot.

  Inductive Upper_Bound B (x:U) : Prop :=
    UB_def : B ⊂ C -> x ∈ C -> (forall y, y ∈ B -> y ⊑ x) -> Upper_Bound B x.

  Inductive supremum d X :=
    sup_def : X ⊂ C -> Upper_Bound X d -> (forall y: U, Upper_Bound X y -> d ⊑ y) -> supremum d X.

  Inductive directed X :=
    diredted_def : X ⊂ C -> (exists x, x ∈ X) -> (forall a b, exists c, a ∈ X /\ b ∈ X /\ a ⊑ c /\ b ⊑ c) -> directed X.

  Inductive complete :=
    comp_def : (forall X, X ⊂ C /\ directed X /\ exists sup, supremum sup X) -> complete.

End defs.

Section cpo.

  Variable U : Type.

  Record cpo :=
    cpo_def {
        po_cpo : partial_order U;
        ex_bot : exists bot, bottom U po_cpo bot;
        com_cpo : complete U po_cpo
      }.

End cpo.
