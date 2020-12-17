Require Coq.extraction.Extraction.
Require Import Ascii String Coq.Strings.Byte.
Require Import PeanoNat.
Require Export ExtrOcamlChar.
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive string => "char list" [ "[]" "(::)" ].
From Coq Require Import Lists.List.
Extract Inductive list => "list" [ "[]" "(::)" ].
Extraction Language OCaml.
Import ListNotations.
Import Nat.

Inductive deBruijn : Type :=
| var : nat -> deBruijn
| abs : string -> deBruijn -> deBruijn
| app : deBruijn -> deBruijn -> deBruijn.

Fixpoint shift k t :=
match t with
| var x => var (if leb k x then (S x) else x)
| abs x t' => abs x (shift (S k) t')
| app t1 t2 => app (shift k t1) (shift k t2)
end.

Fixpoint subst (d : nat) s t :=
match t with
| var x =>
  if eqb d x then s
  else if ltb d x then var (pred x) else var x
| abs x t' => abs x (subst (S d) (shift 0 s) t')
| app t1 t2 => app (subst d s t1) (subst d s t2)
end.

Inductive namelambda : Type :=
| Var (name: string)
| Abs (name: string) (t: namelambda)
| App (t1 t2: namelambda).

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst_name (x : string) s t :=
  match t with
  | Var x' => if String.eqb x x' then s else t
  | Abs x' t1 => Abs x' (if String.eqb x x' then t1 else ([x:=s] t1))
  | App t1 t2 => App ([x:=s] t1) ([x:=s] t2)
  end
where "'[' x ':=' s ']' t" := (subst_name x s t).


Fixpoint in_list x l n :=
  match l with
  | nil => None
  | h :: t => if String.eqb h x then Some n else in_list x t (S n)
  end.

Fixpoint inb x l :=
  match l with
  | nil => false
  | h :: t => if String.eqb h x then true else (inb x t)
  end.

Fixpoint free_list l1 l2 t :=
  match t with
  | Var x =>
    if orb (inb x l1) (inb x l2) then l2 else (x :: l2)
  | Abs x t1 => (free_list (x :: l1) l2 t1)
  | App t1 t2 =>
    free_list l1 (free_list l1 l2 t1) t2
  end.

Fixpoint removenames l t :=
  match t with
  | Var x =>
    match in_list x l 0 with
    | Some n => Some (var n)
    | None => None
    end
  | Abs x t' =>
    match (removenames (x :: l) t') with
    | Some t1 => Some (abs x t1)
    | None => None
    end
  | App t1 t2 =>
    match ((removenames l t1) ,(removenames l t2)) with
      | (Some t1', Some t2') => Some (app t1' t2')
      | _ => None
    end
  end.

Definition lambda_to_debruijn t := removenames (free_list [] [] t) t.

Fixpoint nth {A: Type} (l: list A) n :=
  match n with
  | 0 =>
    match l with
    | nil => None
    | h :: t => Some h
    end
  | S n' =>
    match l with
    | nil => None
    | h :: t => nth t n'
    end
  end.

Fixpoint debruijn_to_lambda l t:=
  match t with
  | var n =>
    match nth l n with
    | Some x => Some (Var x)
    | None => None
    end
  | abs x t1 =>
    match debruijn_to_lambda (x :: l) t1 with
    | Some t' => Some (Abs x t')
    | None => None
    end
  | app t1 t2 =>
    match (debruijn_to_lambda l t1, debruijn_to_lambda l t2) with
    | (Some t1', Some t2') => Some (App t1' t2')
    | _ => None
    end
  end.

Fixpoint left_eval t :=
  match t with
  | abs x t1 =>
    match left_eval t1 with
    | Some t1' => Some (abs x t1')
    | None => None
    end
  | app t1 t2 =>
    match t1 with
    | abs x t1' => Some (subst 0 t2 t1')
    | _ =>
      match left_eval t1 with
      | Some t1' => Some (app t1' t2)
      | _ =>
        match left_eval t2 with
        | Some t2' => Some (app t1 t2')
        | None => None
        end
      end
    end
  | _ => None
  end.

Definition result_lambda t l :=
  match left_eval t with
  | Some t' => debruijn_to_lambda l t'
  | None => None
  end.

Extraction "ocaml/src/eval.ml" lambda_to_debruijn left_eval debruijn_to_lambda result_lambda.

Lemma remove_subst : forall t1 t2 x Γ n t1' t2',
    removenames Γ t2 = Some t2' ->
    removenames Γ t1 = Some t1' ->
    in_list x Γ 0 = Some n ->
    removenames Γ ([x := t2]t1) = Some (subst n t2' t1').
Proof.
  induction t1; simpl; intros; auto.
  destruct String.eqb eqn:IH1. apply String.eqb_eq in IH1; subst.
  rewrite H. destruct in_list. inversion H0; inversion H1; subst. simpl. rewrite eqb_refl. reflexivity.
  inversion H1.

  destruct in_list eqn:IH2. inversion H0; subst. simpl. rewrite IH2.
  admit.
  inversion H0.
  destruct (String.eqb) eqn:IH1.
  apply String.eqb_eq in IH1; subst. erewrite <- IHt1.
  admit. admit. admit.
Abort.

(*
Fixpoint in_list x l n :=
  match l with
  | nil => None
  | x' :: l' =>
    if String.eqb x x' then Some n else in_list x l' (S n)
  end.

Fixpoint nth {A: Type} n (l: list A) : option A :=
  match n with
  | 0 => match l with
        | nil => None
        | x :: _ => Some x
        end
  | S m => match l with
          | nil => None
          | _ :: l' => nth m l'
          end
  end.

Fixpoint removenames l t :=
  match t with
  | Var x =>
    match in_list x l 0 with
    | Some n => Some (var n)
    | None => None
    end
  | Abs x t' =>
    match removenames (x :: l) t' with
    | Some t1 => Some (abs t1)
    | None => None
    end
  | App t1 t2 =>
    match removenames l t1 with
    | Some t1' =>
      match removenames l t2 with
      | Some t2' => Some (app t1' t2')
      | None => None
      end
    | None => None
    end
  end.
Fixpoint eq_lambda t1 t2 l:=
  match t1 with
  | Var x =>
      match t2 with
      | var n =>
        match nth n l with
        | Some x' => String.eqb x x'
        | None =>
          match in_list x l 0 with
          | Some _ => false
          | None => true
          end
        end
      | _ => false
      end
  | Abs x t1' =>
      match t2 with
      | abs t2' => eq_lambda t1' t2' (x :: l)
      | _ => false
      end
  | App t11 t12 =>
      match t2 with
      | app t21 t22 => andb (eq_lambda t11 t21 l) (eq_lambda t12 t22 l)
      | _ => false
      end
  end.
*)

Reserved Notation " t '-->n' t' " (at level 40).

Inductive value_name : namelambda -> Prop :=
  | v_abs : forall t x, value_name (Abs x t).

Inductive eval : namelambda -> namelambda -> Prop :=
  | E_App1 : forall t1 t1' t2,
      t1 -->n t1' ->
      App t1 t2 -->n App t1' t2
  | E_App2 : forall v1 t2 t2',
      value_name v1 ->
      t2 -->n t2' ->
      App v1 t2 -->n App v1 t2'
  | E_AppAbs : forall t1 v2 x,
      value_name v2 ->
      App (Abs x t1) v2 -->n ([x := v2] t1)

  where " t '-->n' t' " := (eval t t').

Definition valueB t :=
  match t with
  | abs x t' => true
  | _ => false
  end.

Fixpoint step_fix t :=
  match t with
  | app t1 t2 =>
    match step_fix t1 with
    | Some t1' => Some (app t1' t2)
    | None =>
      match step_fix t2 with
      | Some t2' => Some (app t1 t2')
      | None =>
        if valueB t2 then
          match t1 with
          | abs x t => Some (subst 0 t2 t)
          | _ => None
          end
        else None
      end
    end
  | _ => None
  end.

Fixpoint left_app t :=
  match t with
  | var _ => None
  | abs x t' =>
    match left_app t'  with
    | Some t1 => Some (abs x t1)
    | None => None
    end
  | app t1 t2 =>
    match left_app t1 with
    | Some t1' => Some (app t1' t2)
    | None =>
      match left_app t2 with
      | Some t2' => Some (app t1 t2')
      | None =>
        if valueB t2 then
          match t1 with
          | abs x t1' => Some (subst 0 t2 t1')
          | _ => None
          end
        else None
      end
    end
  end.

Reserved Notation " t '-->d' t' " (at level 40).

Inductive value : deBruijn -> Prop :=
  | vd_abs : forall t x, value (abs x t).

Inductive step : deBruijn -> deBruijn -> Prop :=
  | D_App1 : forall t1 t1' t2,
      t1 -->d t1' ->
      app t1 t2 -->d app t1' t2
  | D_App2 : forall v1 t2 t2',
      value v1 ->
      t2 -->d t2' ->
      app v1 t2 -->d app v1 t2'
  | D_AppAbs : forall t1 v2 x,
      value v2 ->
      app (abs x t1) v2 -->d subst 0 v2 t1

  where " t '-->d' t' " := (step t t').


Theorem deBruijn_correct : forall t t',
    t -->n t' ->
    removenames [] t -->d removenames [] t'.
Proof.
  intros. induction H; simpl.
  constructor; auto. constructor; auto. destruct H; simpl. constructor.
Abort.

(*
Theorem deBruijn_correct : forall t Γ t' s,
    t -->n t' ->
    eq_lambda t s Γ = true ->
    exists s', s -->d s'.
Proof.
  induction t0; simpl; intros; auto; try solve [inversion H].
  destruct s; try solve [inversion H0].
  apply Bool.andb_true_iff in H0. destruct H0.
  inversion H; subst.
  eapply IHt0_1 in H0; eauto. destruct H0.
  exists (app x s2); constructor; auto.
  eapply IHt0_2 in H6. inversion H6. exists (app s1 x). constructor; eauto. destruct H4. simpl in H0.
  destruct s1; try solve [inversion H0]. constructor. apply H1.
  simpl in H0. destruct s1; try solve [inversion H0].
  inversion H5; subst. simpl in H1. destruct s2; try solve [inversion H1].


Theorem deBruijn_correct : forall t s x Γ t' s' n,
  removenames Γ s = Some s' ->
  removenames Γ t = Some t' ->
  in_list x Γ 0 = Some n ->
  removenames Γ ([x := s]t) = Some (subst n s' t').
Proof.
  induction t0; simpl; intros; auto.
  destruct String.eqb eqn:IH. apply String.eqb_eq in IH; subst. rewrite H1 in H0. inversion H0; subst; simpl.
  rewrite eqb_refl. apply H. admit.
*)
