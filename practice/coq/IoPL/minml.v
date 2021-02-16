Require Import String.
Require Import List.
Import ListNotations.

Module Syntax.
Definition id : Set := string.

Inductive binOp : Set := Plus | Mult | Minus | Lt | Band | Bor.

Inductive exp : Set :=
| var : id -> exp
| ilit : nat -> exp
| blit : bool -> exp
| BinOp : binOp -> exp -> exp -> exp
| IfExp : exp -> exp -> exp -> exp
| LET : id -> exp -> exp -> exp
| FunExp : id -> exp -> exp
| AppExp : exp -> exp -> exp
| RecExp : id -> id -> exp -> exp -> exp.

Inductive program : Set :=
| Exp : exp -> program
| Decl: id -> exp -> program
| RexDecl : id -> id -> exp -> program.

Definition tyvar := nat.

Inductive ty : Set :=
| TyNat
| TyBool
(* | TyVar : tyvar -> ty *)
| TyFun : ty -> ty -> ty.

End Syntax.


Module Environment.

Definition t (a: Type) : Type := list (Syntax.id * a).

Definition extend {A: Type} x (v: A) (env: t A) := ((x, v) :: env).

Fixpoint assoc {B: Type} x (l: t B) :=
  match l with
  | [] => None
  | (d, v) :: t => if String.eqb d x then Some v else assoc x t
  end.

Definition lookup {A: Type} x (env: t A) := assoc x env.

Fixpoint map {A B: Type} (f: A -> B) (l: t A) :=
  match l with
  | nil => nil
  | (id, v):: t => (id, f v) :: (map f t)
  end.

Fixpoint fold_right {A B: Type} (f: A -> B -> B) (env: t A) a :=
  match env with
  | nil => a
  | (_, v):: rest => f v (fold_right f rest a)
  end.

End Environment.


Module eval.

Import Syntax.

Inductive exval : Set :=
| NatV  : nat -> exval
| BoolV : bool -> exval
| ProcV : id -> exp -> list (id * exval) -> exval
| RecV  : id -> id -> exp -> list (id * exval) -> exval.

Definition dnval := exval.

Inductive opt {A: Type}: Type :=
| Som : A -> opt
| Err : string -> opt.

Definition apply_prim op arg1 arg2 :=
  match (op, arg1, arg2) with
  | (Plus, NatV i1, NatV i2) => Som (NatV (i1 + i2))
  | (Plus, _, _) => Err "Both arguments must be integer: +"
  | (Mult, NatV i1, NatV i2) => Som (NatV (i1 * i2))
  | (Mult, _ , _) => Err "Both arguments must be integer: *"
  | (Minus, NatV i1, NatV i2) => Som (NatV (i1 - i2))
  | (Minus, _ , _) => Err "Both arguments must be integer: -"
  | (Lt, NatV i1, NatV i2) => Som (BoolV (Nat.ltb i1 i2))
  | (Lt, _, _) => Err "Both arguments must be integer: <"
  | (Band, BoolV b1, BoolV b2) => Som(BoolV (andb b1 b2))
  | (Band, _, _) => Err "Both arguments must be bool: and"
  | (Bor, BoolV b1, BoolV b2) => Som(BoolV (orb b1 b2))
  | (Bor, _, _) => Err "Both arguments must be bool: or"
  end.

Definition envt := (Environment.t exval).

Reserved Notation " t '[[' e ']]' '-->' t' " (at level 40).
Inductive eval_exp : envt -> exp -> exval -> Prop :=
| VarE : forall x v env,
    Environment.lookup x env = Some v -> (var x)[[env]] --> v
| IlitE : forall n env, (ilit n)[[env]] --> (NatV n)
| BlitE : forall b env, (blit b)[[env]] --> (BoolV b)
| BinOpE : forall op e1 e2 v1 v2 env v,
    e1[[env]] --> v1 -> e2[[env]] --> v2 -> (apply_prim op v1 v2) = Som v ->
    (BinOp op e1 e2)[[env]] --> v
| IfTrueE : forall e1 e2 e3 v env,
    e1 [[env]] --> (BoolV true) -> e2[[env]] --> v ->
    (IfExp e1 e2 e3)[[env]] --> v
| IfFalseE : forall e1 e2 e3 v env,
    e1 [[env]] --> (BoolV false) -> e3[[env]] --> v ->
    (IfExp e1 e2 e3)[[env]] --> v
| LetE : forall x e1 e2 v1 v env,
    e1[[env]] --> v1 -> e2[[(Environment.extend x v1 env)]] --> v ->
    (LET x e1 e2)[[env]] --> v
| FunE : forall x e env, (FunExp x e)[[env]] --> (ProcV x e env)
| AppE : forall e1 e2 body env' x v arg env,
    e1[[env]] --> (ProcV x body env') ->
    e2[[env]] --> arg ->
      body[[Environment.extend x arg env']] --> v ->
    (AppExp e1 e2)[[env]] --> v
| RecE : forall x para e1 e2 v env,
    e2[[Environment.extend x (RecV x para e1 env) env]] --> v ->
    (RecExp x para e1 e2)[[env]] --> v
| AppRecE : forall v e1 v2 e2 f x body E env,
    let ev := (RecV f x body E) in
    e1[[env]] --> ev -> e2[[env]] --> v2 ->
    body[[Environment.extend f ev (Environment.extend x v2 E)]] --> v ->
    (AppExp e1 e2)[[env]] --> v

where " e '[[' env ']]' '-->' v " := (eval_exp env e v).

Section example.

Open Scope string_scope.
Example evalExa1 :
  (LET "f" (ilit 2) (BinOp Plus (var "f") (ilit 3)))[[nil]] --> (NatV 5).
Proof.
  econstructor; eauto. econstructor.
  eapply BinOpE. apply VarE. simpl. reflexivity. apply IlitE.
  repeat econstructor; eauto.
Qed.

Example evalExa2 :
  (LET "f"
       (LET "x" (ilit 2)
            (LET "addx" (FunExp "y" (BinOp Plus (var "x") (var "y"))) (var "addx")))
       (AppExp (var "f") (ilit 4)))[[nil]] --> (NatV 6).
Proof.
  eapply LetE. eapply LetE. apply IlitE.
  eapply LetE. eapply FunE. apply VarE. simpl. reflexivity.
  eapply AppE. apply VarE. simpl. reflexivity.
  apply IlitE. eapply BinOpE. apply VarE. simpl. reflexivity.
  apply VarE. simpl. reflexivity.
  compute. reflexivity.
Qed.

Example evalExa3 :
  (RecExp "fact" "n"
          (IfExp (BinOp Lt (ilit 0) (var "n"))
                 (BinOp Mult (var "n") (AppExp (var "fact") (BinOp Minus (var "n") (ilit 1)) ) )
                 (ilit 1)
  ) (AppExp (var "fact") (ilit 3)))[[nil]] --> (NatV 6).
Proof.
  eapply RecE. eapply AppRecE. apply VarE. simpl. reflexivity. apply IlitE.
  apply IfTrueE. eapply BinOpE. apply IlitE. apply VarE. simpl. reflexivity.
  compute. reflexivity.
  eapply BinOpE. apply VarE. simpl. reflexivity.
  eapply AppRecE. apply VarE. simpl. reflexivity.
  eapply BinOpE. apply VarE. simpl. reflexivity.
  apply IlitE. compute. reflexivity.
  apply IfTrueE. eapply BinOpE. apply IlitE. apply VarE. simpl. reflexivity.
  compute. reflexivity.
  eapply BinOpE. apply VarE. simpl. reflexivity.
  eapply AppRecE. apply VarE. simpl. reflexivity.
  eapply BinOpE. apply VarE. simpl. reflexivity.
  apply IlitE. compute. reflexivity.
  apply IfTrueE. eapply BinOpE. apply IlitE. apply VarE. simpl. reflexivity.
  compute. reflexivity.
  eapply BinOpE. apply VarE. simpl. reflexivity.
  eapply AppRecE. apply VarE. simpl. reflexivity.
  eapply BinOpE. apply VarE. simpl. reflexivity.
  apply IlitE. compute. reflexivity.
  apply IfFalseE. eapply BinOpE. apply IlitE. apply VarE. simpl. reflexivity.
  compute. reflexivity.
  apply IlitE. compute. reflexivity.
  compute. reflexivity.
  compute. reflexivity.
Qed.

Fixpoint fact n :=
  match n with
  | 0 => 1
  | S m => n * (fact m)
  end.

Lemma fact_correct : forall n,
  (RecExp "fact" "n"
          (IfExp (BinOp Lt (ilit 0) (var "n"))
                 (BinOp Mult (var "n") (AppExp (var "fact") (BinOp Minus (var "n") (ilit 1)) ) )
                 (ilit 1)
  ) (AppExp (var "fact") (ilit n)))[[nil]] --> (NatV (fact n)).
Proof.
  induction n.
  -
    apply RecE. eapply AppRecE. constructor.
    simpl. reflexivity.
    constructor.
    apply IfFalseE; repeat (econstructor; eauto).
  -
    inversion IHn; subst.
    inversion H5; subst.
    inversion H1; subst. simpl in H2. inversion H2.
    inversion H1; subst. simpl in H2. inversion H2; subst.
    constructor. eapply AppRecE; eauto. econstructor.
    apply IfTrueE. econstructor. constructor. constructor. simpl. reflexivity.
    compute. reflexivity.
    econstructor. constructor. simpl. reflexivity.
    eapply AppRecE; eauto. constructor. simpl. reflexivity.
    econstructor. constructor. simpl. reflexivity. constructor.
    inversion H3; subst. unfold apply_prim. simpl. rewrite <- Minus.minus_n_O. reflexivity.
    unfold apply_prim. simpl. reflexivity.
Qed.

End example.

Theorem Eval_Unique : forall e env v1 v2,
    e[[env]] --> v1 -> e[[env]] --> v2 ->
    v1 = v2.
Proof.
  intros. generalize dependent v2. induction H; intros; try solve [inversion H0; subst; reflexivity].
  -
    inversion H0; subst. rewrite H in H3. inversion H3; subst. reflexivity.
  -
    inversion H2; subst. apply IHeval_exp1 in H7. apply IHeval_exp2 in H9. subst.
    rewrite H1 in H10. inversion H10; subst. reflexivity.
  -
    inversion H1; subst. apply IHeval_exp2. apply H8.
    apply IHeval_exp1 in H7. inversion H7.
  -
    inversion H1; subst.
    apply IHeval_exp1 in H7. inversion H7.
    apply IHeval_exp2. apply H8.
  -
    inversion H1; subst. apply IHeval_exp1 in H7. subst. apply IHeval_exp2 in H8. apply H8.
  -
    inversion H2; subst. apply IHeval_exp1 in H5. inversion H5; subst.
    apply IHeval_exp2 in H7. subst. apply IHeval_exp3 in H9. apply H9.
    apply IHeval_exp1 in H5. inversion H5; subst.
  -
    inversion H0; subst. apply IHeval_exp in H7. apply H7.
  -
    inversion H2; subst. apply IHeval_exp1 in H5. inversion H5.
    apply IHeval_exp1 in H5. inversion H5; subst.
    apply IHeval_exp2 in H7. subst. apply IHeval_exp3 in H9. apply H9.
Qed.

Inductive eval_decl : envt -> program -> (string * envt * exval) -> Prop :=
| ExpE : forall e env v,
    e[[env]] --> v -> eval_decl env (Exp e) ("-"%string, env, v)
| DeclP : forall x e v env,
    e[[env]] --> v -> eval_decl env (Decl x e) (x, Environment.extend x v env, v).

(*
Definition isval e :=
  match e with
  | ilit _ => true
  | blit _ => true
  | FunExp _ _ => true
  | _ => false
  end.

Definition compute_op op arg1 arg2 :=
  match (op, arg1, arg2) with
  | (Plus, ilit i1, ilit i2) => Som (ilit (i1 + i2))
  | (Plus, _, _) => Err "Both arguments must be integer: +"
  | (Mult, ilit i1, ilit i2) => Som (ilit (i1 * i2))
  | (Mult, _ , _) => Err "Both arguments must be integer: *"
  | (Minus, ilit i1, ilit i2) => Som (ilit (i1 - i2))
  | (Minus, _ , _) => Err "Both arguments must be integer: -"
  | (Lt, ilit i1, ilit i2) => Som (blit (Nat.ltb i1 i2))
  | (Lt, _, _) => Err ("Both arguments must be integer: <")
  end.

Definition value_to_ExpEnv v env :=
  match v with
  | NatV n => (ilit n, env) 
  | BoolV b => (blit b, env)
  | ProcV x e E => (FunExp x e, E)
  end.

Fixpoint eval_exp_fix env e :=
  match e with
  | var x => match Environment.lookup x env with
             | Some v => match value_to_ExpEnv v env with
                         | (v1, E) => (Som v1, E)
                         end
             | None => (Err "Variable not bound", env)
             end
  | ilit n => (Som (ilit n), env)
  | blit b => (Som (blit b), env)
  | BinOp op e1 e2 =>
    match (isval e1, isval e2) with
    | (true, true) => (compute_op op e1 e2, env)
    | (false, _) => match eval_exp_fix env e1 with
                    | (Som v1, E) => (Som (BinOp op v1 e2), env)
                    | (Err s, E) => (Err s, E)
                    end
    | (true, false) => match eval_exp_fix env e2 with
                       | (Som v2, env) => (Som (BinOp op e1 v2), env)
                       | (Err s, env) => (Err s, env)
                       end
    end
  | IfExp e1 e2 e3 =>
    if isval e1 then
      match e1 with
      | blit true =>  eval_exp_fix env e2
      | blit false => eval_exp_fix env e3
      | _ => (Err "Test expression must be boolean: if", env)
      end
    else
      match eval_exp_fix env e1 with
      | (Som v1, E) => (Som (IfExp v1 e2 e3), env)
      | (Err s, env) => (Err s, env)
      end
  | LET id e1 e2 =>
    match eval_exp_fix env e1 with
    | (Som value, E) => eval_exp_fix (Environment.extend id value E) e2
    | (Err s, E) => (Err s, E)
    end
  | FunExp x exp => Som (FunExp x exp)
  | AppExp e1 e2 =>
    match (isval e1, isval e2) with
    | (true, true) =>
      match e1 with
      | FunExp x body => eval_exp_fix (Environment.extend x e2 env) body
      | _ => Err "Non-function value is applied"
      end
    | (false, _) => match eval_exp_fix env e1 with
                    | Som v1 => Som (AppExp v1 e2)
                    | Err s => Err s
                    end
    | (true, false) => match eval_exp_fix env e2 with
                       | Som v2 => Som (AppExp e1 v2)
                       | Err s => Err s
                       end
    end
  end.

Definition eval_decl_def env p :=
  match p with
  | Exp e =>
    match eval_exp_fix env e with
    | Som v => Som ("-"%string, env, v)
    | Err s => Err s
    end
  | Decl id e =>
    match eval_exp_fix env e with
    | Som v => Som (id, Environment.extend id v env, v)
    | Err s => Err s
    end
  end.

Inductive multi_eval_fix : exp -> list (id * exp) -> opt -> Prop :=
| Refl : forall e env, multi_eval_fix e env (Som e)
| trans_eval : forall e1 e2 e3 env,
    multi_eval_fix e1 env (Som e2) -> eval_exp_fix env e2 = e3 ->
    multi_eval_fix e1 env e3.
*)

End eval.

Module Typying.

Import Syntax.
Import Environment.
Import eval.

Reserved Notation "G |- e ;; T" (at level 50).
Inductive has_type : list (id * ty) -> exp -> ty -> Prop :=
| T_Var : forall x G T, lookup x G = Some T -> G |- var x;; T
| T_int : forall n G, G |- ilit n ;; TyNat
| T_Bool : forall b G, G |- blit b ;; TyBool
| T_Plus : forall e1 e2 G,
    G |- e1 ;; TyNat -> G |- e2 ;; TyNat ->
    G |- BinOp Plus e1 e2 ;; TyNat
| T_Mult : forall e1 e2 G,
    G |- e1 ;; TyNat -> G |- e2 ;; TyNat ->
    G |- BinOp Mult e1 e2 ;; TyNat
| T_Minus : forall e1 e2 G,
    G |- e1 ;; TyNat -> G |- e2 ;; TyNat ->
    G |- BinOp Minus e1 e2 ;; TyNat
| T_Lt : forall e1 e2 G,
    G |- e1 ;; TyNat -> G |- e2 ;; TyNat ->
    G |- BinOp Lt e1 e2 ;; TyBool
| T_Band : forall e1 e2 G,
    G |- e1 ;; TyBool -> G |- e2 ;; TyBool ->
    G |- BinOp Band e1 e2 ;; TyBool
| T_Bor : forall e1 e2 G,
    G |- e1 ;; TyBool -> G |- e2 ;; TyBool ->
    G |- BinOp Bor e1 e2 ;; TyBool
| T_If : forall e1 e2 e3 T G,
    G |- e1 ;; TyBool -> G |- e2 ;; T -> G |- e3 ;; T ->
    G |- IfExp e1 e2 e3 ;; T
| T_Let : forall e1 x T1 e2 T2 G,
    G |- e1;; T1 -> ((x, T1):: G) |- e2;; T2 ->
    G |- LET x e1 e2 ;; T2
| T_Fun : forall x T1 e T G,
    ((x, T1):: G) |- e;; T ->
    G |- FunExp x e;; TyFun T1 T
| T_App : forall e1 e2 T1 T G,
    G |- e1;; TyFun T1 T -> G |- e2;; T1 ->
    G |- AppExp e1 e2 ;; T
| T_Rec : forall f T1 T2 x e1 e2 T G,
    ((f, TyFun T1 T2):: (x, T1):: G) |- e1;; T2 ->
    ((f, TyFun T1 T2):: G) |- e2;; T ->
    G |- RecExp f x e1 e2;; T

where "G |- e ;; T" := (has_type G e T).

End Typying.
