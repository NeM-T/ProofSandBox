Require Import String.
Require Import List.
Import ListNotations.

Module Syntax.
Definition id : Set := string.

Inductive binOp : Set := Plus | Mult | Minus | Lt.

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
| TyVar : tyvar -> ty
| TyFun : ty -> ty -> ty
| TyList : ty -> ty.

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
  | (Lt, _, _) => Err ("Both arguments must be integer: <")
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

End example.

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
