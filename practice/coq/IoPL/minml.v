Require Import String.
Require Import List.
Import ListNotations.

Module Syntax.
Definition id : Set := string.

Inductive binOp : Set := Plus | Mult | Lt.

Inductive exp : Set :=
| var : id -> exp
| ilit : nat -> exp
| blit : bool -> exp
| BinOp : binOp -> exp -> exp -> exp
| IfExp : exp -> exp -> exp -> exp
| LET : id -> exp -> exp -> exp
| FunExp : id -> exp -> exp
| AppExp : exp -> exp -> exp.

Inductive program : Set :=
| Exp : exp -> program
| Decl: id -> exp -> program.

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
| NatV : nat -> exval
| BoolV : bool -> exval
| ProcV : id -> exp -> list (id * exval) -> exval.

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
    e1[[env]] --> v1 -> e2[[(Environment.extend x v env)]] --> v ->
    (LET x e1 e2)[[env]] --> v
| FunE : forall x e env, (FunExp x e)[[env]] --> (ProcV x e env)
| AppE : forall e1 e2 body env' x v arg env,
    e1[[env]] --> (ProcV x body env') ->
    e2[[env]] --> arg ->
      body[[Environment.extend x arg env']] --> v ->
    (AppExp e1 e2)[[env]] --> v

where " e '[[' env ']]' '-->' v " := (eval_exp env e v).

Inductive eval_decl : envt -> program -> (string * envt * exval) -> Prop :=
| ExpE : forall e env v,
    e[[env]] --> v -> eval_decl env (Exp e) ("-"%string, env, v)
| DeclP : forall x e v env,
    e[[env]] --> v -> eval_decl env (Decl x e) (x, Environment.extend x v env, v).

(*
Fixpoint eval_exp env e :=
  match e with
  | var x => match Environment.lookup x env with
             | Some v => Som v
             | None => Err "Variable not bound"
             end
  | ilit n => Som (NatV n)
  | blit b => Som (BoolV b)
  | BinOp op e1 e2 =>
    match (eval_exp env e1, eval_exp env e2) with
    | (Som v1, Som v2) => apply_prim op v1 v2
    | (Err s, _) => Err s
    | (_, Err s) => Err s
    end
  | IfExp e1 e2 e3 =>
    match eval_exp env e1 with
    | Som (BoolV true) => eval_exp env e2
    | Som (BoolV false) => eval_exp env e3
    | _ => Err "Test expression must be boolean: if"
    end
  | LET id e1 e2 =>
    match eval_exp env e1 with
    | Som value =>
      eval_exp (Environment.extend id value env) e2
    | Err s => Err s
    end
  | FunExp x exp => Som (ProcV x exp env)
  | AppExp e1 e2 =>
    match (eval_exp env e1, eval_exp env e2) with
    | (Som funval, Som arg) =>
      match funval with
      | ProcV x body env' =>
        eval_exp (Environment.extend x arg env') body
      | _ => Err "Non-function value is applied"
      end
    | (Err s, _) => Err s
    | (_ ,Err s) => Err s
    end
  end.

Definition eval_decl env p :=
  match p with
  | Exp e =>
    match eval_exp env e with
    | Som v => Som ("-"%string, env, v)
    | Err s => Err s
    end
  | Decl id e =>
    match eval_exp env e with
    | Som v => Som (id, Environment.extend id v env, v)
    | Err s => Err s
    end
  end.
 *)

End eval.
