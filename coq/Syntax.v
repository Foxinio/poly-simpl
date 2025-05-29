Require Import Utf8.
From PolySimpl Require Export Maps.
From Coq Require Export Lists.List Strings.String.
From Coq Require Export ZArith.Int ZArith.

Require Import Utils.

Import Int.
Import ListNotations.

Open Scope Int_scope.

Definition state := total_map Z.

Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".

Coercion AId : string >-> aexp.
Coercion ANum : Z >-> aexp.
Definition ZNum n := ANum (Z.of_nat n).
Coercion ZNum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.

Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.

Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).

Open Scope com_scope.

Definition var_list := list (string * nat).

Inductive pterm :=
  | PTerm (c : Z) (vars : var_list).


Fixpoint aeval (st : state) (a : aexp) : Z :=
  match a with
  | ANum z => z
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Definition pow (st : state) '(x, n) : Z :=
  Z.pow (st x) (Z.of_nat n).

Definition eval_pterm (st : state) '(PTerm c vars) : Z :=
  fold_left Z.mul (map (pow st) vars) c.

Fixpoint eval_pterm_list (st : state) (l : list pterm) : Z :=
  match l with
  | [] => 0_
  | c :: l' => eval_pterm_list st l' + eval_pterm st c
  end.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.
Hint Unfold aequiv : core.

Notation "a '≡' b" :=  (aequiv a b) (at level 70).

Definition ptequiv (l1 l2 : list pterm) : Prop :=
  forall (st : state),
    eval_pterm_list st l1 = eval_pterm_list st l2.
Hint Unfold ptequiv : core.

Notation "a '≡ₗ' b" :=  (ptequiv a b) (at level 70).

Definition asimpt a l :=
  forall st : state, aeval st a = eval_pterm_list st l.
Hint Unfold asimpt : core.

Notation "a '≲ₗ' l" := (asimpt a l) (at level 70).

Definition Correctness (f : aexp → aexp) :=
  forall a : aexp, a ≡ f a.
Hint Unfold Correctness : core.

Definition Canonality (f : aexp → aexp) :=
  forall a1 a2, a1 ≡ a2 → f a1 = f a2.
Hint Unfold Canonality : core.

Definition pterm_list_well_formed (l : list pterm) :=
  Forall (λ '(PTerm _ vars), sorted_uniq vars) l.
Hint Unfold pterm_list_well_formed : core.

