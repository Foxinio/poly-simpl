Require Import Utf8.
From Coq Require Import ZArith.Int ZArith Lists.List.
Require Import Syntax.

Import Int.
Open Scope Int_scope.
Import ListNotations.

Fixpoint clear_zero_powers_vl (l : var_list) : var_list :=
  match l with
  | (x , n) :: l' =>
    if n =? 0
    then clear_zero_powers_vl l'
    else (x, n) :: clear_zero_powers_vl l'
  | [] => []
  end.

Fixpoint clear_zero_powers (l : list pterm) : list pterm :=
  match l with
  | PTerm c v :: l' =>
      PTerm c (clear_zero_powers_vl v) :: clear_zero_powers l'
  | [] => []
  end.

Definition no_zero_powers (l : list pterm) :=
  Forall (λ '(PTerm _ vars),
    Forall (λ '(_, n), n <> 0) vars) l.
