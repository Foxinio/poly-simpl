Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia Lists.List Strings.String Recdef Wf_nat.
Import ListNotations.

Require Import Syntax Utils.

Fixpoint reconstruct_var_pow x n :=
  match n with
  | 0    => ANum 1
  | S 0  => AId x
  | S n' => AMult (AId x) (reconstruct_var_pow x n')
  end.

Fixpoint reconstruct_monom c (l : var_list) : aexp :=
  match l with
  | [] => ANum c
  | (x, n) :: l' => 
      AMult (reconstruct_var_pow x n) (reconstruct_monom c l')
  end.

Fixpoint reconstruct (l : list pterm) : aexp :=
  match l with
  | [] => ANum 0
  | [PTerm c vars] => reconstruct_monom c vars
  | PTerm c vars :: l' =>
      AMult (reconstruct_monom c vars) (reconstruct l')
  end.


