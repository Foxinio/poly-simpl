Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia Lists.List Strings.String Recdef Wf_nat.
Import ListNotations.

Require Import Syntax Utils ClearZP ReduceMonom.




Theorem reduce_monomials_correct (l : list pterm) :
  pterm_list_well_formed l →
  no_zero_powers l →
  l ≡ₗ (reduce_monomials l).
Proof.
Admitted.

Theorem reduce_monomials_well_formed_preserving (l : list pterm) :
  pterm_list_well_formed l →
  no_zero_powers l →
  pterm_list_well_formed (reduce_monomials l).
Proof.
Admitted.


