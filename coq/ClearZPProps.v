Require Import Utf8.
From Coq Require Import Recdef Wf_nat.
From Coq Require Import Lia Lists.List Strings.String.
Require Import Syntax Utils ClearZP.

Theorem clear_zero_powers_correct (l : list pterm) (st : state) :
  pterm_list_well_formed l →
  l ≡ₗ clear_zero_powers l.
Proof.
Admitted.

Theorem clear_zero_powers_well_formed_preserving (l : list pterm) :
  pterm_list_well_formed l →
  pterm_list_well_formed (clear_zero_powers l).
Proof.
Admitted.

Theorem clear_zero_powers_no_zeros (l : list pterm) :
  pterm_list_well_formed l →
  no_zero_powers (clear_zero_powers l).
Proof.
Admitted.

