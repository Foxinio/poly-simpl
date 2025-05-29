Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia Lists.List Strings.String Recdef Wf_nat.
Import ListNotations.

Require Import Syntax Utils Reconstruct ClearZP.





Theorem reconstruct_correct (st : state) (l : list pterm) :
  pterm_list_well_formed l →
  no_zero_powers l →
  reconstruct l ≲ₗ l.
Proof.
Admitted.

