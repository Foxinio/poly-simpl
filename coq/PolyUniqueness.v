From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Lia Lists.List Strings.String Recdef Wf_nat Sorting.Sorted.
Import ListNotations.

From PolySimpl Require Import Syntax Utils BasicProps Algorithm VarList.

Theorem polynom_uniqueness :
  ∀ l1 l2, l1 ≡ₗ l2 →
  sorted l1 → sorted l2 →
  canon_pterm l1 → canon_pterm l2 →
  non_zero_const l1 → non_zero_const l2 →
  l1 = l2.
Proof.
  strong_list_induction.
  intros n' IH l1 l2 Hlen Heqv Hsort1 Hsort2 Hcanon1 Hcanon2 Hnzc1 Hnzc2.
Admitted.
