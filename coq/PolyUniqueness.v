From PolySimpl Require Import Syntax Utils BasicProps Algorithm.

Theorem polynom_uniqueness :
  ∀ l1 l2, l1 ≡ₗ l2 →
  sorted l1 → sorted l2 →
  canon_pterm l1 → canon_pterm l2 →
  non_zero_const l1 → non_zero_const l2 →
  l1 = l2.
Proof.
Admitted.
