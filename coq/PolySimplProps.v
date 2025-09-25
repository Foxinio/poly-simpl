Require Import Stdlib.Classes.Equivalence.

From PolySimpl Require Import Syntax Utils Algorithm BasicProps.
From PolySimpl Require Import PFlattenProps ClearZPProps ReduceMonomProps ReconstructProps.
From PolySimpl Require Import PolyUniqueness.

Theorem poly_simpl_correctness : Correctness poly_simpl.
Proof.
  unfold Correctness, poly_simpl.
  intros a st.
  rewrite reconstruct_correct.
  rewrite <- reduce_monomials_correct.
  rewrite <- sort_monomials_correct.
  rewrite <- clear_zero_powers_correct.
  now rewrite <- poly_flatten_correct.
Qed.

Theorem poly_simpl_canonality : Canonality poly_simpl.
Proof.
  unfold Canonality, poly_simpl.
  intros a1 a2 Heqv. f_equal.
  apply polynom_uniqueness.
  - intro st.
    repeat rewrite <- reduce_monomials_correct.
    repeat rewrite <- sort_monomials_correct.
    repeat rewrite <- clear_zero_powers_correct.
    now repeat rewrite <- poly_flatten_correct.
  - apply reduce_monomials_sort_preserve.
    apply sort_monomials_sorts.
  - apply reduce_monomials_sort_preserve.
    apply sort_monomials_sorts.
  - apply reduce_monomials_canonical.
    apply sort_monomials_sorts.
  - apply reduce_monomials_canonical.
    apply sort_monomials_sorts.
  - apply reduce_monomials_non_zero_const.
    apply sort_monomials_sorts.
  - apply reduce_monomials_non_zero_const.
    apply sort_monomials_sorts.
Qed.

Print Assumptions poly_simpl_canonality.
(*
  Axioms:
  polynom_uniqueness :
    ∀ l1 l2 : list pterm,
      l1 ≡ₗ l2
      → sorted l1
        → sorted l2
          → canon_pterm l1
            → canon_pterm l2 → non_zero_const l1 → non_zero_const l2 → l1 = l2
  AsciiProps.ascii_compare_trans :
    ∀ a b c : Ascii.ascii,
      Ascii.compare a b = Lt → Ascii.compare b c = Lt → Ascii.compare a c = Lt
 *)

Print Assumptions poly_simpl_correctness.
(* Closed under the global context *)


(* ======================================================================== *)
(* New poly_simpl *)

Theorem poly_simpl'_canonality : Canonality poly_simpl'.
Proof.
  unfold Canonality, poly_simpl'.
  intros a1 a2 Heqv.
  f_equal.
  apply polynom_uniqueness.
  - intro st.
    repeat rewrite <- reduce_monomials_correct.
    repeat rewrite <- sort_monomials_correct.
    repeat rewrite <- clear_zero_powers_correct.
    now repeat rewrite <- poly_flatten_correct.
  - apply reduce_monomials_sort_preserve.
    apply sort_monomials_sorts.
  - apply reduce_monomials_sort_preserve.
    apply sort_monomials_sorts.
  - apply reduce_monomials_canonical.
    apply sort_monomials_sorts.
  - apply reduce_monomials_canonical.
    apply sort_monomials_sorts.
  - apply reduce_monomials_non_zero_const.
    apply sort_monomials_sorts.
  - apply reduce_monomials_non_zero_const.
    apply sort_monomials_sorts.
Qed.

Theorem poly_simpl'_correctness : Correctness poly_simpl'.
Proof.
  unfold Correctness, poly_simpl', reconstruct'.
  intros a st.
  assert (aeval st a = eval_pterm_list st
    (reduce_monomials (sort_monomials (clear_zero_powers (poly_flatten a))))).
  { rewrite <- reduce_monomials_correct.
    rewrite <- sort_monomials_correct.
    rewrite <- clear_zero_powers_correct.
    now rewrite <- poly_flatten_correct. }
  destruct (reduce_monomials _) eqn:?.
  - now transitivity (eval_pterm_list st (@nil pterm)).
  - now rewrite reconstruct'_correct.
Qed.

Print Assumptions poly_simpl'_correctness.
