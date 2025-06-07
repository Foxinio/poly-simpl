Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia Strings.String Recdef Wf_nat Sorting.Permutation.
From Coq.Lists Require Import List ListDec.
Require Import Coq.Classes.Equivalence.
Import ListNotations.

From PolySimpl Require Import Syntax Utils VarList Algorithm BasicProps.
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
  sorted_shadow :
    ∀ (l'' : list pterm) (c1 c2 : Z) (v1 v2 : var_list),
      sorted (PTerm c1 v1 :: PTerm c2 v2 :: l'') → sorted (PTerm c1 v1 :: l'')
  sorted_const_invariant :
    ∀ (l'' : list pterm) (c1 c2 c3 : Z) (v1 v2 : var_list),
      sorted (PTerm c1 v1 :: PTerm c2 v2 :: l'')
      → sorted (PTerm c1 v1 :: PTerm c3 v2 :: l'')
  polynom_uniqueness :
    ∀ l1 l2 : list pterm,
      l1 ≡ₗ l2
      → sorted l1
        → sorted l2
          → canon_pterm l1
            → canon_pterm l2 → non_zero_const l1 → non_zero_const l2 → l1 = l2
  nat_lt_antisym : ∀ x y : nat, (x <? y) = false → (y <? x) = false → x = y
  cmp_vars_trans :
    ∀ v1 v2 v3 : var_list,
      cmp_vars v1 v2 = Lt → cmp_vars v2 v3 = Lt → cmp_vars v1 v3 = Lt
  cmp_vars_refl : ∀ v : var_list, cmp_vars v v = Eq
  Transitive_pterm_le : Transitive pterm_le
 *)

Print Assumptions poly_simpl_correctness.
(*
  Axioms:
  nat_lt_antisym : ∀ x y : nat, (x <? y) = false → (y <? x) = false → x = y
 *)

