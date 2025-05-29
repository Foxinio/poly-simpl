Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia Lists.List Strings.String Recdef Wf_nat.
Import ListNotations.

Require Import Syntax Utils.
Require Import PFlatten PFlattenProps.
Require Import ClearZP ClearZPProps.
Require Import ReduceMonom ReduceMonomProps.
Require Import Reconstruct ReconstructProps.
(* Require Import  *)

Definition poly_simpl (a : aexp) :=
  let l1 := poly_flatten a in
  let l2 := clear_zero_powers l1 in
  let l3 := reduce_monomials l2 in
  reconstruct l2.

Theorem poly_simpl_correctness : Correctness poly_simpl.
Proof.
  unfold Correctness, poly_simpl.
  intros a st.
  rewrite <- reconstruct_correct.
  - rewrite <- clear_zero_powers_correct.
    + now rewrite <- poly_flatten_correct.
    + apply poly_flatten_well_formed.
  - apply clear_zero_powers_well_formed_preserving.
    apply poly_flatten_well_formed.
  - apply clear_zero_powers_no_zeros.
    apply poly_flatten_well_formed.
Qed.

Theorem poly_simpl_canonility : Canonality poly_simpl.
Proof.
Admitted.


