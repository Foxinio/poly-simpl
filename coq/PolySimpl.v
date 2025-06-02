Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia Strings.String Recdef Wf_nat Sorting.Permutation.
From Coq.Lists Require Import List ListDec.
Require Import Coq.Classes.Equivalence.
Import ListNotations.

From PolySimpl Require Import Syntax Utils VarList.
From PolySimpl Require Import PFlatten PFlattenProps.
From PolySimpl Require Import ClearZP ClearZPProps.
From PolySimpl Require Import ReduceMonom ReduceMonomProps.
From PolySimpl Require Import Reconstruct ReconstructProps.

Definition poly_simpl (a : aexp) :=
  let l1 := poly_flatten a in
  let l2 := clear_zero_powers l1 in
  let l3 := reduce_monomials l2 in
  reconstruct l3.

Theorem poly_simpl_correctness : Correctness poly_simpl.
Proof.
  unfold Correctness, poly_simpl.
  intros a st.
  rewrite reconstruct_correct.
  rewrite <- reduce_monomials_correct.
  rewrite <- clear_zero_powers_correct.
  now rewrite <- poly_flatten_correct.
Qed.


Lemma grouping_lemma :
  ∀ l1 l2,
  Forall pterm_list_well_formed l1 →
  Forall pterm_list_well_formed l2 →
  Forall no_zero_powers l1 →
  Forall no_zero_powers l2 →
  grouped_pterms l1 →
  grouped_pterms l2 →
  (∀ st, grouped_eval_pl st l1 = grouped_eval_pl st l2) →
  List.concat l1 ≡ᵥ List.concat l2. 
Proof.
Admitted.


Theorem var_list_canonality :
  ∀ l1 l2, l1 ≡ₚ l2 →
  Forall pterm_list_well_formed l1 → Forall pterm_list_well_formed l2 →
  Forall no_zero_powers l1 → Forall no_zero_powers l2 →
  grouped_pterms l1 → grouped_pterms l2 →
  List.concat l1 ≡ᵥ List.concat l2.
Proof.
  intros l1 l2 Heqv Hwf1 Hwf2 Hnz1 Hnz2 vars.
  (* pose proof (grouping_exists l1) as [ls1 [Hgp1 [Hccat1 Heqv1]]]. *)
  (* pose proof (grouping_exists l2) as [ls2 [Hgp2 [Hccat2 Heqv2]]]. *)
  (* rewrite <- Hccat1, <- Hccat2. *)
  (* apply grouping_lemma; auto. *)


Admitted.

Lemma reduce_List_concat_homo l ls :
  grouped_pterms (l::ls) →
  Forall pterm_list_well_formed (l::ls) →
  Forall no_zero_powers (l::ls) →
  reduce_monomials (List.concat (l::ls)) =
  reduce_monomials l ++ reduce_monomials (List.concat ls).
Proof.


Theorem reduce_monomials_canonality :
  ∀ l1 l2, l1 ≡ᵥ l2 →
  pterm_list_well_formed l1 → pterm_list_well_formed l2 →
  no_zero_powers l1 → no_zero_powers l2 →
  reduce_monomials l1 = reduce_monomials l2.
Proof.
  strong_list_induction.
  intros n' IH l1 l2 Hlen Heqv Hwf1 Hwf2 Hnz1 Hnz2.
  destruct l1 as [| [c1 v1] l1'] eqn:Eql1,
           l2 as [| [c2 v2] l2'] eqn:Eql2; auto.
  + 
Admitted.



Theorem to_reduce_poly_canonality :
  ∀ a1 a2, a1 ≡ a2 →
  reduce_monomials (clear_zero_powers (poly_flatten a1)) =
  reduce_monomials (clear_zero_powers (poly_flatten a2)).
Proof.
  intros a1 a2 Heqv.
  (* Prepare some properties *)
  assert (no_zero_powers (clear_zero_powers (poly_flatten a1)));
  [ apply clear_zero_powers_no_zeros, poly_flatten_well_formed |].
  assert (pterm_list_well_formed (clear_zero_powers (poly_flatten a1)));
  [ apply clear_zero_powers_well_formed_preserving,
          poly_flatten_well_formed |].
  assert (no_zero_powers (clear_zero_powers (poly_flatten a2)));
  [ apply clear_zero_powers_no_zeros, poly_flatten_well_formed |].
  assert (pterm_list_well_formed (clear_zero_powers (poly_flatten a2)));
  [ apply clear_zero_powers_well_formed_preserving,
          poly_flatten_well_formed |].
  (* reduce_monomials produces unique 
  apply reduce_monomials_canonality; auto.
  apply var_list_canonality; auto.
  intro st.
  repeat rewrite <- clear_zero_powers_correct.
  now repeat rewrite <- poly_flatten_correct.
Qed.

Theorem reconstruct_canonality :
  ∀ l1 l2, l1 ≡ₗ l2 →
  reconstruct l1 = reconstruct l2.
(* This is not true *)
Abort.

Theorem reconstruct_canonality :
  ∀ l1 l2, l1 = l2 →
  reconstruct l1 = reconstruct l2.
Proof.
  induction l1; simpl; intros l2 Heq;
  now rewrite <- Heq.
Qed.

Theorem poly_simpl_canonility : Canonality poly_simpl.
Proof.
  unfold Canonality, poly_simpl.
  intros a1 a2 Heqv.
  apply reconstruct_canonality.
  apply to_reduce_poly_canonality, Heqv.
Qed.


