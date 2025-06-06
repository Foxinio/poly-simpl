Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia Strings.String Recdef Wf_nat Sorting.Permutation.
From Coq.Lists Require Import List ListDec.
Require Import Coq.Classes.Equivalence.
Import ListNotations.

From PolySimpl Require Import Syntax Utils VarList Algorithm BasicProps.
From PolySimpl Require Import PFlattenProps ClearZPProps ReduceMonomProps ReconstructProps.
From Poly








    



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

Theorem poly_simpl_canonility : Canonality poly_simpl.
Proof.
  unfold Canonality, poly_simpl.
  intros a1 a2 Heqv. f_equal.
  apply reconstruct_canonality.
  apply to_reduce_poly_canonality, Heqv.
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


Lemma reduce_monom_List_concat_homo l ls :
  grouped_pterms (l::ls) →
  Forall pterm_list_well_formed (l::ls) →
  Forall no_zero_powers (l::ls) →
  reduce_monomials (List.concat (l::ls)) =
  reduce_monomials l ++ reduce_monomials (List.concat ls).
Proof.
Admitted.

Lemma reduce_monom_perm_invariant :
  ∀ l1 l2, Permutation l1 l2 →
  pterm_list_well_formed l1 → pterm_list_well_formed l2 →
  no_zero_powers l1 → no_zero_powers l2 →
  reduce_monomials l1 = reduce_monomials l2.
Proof.
Admitted.

Lemma reduce_monom_perm_invariant' :
  ∀ l1 l2, Permutation (reduce_monomials l1) l2 →
  reduce_monomials l1 = reduce_monomials l2.
Proof.
  strong_list_induction.
  intros n' IH l1 l2 Hlen HPerm.
  destruct l1 as [| [c1 v1] l1'] eqn:Eql1;
  destruct l2 as [| [c2 v2] l2'] eqn:Eql2; auto;
  (* - rewrite reduce_monomials_equation in HPerm. *)
  [ destruct (reduce_monomials (PTerm c2 v2 :: l2')) eqn:?; auto;
    apply Permutation_nil_cons in HPerm; contradiction
  | destruct (reduce_monomials (PTerm c1 v1 :: l1')) eqn:?; auto;
    symmetry in HPerm; apply Permutation_nil_cons in HPerm; contradiction |].
  rewrite <- Eql1 in *.
  clear Eql1 l1' c1 v1.
  destruct (Permutation_vs_cons_inv HPerm) as [la [lb Hab]].
  (* rewrite Hab in HP. *)
  specialize HPerm as HPerm'; rewrite Hab in HPerm'.
  assert (Permutation (la ++ lb) l2')
    by (eapply Permutation_cons_inv; etransitivity; [| apply HPerm' ];
      apply Permutation_middle).
Abort.

Lemma reduce_monomials_sorts :
  ∀ l1 l2, Permutation l1 l2 →
  reduce_monomials l1 = reduce_monomials l2.
Proof.
  strong_list1_induction.
  intros n' IH [| [c1 v1] l1] HLen [| [c2 v2] l2] HPerm; auto.
  - apply Permutation_nil_cons in HPerm; contradiction.
  - symmetry in HPerm; apply Permutation_nil_cons in HPerm; contradiction.
  - {
  destruct l1 as [| [c1' v1'] l1'] eqn:Eql1;
  destruct l2 as [| [c2' v2'] l2'] eqn:Eql2; auto;
  try (apply Permutation_length in HPerm; discriminate HPerm);
  [ apply Permutation_length_1 in HPerm; inv HPerm; subst; auto |].
  rewrite reduce_monomials_equation; symmetry;
  rewrite reduce_monomials_equation; symmetry.
  destruct (split (PTerm c1 v1 :: _)) eqn:?.
  destruct (split (PTerm c2 v2 :: _)) eqn:?.
Abort.

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
  + rewrite reduce_monomials_equation.
Admitted.

Definition rep (l : list pterm) (H: equiv_list l) : pterm.
Proof.
  destruct l.
  - exfalso. inversion H.
  - apply p.
Defined.

Fixpoint reduce_vequiv (l : list pterm) (H: equiv_list l) :
  { p : pterm | pterm_equiv p (rep l H)}.
Proof.
  destruct l as [| [c1 v1] [| [c2 v2] l]];
  [ exfalso; inv H | exists (PTerm c1 v1); now simpl |].
  assert (equiv_list (PTerm c2 v2 :: l)) by (inv H; auto).
  destruct (reduce_vequiv (PTerm c2 v2 :: l) H0) as [[c_res v_res] Hp].
  simpl in Hp.
  exists (PTerm (c1+c_res) v1); now simpl.
Defined.

Lemma reduce_vequiv_correct (l : list pterm) (H: equiv_list l) :
  let '(PTerm c _) := proj1_sig (reduce_vequiv l H) in
  (fold_left (λ c '(PTerm c' _), c+c') l 0)%Z = c.
Admitted.

Fixpoint reduce_grouped_monomials (ls : list (list pterm)) :
  Forall equiv_list ls → list pterm.
Proof.
  intro HFa.
  destruct ls as [| l ls]; [ apply [] |].
  refine (let (Heqv, HFa') := (_ : equiv_list l * Forall equiv_list ls) in
          let p := proj1_sig (reduce_vequiv l Heqv) in
          let l := reduce_grouped_monomials ls HFa' in
          p :: l).
  inversion HFa; split; auto.
Defined.

Definition reduce_monomials_simply (l : list pterm) : list pterm :=
  match group_pterms l with
  | exist _ ls (conj (conj H _) _) =>
      reduce_grouped_monomials ls H
  end.

Theorem merge_monom_reduce_monomials_simply : ∀ (l' l1 l2 : list pterm),
  (* split l' = (l1, l2) → *)
  Permutation l' (l1++l2) →
  merge_monom (reduce_monomials_simply l1, reduce_monomials_simply l2) =
  reduce_monomials_simply l'.
Proof.
  strong_list1_induction.
  intros n' IH l' Hlen l1 l2 Hperm.
  rewrite merge_monom_equation.
Abort.


Theorem reduce_monomials_spec :
  ∀ l, Permutation (reduce_monomials l) (reduce_monomials_simply l).
Proof.
  strong_list_induction.
  intros n' IH l Hlen.
  destruct l as [| [c1 v1] [| [c2 v2] l']] eqn:?;
      try (rewrite reduce_monomials_equation; simpl; now auto).
  remember (PTerm c1 v1 :: PTerm c2 v2 :: l').
  rewrite reduce_monomials_equation, Heql1.
  destruct (split (PTerm c1 v1 :: PTerm c2 v2 :: l')) eqn:Hsplt.
  pose proof (split_len_strict _ _ _ _ _ Hsplt) as [? ?].
  (* rewrite (IH (List.length l1)); *)
  (* subst; simpl in *; try lia. *)
  (* rewrite (IH (List.length l2)); *)
  subst; simpl in *; try lia.
  destruct (split l') eqn:?.
  inv Hsplt.
  rewrite merge_monom_equation.
  destruct (reduce_monomials _) as [| [c1' v1'] l1'] eqn:Heql1',
           (reduce_monomials (PTerm c2 v2 :: l0)) as [| [c2' v2'] l2'] eqn:Heql2';
  try (pose proof (reduce_monom_cons_nil _ _ Heql2'); contradiction);
  try (pose proof (reduce_monom_cons_nil _ _ Heql1'); contradiction).
  destruct (cmp_vars v1' v2').
  - unfold reduce_monomials_simply.
    destruct (group_pterms _) as [ls [[HFa Hdis] HPerm]].
Abort.


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
  (* reduce_monomials produces unique pterm lists *)
  apply reduce_monomials_canonality; auto.
  apply var_list_canonality; auto.
  intro st.
  repeat rewrite <- clear_zero_powers_correct.
  now repeat rewrite <- poly_flatten_correct.
Qed.

Theorem reconstruct_canonality :
  ∀ l1 l2, l1 = l2 →
  reconstruct l1 = reconstruct l2.
Proof.
  induction l1; simpl; intros l2 Heq;
  now rewrite <- Heq.
Qed.


