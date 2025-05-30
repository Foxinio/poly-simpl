Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia Lists.List Strings.String Recdef Wf_nat.
Import ListNotations.

From PolySimpl Require Import Syntax Utils ClearZP ReduceMonom.

Lemma cmp_vars_eq_iff : ∀ v1 v2 : list (string*nat),
  cmp_vars v1 v2 = Eq → v1 = v2.
Proof.
  strong_list_induction.
  intros n' IH l1 l2 Hlen Hcmp.
  destruct l1 as [| [x n] l1'] eqn:?, l2 as [| [y m] l2'] eqn:?; auto;
  try now inversion Hcmp.
  simpl in Hcmp.
  destruct (x ?= y)%string eqn:?; try discriminate.
  pose proof (String.compare_eq_iff _ _ Heqc).
  destruct (n <? m) eqn:?; try discriminate;
  destruct (m <? n) eqn:?; try discriminate.
  pose proof (nat_lt_antisym _ _ Heqb Heqb0). 
  f_equal; [ now subst |].
  simpl in Hlen.
  apply (IH (len2 (l1', l2'))); auto; simpl; lia.
Qed.

Lemma merge_monom_correct (st : state) :
  ∀ l1 l2,
  (eval_pterm_list st l1 + eval_pterm_list st l2)%Z =
    eval_pterm_list st (merge_monom (l1, l2)).
Proof.
  strong_list_induction.
  intros n IH [| [c1 v1] l1] [| [c2 v2] l2] Hlen;
  rewrite merge_monom_equation; auto using Z.add_0_r.
  destruct (cmp_vars v1 v2) eqn:?; simpl in *.
  - pose proof (cmp_vars_eq_iff _ _ Heqc); subst.
    rewrite <- (IH (len2 (l1, l2))); simpl; try lia.
    repeat rewrite <- Z.add_assoc.
    f_equal.
    now rewrite Z.add_comm, <- Z.add_assoc, fold_left_mul_add_distr.
  - rewrite <- (IH (1+len2(l1, l2))); simpl; lia.
  - rewrite <- (IH (1+len2(l1, l2))); simpl; lia.
Qed.

Lemma split_len_strict:
    forall {X} (l:list X) (l1 l2: list X) a b,
    split (a::b::l) = (l1,l2) ->
    List.length l1 < List.length (a::b::l) /\
    List.length l2 < List.length (a::b::l).
Proof.
  intros.
  simpl in H.
  destruct (split l) eqn:?.
  specialize (split_len _ _ _ Heqp) as ?.
  inv H.
  simpl in *. lia.
Qed.

Lemma split_eval_pt_correct :
  ∀ l l1 l2, split l = (l1, l2) →
  ∀ st, eval_pterm_list st l =
  (eval_pterm_list st l1 + eval_pterm_list st l2)%Z.
Proof.
  strong_list1_induction.
  intros n IH l Hlen l1 l2 Hsplit st.
  destruct l as [| [c1 v1] [| [c2 v2] l']] eqn:?;
  try now (inv Hsplit; auto using Z.add_0_r).
  simpl in Hsplit; destruct (split l') eqn:?.
  inversion Hsplit; simpl.
  repeat (simpl in Hlen; destruct n; [ now inversion Hlen | inversion Hlen ]).
  erewrite (IH n); try lia; eauto.
  lia.
Qed.

Lemma split_inl {A} :
  ∀ l l1 l2, split l = (l1, l2) →
  ∀ a : A, In a l → In a l1 \/ In a l2.
Proof.
  strong_list1_induction.
  intros n' IH l Hlen l1 l2 Hsplit x HIn.
  destruct l as [| a [| b l' ]] eqn:?;
  [ inv HIn | inv Hsplit; left; assumption |].
  simpl in *.
  destruct (split l') eqn:?; inversion Hsplit.
  destruct HIn as [HIn | [HIn | HIn]];
  [ subst; left; now left | subst; right; now left |].
  edestruct (IH (List.length l'));
  [ lia
  | reflexivity
  | eassumption
  | eassumption
  | left; right; assumption
  | right; right; assumption ].
Qed.

Lemma split_inr {A} :
  ∀ l l1 l2, split l = (l1, l2) →
  ∀ a : A, (In a l1 \/ In a l2) → In a l.
Proof.
  strong_list1_induction.
  intros n' IH l Hlen l1 l2 Hsplit x HIn.
  destruct l as [| a [| b l' ]] eqn:Eql;
  try now (inv Hsplit; destruct HIn as [HIn | HIn]; try now inversion HIn).
  inversion Hsplit; destruct (split l') eqn:Hsplit'. inversion H0.
  assert (In x l0 ∨ In x l3 → In x l'). {
    simpl in Hlen.
    apply (IH (List.length l')); auto; lia.
  }
  rewrite <- H1, <- H2 in HIn; inversion HIn as [[He | HIn'] | [He | HIn']];
  [ subst; now left | | subst; right; now left |];
  right; right; apply H; [ left | right ]; assumption.
Qed.

Lemma merge_monom_wf_preserving :
  ∀ l1 l2,
  pterm_list_well_formed l1 →
  pterm_list_well_formed l2 →
  pterm_list_well_formed (merge_monom (l1, l2)).
Proof.
  strong_list_induction.
  intros n' IH l1 l2 Hlen Hnz1 Hnz2.
  rewrite merge_monom_equation.
  destruct l1 as [| [c1 v1] l1'] eqn:Eql1,
           l2 as [| [c2 v2] l2'] eqn:Eql2; auto.
  destruct (cmp_vars v1 v2) eqn:?.
  - inversion Hnz1; inversion Hnz2; constructor; auto.
    apply (IH (len2 (l1', l2'))); simpl in *; subst; auto; lia.
  - inversion Hnz1; inversion Hnz2; constructor; auto.
    apply (IH (1+len2 (l1', l2'))); simpl in *; subst; auto; lia.
  - inversion Hnz1; inversion Hnz2; constructor; auto.
    apply (IH (1+len2 (l1', l2'))); simpl in *; subst; auto; lia.
Qed.

Lemma merge_monom_nz_preserving :
  ∀ l1 l2,
  no_zero_powers l1 →
  no_zero_powers l2 →
  no_zero_powers (merge_monom (l1, l2)).
Proof.
  strong_list_induction.
  intros n' IH l1 l2 Hlen Hnz1 Hnz2.
  rewrite merge_monom_equation.
  destruct l1 as [| [c1 v1] l1'] eqn:Eql1,
           l2 as [| [c2 v2] l2'] eqn:Eql2; auto.
  destruct (cmp_vars v1 v2) eqn:?.
  - inversion Hnz1; inversion Hnz2; constructor; auto.
    apply (IH (len2 (l1', l2'))); simpl in *; subst; auto; lia.
  - inversion Hnz1; inversion Hnz2; constructor; auto.
    apply (IH (1+len2 (l1', l2'))); simpl in *; subst; auto; lia.
  - inversion Hnz1; inversion Hnz2; constructor; auto.
    apply (IH (1+len2 (l1', l2'))); simpl in *; subst; auto; lia.
Qed.

Theorem reduce_monomials_correct :
  ∀ l, l ≡ₗ (reduce_monomials l).
Proof.
  strong_list_induction.
  intros n IH [| [c1 v1] [| [c2 v2] l]] Hlen st;
  rewrite reduce_monomials_equation; auto.
  destruct (split (PTerm c1 v1 :: PTerm c2 v2 :: l)) eqn:?.
  specialize (split_len_strict  _ _ _ _ _ Heqp) as [Hlen0 Hlen1]; 
  rewrite <- merge_monom_correct; simpl.
  simpl in Heqp.
  erewrite <- (IH (List.length l0)); try lia;
  erewrite <- (IH (List.length l1)); try lia; clear Hlen0 Hlen1.
  simpl in *.
  destruct (split l) eqn:Hsp; inversion Heqp.
  simpl in *.
  rewrite (split_eval_pt_correct _ _ _ Hsp).
  lia.
Qed.

Theorem reduce_monomials_well_formed_preserving : ∀ l : list pterm,
  pterm_list_well_formed l →
  pterm_list_well_formed (reduce_monomials l).
Proof.
  strong_list_induction.
  intros n IH l Hlen Hwf; rewrite reduce_monomials_equation.
  destruct l as [| [c1 ?] [| [c2 ?] l']] eqn:?; auto.
  destruct (split (PTerm c1 vars :: PTerm c2 vars0 :: l')) eqn:?.
  specialize (split_len_strict _ _ _ _ _ Heqp) as [? ?].
  rewrite <- Heql0 in *; clear Heql0 l'.
  unfold pterm_list_well_formed in *.
  apply merge_monom_wf_preserving;
  [ apply (IH (List.length l0)) | apply (IH (List.length l1)) ];
  remember (λ '(PTerm _ vars), sorted_uniq vars) as P;
  try (subst; simpl in *; lia).
  - apply Forall_forall; intros x HIn.
    specialize (split_inr _ _ _ Heqp _ (or_introl HIn)).
    now apply Forall_forall.
  - apply Forall_forall; intros x HIn.
    specialize (split_inr _ _ _ Heqp _ (or_intror HIn)).
    now apply Forall_forall.
Qed.

Theorem reduce_monomials_no_zeros_preserving : ∀ l : list pterm,
  no_zero_powers l →
  no_zero_powers (reduce_monomials l).
Proof.
  strong_list_induction.
  intros n IH l Hlen Hwf; rewrite reduce_monomials_equation.
  destruct l as [| [c1 ?] [| [c2 ?] l']] eqn:?; auto.
  destruct (split (PTerm c1 vars :: PTerm c2 vars0 :: l')) eqn:?.
  specialize (split_len_strict _ _ _ _ _ Heqp) as [? ?].
  rewrite <- Heql0 in *; clear Heql0 l'.
  unfold no_zero_powers in *.
  apply merge_monom_nz_preserving;
  [ apply (IH (List.length l0)) | apply (IH (List.length l1)) ];
  remember (λ '(PTerm _ vars), Forall (λ '(_, n), n ≠ 0) vars) as P;
  try (subst; simpl in *; lia).
  - apply Forall_forall; intros x HIn.
    specialize (split_inr _ _ _ Heqp _ (or_introl HIn)).
    now apply Forall_forall.
  - apply Forall_forall; intros x HIn.
    specialize (split_inr _ _ _ Heqp _ (or_intror HIn)).
    now apply Forall_forall.
Qed.


