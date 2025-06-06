Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia Recdef Wf_nat.
From Coq Require Import Bool.Bool Lists.List Strings.String Sorting.Sorted.
Import ListNotations.

From PolySimpl Require Import Syntax Utils BasicProps Algorithm VarList.

Lemma merge_monom_correct (st : state) :
  ∀ l1 l2,
  (eval_pterm_list st l1 + eval_pterm_list st l2)%Z =
    eval_pterm_list st (mergesort_monom (l1, l2)).
Proof.
  strong_list_induction.
  intros n IH [| [c1 v1] l1] [| [c2 v2] l2] Hlen;
  rewrite mergesort_monom_equation; auto using Z.add_0_r.
  destruct (cmp_vars v1 v2) eqn:?; simpl in *.
  - pose proof (cmp_vars_eq_iff _ _ Heqc); subst.
    rewrite <- (IH (1+len2 (l1, l2))); simpl; try lia.
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
  pterm_list_well_formed (mergesort_monom (l1, l2)).
Proof.
  strong_list_induction.
  intros n' IH l1 l2 Hlen Hnz1 Hnz2.
  rewrite mergesort_monom_equation.
  destruct l1 as [| [c1 v1] l1'] eqn:Eql1,
           l2 as [| [c2 v2] l2'] eqn:Eql2; auto.
  destruct (cmp_vars v1 v2) eqn:?.
  - inversion Hnz1; inversion Hnz2; constructor; auto.
    apply (IH (1+len2 (l1', l2'))); simpl in *; subst; auto; lia.
  - inversion Hnz1; inversion Hnz2; constructor; auto.
    apply (IH (1+len2 (l1', l2'))); simpl in *; subst; auto; lia.
  - inversion Hnz1; inversion Hnz2; constructor; auto.
    apply (IH (1+len2 (l1', l2'))); simpl in *; subst; auto; lia.
Qed.

Lemma merge_monom_nz_preserving :
  ∀ l1 l2,
  no_zero_powers l1 →
  no_zero_powers l2 →
  no_zero_powers (mergesort_monom (l1, l2)).
Proof.
  strong_list_induction.
  intros n' IH l1 l2 Hlen Hnz1 Hnz2.
  rewrite mergesort_monom_equation.
  destruct l1 as [| [c1 v1] l1'] eqn:Eql1,
           l2 as [| [c2 v2] l2'] eqn:Eql2; auto.
  destruct (cmp_vars v1 v2) eqn:?.
  - inversion Hnz1; inversion Hnz2; constructor; auto.
    apply (IH (1+len2 (l1', l2'))); simpl in *; subst; auto; lia.
  - inversion Hnz1; inversion Hnz2; constructor; auto.
    apply (IH (1+len2 (l1', l2'))); simpl in *; subst; auto; lia.
  - inversion Hnz1; inversion Hnz2; constructor; auto.
    apply (IH (1+len2 (l1', l2'))); simpl in *; subst; auto; lia.
Qed.

Lemma mergesort_monomials_sorted1 : forall x x1 l1 x2 l2,
    pterm_le x x1 -> pterm_le x x2 ->
    sorted (mergesort_monom (x1::l1, x2::l2)) ->
    sorted (x :: mergesort_monom (x1::l1, x2::l2)).
Proof.
  intros.
  rewrite mergesort_monom_equation in *.
  destruct x1 as [c1 v1], x2 as [c2 v2].
  destruct (cmp_vars v1 v2);
  constructor; assumption.
Qed.

Lemma mergesort_monomials_sorted : forall l1, sorted l1 ->
                     forall l2, sorted l2 ->
                     sorted (mergesort_monom (l1, l2)).
Proof.
  induction l1 as [| [c1 v1] l1]; intros;
  [ simpl; destruct l2; auto |].
  induction l2 as [| [c2 v2] l2]; rewrite mergesort_monom_equation; auto.
  cbn.
  enough (cmp_vars v1 v2 = Lt → sorted (PTerm c1 v1 :: mergesort_monom (l1, PTerm c2 v2 :: l2)));
  [ enough (cmp_vars v1 v2 <> Lt → sorted (PTerm c2 v2 :: mergesort_monom (PTerm c1 v1 :: l1, l2))) |];
  [ (destruct (cmp_vars v1 v2); auto); apply H2; intro HC; discriminate | |]; intro HLt.
  - assert (∀ v1 v2, cmp_vars v1 v2 <> Lt → cmp_vars v2 v1 <> Gt). {
      clear; intros v1 v2 HLt.
      intro C. apply HLt. rewrite cmp_vars_antisym.
      unfold CompOpp. now rewrite C. }
    destruct l2 as [| [c2' v2'] l2];
    [ constructor; unfold pterm_le; auto |].
    inv H0; unfold pterm_le in *; simpl in *.
    apply mergesort_monomials_sorted1; unfold pterm_le; auto; simpl.
  - assert (∀ v1 v2, cmp_vars v1 v2 = Lt → cmp_vars v1 v2 <> Gt). {
      clear; simpl; intros v1 v2 HLt HGt.
      rewrite HGt in HLt; discriminate. }
    destruct l1 as [| [c1' v1'] l1];
    [ constructor; unfold pterm_le; auto |].
    inv H; unfold pterm_le in *; simpl in *.
    apply mergesort_monomials_sorted1; unfold pterm_le; auto; simpl.
Qed.

Lemma vars_pow_add v c1 c2 st :
  (fold_left Z.mul (map (pow st) v) c2 + fold_left Z.mul (map (pow st) v) c1)%Z =
  fold_left Z.mul (map (pow st) v) (c1 + c2)%Z.
Proof.
  induction v; simpl; try lia.
  repeat rewrite <- fold_left_mul_acc.
  now rewrite <- Z.mul_add_distr_r, <- IHv.
Qed.

Lemma HdRel_pterm_le_const_invariant c1 c2 v l :
  HdRel pterm_le (PTerm c2 v) l →
  HdRel pterm_le (PTerm c1 v) l.
Proof.
  induction l; auto.
  intros H. inv H.
  econstructor; apply H1.
Qed.

Lemma reduce_monomials_HdRel_pterm_le :
  ∀ l c1 c2 v1 v2,
  cmp_vars v1 v2 = Lt →
  sorted (PTerm c1 v1 :: PTerm c2 v2 :: l) →
  HdRel pterm_le (PTerm c1 v1) (reduce_monomials (PTerm c2 v2 :: l)).
Proof.
  strong_list_induction.
  intros n' IH l Hlen c1 c2 v1 v2 Hcmp Hsort.
  destruct l as [| [c3 v3] l'] eqn:?; auto;
  rewrite reduce_monomials_equation.
  { destruct (Z.eqb_spec c2 0); auto.
    constructor. unfold pterm_le; simpl.
    intro H; rewrite H in Hcmp; discriminate. }
  destruct (cmp_vars v2 v3) eqn:?.
  - simpl in *.
    apply (IH (List.length l')); try (subst; simpl; lia); auto.
    pose proof (cmp_vars_eq_iff _ _ Heqc); subst v3.
    apply Sorted_LocallySorted_iff.
    apply Sorted_LocallySorted_iff in Hsort.
    inv Hsort. inv H1. inv H3.
    econstructor.
    + econstructor; auto.
      eapply HdRel_pterm_le_const_invariant, H5.
    + inv H2.
      econstructor; unfold pterm_le in *; now simpl in *.
  - destruct (Z.eqb_spec c2 0).
    + apply Sorted_LocallySorted_iff, Sorted_StronglySorted in Hsort;
        [| apply Rel1_Transitive_pterm_le ].
      inversion Hsort; inversion H1.
      assert (StronglySorted pterm_le (PTerm c1 v1 :: PTerm c3 v3 :: l'))
        by (inv H2; econstructor; auto).
      simpl in Hlen; apply StronglySorted_Sorted, Sorted_LocallySorted_iff in H7;
      apply (IH (List.length l')); try (subst; simpl; lia); auto.
      eapply cmp_vars_trans; eauto.
    + econstructor.
      unfold pterm_le in *; simpl in *.
      intro HGt; rewrite HGt in Hcmp; discriminate.
  - inv Hsort. inv H1. unfold pterm_le in H5; simpl in H5.
    exfalso; apply H5, Heqc.
Qed.

Theorem sort_monomials_correct :
  ∀ l, l ≡ₗ (sort_monomials l).
Proof.
  strong_list_induction.
  intros n IH [| [c1 v1] [| [c2 v2] l]] Hlen st;
  rewrite sort_monomials_equation; auto.
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

Theorem sort_monomials_well_formed_preserving : ∀ l : list pterm,
  pterm_list_well_formed l →
  pterm_list_well_formed (sort_monomials l).
Proof.
  strong_list_induction.
  intros n IH l Hlen Hwf; rewrite sort_monomials_equation.
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

Theorem sort_monomials_no_zeros_preserving : ∀ l : list pterm,
  no_zero_powers l →
  no_zero_powers (sort_monomials l).
Proof.
  strong_list_induction.
  intros n IH l Hlen Hwf; rewrite sort_monomials_equation.
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

Theorem sort_monomials_sorts :
  ∀ l, sorted (sort_monomials l).
Proof.
  remember (λ (_ : list pterm) ls, LocallySorted pterm_le ls) as P.
  pose proof (sort_monomials_ind P); subst P; apply H; clear H;
  try now (intros; constructor).
  intros l la Heq Hc2 l1 l2 Hsplit Hsort1 Hsort2.
  apply mergesort_monomials_sorted; auto.
Qed.

Theorem reduce_monomials_correct :
  ∀ l, l ≡ₗ (reduce_monomials l).
Proof.
  apply reduce_monomials_ind; simpl; auto.
  - intros l z v Hl HEq st.
    apply Z.eqb_eq in HEq; subst.
    apply fold_left_mul_0.
  - intros l z1 v1 z2 v2 l' Hl HEq Heqv st.
    rewrite <- Heqv; simpl.
    pose proof (cmp_vars_eq_iff _ _ HEq); subst.
    rewrite <- Z.add_assoc. f_equal.
    apply vars_pow_add.
  - intros l z1 v1 z2 v2 l' Hl cmp_res HEq Hcmp Hnz Heqv st; simpl.
    pose proof (reflect_iff _ _ (Z.eqb_spec z1 0)) as Hreflect.
    apply Hreflect in Hnz; subst z1.
    rewrite fold_left_mul_0.
    rewrite <- Heqv; simpl; lia.
  - intros l z1 v1 z2 v2 l' Hl cmp_res HEq Hcmp Hnz Heqv st; simpl.
    rewrite <- Heqv; auto.
Qed.

Theorem reduce_monomials_sort_preserve :
  ∀ l, sorted l → sorted (reduce_monomials l).
Proof.
  strong_list_induction.
  intros n' IH l Hlen Hsort.
  destruct l as [| [c1 v1] l'] eqn:?; auto;
  destruct l' as [| [c2 v2] l''] eqn:?; auto;
  rewrite reduce_monomials_equation;
  [ destruct (Z.eqb_spec c1 0); auto; constructor |].
  destruct (cmp_vars v1 v2) eqn:?; [| destruct (Z.eqb_spec c1 0) |].
  - simpl in *.
    apply (IH (1+List.length l'')); try (subst; simpl; lia).
    inv Hsort.
    apply Sorted_LocallySorted_iff, Sorted_inv in H1.
    destruct H1.
    apply Sorted_LocallySorted_iff, Sorted_cons; auto.
    pose proof (cmp_vars_eq_iff _ _ Heqc); subst.
    eapply HdRel_pterm_le_const_invariant, H0.
  - inv Hsort.
    apply (IH (1+List.length l'')); auto;
      try (subst; simpl; lia).
  - apply Sorted_LocallySorted_iff, Sorted_cons.
    + simpl in *. inv Hsort.
      apply Sorted_LocallySorted_iff, (IH (1+List.length l'')); auto;
      subst; simpl; lia.
    + apply reduce_monomials_HdRel_pterm_le; auto.
  - inversion Hsort.
    unfold pterm_le in H3; simpl in H3.
    exfalso; apply H3, Heqc.
Qed.

Lemma reduce_clears_zeros :
  ∀ l, reduce_monomials l = [] → Forall (λ '(PTerm c _), c = 0%Z) l.
Admitted.

Lemma reduce_monom_not_rep1 :
  ∀ l' c1 c2 v1 v2 l1, cmp_vars v1 v2 = Lt →
  sorted (PTerm c1 v1 :: PTerm c2 v2 :: l') →
  PTerm c1 v1 :: l1 = PTerm c1 v1 :: reduce_monomials (PTerm c2 v2 :: l') →
  (∃ c3 v3 l2, l1 = PTerm c3 v3 :: l2 /\ cmp_vars v1 v3 = Lt) \/
    fold_left Z.add (map const (PTerm c2 v2 :: l')) 0%Z = 0%Z /\
    reduce_monomials (PTerm c2 v2 :: l') = [].
Proof.
  strong_list1_induction.
  intros n' IH l' Hlen c1 c2 v1 v2 l1 HLt Hsort Heq.
  destruct l' as [| [c3 v3] l''];
  [ rewrite reduce_monomials_equation in *; destruct (Z.eqb_spec c2 0);
    [ right; auto |] |];
  [ left; destruct l1; [ inv Heq; apply cmp_vars_refl_nlt in Heqc; contradiction |];
    inv Heq; repeat eexists; auto |].
  rewrite reduce_monomials_equation in Heq.
  destruct (cmp_vars v2 v3) eqn:?; [| destruct (Z.eqb_spec c2 0) |].
  - simpl in Hlen.
    edestruct (IH (List.length l'')) as [[c4 [v4 [l4 [Hsplit Hcmp]]]] | [Heqz Hl'nil]];
    try (subst; simpl; lia);
    [ reflexivity | apply HLt | | apply Heq | left; repeat eexists; eauto
    | right; rewrite reduce_monomials_equation, Heqc; split; auto ].
    pose proof (cmp_vars_eq_iff _ _ Heqc); subst v2.
    eapply sorted_const_invariant, sorted_shadow, Hsort.
  - pose proof (cmp_vars_trans _ _ _ HLt Heqc).
    edestruct (IH (List.length l'')) as [[c4 [v4 [l4 [Hsplit Hcmp]]]]|[Heqz Hl'nil]];
    try (subst; simpl; lia);
    [ reflexivity | apply H | | apply Heq | left; repeat eexists; eauto
    | right; rewrite reduce_monomials_equation, Heqc; split; auto ].
    + eapply sorted_const_invariant, sorted_shadow, Hsort.
    + apply reduce_clears_zeros in Hl'nil. inv Hl'nil.
      rewrite map_spec, fold_left_spec.
      replace (0+_)%Z with 0%Z by (simpl; lia); auto.
    + apply Z.eqb_eq in e; now rewrite e.
  - inversion Heq. destruct l1; inversion H0; subst p. simpl in Hlen.
    edestruct (IH (List.length l'')) as [[c4 [v4 [l4 [Hsplit Hcmp]]]]|[Heqz Hl'nil]];
    try (subst; simpl; lia);
    [ reflexivity | apply Heqc | | apply H0 | left; repeat eexists; eauto
    | left; repeat eexists; eauto ].
    inv Hsort; auto.
  - inv Hsort; inv H1. unfold pterm_le in H5; simpl in H5.
    exfalso. apply H5, Heqc.
Qed.

Lemma reduce_monomials_not_rep :
  ∀ l l' a, sorted l → a :: l' = reduce_monomials l →
    ~In a l'.
Proof.
  strong_list1_induction.
  intros n' IH l Hlen l' a Hsort Heq.
  intro HIn.
  edestruct (in_split _ _ HIn) as [l1 [l2 Hsplit]].
  subst l'.
  pose proof (reduce_monomials_sort_preserve _ Hsort).
  rewrite reduce_monomials_equation in Heq.
  destruct l as [| [c1 v1] [| [c2 v2] l']] eqn:?;
  [ inv Heq
  | destruct (Z.eqb_spec c1 0); [ inv Heq | inv Heq; destruct l1; inv H2 ] |].
  destruct (cmp_vars v1 v2) eqn:?; [| destruct (Z.eqb_spec c1 0) |].
  - assert (~In a (l1++a::l2)). {
      simpl in Hlen.
      (* inversion Hsort; clear Hsort. *)
      eapply (IH (1+List.length l')); try (subst; simpl; lia);
      [| | apply Heq ]; simpl; try lia.
      apply Sorted_LocallySorted_iff, Sorted_inv in Hsort; destruct Hsort.
      apply Sorted_inv in H0; destruct H0.
      apply Sorted_LocallySorted_iff, Sorted_cons; auto.
      destruct l' as [| [c3 v3] l']; constructor.
      pose proof (cmp_vars_eq_iff _ _ Heqc); subst v2.
      inv H2.
      unfold pterm_le in *; now simpl in *.
    }
    apply H0, HIn.
  - simpl in Hlen.
    eapply (IH (1+List.length l')); try (subst; simpl; lia);
    [| inv Hsort | apply Heq | ]; eauto; simpl; lia.
  - apply Z.eqb_neq in n.
    inversion Heq; subst a.
    rewrite reduce_monomials_equation, Heqc, n in H.
    remember H as HContra; clear HeqHContra; rewrite <- H2 in HContra.
    destruct (reduce_monom_not_rep1 _ _ _ _ _ _ Heqc Hsort Heq)
      as [[c3 [v3 [l'' [Hsplit Hcmp]]]]|[Heqz Hl'nil]].
    + destruct l1; inversion Hsplit;
        [ subst; apply cmp_vars_refl_nlt in Hcmp; contradiction |].
      subst p.
      apply Sorted_LocallySorted_iff, Sorted_StronglySorted in HContra;
      [| apply Rel1_Transitive_pterm_le ].
      simpl in HContra.
      inv HContra; inv H4.
      apply Forall_app in H6; destruct H6 as [? ?].
      inv H1; unfold pterm_le in H7; simpl in H7.
      apply H7. now rewrite cmp_vars_antisym, Hcmp.
    + rewrite Hl'nil in H2. destruct l1; inv H2.
  - inv Hsort. unfold pterm_le in H4; simpl in H4.
    apply H4, Heqc.
Qed.

Theorem reduce_monomials_canonical :
  ∀ l, sorted l → canon_pterm (reduce_monomials l).
Proof.
  strong_list_induction.
  intros n' IH l Hlen Hsort.
  destruct l as [| [c1 v1] l'] eqn:?; auto;
  destruct l' as [| [c2 v2] l''] eqn:?; auto;
  [ rewrite reduce_monomials_equation; simpl;
    destruct (Z.eqb_spec c1 0); [ auto | apply canon_pterm_single ] |].
  rewrite reduce_monomials_equation.
  destruct (cmp_vars v1 v2) eqn:?; [| destruct (Z.eqb_spec c1 0) |].
  - simpl in *.
    apply (IH (1+List.length l'')); try (subst; simpl; lia).
    inv Hsort.
    apply Sorted_LocallySorted_iff, Sorted_inv in H1.
    destruct H1.
    apply Sorted_LocallySorted_iff, Sorted_cons; auto.
    pose proof (cmp_vars_eq_iff _ _ Heqc); subst.
    eapply HdRel_pterm_le_const_invariant, H0.
  - inv Hsort.
    apply (IH (1+List.length l'')); auto; subst; simpl; lia.
  - apply Z.eqb_neq in n.
    apply canon_pterm_cons.
    + eapply reduce_monomials_not_rep; [ eassumption |].
      symmetry; now rewrite reduce_monomials_equation, Heqc, n.
    + simpl in *.
      apply (IH (1+List.length l'')); try (subst; simpl; lia).
      inv Hsort; assumption.
  - inv Hsort. unfold pterm_le in H3; simpl in H3.
    exfalso; apply H3, Heqc.
Qed.

Theorem reduce_monomials_non_zero_const :
  ∀ l, sorted l → non_zero_const (reduce_monomials l).
Proof.
  strong_list_induction.
  intros n' IH l Hlen Hsort.
  destruct l as [| [c1 v1] l'] eqn:?; auto;
  destruct l' as [| [c2 v2] l''] eqn:?; rewrite reduce_monomials_equation;
    [ destruct (Z.eqb_spec c1 0) |]; auto.
  destruct (cmp_vars v1 v2) eqn:?; [| destruct (Z.eqb_spec c1 0) |].
  - simpl in *.
    apply (IH (1+List.length l'')); try (subst; simpl; lia).
    inv Hsort.
    apply Sorted_LocallySorted_iff, Sorted_inv in H1.
    destruct H1.
    apply Sorted_LocallySorted_iff, Sorted_cons; auto.
    pose proof (cmp_vars_eq_iff _ _ Heqc); subst.
    eapply HdRel_pterm_le_const_invariant, H0.
  - inv Hsort.
    apply (IH (1+List.length l'')); auto; subst; simpl; lia.
  - constructor; auto.
    inv Hsort.
    apply (IH (1+List.length l'')); auto; subst; simpl; lia.
  - inv Hsort. unfold pterm_le in H3; simpl in H3.
    exfalso; apply H3, Heqc.
Qed.

  

