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

Print Assumptions poly_simpl_correctness.

Fixpoint grouped_eval_pl (st : state) (l : list (list pterm)) :=
  match l with
  | [] => 0%Z
  | ls :: l' => (eval_pterm_list st ls + grouped_eval_pl st l')%Z
  end.

Lemma grouped_eval_pl_correct l st :
  grouped_eval_pl st l = eval_pterm_list st (List.concat l).
Proof.
  induction l; auto; simpl.
  now rewrite eval_pterm_list_homo, IHl.
Qed.

Definition grouped_eval_equiv l1 l2 :=
  ∀ st, grouped_eval_pl st l1 = grouped_eval_pl st l2. 
Hint Unfold grouped_eval_equiv : core.
Notation "a '≡ₚ' b" := (grouped_eval_equiv a b) (at level 70).

Definition pterm_equiv (p1 p2 : pterm) :=
  let '(PTerm _ v1) := p1 in
  let '(PTerm _ v2) := p2 in
  v1 = v2.
Definition pterm_equiv_dec :
  ∀ l1 l2 : pterm, {pterm_equiv l1 l2} + {¬ pterm_equiv l1 l2}.
Proof.
  intros [c1 v1] [c2 v2]; simpl.
  apply list_eq_dec.
  intros [x n] [y m].
  destruct (Nat.eq_dec n m), (string_dec x y);
  try now (left; f_equal; auto).
  all: right; intro Heq; inv Heq; auto.
Qed.

Instance Equivalence_pterm_equiv : Equivalence pterm_equiv.
Proof.
  split; unfold Reflexive, Symmetric, Transitive, pterm_equiv;
  [ intros [_ v]
  | intros [_ v1] [_ v2]
  | intros [_ v1] [_ v2] [_ v3] Eq12 Eq23]; auto;
  now transitivity v2.
Qed.

Inductive equiv_list : list pterm → Prop :=
  | EL_Single a :
      equiv_list [a]
  | EL_Cons a b l :
      equiv_list (a :: l) →
      pterm_equiv a b →
      equiv_list (b :: a :: l).
Hint Constructors equiv_list : core.

Inductive Disjoint : list (list pterm) → Prop :=
  | disjoint_nil : Disjoint []
  | disjoint_single l :
      equiv_list l →
      Disjoint [l]
  | disjoint_cons p p' (l l' : list pterm) (ls : list (list pterm)) :
      equiv_list (p::l) →
      ~In (p'::l') ls →
      pterm_equiv p p' →
      Disjoint ls →
      Disjoint ((p::l)::ls).
Hint Constructors Disjoint : core.

Definition grouped_pterms (l : list (list pterm)) :=
  Forall equiv_list l /\ Disjoint l.
Hint Unfold grouped_pterms : core.

Fixpoint Disjoint_covered_dec (ls : list (list pterm)) (p : pterm) :
  grouped_pterms ls →
  { l1 & {p' & {l & {l2 | ls = l1 ++ (p'::l) :: l2 /\ pterm_equiv p p' }}}} +
  { ~exists l1 p' l l2, ls = l1 ++ (p'::l) :: l2 /\ pterm_equiv p p' }.
Proof.
  intros H.
  destruct ls as [| [| p' l] ls'].
  - right; intros [l1 [p' [l [l2 [Hdiv Heqv]]]]].
    assert (Contra: List.length (l1 ++ (p'::l) :: l2) = List.length (A:=list pterm) []).
    { now rewrite Hdiv. }
    rewrite length_app in Contra; simpl in Contra.
    rewrite Nat.add_comm in Contra; simpl in Contra.
    discriminate.
  - exfalso; inv H; inv H1; inv H2.
  - destruct (pterm_equiv_dec p p').
    + left. exists [], p', l, ls'; split; auto.
    + destruct (Disjoint_covered_dec ls' p) as [[l1 [p'' [l' [l2 [Hdiv Heqv]]]]] | ?];
      [ inv H; inv H0; inv H1; auto | |].
      { left; exists ((p'::l)::l1), p'', l', l2; split; auto.
        now rewrite Hdiv. }
      { right; intros [l1 [p'' [l' [l2 [Hdiv Heqv]]]]].
        apply n0.
        destruct l1 as [| [| p''' l'''] l1' ]; inv Hdiv.
        - exfalso; apply n, Heqv.
        - exists l1', p'', l', l2; split; auto. }
Defined.

Theorem Disjoint_perm: forall al bl,
  Permutation al bl ->
  Disjoint al -> Disjoint bl.
Proof.
Admitted.

Theorem grouped_eval_perm : forall al bl,
  Permutation al bl ->
  (∀ st, grouped_eval_pl st al = grouped_eval_pl st bl).
Proof.
Admitted.

Lemma group_pter_impl_perm_helper l1 : ∀ (p p' : pterm) l' l2,
  Permutation (p :: List.concat (l1 ++ (p' :: l') :: l2))
    (List.concat (l1 ++ (p :: p' :: l') :: l2)).
Proof.
  induction l1; simpl; intros; auto.
  etransitivity;
  [ rewrite app_spec; eapply Permutation_app; [| reflexivity ];
    apply Permutation_cons_append |].
  rewrite <- app_assoc; apply Permutation_app; auto.
  simpl. apply IHl1.
Qed.

Fixpoint group_pterms_impl (l : list pterm) (ls : list (list pterm)) {struct l} :
    grouped_pterms ls →
    { ls' : list (list pterm) | grouped_pterms ls' /\
        Permutation (l ++ List.concat ls) (List.concat ls')  }.
Proof.
  intro Hls;
  destruct l; [ exists ls; split; [ apply Hls | reflexivity ] |].
  destruct (Disjoint_covered_dec ls p Hls)
    as [[l1 [p' [l' [l2 [Hdiv Heqv]]]]] | Contra].
    - remember (l1 ++ (p :: p' :: l') :: l2) as ls'.
      assert (Perm1: Permutation (((p :: p' :: l') :: l1) ++ l2) ls').
      { eapply Permutation_trans; subst ls'; [| apply Permutation_app_comm ].
        simpl; apply perm_skip.
        apply Permutation_app_comm. }
      assert (Perm2: Permutation (l1 ++ (p' :: l') :: l2) (((p' :: l') :: l1) ++ l2)).
      { eapply Permutation_trans; [ apply Permutation_app_comm |].
        simpl; apply perm_skip.
        apply Permutation_app_comm. }
      destruct Hls as [HFa Hdis].
      destruct (group_pterms_impl l ls') as [ls_res [Hgp_res HPerm_res]].
      { split; subst ls'.
      - apply (Forall_perm _ (((p :: p' :: l') :: l1) ++ l2)); auto.
        apply (Forall_perm _ _ (((p' :: l') :: l1) ++ l2)) in HFa; subst ls; auto.
        inv HFa; simpl.
        constructor; auto.
        constructor; [| symmetry ]; assumption.
      - eapply Disjoint_perm; eauto.
        eapply Disjoint_perm in Hdis; [| subst ls; apply Perm2 ].
        inv Hdis;
        [ assert (l1=[] /\ l2=[]) as [? ?];
          [ destruct l1, l2; try discriminate; auto |]; subst;
          rewrite app_nil_r; constructor;
          constructor; [| symmetry ]; auto |].
        simpl; econstructor; eauto.
        * constructor; [| symmetry ]; auto.
        * etransitivity; eassumption.
      }
      exists ls_res; split; [ assumption |].
      etransitivity; [| eassumption ]; subst ls ls'.
      transitivity ((l ++ [p]) ++ List.concat (l1 ++ (p' :: l') :: l2));
      [ apply Permutation_app; auto using Permutation_cons_append |].
      rewrite <- app_assoc.
      apply Permutation_app; auto; simpl.
      apply group_pter_impl_perm_helper.
    - destruct Hls as [HFa Hdis].
      destruct (group_pterms_impl l ([p]::ls)) as [ls_res [Hgp_res HPerm_res]].
      { split.
        - constructor; auto.
        - apply (disjoint_cons _ p _ []); auto.
          * intro HIn.
            pose proof (In_witness _ _ HIn) as [l1 [l2 Hdiv]].
            apply Contra. repeat eexists; eauto; reflexivity.
          * reflexivity.
      }
      exists ls_res; split; [ assumption |].
      etransitivity; [| eassumption ].
      transitivity ((l ++ [p]) ++ List.concat ls);
      [ apply Permutation_app; auto using Permutation_cons_append |].
      rewrite <- app_assoc.
      apply Permutation_app; auto; simpl.
Defined.

Definition group_pterms (l : list pterm) : 
    { ls' : list (list pterm) | grouped_pterms ls' /\
        Permutation l (List.concat ls')  }.
Proof.
  assert (grouped_pterms []) by (split; constructor).
  specialize (group_pterms_impl l [] H); simpl; intros res.
  rewrite app_nil_r in res.
  apply res.
Defined.

Lemma group_pterms_permutates l ls :
  ∀ H,
  group_pterms l = exist _ ls H →
  Permutation l (List.concat ls).
Proof.
  intros [_ H] _; apply H.
Qed.

Lemma grouping_exists l :
  ∃ ls, grouped_pterms ls /\ List.concat ls ≡ᵥ l /\
  (* Permutation (List.concat ls) l /\ *)
  (* ↑ this can be difficult to prove, but probably essential *)
  (∀ st, grouped_eval_pl st ls = eval_pterm_list st l).
(* Extend this lemma to assure well formedness and no zero powers for ls *)
Proof.
  induction l as [| [c v] l']; unfold grouped_pterms.
  { exists []; split; [ split | split ]; auto. }
  destruct IHl' as [ls [[HFa Hdis] [Hvareqv Hlseqv]]]; auto.
  destruct (Disjoint_covered_dec ls (PTerm c v))
      as [[l1 [p' [l [l2 [Hdiv Heqv]]]]] | Contra]; auto.
  + subst ls; exists (l1 ++ (PTerm c v::p'::l) :: l2).
    assert (Perm1: Permutation (((PTerm c v :: p' :: l) :: l1) ++ l2)
                               (l1 ++ (PTerm c v :: p' :: l) :: l2)).
    { eapply Permutation_trans; [| apply Permutation_app_comm ].
      simpl; apply perm_skip.
      apply Permutation_app_comm. }
    assert (Perm2: Permutation (l1 ++ (p' :: l) :: l2) (((p' :: l) :: l1) ++ l2)).
    { eapply Permutation_trans; [ apply Permutation_app_comm |].
      simpl; apply perm_skip.
      apply Permutation_app_comm. }
    repeat split.
    - apply (Forall_perm _ (((PTerm c v :: p' :: l) :: l1) ++ l2)); auto.
      apply (Forall_perm _ _ (((p' :: l) :: l1) ++ l2)) in HFa; auto.
      inv HFa; simpl.
      constructor; auto.
      constructor; [| symmetry ]; assumption.
    - eapply Disjoint_perm; eauto.
      eapply Disjoint_perm in Hdis; [| apply Perm2 ].
      inv Hdis;
      [ assert (l1=[] /\ l2=[]) as [? ?];
        [ destruct l1, l2; try discriminate; auto |]; subst;
        rewrite app_nil_r; constructor;
        constructor; [| symmetry ]; auto |].
      simpl; econstructor; eauto.
      * constructor; [| symmetry ]; auto.
      * etransitivity; eassumption.
    - intro vars.
      symmetry in Perm1.
      rewrite (vlequiv_list_perm _ _ Perm1).
      remember (p' :: l) as l''.
      simpl.
      rewrite <- Hvareqv.
      subst l''.
      now rewrite (vlequiv_list_perm _ _ Perm2).
    - intro st; simpl.
      rewrite <- Hlseqv.
      erewrite grouped_eval_perm; [| symmetry; exact Perm1 ].
      symmetry.
      erewrite grouped_eval_perm; [| exact Perm2 ].
      simpl; lia.
  + exists ([PTerm c v] :: ls).
    repeat split.
    - constructor; auto.
    - apply (disjoint_cons _ (PTerm c v) _ []); auto.
      * intro HIn.
        pose proof (In_witness _ _ HIn) as [l1 [l2 Hdiv]].
        apply Contra. repeat eexists; eauto; reflexivity.
      * reflexivity.
    - intros vars; simpl.
      now rewrite Hvareqv.
    - intros st; simpl; rewrite Hlseqv; lia.
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


