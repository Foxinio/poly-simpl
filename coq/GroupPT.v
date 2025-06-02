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

Fixpoint group_pterms (l : list pterm) {struct l} :
    { ls' : list (list pterm) | grouped_pterms ls' /\
        Permutation l (List.concat ls')  }.
Proof.
  destruct l; [ exists []; split; repeat constructor |].
  destruct (group_pterms l) as [ls_res [Hgp_res  HPerm_res]].
  destruct (Disjoint_covered_dec ls_res p Hgp_res)
    as [[l1 [p' [l' [l2 [Hdiv Heqv]]]]] | Contra];
  destruct Hgp_res as [HFaeqv_res HDis_res].
  - remember (l1 ++ (p :: p' :: l') :: l2) as ls'.
    assert (Perm1: Permutation (((p :: p' :: l') :: l1) ++ l2) ls').
    { eapply Permutation_trans; subst ls'; [| apply Permutation_app_comm ].
      simpl; apply perm_skip.
      apply Permutation_app_comm. }
    assert (Perm2: Permutation (l1 ++ (p' :: l') :: l2) (((p' :: l') :: l1) ++ l2)).
    { eapply Permutation_trans; [ apply Permutation_app_comm |].
      simpl; apply perm_skip.
      apply Permutation_app_comm. }
    exists ls'.
    { repeat split; subst ls_res ls'.
    - apply (Forall_perm _ (((p :: p' :: l') :: l1) ++ l2)); auto.
      apply (Forall_perm _ _ (((p' :: l') :: l1) ++ l2)) in HFaeqv_res; auto.
      inv HFaeqv_res; simpl.
      constructor; auto.
      constructor; [| symmetry ]; assumption.
    - eapply Disjoint_perm; eauto.
      eapply Disjoint_perm in HDis_res; [| apply Perm2 ].
      inv HDis_res;
      [ assert (l1=[] /\ l2=[]) as [? ?];
        [ destruct l1, l2; try discriminate; auto |]; subst;
        rewrite app_nil_r; constructor;
        constructor; [| symmetry ]; auto |].
      simpl; econstructor; eauto.
      * constructor; [| symmetry ]; auto.
      * etransitivity; eassumption.
    - rewrite Permutation_app_comm in HPerm_res.
      rewrite Permutation_app_comm; simpl; simpl in HPerm_res.
      apply perm_skip, HPerm_res.
    }
  - exists ([p]::ls_res).
    { repeat split.
    - constructor; [ constructor | assumption ].
    - apply (disjoint_cons _ p _ []); auto; try reflexivity.
      intro HIn.
      pose proof (In_witness _ _ HIn) as [l1 [l2 Hdiv]].
      apply Contra. repeat eexists; eauto; reflexivity.
    - simpl; apply perm_skip, HPerm_res.
    }
Defined.

Lemma group_pterms_permutates l ls :
  ∀ H,
  group_pterms l = exist _ ls H →
  Permutation l (List.concat ls).
Proof.
  intros [_ H] _; apply H.
Qed.

Lemma group_pterms_wf_preserving l :
  ∀ ls,
  (proj1_sig (group_pterms l)) = ls →
  pterm_list_well_formed l →
  Forall pterm_list_well_formed ls.
Proof.
  induction l as [| p l];
  [ unfold group_pterms; simpl; intros; subst; auto |].
  simpl; intros; subst.
  destruct (group_pterms l) as [ls [Hgp Hperm]]; simpl.
  destruct (Disjoint_covered_dec ls p Hgp).
  - destruct s as [l1 s], s as [p' s], s as [l' s], s as [l2 s],
             s as [Hgp_res Hperm_res], Hgp as [HFaeqv HDis]; simpl.
    specialize (IHl ls); simpl in IHl.
    auto_specialize IHl.
    inv H0.
    auto_specialize IHl.
    apply (Forall_perm _ (((p :: p' :: l') :: l1) ++ l2)); auto.
    { eapply Permutation_trans; [| apply Permutation_app_comm ].
      simpl; apply perm_skip.
      apply Permutation_app_comm. }
    apply (Forall_perm _ _ (((p' :: l') :: l1) ++ l2)) in IHl.
    2: { eapply Permutation_trans; [ apply Permutation_app_comm |].
      simpl; apply perm_skip.
      apply Permutation_app_comm. }
    simpl in *.
    inv IHl; auto.
  - destruct Hgp as [HFaeqv HDis]; simpl.
    specialize (IHl ls); simpl in IHl.
    auto_specialize IHl.
    inv H0.
    auto_specialize IHl.
    constructor; auto.
Qed.

Lemma group_pterms_nz_preserving l :
  ∀ ls,
  (proj1_sig (group_pterms l)) = ls →
  no_zero_powers l →
  Forall no_zero_powers ls.
Proof.
Admitted.

