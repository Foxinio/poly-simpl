Require Import Utf8.
From Coq Require Import Recdef Wf_nat.
From Coq Require Import Bool.Bool Lia Lists.List Strings.String.
From Coq Require Import ZArith ZArith.Int.
Require Import Syntax Utils ClearZP.

Import ListNotations.

Theorem clear_zero_powers_correct (l : list pterm) :
  l ≡ₗ clear_zero_powers l.
Proof.
  induction l as [| [c vars] l]; intros st; auto.
  cbn.
  rewrite IHl.
  f_equal.
  clear IHl l.
  induction vars as [| [x ?] l]; auto.
  cbn.
  destruct (Nat.eqb_spec n 0); subst.
  - change (Z.of_nat 0)%Z with 0%Z.
    now rewrite Z.pow_0_r, <- IHl, Z.mul_1_r.
  - rewrite map_spec, fold_left_spec.
    now rewrite <- fold_left_mul_acc, IHl, fold_left_mul_acc.
Qed.

Lemma clear_zero_powers_vl_mono (l : var_list) :
  ∀ a, In a (clear_zero_powers_vl l) → In a l.
Proof.
  induction l as [| [x n] l ]; auto; simpl; intros [x' ?].
  destruct (Nat.eqb_spec n 0); intro H; [| inv H ].
  - right; apply IHl, H.
  - left; assumption.
  - right; apply IHl, H0.
Qed.

Lemma clear_zero_powers_sorted_pres (v : var_list) :
  sorted_uniq v → sorted_uniq (clear_zero_powers_vl v).
Proof.
  induction v as [| [x ?] vars]; intros; auto; simpl.
  destruct (Nat.eqb_spec n 0); simpl; subst.
  - eapply IHvars, sorted_uniq_cons, H.
  - pose proof (sorted_forall _ _ H) as H0.
    pose proof (sorted_uniq_cons _ _ H) as H1.
    apply sorted_forall_inv; [ apply IHvars, H1 |].
    apply Forall_forall; intros [x0 ?] HIn0.
    apply clear_zero_powers_vl_mono in HIn0.
    enough (∀ p, In p vars → (fst (x, n) <? fst p)%string = true).
    + subst; apply H2, HIn0.
    + apply Forall_forall; subst; assumption.
Qed.

Theorem clear_zero_powers_well_formed_preserving (l : list pterm) :
  pterm_list_well_formed l →
  pterm_list_well_formed (clear_zero_powers l).
Proof.
  induction l as [| [c vars] l]; intro H; auto.
  inv H. constructor; [| apply IHl, H3 ].
  apply clear_zero_powers_sorted_pres, H2.
Qed.

Lemma clear_zero_powers_vl_no_zeros (l : var_list) :
  sorted_uniq l → Forall (λ '(_, n), n <> 0) (clear_zero_powers_vl l).
Proof.
  induction l as [| [x ?] l]; simpl; intro H; auto.
  destruct (Nat.eqb_spec n 0).
  - eapply IHl, sorted_uniq_cons, H.
  - constructor; auto.
    eapply IHl, sorted_uniq_cons, H.
Qed.

Theorem clear_zero_powers_no_zeros (l : list pterm) :
  pterm_list_well_formed l →
  no_zero_powers (clear_zero_powers l).
Proof.
  induction l as [| [c vars] l]; simpl; intros H; auto.
  inv H.
  unfold no_zero_powers; constructor.
  - apply clear_zero_powers_vl_no_zeros, H2.
  - apply IHl; assumption.
Qed.

