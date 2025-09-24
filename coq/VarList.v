From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Lia Bool.Bool Strings.String Lists.List Recdef Wf_nat Sorting.Permutation.
From Stdlib Require Import ZArith.Int ZArith Lists.List.
(* From Coq Require Import ssreflect. *)
Require Import Stdlib.Classes.Equivalence.
Import ListNotations.

Require Import Syntax Utils BasicProps Algorithm PFlattenProps.

Lemma In_vars_dec (v : var_list) (l : list pterm) :
  { In v (map vars l) } + {~In v (map vars l) }.
Proof.
  destruct In_dec with (a:=v) (l:=map vars l) as [ In | nIn ];
  [| left; apply In
  | right; apply nIn ].
  apply list_eq_dec; intros [x n] [y m].
  destruct (Nat.eq_dec n m) as [ HEqn | HnEqn ],
           (string_dec x y) as [ HEqx | HnEqx ];
    try (right; intro Contra; inv Contra; now auto).
    left; f_equal; auto.
Qed.

Lemma vars_rewrite (l1 l2 : list pterm) v :
  l1 ≡ᵥ l2 →
  { In v (map vars (l1++l2)) /\ cvar_count l1 v = cvar_count l2 v } +
  { (~In v (map vars (l1++l2)) /\ cvar_count l1 v = 0 /\ cvar_count l2 v = 0)%Z }.
Proof.
  intros.
  destruct (In_vars_dec v (l1++l2)).
  - left; split;  [ assumption | apply H, i ].
  - right; split; [ assumption |].
    assert (∀ l, ~In v (map vars l) → cvar_count l v = 0%Z). 
    { clear. induction l as [| [c v'] l']; simpl; intro H; auto.
      destruct (Decidable.not_or _ _ H).
      destruct (cmp_vars v' v) eqn:Eq; [ pose proof (cmp_vars_eq_iff _ _ Eq); exfalso; auto | |];
      apply IHl', H1. }
    rewrite map_app in n.
    split; apply H0; intro H1;
    apply n, in_or_app; [ left | right ]; apply H1.
Qed.

Lemma vars_nIn (v : var_list) (l : list pterm) :
  ~In v (map vars l) →
  cvar_count l v = 0%Z.
Proof.
  induction l as [| [ c v' ] l]; simpl; intros; auto.
  destruct (Decidable.not_or _ _ H).
  destruct (cmp_vars v' v) eqn:Eq;
  try apply IHl, H1.
  pose proof (cmp_vars_eq_iff _ _ Eq); exfalso; auto.
Qed.

Lemma vlequiv_app l1 l2 vars :
  cvar_count (l1++l2) vars = (cvar_count l1 vars + cvar_count l2 vars)%Z.
Proof.
  induction l1 as [| [c v] l1']; simpl; auto.
  rewrite IHl1'.
  destruct (cmp_vars v vars); lia.
Qed.

Lemma vlequiv_perm (la lb : list pterm) :
  Permutation la lb → vlequiv la lb.
Proof.
  generalize dependent lb.
  induction la as [| [c v] la']; simpl; intros lb HPerm vars HIn; auto.
  - pose proof (Permutation_nil HPerm); now subst.
  - symmetry in HPerm.
    pose proof (Permutation_vs_cons_inv HPerm) as [l1 [l2 Hdiv]]; subst.
    assert (Permutation ((PTerm c v) :: l1 ++ l2) ((PTerm c v) :: la'));
    [ etransitivity; [ eapply Permutation_middle | assumption] |].
    pose proof (Permutation_cons_inv H); symmetry in H0.
    rewrite vlequiv_app; simpl.
    rewrite (IHla' _ H0).
    + rewrite vlequiv_app.
      destruct (cmp_vars v vars); lia.
    + simpl in HIn.
Admitted.

Lemma vlequiv_skip l1 : ∀ a l2,
  vlequiv l1 l2 → vlequiv (a :: l1) (a :: l2).
Proof.
  induction l1; simpl; intros b l2 H vars HIn.
  - simpl; rewrite <- H.
    destruct b as [c v], (cmp_vars v vars); simpl; lia.
    admit.
  - remember (a::l1) as l1'.
    simpl; subst.
    rewrite H; [ now simpl |].
    admit.
Admitted.

Lemma cvar_count_app l1 : ∀ l2 v,
  cvar_count (l1++l2) v = (cvar_count l1 v + cvar_count l2 v)%Z.
Admitted.

Lemma vlequiv_skip_rev l1 : ∀ a l2,
  vlequiv l1 l2 → vlequiv (a :: l1) (l2 ++ [a]).
Proof.
  induction l1 as [| [c1 v1] l1]; simpl; intros b l2 H vars [Heq|HIn].
  - destruct (vars_rewrite _ _ vars H) as [[? ?] | [? [? ?]]].
    + simpl; rewrite vlequiv_app, <- H; auto.
    + now rewrite vlequiv_app, H2.
  - destruct (vars_rewrite _ _ vars H) as [[? ?] | [? [? ?]]].
    + simpl; rewrite vlequiv_app, <- H; auto.
    + now rewrite vlequiv_app, H2.
  - remember (PTerm c1 v1::l1) as l1'.
    simpl; subst vars.
    destruct b as [c v], (vars_rewrite _ _ v H) as [[? ?] | [? [? ?]]]; f_equal; simpl.
    + rewrite cvar_count_app, H1; simpl; rewrite cmp_vars_refl; lia.
    + rewrite cvar_count_app, H1; simpl; rewrite cmp_vars_refl; lia.
  - remember (PTerm c1 v1::l1) as l1'.
    simpl.
    destruct b as [c v], (vars_rewrite _ _ vars H) as [[? ?] | [? [? ?]]]; f_equal.
    + rewrite H1, cvar_count_app; simpl; destruct (cmp_vars v vars); lia.
    + rewrite H1, cvar_count_app; simpl; destruct (cmp_vars v vars); lia.
Qed.

Lemma vlequiv_list_perm (la lb : list(list pterm)) :
  Permutation la lb → vlequiv (List.concat la) (List.concat lb).
Proof.
Admitted.

Lemma polynom_difference :
  ∀ l1 l2, l1 ≡ₗ l2 ↔
  [] ≡ₗ (l1 ++ map flip_sign l2).
  (* ∀ st, 0%Z = (eval_pterm_list st l1 - eval_pterm_list st l2)%Z. *)
Proof.
  intros; split; intro. {
    intro st; rewrite eval_pterm_list_homo, H; clear.
    rewrite eval_pterm_list_map_flip; apply Zminus_diag_reverse.
  } {
    intro st; unfold ptequiv in *; specialize H with st.
    rewrite eval_pterm_list_homo, eval_pterm_list_map_flip in H.
    symmetry in H; pose proof (Zminus_eq _ _ H); auto.
  }
Qed.

Lemma var_list_canonality_helper l1 l2 :
  Exists (λ v : var_list, cvar_count l1 v ≠ cvar_count l2 v)
    (map vars (l1 ++ l2)) → ~(l1 ≡ₗ l2). 
Proof.
  intro H; apply Exists_exists in H; destruct H as [v [HIn Hneq]].
  intro; apply polynom_difference in H.
Admitted.

Theorem var_list_canonality :
  ∀ l1 l2, l1 ≡ₗ l2 →
  pterm_list_well_formed l1 → pterm_list_well_formed l2 →
  no_zero_powers l1 → no_zero_powers l2 →
  l1 ≡ᵥ l2.
Proof.
  intros l1 l2 Heqv Hwf1 Hwf2 Hnz1 Hnz2 v.
  unfold vlequiv.
  remember (λ v, cvar_count l1 v = cvar_count l2 v) as P.
  replace (cvar_count l1 v = cvar_count l2 v) with (P v); [| now rewrite HeqP ].
  generalize dependent v.
  apply Forall_forall, not_Exists_not_Forall; subst; intro; [ apply Z.eq_dec |].
  apply Exists_exists in H; destruct H as [v [HIn Hneq]].

Abort.














(* Reserved Notation "a '=ᵥ' b" (at level 70). *)
(**)
(* Inductive vars_eq : var_list → var_list → Prop := *)
(*   | VEq_Nil : [] =ᵥ [] *)
(*   | VEq_Cons x n y m l1 l2 : *)
(*     x = y → n = m → *)
(*     l1 =ᵥ l2 → *)
(*     (x,n)::l1 =ᵥ (y,m)::l2 *)
(**)
(* where "a '=ᵥ' b" := (vars_eq a b). *)
(* Hint Constructors vars_eq : core. *)
(**)
(* Instance Equivalence_vars_eq : Equivalence vars_eq. *)
(* Proof. *)
(*   split. *)
(*   + intro v; induction v as [| [x n] v']; auto. *)
(*   + intro v1; induction v1 as [| [x n] v1']; intros v Heq. *)
(*     - now inv Heq. *)
(*     - inv Heq. constructor; auto. *)
(*   + intro v1; induction v1 as [| [x n] vl']; intros v2 v3 H12 H23. *)
(*     - now inv H12. *)
(*     - inv H12; inv H23. *)
(*       constructor; auto. *)
(*       eapply IHvl'; eauto. *)
(* Qed. *)
(**)
(* Lemma cmp_if_vars_eq (l1 l2: var_list) : l1 =ᵥ l2 → cmp_vars l1 l2 = Eq. *)
(* Proof. *)
(*   generalize dependent l2. *)
(*   induction l1 as [| [x n] l1']; intros l2 Heq; inv Heq; auto. *)
(*   simpl. *)
(*   rewrite Nat.ltb_irrefl, string_compare_refl. *)
(*   apply IHl1', H5. *)
(* Qed. *)
(**)
(* Lemma vars_eq_if_cmp (l1 l2: var_list) : cmp_vars l1 l2 = Eq → l1 =ᵥ l2. *)
(* Proof. *)
(*   generalize dependent l2. *)
(*   induction l1 as [| [x n] l1']; intros [| [y m] l2'] Heq; inv Heq; auto. *)
(*   simpl. *)
(*   destruct (x ?= y)%string eqn:Exy; try discriminate. *)
(*   destruct (n <? m) eqn:Enm; try discriminate; *)
(*   destruct (m <? n) eqn:Emn; try discriminate. *)
(*   pose proof (compare_eq_iff _ _ Exy). *)
(*   pose proof (nat_lt_antisym _ _ Enm Emn). *)
(*   constructor; auto. *)
(* Qed. *)
