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

Inductive equiv_list {A} {equiv : A → A → Prop} {Equiv : Equivalence equiv}
    : list A → Prop :=
  | EL_Single a :
      equiv_list [a]
  | EL_Cons a b l :
      equiv_list (a :: l) →
      equiv a b →
      equiv_list (b :: a :: l).
Arguments equiv_list _ equiv _ : clear implicits.
Arguments equiv_list {A} _ {Equiv}.

Definition rep {A} {equiv : A → A → Prop} (l : list A)
  {Equiv : Equivalence equiv} (H: equiv_list equiv l) : A.
Proof.
  destruct l.
  - exfalso. inversion H.
  - apply a.
Defined.

Definition drep {A} {equiv : A → A → Prop} {Equiv : Equivalence equiv}
  (l : {l : list A | equiv_list equiv l}) : A :=
    rep (proj1_sig l) (proj2_sig l).

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

Definition pl_equiv := equiv_list pterm_equiv.

Lemma pterm_equiv_dep_dec p :
  ∀ x0 : {l : list pterm | pl_equiv l},
    {pterm_equiv (drep x0) p} + {¬ pterm_equiv (drep x0) p}.
Proof.
  intros [p' Hp'].
  induction p'; [ exfalso; inversion Hp' |].
  unfold drep; simpl.
  apply pterm_equiv_dec.
Qed.


Fixpoint forall_to_sig_list (l : list (list pterm)) {struct l}
    : Forall pl_equiv l → list {a | pl_equiv a}.
Proof.
  intro pf; destruct l; [ apply [] |].
  apply cons.
  - exists l; inversion pf; apply H1.
  - eapply forall_to_sig_list; inversion pf; apply H2.
Defined.

Definition dl_fst (l : list {a | pl_equiv a}) : list (list pterm).
  induction l as [| [a Ha] l]; simpl.
  - constructor.
  - apply (cons a IHl).
Defined.
Definition dl_snd (l : list {a | pl_equiv a})
    : Forall pl_equiv (dl_fst l).
  induction l as [| [a Ha] l]; simpl; constructor.
  - apply Ha.
  - apply IHl.
Defined.

Lemma forall_to_sig_list_fst (l : list (list pterm)) (H: Forall pl_equiv l) :
  dl_fst (forall_to_sig_list l H) = l.
Proof.
  induction l; auto; simpl; now rewrite IHl.
Qed.

Lemma forall_to_sig_list_ext' l :
  ∀ Hl', dl_snd l = Hl' →
  forall_to_sig_list (dl_fst l) Hl' = l.
Proof.
  induction l; auto; simpl; intros Hl' Hl'eq.
  destruct a; simpl.
  rewrite <- Hl'eq.
  f_equal.
  rewrite IHl; auto.
Qed.

Lemma forall_to_sig_list_ext l :
  forall_to_sig_list (dl_fst l) (dl_snd l) = l.
Proof.
  now apply forall_to_sig_list_ext'.
Qed.

(* Lemma forall_to_sig_list_app (l1 l1 : list (list pterm)) (/ *)

Inductive Distinct :
  list {l : list pterm | pl_equiv l } →
  Prop :=
  | DNil : Distinct []
  | DCons (a : list pterm) l (H : pl_equiv a) :
      Forall (λ b, ~ pterm_equiv (drep b) (rep a H)) l →
      Distinct l →
      Distinct (exist _ a H :: l).

Definition grouped_pterms (l : list (list pterm)) :=
  { H : Forall pl_equiv l | Distinct (forall_to_sig_list l H)}.
Hint Unfold grouped_pterms : core.

Lemma equiv_list_cons (l : list pterm) p (Hl: pl_equiv l) :
  pterm_equiv (rep l Hl) p →
  pl_equiv (p :: l).
Admitted.

Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
  Permutation al bl ->
  Forall f al -> Forall f bl.
Proof.
Admitted.

Lemma grouping_exists l :
  pterm_list_well_formed l →
  no_zero_powers l →
  ∃ ls, grouped_pterms ls /\
  (∀ st, grouped_eval_pl st ls = eval_pterm_list st l).
Proof.
  induction l as [| [c v] l']; intros Hwf Hnz.
  { exists []; split; auto.
    assert (Forall pl_equiv []) by constructor.
    exists H; constructor. }
  inv Hwf; inv Hnz.
  destruct IHl' as [ls [[HFa Hdist] Hlseqv]]; auto.
  remember (forall_to_sig_list ls HFa) as dep_list.
  destruct (Exists_dec (λ a, pterm_equiv (drep a) (PTerm c v)) dep_list).
  { intros [p' Hp'].
    induction p'; [ exfalso; inversion Hp' |].
    unfold drep; simpl.
    apply pterm_equiv_dec. }
  - destruct (Exists_witness _ _ e) as [l1 [[l Hl] [l2 [Hdiv HP]]]].
    subst dep_list; rewrite Hdiv in *.
    exists ((PTerm c v :: l) :: dl_fst l1 ++ dl_fst l2); split.
    + unfold grouped_pterms.
      assert (Forall pl_equiv ((PTerm c v :: l) :: dl_fst l1 ++ dl_fst l2)). {
        apply (Forall_perm _ (dl_fst l1 ++ (PTerm c v :: l) :: dl_fst l2));
        [ admit |].
        apply Forall_app; split; [ apply (dl_snd l1) |].
        apply Forall_cons; [| apply (dl_snd l2) ].
        apply (equiv_list_cons _ _ Hl HP).
      }
      exists H.
      inversion H; subst.
      
      admit.
    + cbn. intro st. rewrite <- Hlseqv.
      rewrite Z.add_comm.
      rewrite Z.add_assoc.
      rewrite Z.add_comm.
      symmetry. rewrite Z.add_comm.
      f_equal.
      rewrite <- (forall_to_sig_list_fst ls HFa), Hdiv.
Abort.

(* Lemma grouping_lemma : *)
(*   ∀ l1 l2, *)
(*   Forall pterm_list_well_formed l1 → *)
(*   Forall pterm_list_well_formed l2 → *)
(*   Forall no_zero_powers l1 → *)
(*   Forall no_zero_powers l2 → *)
(*   grouped_pterms l1 → *)
(*   grouped_pterms l2 → *)


Theorem var_list_canonality :
  ∀ l1 l2, l1 ≡ₗ l2 →
  pterm_list_well_formed l1 → pterm_list_well_formed l2 →
  no_zero_powers l1 → no_zero_powers l2 →
  l1 ≡ᵥ l2.
Proof.
  induction l1; simpl; intros l2 Heqv Hwf1 Hwf2 Hnz1 Hnz2 vars.
  - induction l2 as [| [c v] l2']; auto.
    simpl.
    destruct (cmp_vars v vars); auto; simpl.
    2,3: inv Hnz2; rewrite <- IHl2'; auto; admit.
    unfold ptequiv in Heqv; simpl in Heqv.
    assert (Heqv' : ∀ st : state,
      eval_pterm_list st l2' = (- fold_left Z.mul (map (pow st) v) c)%Z).
    { 

Admitted.

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


