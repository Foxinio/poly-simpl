Require Import Utf8.
Require Import Syntax Utils PFlatten.

From Coq Require Import Lists.List Lia.

Import ListNotations.

(* First we define definitions of what we want to prove *)

(* Next we prove it *)

Lemma pow_correct (st : state) x : st x = pow st (x, 1%nat).
Proof.
  unfold pow; now rewrite Z.pow_1_r.
Qed.

Lemma flip_sign_correct (st : state) (p : pterm) :
  (- eval_pterm st p)%Z = eval_pterm st (flip_sign p).
Proof.
  destruct p.
  simpl.
  induction vars; auto.
  repeat rewrite fold_symmetric; try lia; simpl.
  repeat rewrite <- fold_symmetric; try lia.
Qed.

Lemma eval_pterm_list_homo (st : state) (l1 l2 : list pterm) :
  eval_pterm_list st (l1 ++ l2) =
  (eval_pterm_list st l1 + eval_pterm_list st l2)%Z.
Proof.
  induction l1; auto; simpl.
  destruct a. rewrite IHl1; lia.
Qed.

Lemma eval_pterm_list_map_flip (st : state) (l : list pterm) :
  eval_pterm_list st (map flip_sign l) =
  (- eval_pterm_list st l)%Z.
Proof.
  induction l; auto; simpl.
  rewrite <- flip_sign_correct.
  rewrite IHl; lia.
Qed.

Lemma pow_distr (st : state) x n1 n2 :
  Z.mul (pow st (x, n1)) (pow st (x, n2)) = pow st (x, n1 + n2).
Proof.
  unfold pow.
  rewrite <- Z.pow_add_r; try lia.
Qed.

Lemma merge_vl_correct (st : state) : ∀ vars1 vars2 : list (string * nat),
  fold_left Z.mul (map (pow st) (merge_vl (vars1, vars2))) 1%Z =
  (fold_left Z.mul (map (pow st) vars1) 1 *
  fold_left Z.mul (map (pow st) vars2) 1)%Z.
Proof.
  remember (λ n,
    ∀ vars1 vars2 : list (string * nat), n = len2 (vars1, vars2) →
    fold_left Z.mul (map (pow st) (merge_vl (vars1, vars2))) 1%Z =
    (fold_left Z.mul (map (pow st) vars1) 1 *
    fold_left Z.mul (map (pow st) vars2) 1)%Z) as P.
  assert (∀ n, P n). {
    Opaque pow.
    apply (well_founded_induction lt_wf); subst.
    intros n IH [| [x ?] vars1] [| [y ?] vars2] Hlen;
    rewrite merge_vl_equation; simpl in *;
    [ reflexivity
    | now repeat autorewrite with zsimpl
    | repeat autorewrite with zsimpl;
      now rewrite Z.mul_1_r |].
    destruct (x <? y)%string eqn:?;
    [| destruct (y <? x)%string eqn:? ]; autorewrite with zsimpl.
    - rewrite map_spec, fold_left_spec.
      rewrite <- fold_left_mul_acc.
      erewrite IH; [| | now inversion Hlen ]; [| inversion Hlen; simpl; lia ].
      rewrite map_spec, fold_left_spec.
      rewrite mul_1_l.
      replace ((fold_left Z.mul (map (pow st) vars1) 1 *
                fold_left Z.mul (map (pow st) vars2) (pow st (y, n1)) * 
                pow st (x, n0))%Z)
         with (((fold_left Z.mul (map (pow st) vars1) 1 * pow st (x, n0)) *
                fold_left Z.mul (map (pow st) vars2) (pow st (y, n1)))%Z);
      [ now rewrite fold_left_mul_acc, mul_1_l | lia ].
    - rewrite map_spec, fold_left_spec.
      rewrite <- fold_left_mul_acc.
      erewrite IH; [| | now inversion Hlen ]; [| inversion Hlen; simpl; lia ].
      rewrite <- Z.mul_assoc.
      rewrite map_spec, fold_left_spec, mul_1_l.
      f_equal; now rewrite fold_left_mul_acc, mul_1_l.
    - rewrite map_spec, fold_left_spec.
      rewrite <- fold_left_mul_acc.
      erewrite IH; [| | now inversion Hlen ]; [| inversion Hlen; simpl; lia ].
      symmetry.
      rewrite fold_left_pull_acc.
      rewrite Z.mul_comm, fold_left_pull_acc.
      pose proof (lt_antisym _ _ Heqb Heqb0); subst.
      rewrite <- pow_distr.
      lia.
  }
  subst.
  intros vars1 vars2.
  now apply (H (len2 (vars1, vars2)) vars1 vars2).
Qed.

Lemma times_pterm_correct (st : state) (p1 p2 : pterm) :
  eval_pterm st (times_pterm p1 p2) = (eval_pterm st p1 * eval_pterm st p2)%Z.
Proof.
  destruct p1, p2.
  unfold times_pterm; simpl.
  rewrite fold_left_pull_acc, Z.mul_comm.
  symmetry.
  replace (fold_left Z.mul (map (pow st) vars) c *
    fold_left Z.mul (map (pow st) vars0) c0)%Z
    with (c * c0 * (fold_left Z.mul (map (pow st) vars) 1 *
    fold_left Z.mul (map (pow st) vars0) 1))%Z.
  + f_equal. symmetry; apply merge_vl_correct.
  + symmetry.
    rewrite fold_left_pull_acc, Z.mul_comm.
    rewrite fold_left_pull_acc, Z.mul_assoc, Z.mul_comm.
    symmetry; rewrite <- Z.mul_assoc.
    f_equal.
    symmetry. rewrite <- Z.mul_assoc, Z.mul_comm.
    now rewrite Z.mul_assoc.
Qed.

Lemma eval_pterm_list_cross (st : state) (l1 l2 : list pterm) :
  (eval_pterm_list st l1 * eval_pterm_list st l2)%Z =
  eval_pterm_list st (cross times_pterm l1 l2).
Proof.
  induction l1; auto; simpl.
  unfold cross; cbn.
  rewrite eval_pterm_list_homo.
  unfold cross in IHl1; cbn.
  rewrite <- IHl1, Z.mul_add_distr_r.
  rewrite Z.add_comm; f_equal.
  clear IHl1 l1.
  induction l2; simpl; [ now rewrite Z.mul_0_r |].
  rewrite <- IHl2, Z.mul_add_distr_l.
  f_equal; now rewrite times_pterm_correct.
Qed.

Theorem poly_flatten_correct (a : aexp) : a ≲ₗ (poly_flatten a).
Proof.
  induction a; intro.
  + auto.
  + simpl;
    rewrite <- pow_correct; destruct (st x); auto.
  + simpl; rewrite IHa1, IHa2; simpl.
    symmetry; apply eval_pterm_list_homo.
  + simpl; rewrite IHa1, IHa2.
    rewrite eval_pterm_list_homo, eval_pterm_list_map_flip.
    lia.
  + simpl; rewrite IHa1, IHa2.
    now rewrite eval_pterm_list_cross.
Qed.

(* ======================================================================== *)
(* Well formed *)

Lemma flip_sign_pterm_well_formed (a : aexp) :
  pterm_list_well_formed (poly_flatten a) →
  pterm_list_well_formed (map flip_sign (poly_flatten a)).
Proof.
  intro H.
  unfold flip_sign.
  apply Forall_map, Forall_forall; intros [c v] Hx.
  remember (PTerm c v) as x.
  enough ((λ '(PTerm _ vars), sorted_uniq vars) x);
  [ subst; exact H0 |].
  clear Heqx c v.
  generalize dependent x.
  now apply Forall_forall.
Qed.

Lemma merge_vl_sorted_preserving : ∀ x y : var_list,
  sorted_uniq x → sorted_uniq y →
  sorted_uniq (merge_vl (x, y)).
Proof.
  remember (λ n, ∀ x y : var_list, n = len2 (x, y) → 
    sorted_uniq x → sorted_uniq y →
    sorted_uniq (merge_vl (x, y))) as P.
  assert (∀ n, P n). {
    apply (well_founded_induction lt_wf); subst.
    intros n IHn [| [x ?] vars1] [| [y ?] vars2] Hlen Hvars1 Hvars2;
    try now (rewrite merge_vl_equation; subst; auto).
    assert (
      sorted_uniq (merge_vl (vars1, (y, n1) :: vars2)) /\
      sorted_uniq (merge_vl ((x, n0) :: vars1, vars2)) /\
      sorted_uniq (merge_vl (vars1, vars2))). {
      simpl in Hlen.
      destruct n; try discriminate; inversion Hlen.
      repeat split.
      - eapply (IHn n); subst; simpl; try lia; auto.
        destruct vars1 as [| [x' ?] vars1]; [| inversion Hvars1 ]; now auto.
      - eapply (IHn n); subst; simpl; try lia; auto.
        destruct vars2 as [| [y' ?] vars2]; [| inversion Hvars2 ]; now auto.
      - rewrite Nat.add_comm in H0; simpl in H0.
        destruct n; try discriminate; inversion H0.
        eapply (IHn n); subst; simpl; try lia; auto.
        * destruct vars1 as [| [x' ?] vars1]; [| inversion Hvars1 ]; now auto.
        * destruct vars2 as [| [y' ?] vars2]; [| inversion Hvars2 ]; now auto.
    } destruct H as [? [? ?]].
    remember H1 as H2; clear HeqH2.
    rewrite merge_vl_equation in H;
    rewrite merge_vl_equation in H0;
    rewrite merge_vl_equation in H1;
    rewrite merge_vl_equation;
    destruct (x <? y)%string eqn:?;
    [| destruct (y <? x)%string eqn:? ]; autorewrite with zsimpl.
    - destruct vars1 as [| [x' ?] vars1]; rewrite merge_vl_equation;
      [ econstructor; auto |].
      destruct (x' <? y)%string eqn:?;
      [| destruct (y <? x')%string eqn:? ]; autorewrite with zsimpl;
      inversion Hvars1; subst; econstructor; auto.
    - destruct vars2 as [| [y' ?] vars2]; rewrite merge_vl_equation;
      [ econstructor; auto |].
      destruct (x <? y')%string eqn:?;
      [| destruct (y' <? x)%string eqn:? ]; autorewrite with zsimpl;
      inversion Hvars2; subst; econstructor; auto.
    - destruct vars2 as [| [y' ?] vars2], vars1 as [| [x' ?] vars1]; rewrite merge_vl_equation;
      pose proof (lt_antisym _ _ Heqb Heqb0); subst;
      try now (econstructor; auto).
      + inversion H0; constructor; auto.
      + inversion Hvars2; constructor; auto.
      + destruct (x' <? y')%string eqn:?;
        [| destruct (y' <? x')%string eqn:? ]; autorewrite with zsimpl;
        inversion Hvars1; inversion Hvars2; subst; econstructor; auto.
  }
    subst; intros x y.
    now apply (H (len2 (x, y)) x y).
Qed.

Lemma aexp_mul_pt_well_formed (l1 l2 : list pterm) :
  pterm_list_well_formed l1 →
  pterm_list_well_formed l2 →
  pterm_list_well_formed (cross times_pterm l1 l2).
Proof.
  intros Hl1 Hl2.
  apply Forall_concat, Forall_map, Forall_forall; intros [c1 v1] Hx.
  apply Forall_map, Forall_forall; intros [c2 v2] Hy.
  unfold times_pterm.
  apply merge_vl_sorted_preserving.
  - remember (PTerm c1 v1) as x eqn:Heq.
    enough ((λ '(PTerm _ vars), sorted_uniq vars) x);
    [ subst; exact H | clear Heq c1 v1 ].
    generalize dependent x.
    now apply Forall_forall.
  - remember (PTerm c2 v2) as y eqn:Heq.
    enough ((λ '(PTerm _ vars), sorted_uniq vars) y);
    [ subst; exact H | clear Heq c2 v2 ].
    generalize dependent y.
    now apply Forall_forall.
Qed.

Theorem poly_flatten_well_formed (a : aexp) :
  pterm_list_well_formed (poly_flatten a).
Proof.
  unfold pterm_list_well_formed.
  induction a; simpl.
  - repeat constructor.
  - repeat constructor.
  - apply Forall_app; auto.
  - apply Forall_app; split; auto.
    apply flip_sign_pterm_well_formed; now unfold pterm_list_well_formed.
  - apply aexp_mul_pt_well_formed; auto.
Qed.

