From Stdlib Require Import Lia List.
Import ListNotations.

Require Import Syntax Utils BasicProps Algorithm.

Lemma reconstruct_var_pow_correct st x n :
  aeval st (reconstruct_var_pow x n) = (st x ^ Z.of_nat n)%Z.
Proof.
  Opaque Z.pow.
  Opaque Z.of_nat.
  induction n; auto; simpl;
  remember (reconstruct_var_pow x n) as a'.
  destruct n eqn:Ep; [ simpl; now rewrite <- Z.pow_1_r with (a:=st x) at 1 |].
  assert (0 < n) by lia.
  rewrite <- Ep in *; clear Ep n0.
  cbn.
  rewrite IHn; simpl.
  replace (Z.of_nat (S n)) with (1 + Z.of_nat n)%Z by lia.
  rewrite Z.pow_add_r; try lia.
  Transparent Z.pow.
  Transparent Z.of_nat.
Qed.

Lemma reconstruct_monom_correct st c v :
  aeval st (reconstruct_monom c v) = fold_left Z.mul (map (pow st) v) c.
Proof.
  induction v as [| [x n] l']; auto.
  simpl. rewrite IHl', Z.mul_comm, fold_left_mul_acc.
  now rewrite reconstruct_var_pow_correct.
Qed.

Theorem reconstruct_correct (l : list pterm) :
  reconstruct l ≲ₗ l.
Proof.
  intro st.
  induction l as [| [c v] l']; auto.
  cbn. remember (reconstruct l') as a'.
  destruct l' eqn:Ep; [ simpl; now rewrite reconstruct_monom_correct |].
  rewrite <- Ep in *; clear Ep l.
  simpl; subst.
  rewrite IHl', reconstruct_monom_correct.
  lia.
Qed.


(* ======================================================================== *)
(* New reconstruct *)

Lemma reconstruct_var_pow'_correct st x n :
  aeval st (reconstruct_var_pow' x n) = (st x ^ Z.of_nat n)%Z.
Proof.
  Opaque Z.pow.
  Opaque Z.of_nat.
  induction n; auto; simpl;
  remember (reconstruct_var_pow x n) as a'.
  destruct n eqn:Ep; [ simpl; now rewrite <- Z.pow_1_r with (a:=st x) at 1 |].
  assert (0 < n) by lia.
  rewrite <- Ep in *; clear Ep n0.
  cbn.
  rewrite IHn; simpl.
  replace (Z.of_nat (S n)) with (1 + Z.of_nat n)%Z by lia.
  rewrite Z.pow_add_r; try lia.
  Transparent Z.pow.
  Transparent Z.of_nat.
Qed.

Lemma reconstruct_monom_fix'_correct st vs v :
  aeval st (reconstruct_monom_fix' v vs) = fold_left Z.mul (map (pow st) (v::vs)) 1%Z.
Proof.
  revert v.
  induction vs as [| [x n] l']; auto; simpl; intros [x' n']; autorewrite with zsimpl.
  - apply reconstruct_var_pow'_correct.
  - simpl. rewrite IHl', reconstruct_var_pow'_correct.
    rewrite map_spec, fold_left_spec.
    rewrite Z.mul_comm, Z.mul_1_l, fold_left_mul_acc.
    f_equal; simpl; lia.
Qed.

Lemma reconstruct_monom'_correct st c v :
  aeval st (reconstruct_monom' c v) = fold_left Z.mul (map (pow st) v) c.
Proof.
  unfold reconstruct_monom'.
  assert(aeval st
    match v with
    | [] => c
    | v0 :: vs => <{ c * (reconstruct_monom_fix' v0 vs) }>
    end = fold_left Z.mul (map (pow st) v) c). {
    destruct v; auto.
    rewrite fold_left_pull_acc, <- reconstruct_monom_fix'_correct; simpl; lia.
    }
  destruct c eqn:?; auto.
  - destruct v; auto.
  - destruct p eqn:?; auto.
    destruct v; auto.
    now rewrite <- reconstruct_monom_fix'_correct.
Qed.


Theorem reconstruct'_correct (p : pterm) (l : list pterm) :
  reconstruct_fix' p l ≲ₗ (p :: l).
Proof.
  intro st. revert p.
  induction l as [| [c v] l']; auto; intros [c' v']; simpl.
  - now rewrite reconstruct_monom'_correct.
  - now rewrite IHl', reconstruct_monom'_correct.
Qed.

