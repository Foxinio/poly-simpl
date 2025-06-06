Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia Lists.List Strings.String Recdef Wf_nat.
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

