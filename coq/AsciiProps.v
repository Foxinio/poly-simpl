From Stdlib Require Import Utf8.
From Stdlib Require Import Strings.String ZArith.Int ZArith Lists.List.
From Stdlib Require Import Ascii.

Lemma ascii_compare_refl a : Ascii.compare a a = Eq.
Proof.
  destruct a.
  unfold compare. cbn.
  destruct b eqn:?;
  destruct b0 eqn:?;
  destruct b1 eqn:?;
  destruct b2 eqn:?;
  destruct b3 eqn:?;
  destruct b4 eqn:?;
  destruct b5 eqn:?;
  destruct b6 eqn:?;
  auto.
Qed.

Lemma ascii_compare_trans a : forall b c,
  Ascii.compare a b = Lt →
  Ascii.compare b c = Lt →
  Ascii.compare a c = Lt.
Proof.
  intros.
  unfold compare.
  unfold N_of_ascii.
Admitted.

Lemma N_of_digits_Lt_trans a : forall b c,
  (N_of_digits a ?= N_of_digits b = Lt →
  N_of_digits b ?= N_of_digits c = Lt →
  N_of_digits a ?= N_of_digits c = Lt)%N.
Proof.
Abort.
