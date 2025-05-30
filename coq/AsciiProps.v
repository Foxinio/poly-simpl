Require Import Utf8.
From Coq Require Import Strings.String ZArith.Int ZArith Lists.List.
From Coq Require Import Ascii.

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
(**)
(* Lemma ascii_compare_trans a : forall b c, *)
(*   Ascii.compare a b = Lt → *)
(*   Ascii.compare b c = Lt → *)
(*   Ascii.compare a c = Lt. *)
(* Proof. *)
(*   intros. *)
(*   destruct a, b, c. *)
(*   unfold compare in *. cbn in *. *)
(*   destruct b  eqn:?; *)
(*   destruct b0 eqn:?; *)
(*   destruct b1 eqn:?; *)
(*   destruct b2 eqn:?; *)
(*   destruct b3 eqn:?; *)
(*   destruct b4 eqn:?; *)
(*   destruct b5 eqn:?; *)
(*   destruct b6 eqn:?; *)
(*   destruct b7  eqn:?; *)
(*   destruct b8  eqn:?; *)
(*   destruct b9  eqn:?; *)
(*   destruct b10 eqn:?; *)
(*   destruct b11 eqn:?; *)
(*   destruct b12 eqn:?; *)
(*   destruct b13 eqn:?; *)
(*   destruct b14 eqn:?; *)
(*   destruct b15  eqn:?; *)
(*   destruct b16 eqn:?; *)
(*   destruct b17 eqn:?; *)
(*   destruct b18 eqn:?; *)
(*   destruct b19 eqn:?; *)
(*   destruct b20 eqn:?; *)
(*   destruct b21 eqn:?; *)
(*   destruct b22 eqn:?; try discriminate; auto. *)
(* Qed. *)

(* Lemma ascii_compare_refl a : Ascii.compare a a = Eq. *)
(* Admitted. *)

Lemma ascii_compare_trans a : forall b c,
  Ascii.compare a b = Lt →
  Ascii.compare b c = Lt →
  Ascii.compare a c = Lt.
Admitted.
