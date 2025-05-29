Require Import Utf8.
From Coq Require Import Strings.String ZArith.Int ZArith Lists.List.

Import Int.
Open Scope Int_scope.
Import ListNotations.

Ltac inv H := inversion H; clear H; subst.

Inductive sorted_uniq : list (string*nat) -> Prop :=
| sorted_nil:
    sorted_uniq []
| sorted_1: forall x,
    sorted_uniq [x]
| sorted_cons: forall x y l,
    (fst x <? fst y)%string = true ->
    sorted_uniq (y :: l) ->
    sorted_uniq (x :: y :: l).
Hint Constructors sorted_uniq : core.

Definition cross {A B C : Type} (f : A -> B -> C)
    (l1 : list A) (l2 : list B) : list C :=
  List.concat (map (fun a => map (f a) l2) l1).

Definition len2 {A} (p : list A*list A) : nat :=
  let '(l1, l2) := p in
  List.length l1 + List.length l2.
Hint Unfold len2 : core.

Lemma lt_antisym (x y : string) :
  (ltb x y)%string = false →
  (y <? x)%string = false →
  x = y.
Proof.
  unfold ltb.
  replace (y ?= x)%string with (CompOpp (x ?= y)%string)
    by now rewrite <- compare_antisym.
  destruct (x ?= y)%string eqn:Eq.
  - intros _ _. now apply compare_eq_iff.
  - intros; discriminate.
  - intros; discriminate.
Qed.

Lemma ltb_trans a : forall b c,
  (a <? b)%string = true →
  (b <? c)%string = true →
  (a <? c)%string = true.
Proof.
  induction a; auto; simpl; intros.
  - destruct c; cbn in *; auto.
    destruct b; cbn in *; discriminate.
  - destruct c; cbn in *; auto;
    [ destruct b; cbn in *; discriminate |].
    cbn.
Admitted.

Lemma Z_match_id (z : Z) :
  (match z with
   | Z0 => Z0
   | Zpos p => Zpos p
   | Zneg p => Zneg p
   end) = z.
Proof.
  destruct z; reflexivity.
Qed.

#[global]
Hint Rewrite Z_match_id : zsimpl.

Lemma fold_left_mul_acc (l : list Z) : ∀ a b : Z,
  (fold_left Z.mul l a * b)%Z = fold_left Z.mul l (a * b)%Z.
Proof.
  induction l; auto; simpl; intros.
  rewrite IHl.
  f_equal.
  repeat rewrite <- Z.mul_assoc.
  replace (a*b)%Z with (b*a)%Z; [ auto | now rewrite Z.mul_comm ].
Qed.

Lemma fold_left_mul_0 (l : list Z) : fold_left Z.mul l 0%Z = 0%Z.
Proof.
  induction l; auto.
Qed.

Lemma fold_left_pull_acc (l : list Z) : ∀ a : Z,
   fold_left Z.mul l a = (fold_left Z.mul l 1 * a)%Z.
Proof.
  induction l; auto; simpl; autorewrite with zsimpl;
  [ now intros [| a | a ] | intro b ].
  rewrite IHl. symmetry. rewrite IHl.
  rewrite <- Z.mul_assoc; f_equal.
  apply Z.mul_comm.
Qed.

Lemma fold_left_spec {A B : Type} (f : A → B → A) l a b :
  fold_left f (a :: l) b = fold_left f l (f b a).
Proof. reflexivity. Qed.

Lemma map_spec {A B : Type} (f : A → B) l a :
  map f (a :: l) = f a :: map f l.
Proof. reflexivity. Qed.

Lemma mul_1_l a : (1 * a)%Z = a.
Proof. destruct a; auto. Qed.

Theorem strong_induction (P : nat → Prop) :
  (∀ n, (∀ k, k < n → P k) -> P n) -> forall n, P n.
Proof.
  intros H.
  apply (well_founded_induction lt_wf).
  exact H.
Qed.

