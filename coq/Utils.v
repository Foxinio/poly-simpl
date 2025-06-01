Require Import Utf8.
From Coq Require Import Strings.String ZArith.Int ZArith Lists.List.
Require Import AsciiProps.


Import Int.
Open Scope Int_scope.
Import ListNotations.

Ltac inv H := inversion H; clear H; subst.

Definition len2 {A} (p : list A*list A) : nat :=
  let '(l1, l2) := p in
  List.length l1 + List.length l2.
Hint Unfold len2 : core.

Ltac strong_list1_induction :=
  match goal with
  | [ |- forall l : ?ty, ?H ] =>
      let ty := match ty with
          | list ?T => constr:(T)
          | _ => fail "not a list"
          end
      in
      let P := fresh "P" in
      remember (λ n : nat, ∀ l : list ty, n = List.length l → H) as P;
      let H := fresh "H" in let l := fresh "l" in
      enough (H: ∀ n : nat, P n);
      [ subst; try (intros l; now apply (H (List.length l)))
      | apply (well_founded_induction lt_wf); subst ]
  end.


Ltac strong_list_induction :=
  match goal with
  | [ |- forall l1 l2 : ?ty, ?H ] =>
      let ty := match ty with
          | list ?T => constr:(T)
          | _ => fail "not a list"
          end
      in
      let P := fresh "P" in
      remember (λ n : nat, ∀ l1 l2 : list ty, n = List.length l1 + List.length l2 → H) as P;
      let H := fresh "H" in let l1 := fresh "l1" in let l2 := fresh "l2" in
      enough (H: ∀ n : nat, P n);
      [ subst; try (intros l1 l2; now apply (H (len2 (l1, l2))))
      | apply (well_founded_induction lt_wf); subst ]
  | [ |- forall l : ?ty, ?H ] =>
      let ty := match ty with
          | list ?T => constr:(T)
          | _ => fail "not a list"
          end
      in
      let P := fresh "P" in
      remember (λ n : nat, ∀ l : list ty, n = List.length l → H) as P;
      let H := fresh "H" in let l := fresh "l" in
      enough (H: ∀ n : nat, P n);
      [ subst; try (intros l; now apply (H (List.length l)))
      | apply (well_founded_induction lt_wf); subst ]
  end.


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
    destruct b; cbn in *; try discriminate.
    unfold String.ltb in *. cbn in *.
    destruct (Ascii.compare a a2) eqn:?, (Ascii.compare a2 a1) eqn:?; try discriminate.
    + specialize (Ascii.compare_eq_iff _ _ Heqc0) as ?;
      specialize (Ascii.compare_eq_iff _ _ Heqc1) as ?; subst.
      rewrite ascii_compare_refl.
      eapply IHa; eauto.
    + specialize (Ascii.compare_eq_iff _ _ Heqc0) as ?; subst.
      now rewrite Heqc1.
    + specialize (Ascii.compare_eq_iff _ _ Heqc1) as ?; subst.
      now rewrite Heqc0.
    + specialize (ascii_compare_trans _ _ _ Heqc0 Heqc1) as Haa1;
      now rewrite Haa1.
Qed.

Lemma string_compare_refl a : (a ?= a = Eq)%string.
Admitted.

Lemma string_ltb_irrefl a : (a <? a)%string = false.
Admitted.

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

Lemma sorted_uniq_cons l a :
  sorted_uniq (a :: l) → sorted_uniq l.
Proof.
  intro; destruct a as [x ?], l as [| [x' ?] l]; [ constructor |].
  now inv H.
Qed.

Lemma sorted_uniq_shadow l :
  ∀ a b, sorted_uniq (a :: b :: l) → sorted_uniq (a :: l).
Proof.
  induction l as [| [x ?] l]; simpl; auto; intros [y ?] [z ?] H.
  inv H. inv H4.
  constructor; [ eapply ltb_trans; now eassumption | assumption ].
Qed.

Lemma sorted_forall_inv l :
  ∀ a, sorted_uniq l →
  Forall (λ p, fst a <? fst p = true)%string l →
  sorted_uniq (a :: l).
Proof.
  induction l as [| [x ?] l]; simpl; auto; intros [x' ?] Hs HF.
  inv HF.
  constructor; auto.
Qed.

Lemma sorted_forall_in l :
  ∀ a, sorted_uniq (a :: l) →
  ∀ a', In a' l → (fst a <? fst a' = true)%string.
Proof.
  induction l as [| [x ?] l]; simpl; intros [x' ?] H [x'' ?] HIn; auto.
  destruct HIn.
  - inv H0. inv H; auto.
  - apply IHl; auto.
    eapply sorted_uniq_shadow, H.
Qed.

Lemma sorted_forall l :
  ∀ a, sorted_uniq (a :: l) →
  Forall (λ p, fst a <? fst p = true)%string l.
Proof.
  induction l as [| [x ?] l]; intros [x' ?] Hsort; auto.
  inv Hsort. apply Forall_forall; intros [x'' ?] Hin.
  specialize (sorted_uniq_cons _ _ H3) as Hl.
  inv Hin.
  - inv H; auto.
  - eapply sorted_forall_in; [| eassumption ].
    destruct l as [| [x''' ?] l]; auto.
    inv H3.
    constructor; auto.
    eapply ltb_trans; eassumption.
Qed.

Definition cross {A B C : Type} (f : A -> B -> C)
    (l1 : list A) (l2 : list B) : list C :=
  List.concat (map (fun a => map (f a) l2) l1).

Lemma nat_lt_antisym (x y : nat) :
  x <? y = false →
  y <? x = false →
  x = y.
Proof.
Admitted.

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

Lemma fold_left_mul_add_distr (l : list Z) (c1 c2 : Z) :
  (fold_left Z.mul l c2 + fold_left Z.mul l c1)%Z =
   fold_left Z.mul l (c1 + c2)%Z.
Proof.
  induction l; simpl; auto using Z.add_comm.
  repeat rewrite <- fold_left_mul_acc.
  now rewrite <- Z.mul_add_distr_r, IHl.
Qed.

Lemma Exists_witness {A} (P : A → Prop) l :
  Exists P l → ∃ l1 a l2, l = l1 ++ a :: l2 /\ P a. 
Proof.
  induction l; intros H; inv H.
  - exists [], a, l; split; auto.
  - destruct (IHl H1) as [l1 [b [l2 [Hdiv Hp]]]].
    exists (a::l1), b, l2; split; auto; simpl.
    f_equal; auto.
Qed.
