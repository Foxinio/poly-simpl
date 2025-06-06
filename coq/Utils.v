Require Import Utf8.
From Coq Require Import ZArith.Int ZArith Lia.
From Coq Require Import Strings.String Lists.List Sorting.Permutation Sets.Relations_1.
Require Import Coq.Classes.Equivalence.
Require Import AsciiProps BasicProps.

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

Ltac destruct_let :=
  match goal with
  | |- context [ let _ := ?e in _ ] =>
      destruct e eqn:?
  end.

Ltac lia_specialize H :=
  match goal with
  | H: ?Assumption -> _ |- _ =>
      let HAsmpt := fresh in
      assert (HAsmpt: Assumption) by (now lia);
      specialize (H HAsmpt);
      clear HAsmpt
  end.

Ltac auto_specialize H :=
  match goal with
  | H: ?Assumption -> _ |- _ =>
      let HAsmpt := fresh in
      assert (HAsmpt: Assumption) by (now auto);
      specialize (H HAsmpt);
      clear HAsmpt
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

Lemma app_spec {A} l1 l2 (a : A) :
  a :: (l1 ++ l2) = (a :: l1) ++ l2.
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

Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
  Permutation al bl ->
  Forall f al -> Forall f bl.
Proof.
Admitted.

Lemma Forall_neq_nIn {A} (a : A) l :
  Forall (λ b, a ≠ b) l → ~In a l. 
Proof.
  induction l.
  - intros _ HC; inv HC.
  - intros HFa HIn.
    inv HFa.
    inv HIn; auto.
    apply IHl; auto.
Qed.

Lemma In_witness {A} (a : A) l :
  In a l → ∃ l1 l2, l = l1 ++ a :: l2. 
Proof.
  induction l; simpl; [ intros HIn; inv HIn | intros [ Heq | HIn ]].
  - exists [], l; subst; auto.
  - destruct (IHl HIn) as [l1 [l2 Heq]].
    exists (a0::l1), l2; subst; auto.
Qed.

Lemma not_Exists_not_Forall {A} l P :
  (∀ a : A, { P a } + { ~P a }) →
  ~Exists (λ a, ~P a) l → Forall P l.
Proof.
  induction l; simpl; intros; [ constructor |].
  destruct (Exists_dec (λ a, ~P a) l).
  { intro x; destruct (X x).
    - right; intro H0; apply H0, p.
    - left; intro H0; apply n, H0. }
  - exfalso; apply H.
    constructor; apply e.
  - constructor; [| (apply IHl; [ apply X | apply n]) ].
    destruct (X a); [ assumption |].
    exfalso; apply H; constructor; apply n0.
Qed.

Lemma nIn_app {A} l1 l2 (a : A) :
¬ In a (l1 ++ l2) → ~In a l1 /\ ~In a l2.
Proof.
  intro H; split; intro; apply H, in_or_app.
  - left; apply H0.
  - right; apply H0.
Qed.

Lemma cmp_vars_antisym :
  ∀ v1 v2, cmp_vars v1 v2 = CompOpp (cmp_vars v2 v1). 
Proof.
  induction v1, v2; intuition.
  simpl.
  rewrite compare_antisym.
  destruct (compare a a0); simpl; intuition.
  destruct (b <? b0) eqn:?, (b0 <? b) eqn:?; unfold CompOpp; auto.
  apply Nat.ltb_lt in Heqb1.
  apply Nat.ltb_lt in Heqb0.
  lia.
Qed.

Lemma cmp_vars_eq_iff : ∀ v1 v2 : list (string*nat),
  cmp_vars v1 v2 = Eq → v1 = v2.
Proof.
  strong_list_induction.
  intros n' IH l1 l2 Hlen Hcmp.
  destruct l1 as [| [x n] l1'] eqn:?, l2 as [| [y m] l2'] eqn:?; auto;
  try now inversion Hcmp.
  simpl in Hcmp.
  destruct (x ?= y)%string eqn:?; try discriminate.
  pose proof (String.compare_eq_iff _ _ Heqc).
  destruct (n <? m) eqn:?; try discriminate;
  destruct (m <? n) eqn:?; try discriminate.
  pose proof (nat_lt_antisym _ _ Heqb Heqb0). 
  f_equal; [ now subst |].
  simpl in Hlen.
  apply (IH (len2 (l1', l2'))); auto; simpl; lia.
Qed.


Lemma cmp_vars_refl v : cmp_vars v v = Eq.
Admitted.

Lemma cmp_vars_refl_nlt :
  ∀ v, cmp_vars v v <> Lt.
Proof.
  intros v C.
  rewrite cmp_vars_antisym in C; unfold CompOpp in C; simpl in C.
  rewrite cmp_vars_refl in C; discriminate.
Qed.

Lemma canon_pterm_cons p l :
  ~In p l → canon_pterm l → canon_pterm (p :: l).
Proof.
  intros H Hcanon.
  eapply CP_cons; eauto.
  destruct p; reflexivity.
Qed.

Lemma canon_pterm_single a : canon_pterm [a].
Proof.
  apply canon_pterm_cons; auto.
Qed.

Lemma cmp_vars_trans v1 v2 v3 :
  cmp_vars v1 v2 = Lt → cmp_vars v2 v3 = Lt → cmp_vars v1 v3 = Lt.
Proof.
Admitted.

Instance Transitive_pterm_le : Transitive pterm_le.
Proof.
  intros [c1 v1] [c2 v2] [c3 v3]; unfold pterm_le; simpl;
  intros H12 H23; clear c1 c2 c3.
Admitted.

Lemma Rel1_Transitive_pterm_le : Relations_1.Transitive pterm_le.
Proof.
  intros p1 p2 p3 H12 H23.
  transitivity p2; auto.
Qed.

Lemma sorted_shadow :
  ∀ l'' c1 c2 v1 v2,
  sorted (PTerm c1 v1 :: PTerm c2 v2 :: l'') →
  sorted (PTerm c1 v1 ::  l'').
Proof.
  intros.
Admitted.

Lemma sorted_const_invariant :
  ∀ l'' c1 c2 c3 v1 v2,
  sorted (PTerm c1 v1 :: PTerm c2 v2 :: l'') →
  sorted (PTerm c1 v1 :: PTerm c3 v2 ::  l'').
Proof.
Admitted.



