From Stdlib Require Import Int Lia List Equivalence Bool Sorted.

Require Import AsciiProps BasicProps Syntax.

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


Hint Resolve Nat.ltb_spec0 Z.ltb_spec0 Nat.leb_spec0 Z.leb_spec0
        Nat.eqb_spec Z.eqb_spec String.eqb_spec : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [ auto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

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

Lemma compare_lt_trans a : forall b c,
  (a ?= b)%string = Lt →
  (b ?= c)%string = Lt →
  (a ?= c)%string = Lt.
Proof.
  intros b c Hab Hbc.
  assert ((a <? b)%string = true) by (unfold ltb; now rewrite Hab).
  assert ((b <? c)%string = true) by (unfold ltb; now rewrite Hbc).
  enough (a <? c = true)%string.
  - unfold ltb in H1; simpl in H1.
    destruct (a ?= c)%string; try now discriminate.
    reflexivity.
  - eapply ltb_trans; eauto.
Qed.

Lemma string_compare_refl a : (a ?= a = Eq)%string.
Proof.
  induction a; auto; simpl.
  now rewrite ascii_compare_refl.
Qed.

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

Lemma nat_ltb_antisym (x y : nat) :
  x <? y = false →
  y <? x = false →
  x = y.
Proof.
  intros.
  apply Nat.ltb_ge in H, H0.
  apply Nat.le_antisymm; auto.
Qed.

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
  f_equal. lia.
Qed.

Lemma fold_left_add_acc (l : list Z) : ∀ a b : Z,
  (fold_left Z.add l a + b)%Z = fold_left Z.add l (a + b)%Z.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl.
  f_equal. lia.
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
  pose proof (nat_ltb_antisym _ _ Heqb Heqb0). 
  f_equal; [ now subst |].
  simpl in Hlen.
  apply (IH (len2 (l1', l2'))); auto; simpl; lia.
Qed.


Lemma cmp_vars_refl v : cmp_vars v v = Eq.
Proof.
  induction v as [| [x n] v]; auto; simpl.
  now rewrite string_compare_refl, Nat.ltb_irrefl, IHv.
Qed.

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

Lemma nat_antisym a b :
  a >= b → b >= a → a = b.
Proof.
  lia.
Qed.

Ltac find_equalities :=
  let H1 := fresh in let H2 := fresh in
  match goal with
  | [ H1: ?a >= ?b, H2: ?b >= ?a |- _] =>
      pose proof (nat_antisym _ _ H1 H2); subst a
  end.

Inductive LtVars : var_list → var_list → Prop :=
  | LtVars_nil x n v : LtVars ((x,n)::v) []
  | LtVars_end_str (x y : string) (n m : nat) v1 v2 :
      (x ?= y)%string = Lt →
      LtVars ((x, n)::v1) ((y,m)::v2)
  | LtVars_end_nat x y n m v1 v2 :
      (x ?= y)%string = Eq →
      n < m →
      LtVars ((x, n)::v1) ((y,m)::v2)
  | LtVars_cons x y n m v1 v2 :
      (x ?= y)%string = Eq →
      n = m →
      LtVars v1 v2 →
      LtVars ((x, n)::v1) ((y,m)::v2).

Inductive GtVars : var_list → var_list → Prop :=
  | GtVars_nil x n v : GtVars [] ((x,n)::v)
  | GtVars_end_str (x y : string) (n m : nat) v1 v2 :
      (x ?= y)%string = Gt →
      GtVars ((x, n)::v1) ((y,m)::v2)
  | GtVars_end_nat x y n m v1 v2 :
      (x ?= y)%string = Eq →
      n > m →
      GtVars ((x, n)::v1) ((y,m)::v2)
  | GtVars_cons x y n m v1 v2 :
      (x ?= y)%string = Eq →
      n = m →
      GtVars v1 v2 →
      GtVars ((x, n)::v1) ((y,m)::v2).

Inductive LeVars : var_list → var_list → Prop :=
  | LeVars_nil v : LeVars v []
  | LeVars_lt_str (x y : string) (n m : nat) v1 v2 :
      (x ?= y)%string = Lt →
      LeVars ((x, n)::v1) ((y,m)::v2)
  | LeVars_end_nat x y n m v1 v2 :
      (x ?= y)%string = Eq →
      n < m →
      LeVars ((x, n)::v1) ((y,m)::v2)
  | LeVars_cons x y n m v1 v2 :
      (x ?= y)%string = Eq →
      n = m →
      LeVars v1 v2 →
      LeVars ((x, n)::v1) ((y,m)::v2).
Hint Constructors LtVars : core.

Lemma LtVars_cmpVars_iff v1 v2 : LtVars v1 v2 ↔ cmp_vars v1 v2 = Lt.
Proof.
  split.
  - induction 1; simpl; auto.
    + now rewrite H.
    + apply (reflect_iff _ _ (Nat.ltb_spec0 n m)) in H0.
      now rewrite H, H0.
    + subst n; now rewrite H, Nat.ltb_irrefl, IHLtVars.
  - revert v1 v2.
    induction v1 as [| [x n] v1]; intros [| [y m] v2] HLt;
    try now inv HLt; try now constructor.
    simpl in HLt.
    destruct (x ?= y)%string eqn:?.
    + bdestruct (n <? m); [ apply LtVars_end_nat; auto |].
      bdestruct (m <? n); try now inv HLt.
      pose proof (nat_antisym _ _ H H0); subst n.
      apply LtVars_cons; auto.
    + apply LtVars_end_str; auto.
    + inv HLt.
Qed.

Lemma nat_gt_symm_lt n m : n > m → m < n.
Proof.
  intro H; apply H.
Qed.

Lemma GtVars_cmpVars_iff v1 v2 : GtVars v1 v2 ↔ cmp_vars v1 v2 = Gt.
Proof.
  split.
  - induction 1; simpl; auto.
    + now rewrite H.
    + remember H0 as H1; clear HeqH1;
      apply (reflect_iff _ _ (Nat.ltb_spec0 m n)) in H0.
      assert (n >= m) by lia.
      apply nat_gt_symm_lt in H1.
      apply (reflect_iff _ _ (Nat.leb_spec0 m n)) in H2.
      now rewrite H, Nat.ltb_antisym, H2, H0.
    + subst n; now rewrite H, Nat.ltb_irrefl, IHGtVars.
  - revert v1 v2.
    induction v1 as [| [x n] v1]; intros [| [y m] v2] HGt;
    try now inv HGt; try now constructor.
    simpl in HGt.
    destruct (x ?= y)%string eqn:?.
    + bdestruct (n <? m); [ inv HGt |].
      bdestruct (m <? n); [ apply GtVars_end_nat; auto |].
      pose proof (nat_antisym _ _ H H0); subst n.
      apply GtVars_cons; auto.
    + inv HGt.
    + apply GtVars_end_str; auto.
Qed.

Lemma nat_le_implications n m :
  n < m → n <? m = true /\ m <? n = false.
Proof.
  revert m; induction n; simpl; intros; auto; split.
  - destruct m; cbn; auto; inv H.
  - destruct m; cbn; auto; inv H.
  - destruct m; inv H; cbn in *; [ apply Nat.leb_refl |].
    edestruct (IHn m) as [H _]; [| apply H ].
    lia.
  - destruct m; inv H.
    + rewrite Nat.ltb_antisym; cbn.
      destruct (IHn (S (S n))) as [H _]; [ lia | ].
      cbn in H; now rewrite H.
    + cbn.
      destruct (IHn m) as [H H']; [ lia | ].
      cbn in *.
      destruct n; auto.
Qed.

Lemma LeVars_cmpVars_iff v1 v2 :
  LeVars v1 v2 ↔ cmp_vars v1 v2 <> Gt.
Proof.
  split.
{ induction 1; auto.
  + destruct v as [| [? ?]]; simpl; intro; discriminate.
  + simpl; rewrite H; intro; discriminate.
  + simpl; rewrite H.
    apply Nat.ltb_lt in H0; rewrite H0.
    intro; discriminate.
  + simpl; rewrite H, H0.
    rewrite (Nat.ltb_irrefl m).
    apply IHLeVars. }
{ revert v2; induction v1 as [| [x n] v1]; auto; intros.
  + destruct v2; simpl in H.
    - constructor.
    - exfalso; now apply H.
  + simpl in *; destruct v2 as [| [y m] v2]; try now constructor.
    destruct (x ?= y)%string eqn:?.
    - bdestruct (n <? m).
      * apply LeVars_end_nat; auto.
      * bdestruct (m <? n); [ exfalso; now apply H |].
        pose proof (nat_antisym _ _ H0 H1).
        apply LeVars_cons; auto.
    - apply LeVars_lt_str; auto.
    - exfalso; now apply H. }
Qed.

Lemma cmp_vars_trans v1 v2 v3 :
  cmp_vars v1 v2 = Lt → cmp_vars v2 v3 = Lt → cmp_vars v1 v3 = Lt.
Proof.
  intros H12 H23.
  apply LtVars_cmpVars_iff in H12, H23.
  apply LtVars_cmpVars_iff.
  generalize dependent v3.
  induction H12; intros; auto;
  try now inv H23.
  - destruct v3 as [| [z k] v3']; auto.
    inv H23.
    + pose proof (compare_lt_trans _ _ _ H H1).
      apply LtVars_end_str; now apply H0.
    + pose proof (compare_eq_iff _ _ H2); subst y.
      apply LtVars_end_str; now apply H.
    + pose proof (compare_eq_iff _ _ H4); subst y.
      apply LtVars_end_str; now apply H.
  - pose proof (compare_eq_iff _ _ H); subst y.
    destruct v3 as [| [z k] v3']; auto.
    inv H23.
    + apply LtVars_end_str; now apply H2.
    + pose proof (compare_eq_iff _ _ H3); subst x.
      apply LtVars_end_nat; auto.
      etransitivity; eauto.
    + pose proof (compare_eq_iff _ _ H5); subst x.
      apply LtVars_end_nat; auto.
  - pose proof (compare_eq_iff _ _ H); subst y.
    destruct v3 as [| [z k] v3']; auto.
    inv H23.
    + apply LtVars_end_str; now apply H2.
    + pose proof (compare_eq_iff _ _ H3); subst x.
      apply LtVars_end_nat; auto.
    + pose proof (compare_eq_iff _ _ H5); subst x.
      apply LtVars_cons; auto.
Qed.

Instance Transitive_pterm_le : Transitive pterm_le.
Proof.
  intros [c1 v1] [c2 v2] [c3 v3]; unfold pterm_le; simpl;
  intros H12 H23; clear c1 c2 c3.
  apply LeVars_cmpVars_iff in H12, H23.
  apply LeVars_cmpVars_iff.
  generalize dependent v3.
  induction H12; intros.
  - inv H23; constructor.
  - inv H23.
    + constructor.
    + pose proof (compare_lt_trans _ _ _ H H4).
      apply LeVars_lt_str; auto.
    + pose proof (compare_eq_iff _ _ H4); subst y.
      apply LeVars_lt_str; auto.
    + pose proof (compare_eq_iff _ _ H3); subst y.
      apply LeVars_lt_str; auto.
  - pose proof (compare_eq_iff _ _ H); subst y.
    inv H23.
    + constructor.
    + apply LeVars_lt_str; auto.
    + pose proof (compare_eq_iff _ _ H5); subst y.
      pose proof (Nat.lt_trans _ _ _ H0 H6).
      apply LeVars_end_nat; auto.
    + pose proof (compare_eq_iff _ _ H4); subst y.
      apply LeVars_end_nat; auto.
  - pose proof (compare_eq_iff _ _ H); subst x n.
    inv H23.
    + constructor.
    + apply LeVars_lt_str; auto.
    + pose proof (compare_eq_iff _ _ H4); subst y0.
      apply LeVars_end_nat; auto.
    + pose proof (compare_eq_iff _ _ H3); subst y0.
      apply LeVars_cons; auto.
Qed.

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
  apply Sorted_LocallySorted_iff, StronglySorted_Sorted.
  apply Sorted_LocallySorted_iff, Sorted_StronglySorted in H;
    [| apply Rel1_Transitive_pterm_le ].
  inv H. inv H2. inv H3.
  constructor; auto.
Qed.

Lemma sorted_const_invariant :
  ∀ l'' c1 c2 c3 v1 v2,
  sorted (PTerm c1 v1 :: PTerm c2 v2 :: l'') →
  sorted (PTerm c1 v1 :: PTerm c3 v2 ::  l'').
Proof.
  intros.
  apply Sorted_LocallySorted_iff, StronglySorted_Sorted.
  apply Sorted_LocallySorted_iff, Sorted_StronglySorted in H;
    [| apply Rel1_Transitive_pterm_le ].
  inv H; inv H3. unfold pterm_le in H1; simpl in H1.
  constructor; [| constructor; unfold pterm_le; auto ].
  apply StronglySorted_Sorted, Sorted_LocallySorted_iff in H2.
  apply Sorted_StronglySorted, Sorted_LocallySorted_iff;
    [ apply Rel1_Transitive_pterm_le |].
  destruct l'' as [| [v3 c4] l'']; [ constructor |].
  inv H2. unfold pterm_le in H6; simpl in H6.
  constructor; unfold pterm_le; auto.
Qed.

