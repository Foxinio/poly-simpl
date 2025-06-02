Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia Bool.Bool Lists.List Strings.String Recdef Wf_nat Sorting.Permutation.
(* From Coq Require Import ssreflect. *)
Require Import Coq.Classes.Equivalence.
Import ListNotations.


Require Import Syntax Utils.

Fixpoint cmp_vars (l1 l2 : var_list) : comparison :=
  match l1, l2 with
  | (x, n) :: l1', (y, m) :: l2' =>
      match compare x y with
      | Lt => Lt
      | Gt => Gt
      | Eq =>
          if n <? m then Lt
          else if m <? n then Gt
          else cmp_vars l1' l2'
      end
  | [], [] => Eq
  | _,  [] => Lt
  | [],  _ => Gt
  end.

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

Fixpoint cvar_count (l : list pterm) (x : var_list) : Z :=
  match l with
  | PTerm c v :: l' =>
      match cmp_vars v x with
      | Eq => (c + cvar_count l' x)%Z
      | _ => cvar_count l' x
      end
  | [] => 0
  end.

Definition vlequiv (l1 l2 : list pterm) :=
  ∀ vars : var_list, cvar_count l1 vars = cvar_count l2 vars.
Hint Unfold vlequiv : core.
Notation "a '≡ᵥ' b" := (vlequiv a b) (at level 70).

Lemma vlequiv_app l1 l2 vars :
  cvar_count (l1++l2) vars = (cvar_count l1 vars + cvar_count l2 vars)%Z.
Proof.
  induction l1 as [| [c v] l1']; simpl; auto.
  rewrite IHl1'.
  destruct (cmp_vars v vars); lia.
Qed.

Lemma vlequiv_perm (la lb : list pterm) :
  Permutation la lb → vlequiv la lb.
Proof.
  generalize dependent lb.
  induction la as [| [c v] la']; simpl; intros lb HPerm vars; auto.
  - pose proof (Permutation_nil HPerm); now subst.
  - symmetry in HPerm.
    pose proof (Permutation_vs_cons_inv HPerm) as [l1 [l2 Hdiv]]; subst.
    assert (Permutation ((PTerm c v) :: l1 ++ l2) ((PTerm c v) :: la'));
    [ etransitivity; [ eapply Permutation_middle | assumption] |].
    pose proof (Permutation_cons_inv H); symmetry in H0.
    rewrite vlequiv_app; simpl.
    rewrite (IHla' _ H0).
    rewrite vlequiv_app.
    destruct (cmp_vars v vars); lia.
Qed.

Lemma vlequiv_skip l1 : ∀ a l2,
  vlequiv l1 l2 → vlequiv (a :: l1) (a :: l2).
Proof.
  induction l1; simpl; intros b l2 H vars.
  - simpl; rewrite <- H.
    destruct b as [c v], (cmp_vars v vars); simpl; lia.
  - remember (a::l1) as l1'.
    simpl; subst.
    now rewrite H.
Qed.

Lemma vlequiv_skip_rev l1 : ∀ a l2,
  vlequiv l1 l2 → vlequiv (a :: l1) (l2 ++ [a]).
Proof.
  induction l1; simpl; intros b l2 H vars.
  - simpl. rewrite vlequiv_app, <- H. now simpl.
  - remember (a::l1) as l1'.
    simpl; subst.
    destruct l2.
    + rewrite H; simpl.
      destruct b, (cmp_vars vars0 vars); simpl; lia.
    + rewrite vlequiv_app, <- H; simpl.
      destruct b, (cmp_vars vars0 vars); simpl;
      destruct a, (cmp_vars vars1 vars); simpl; lia.
Qed.

Lemma vlequiv_list_perm (la lb : list(list pterm)) :
  Permutation la lb → vlequiv (List.concat la) (List.concat lb).
Proof.
Admitted.

(* Reserved Notation "a '=ᵥ' b" (at level 70). *)
(**)
(* Inductive vars_eq : var_list → var_list → Prop := *)
(*   | VEq_Nil : [] =ᵥ [] *)
(*   | VEq_Cons x n y m l1 l2 : *)
(*     x = y → n = m → *)
(*     l1 =ᵥ l2 → *)
(*     (x,n)::l1 =ᵥ (y,m)::l2 *)
(**)
(* where "a '=ᵥ' b" := (vars_eq a b). *)
(* Hint Constructors vars_eq : core. *)
(**)
(* Instance Equivalence_vars_eq : Equivalence vars_eq. *)
(* Proof. *)
(*   split. *)
(*   + intro v; induction v as [| [x n] v']; auto. *)
(*   + intro v1; induction v1 as [| [x n] v1']; intros v Heq. *)
(*     - now inv Heq. *)
(*     - inv Heq. constructor; auto. *)
(*   + intro v1; induction v1 as [| [x n] vl']; intros v2 v3 H12 H23. *)
(*     - now inv H12. *)
(*     - inv H12; inv H23. *)
(*       constructor; auto. *)
(*       eapply IHvl'; eauto. *)
(* Qed. *)
(**)
(* Lemma cmp_if_vars_eq (l1 l2: var_list) : l1 =ᵥ l2 → cmp_vars l1 l2 = Eq. *)
(* Proof. *)
(*   generalize dependent l2. *)
(*   induction l1 as [| [x n] l1']; intros l2 Heq; inv Heq; auto. *)
(*   simpl. *)
(*   rewrite Nat.ltb_irrefl, string_compare_refl. *)
(*   apply IHl1', H5. *)
(* Qed. *)
(**)
(* Lemma vars_eq_if_cmp (l1 l2: var_list) : cmp_vars l1 l2 = Eq → l1 =ᵥ l2. *)
(* Proof. *)
(*   generalize dependent l2. *)
(*   induction l1 as [| [x n] l1']; intros [| [y m] l2'] Heq; inv Heq; auto. *)
(*   simpl. *)
(*   destruct (x ?= y)%string eqn:Exy; try discriminate. *)
(*   destruct (n <? m) eqn:Enm; try discriminate; *)
(*   destruct (m <? n) eqn:Emn; try discriminate. *)
(*   pose proof (compare_eq_iff _ _ Exy). *)
(*   pose proof (nat_lt_antisym _ _ Enm Emn). *)
(*   constructor; auto. *)
(* Qed. *)
