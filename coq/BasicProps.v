From Stdlib Require Import Int List Sorting.Sorted.
Require Import Syntax.

Import Int.
Import ListNotations.

(* ======================================================================== *)
(* Evaluation equivalence properties *)

Inductive pterm :=
  | PTerm (c : Z) (vars : var_list).

Definition vars '(PTerm _ vars) := vars.
Definition const '(PTerm c _) := c.

Definition pow (st : state) '(x, n) : Z :=
  Z.pow (st x) (Z.of_nat n).

Definition eval_pterm (st : state) '(PTerm c vars) : Z :=
  fold_left Z.mul (map (pow st) vars) c.

Fixpoint eval_pterm_list (st : state) (l : list pterm) : Z :=
  match l with
  | [] => 0_
  | c :: l' => eval_pterm_list st l' + eval_pterm st c
  end.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.
Hint Unfold aequiv : core.

Notation "a '≡' b" :=  (aequiv a b) (at level 70).

Definition ptequiv (l1 l2 : list pterm) : Prop :=
  forall (st : state),
    eval_pterm_list st l1 = eval_pterm_list st l2.
Hint Unfold ptequiv : core.

Notation "a '≡ₗ' b" :=  (ptequiv a b) (at level 70).

Definition asimpt a l :=
  forall st : state, aeval st a = eval_pterm_list st l.
Hint Unfold asimpt : core.

Notation "a '≲ₗ' l" := (asimpt a l) (at level 70).

(* ======================================================================== *)
(* Main Properties *)

Definition Correctness (f : aexp → aexp) :=
  forall a : aexp, a ≡ f a.
Hint Unfold Correctness : core.

Definition Canonality (f : aexp → aexp) :=
  forall a1 a2, a1 ≡ a2 → f a1 = f a2.
Hint Unfold Canonality : core.

(* ======================================================================== *)
(* basic pterm properties *)

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

Definition pterm_list_well_formed (l : list pterm) :=
  Forall (λ '(PTerm _ vars), sorted_uniq vars) l.
Hint Unfold pterm_list_well_formed : core.

Definition no_zero_powers (l : list pterm) :=
  Forall (λ '(PTerm _ vars),
    Forall (λ '(_, n), n <> 0) vars) l.
Hint Unfold no_zero_powers : core.

(* ======================================================================== *)
(* equiv_list properties *)

Definition pterm_equiv (p1 p2 : pterm) :=
  let '(PTerm _ v1) := p1 in
  let '(PTerm _ v2) := p2 in
  v1 = v2.

Inductive equiv_list : list pterm → Prop :=
  | EL_Single a :
      equiv_list [a]
  | EL_Cons a b l :
      equiv_list (a :: l) →
      pterm_equiv a b →
      equiv_list (b :: a :: l).
Hint Constructors equiv_list : core.

(* ======================================================================== *)
(* variables equivalence properties *)

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
  ∀ v : var_list, In v (map vars (l1 ++ l2)) →
    cvar_count l1 v = cvar_count l2 v.
Hint Unfold vlequiv : core.
Notation "a '≡ᵥ' b" := (vlequiv a b) (at level 70).

(* ======================================================================== *)
(* canon pterm properties *)

Inductive canon_pterm : list pterm → Prop :=
  | CP_nil : canon_pterm []
  | CP_cons p p' l :
      ~In p' l →
      pterm_equiv p p' →
      canon_pterm l →
      canon_pterm (p :: l)
  .
Hint Constructors canon_pterm : core.

Definition non_zero_const (ls : list pterm) :=
  Forall (λ '(PTerm c _), c <> 0%Z) ls.
Hint Unfold non_zero_const : core.

(* ======================================================================== *)
(* sorted pterm properties *)

Definition pterm_le p1 p2 :=
  cmp_vars (vars p1) (vars p2) <> Gt.
Hint Unfold pterm_le : core.

Definition sorted := LocallySorted pterm_le.
Hint Unfold sorted : core.

