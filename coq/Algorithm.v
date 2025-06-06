Require Import Utf8.
From Coq Require Import ZArith.Int ZArith Lists.List.
From Coq Require Import Lia Strings.String.
From Coq Require Import Recdef Wf_nat.
Require Import Syntax Utils BasicProps.

Import Int.
Open Scope Int_scope.
Import ListNotations.
Import List.

(* ======================================================================== *)
(* poly_flatten *)

Definition flip_sign pt :=
  match pt with
  | PTerm c vars => PTerm (- c) vars
  end.

Function merge_vl (p : var_list*var_list) {measure len2 p} : var_list :=
  let '(vl1, vl2) := p in
  match vl1, vl2 with
  | (x, n) :: vl1', (y, m) :: vl2' =>
      if (x <? y)%string then
        (x, n) :: merge_vl (vl1', vl2)
      else if (y <? x)%string then
        (y, m) :: merge_vl (vl1, vl2')
      else (x, n+m) :: merge_vl (vl1', vl2')
  | [], _ => vl2
  | _, [] => vl1
  end.
Proof.
  all: unfold len2; simpl; lia.
Defined.
Opaque merge_vl.

Definition times_pterm pt1 pt2 :=
  match pt1, pt2 with
  | PTerm c1 vars1,
    PTerm c2 vars2 =>
    PTerm (c1 * c2) (merge_vl (vars1, vars2))
  end.

Fixpoint poly_flatten (a : aexp) : list pterm :=
  match a with
  | ANum n       => [ PTerm n []]
  | AId  x       => [ PTerm 1 [(x, 1)]]
  | APlus  a1 a2 => poly_flatten a1 ++ poly_flatten a2
  | AMinus a1 a2 => poly_flatten a1 ++ map flip_sign (poly_flatten a2)
  | AMult  a1 a2 => cross times_pterm (poly_flatten a1) (poly_flatten a2)
  end.

(* ======================================================================== *)
(* clear_zero_powers *)

Fixpoint clear_zero_powers_vl (l : var_list) : var_list :=
  match l with
  | (x , n) :: l' =>
    if n =? 0
    then clear_zero_powers_vl l'
    else (x, n) :: clear_zero_powers_vl l'
  | [] => []
  end.

Fixpoint clear_zero_powers (l : list pterm) : list pterm :=
  match l with
  | PTerm c v :: l' =>
      PTerm c (clear_zero_powers_vl v) :: clear_zero_powers l'
  | [] => []
  end.

(* ======================================================================== *)
(* reduce_monom *)

Function mergesort_monom (p : list pterm*list pterm) {measure len2 p} :=
  let '(l1, l2) := p in
  match l1, l2 with
  | PTerm c1 v1 :: l1',
    PTerm c2 v2 :: l2' =>
    match cmp_vars v1 v2 with
    | Lt => PTerm c1 v1 :: mergesort_monom (l1', l2)
    | _ => PTerm c2 v2 :: mergesort_monom (l1, l2')
    (* | Eq => PTerm (c1+c2) v1 :: merge_monom (l1', l2') *)
    end
  | [], _ => l2
  | _, [] => l1
  end.
Proof.
  all: simpl; lia.
Defined.
Opaque mergesort_monom.

Fixpoint split {X:Type} (l:list X) : (list X * list X) :=
  match l with
  | [] => ([],[])
  | [x] => ([x],[])
  | x1::x2::l' =>
    let (l1,l2) := split l' in
    (x1::l1,x2::l2)
  end.

Lemma split_len:
    forall {X} (l:list X) (l1 l2: list X),
    split l = (l1,l2) ->
    List.length l1 <= List.length l /\
    List.length l2 <= List.length l.
Proof.
  assert (IP: forall (A : Type) (P : list A -> Prop),
      P [] ->
      (forall (a:A), P [a]) ->
      (forall (a b : A) (l : list A), P l -> P (a :: b :: l)) ->
      forall l : list A, P l)
  by refine (fun (A : Type)
      (P : list A -> Prop)
      (H : P [])
      (H0 : forall a : A, P [a])
      (H1 : forall (a b : A) (l : list A), P l -> P (a :: b :: l))  =>
    fix IH (l : list A) :  P l :=
    match l with
    | [] => H
    | [x] => H0 x
    | x::y::l' => H1 x y l' (IH l')
    end).
  induction l using IP; intros.
  - inv H. lia.
  - inv H. simpl; lia.
  - inv H. destruct (split l) as [l1' l2']. inv H1.
    simpl.
    destruct (IHl l1' l2') as [P1 P2]; auto; lia.
Qed.

Function sort_monomials (l : list pterm) {measure List.length l} :=
  match l with
  | [] => []
  | [x] => [x]
  | _ => 
    let '(l1, l2) := split l in
    mergesort_monom (sort_monomials l1, sort_monomials l2)
  end.
Proof.
  - intros.
    simpl in *. destruct (split l1) as [l1' l2'] eqn:E. inv teq1. simpl.
    destruct (split_len _ _ _ E).
    lia.
  - intros.
    simpl in *. destruct (split l1) as [l1' l2'] eqn:E. inv teq1. simpl.
    destruct (split_len _ _ _ E).
    lia.
Defined.

Function reduce_monomials (l : list pterm) {measure List.length l} :=
  match l with
  | [] => []
  | [PTerm c v] =>
    if (c =? 0)%Z
    then []
    else [PTerm c v]
  | PTerm c1 v1 :: (PTerm c2 v2 :: l') as l =>
    match cmp_vars v1 v2 with
    | Eq => reduce_monomials (PTerm (c1+c2) v1 :: l')
    | _  =>
      if (c1 =? 0)%Z
      then reduce_monomials l
      else PTerm c1 v1 :: reduce_monomials l
    end
  end.
Proof.
  all: intros; simpl; lia.
Defined.


(* ======================================================================== *)
(* poly_simpl *)

Fixpoint reconstruct_var_pow x n :=
  match n with
  | 0    => ANum 1
  | S 0  => AId x
  | S n' => AMult (AId x) (reconstruct_var_pow x n')
  end.

Fixpoint reconstruct_monom c (l : var_list) : aexp :=
  match l with
  | [] => ANum c
  | (x, n) :: l' =>
      AMult (reconstruct_var_pow x n) (reconstruct_monom c l')
  end.

Fixpoint reconstruct (l : list pterm) : aexp :=
  match l with
  | [] => ANum 0
  | [PTerm c vars] => reconstruct_monom c vars
  | PTerm c vars :: l' =>
      APlus (reconstruct_monom c vars) (reconstruct l')
  end.

(* ======================================================================== *)
(* poly_simpl *)

Definition poly_simpl (a : aexp) :=
  let l1 := poly_flatten a in
  let l2 := clear_zero_powers l1 in
  let l3 := sort_monomials l2 in
  let l4 := reduce_monomials l3 in
  reconstruct l4.


