Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia Lists.List Strings.String Recdef Wf_nat.
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

Function merge_monom (p : list pterm*list pterm) {measure len2 p} :=
  let '(l1, l2) := p in
  match l1, l2 with
  | PTerm c1 v1 :: l1',
    PTerm c2 v2 :: l2' =>
    match cmp_vars v1 v2 with
    | Lt => PTerm c1 v1 :: merge_monom (l1', l2)
    | Gt => PTerm c2 v2 :: merge_monom (l1, l2')
    | Eq => PTerm (c1+c2) v1 :: merge_monom (l1', l2')
    end
  | [], _ => l2
  | _, [] => l1
  end.
Proof.
  all: simpl; lia.
Defined.
Opaque merge_monom.

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

Function reduce_monomials (l : list pterm) {measure List.length l} :=
  match l with
  | [] => []
  | [x] => [x]
  | _ => 
    let '(l1, l2) := split l in
    merge_monom (reduce_monomials l1, reduce_monomials l2)
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

