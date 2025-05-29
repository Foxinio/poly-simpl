Require Import Utf8.
From Coq Require Import Recdef Wf_nat.
From Coq Require Import Lia Lists.List Strings.String.
Require Import Syntax Utils.

Import ListNotations.


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
