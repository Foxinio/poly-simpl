From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Lia Strings.String Recdef Wf_nat.
From Stdlib.Lists Require Import List ListDec.
Require Import Stdlib.Classes.Equivalence.
Import ListNotations.

Section DepList.
  Variable A : Type.
  Variable P : A → Prop.

  Inductive dep_list : Type :=
    | DNil : dep_list
    | DCons a (l : dep_list) : P a → dep_list
    .

  Fixpoint dl_fst (l : dep_list) : list A :=
    match l with
    | DNil => []
    | DCons a l _ => a :: dl_fst l
    end.
  Definition dl_snd (l : dep_list) := Forall P (dl_fst l).
    (* match l with *)
    (* | DNil => Forall_nil _ *)
    (* | DCons a l H => Forall_cons a H (dl_snd l) *)
    (* end. *)

  Fixpoint dl_snd' (l : dep_list) : Forall P (dl_fst l) :=
    match l with
    | DNil => Forall_nil _
    | DCons a l H => Forall_cons a H (dl_snd' l)
    end.

  Definition bad_dl_fst (_ : dep_list) : list A := [].
  (* Definition bad_dl_snd (l : dep_list) : Forall P (bad_dl_fst l) := Forall_nil _. *)


  Definition dep_list_from_list l :
    Forall P l → dep_list.
  Proof.
    induction l; intros.
    - apply DNil.
    - apply (DCons a); [ apply IHl |]; inversion H; auto.
  Defined.

End DepList.
  (*
  Lemma dep_list_non_trivial l :
    ~(Forall P l) → ~(∃ l' : dep_list, dl_snd l').
  Proof.
    unfold not in *.
    induction l; intros H [l' Hl'].
    - now apply H.
    - destruct l'.
      +   
      apply IHl.
      destruct 
    apply H.
    exact (dl_snd' l').


    dep_list_from_list l) 

  Lemma dep_list_iff l (H: Forall P l)
    let dl := dep_list_from_list l H in
    Forall P (dl_fst l) ↔ dl_snd
  Proof.
    split; intros [l Hl].
    - now exists (dep_list_from_list P l Hl).
    - induction l.
      + exists []

        *)

