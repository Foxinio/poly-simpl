From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Lia Strings.String Recdef Wf_nat Sorting.Permutation.
From Stdlib.Lists Require Import List ListDec.
Require Import Stdlib.Classes.Equivalence.
Import ListNotations.

From PolySimpl Require Import Syntax Utils Algorithm BasicProps.
From PolySimpl Require Import PFlattenProps ClearZPProps ReduceMonomProps ReconstructProps.
From PolySimpl Require Import PolyUniqueness.

Import Int.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope Int_scope.


Eval compute in poly_simpl <{ X + X }>.
Eval compute in poly_simpl <{ X - X }>.

Eval compute in poly_simpl <{ 2*X - X }>.
Eval compute in poly_simpl <{ Y - X }>.

Eval compute in poly_simpl <{ 2*W*(X + 4*Y) - 13*(12*X*(7*W + X)+2*Y)+3*W}>.


(* ======================================================================== *)
(* new poly_simpl *)


Eval compute in poly_simpl' <{ X + X }>.
Eval compute in poly_simpl' <{ X - X }>.

Eval compute in poly_simpl' <{ 2*X - X }>.
Eval compute in poly_simpl' <{ Y - X }>.

Eval compute in poly_simpl' <{ 2*W*(X + 4*Y) - 13*(12*X*(7*W + X)+2*Y)+3*W}>.
