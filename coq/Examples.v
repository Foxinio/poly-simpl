From PolySimpl Require Import Syntax Algorithm.

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
