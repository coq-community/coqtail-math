Require Import Reals Rpow_facts.
Local Open Scope R_scope.

Definition nnr_sqr (r : R) : nonnegreal.
Proof.
exists (r ^ 2) ; apply pow2_pos.
Defined.

Definition nnr_abs (r : R) : nonnegreal.
Proof.
exists (Rabs r) ; apply Rabs_pos.
Defined.