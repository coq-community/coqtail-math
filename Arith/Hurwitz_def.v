Require Import ZArith.

Open Scope Z_scope.

Record Hurwitz : Set := mkHurwitz { h : Z ; i : Z ; j : Z ; k : Z }.

Definition hopp (h1 : Hurwitz) : Hurwitz :=
  mkHurwitz (- h h1) (- i h1) (- j h1) (- k h1).

Definition hadd (h1 h2 : Hurwitz) : Hurwitz :=
  mkHurwitz (h h1 + h h2) (i h1 + i h2) (j h1 + j h2) (k h1 + k h2).

Definition hminus (h1 h2 : Hurwitz) : Hurwitz := hadd h1 (hopp h2).

Notation "h-" := hopp.
Infix " h+ " := hadd (at level 50).
Infix " h- " := hminus (at level 60).

Ltac hastuce := unfold hminus, hopp, hadd ; simpl ; f_equal ; ring.


