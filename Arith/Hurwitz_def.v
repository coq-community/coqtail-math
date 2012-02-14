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


(* for x in h i j k; do for y in h i j k; do
 echo "let $x$y := ${x}1 * ${y}2 in"; done; done *)

Definition hmul (h1 h2 : Hurwitz) : Hurwitz :=
  let (h1, i1, j1, k1) := h1 in
  let (h2, i2, j2, k2) := h2 in
  let hh := h1 * h2 in
  let hi := h1 * i2 in
  let hj := h1 * j2 in
  let hk := h1 * k2 in
  let ih := i1 * h2 in
  let ii := i1 * i2 in
  let ij := i1 * j2 in
  let ik := i1 * k2 in
  let jh := j1 * h2 in
  let ji := j1 * i2 in
  let jj := j1 * j2 in
  let jk := j1 * k2 in
  let kh := k1 * h2 in
  let ki := k1 * i2 in
  let kj := k1 * j2 in
  let kk := k1 * k2 in
    mkHurwitz
      (- hh - hi - hj - hk - ih - 2 * ii - jh - 2 * jj - kh - 2 * kk)
      (hh + hi + hk + ih + ii + jh + jj + jk - kj + kk)
      (hh + hi + hj + ii - ik + jh + jj + kh + ki + kk)
      (hh + hj + hk + ih + ii + ij - ji + jj + kh + kk)
    .
