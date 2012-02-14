Require Import ZArith.

Open Scope Z_scope.

Record Hurwitz : Set := mkHurwitz { h : Z ; i : Z ; j : Z ; k : Z }.

(** Internal operations *)

Definition hopp (h1 : Hurwitz) : Hurwitz :=
  let (h1, i1, j1, k1) := h1 in
  mkHurwitz (- h1) (- i1) (- j1) (- k1).

Definition hadd (h1 h2 : Hurwitz) : Hurwitz :=
  let (h1, i1, j1, k1) := h1 in
  let (h2, i2, j2, k2) := h2 in
  mkHurwitz (h1 + h2) (i1 + i2) (j1 + j2) (k1 + k2).

Definition hminus (h1 h2 : Hurwitz) : Hurwitz := hadd h1 (hopp h2).

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
      (hh + hj + hk + ih + ii + ij - ji + jj + kh + kk).

(* awesome bash:
 for x in h i j k; do for y in h i j k; do
 echo "let $x$y := ${x}1 * ${y}2 in"; done; done *)


(** Notations *)

Notation "h-" := hopp.
Infix " h+ " := hadd (at level 50).
Infix " h- " := hminus (at level 10).
Infix " h* " := hmul (at level 70).

(** External operations *)

Definition IZH (n : Z) : Hurwitz := mkHurwitz (2 * n) (- n) (- n) (- n).

Definition hsmul (k : Z) (h1 : Hurwitz) : Hurwitz :=
  let (h1, i1, j1, k1) := h1 in
  mkHurwitz (k * h1) (k * i1) (k * j1) (k * k1).


(** Relation to quaternions *)

Definition H1 := mkHurwitz 2 (- 1) (- 1) (- 1).
Definition Hh := mkHurwitz 1 0 0 0.
Definition Hi := mkHurwitz 0 1 0 0.
Definition Hj := mkHurwitz 0 0 1 0.
Definition Hk := mkHurwitz 0 0 0 1.

Definition is_real (x : Hurwitz) : Prop :=
  h x + 2 * i x = 0 /\ i x = j x /\ i x = k x.

(* Les entiers de Hurwitz ne sont pas à composantes entières
Definition Q1 (h1 : Hurwitz) : Z := h h1 / 2.
Definition Qi (h1 : Hurwitz) : Z := h h1 / 2 + i h1.
Definition Qj (h1 : Hurwitz) : Z := h h1 / 2 + j h1.
Definition Qk (h1 : Hurwitz) : Z := h h1 / 2 + k h1.

Lemma quat_spec : forall h, h =
  hsmul (Q1 h) H1
  h+ hsmul (Qi h) Hi
  h+ hsmul (Qj h) Hj
  h+ hsmul (Qk h) Hk.
Admitted.
*)

Definition hconj (h : Hurwitz) :=
  let (a, b, c, d) := h in
  mkHurwitz a (- a - b) (- a - c) (- a - d).

Definition hnorm2 (h1 : Hurwitz) := (2 * h (hmul h1 (hconj h1)))%Z.


