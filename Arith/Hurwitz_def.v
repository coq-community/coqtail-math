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
Infix " h* " := hmul (at level 60).

(** External operations *)

Definition IZH (n : Z) : Hurwitz := mkHurwitz (2 * n) (- n) (- n) (- n).

Definition hsmul (k : Z) (h1 : Hurwitz) : Hurwitz :=
  let (h1, i1, j1, k1) := h1 in
  mkHurwitz (k * h1) (k * i1) (k * j1) (k * k1).

(** Conjugate, norm *)

Definition hconj (h : Hurwitz) :=
  let (a, b, c, d) := h in
  mkHurwitz a (- a - b) (- a - c) (- a - d).

Definition hnorm2 (h1 : Hurwitz) := (- i (hmul h1 (hconj h1)))%Z.

Definition is_real (x : Hurwitz) : Prop :=
  h x + 2 * i x = 0 /\ i x = j x /\ i x = k x.


(** Divisibility, units *)

Definition h1 := mkHurwitz 2 (- 1) (- 1) (- 1).
Definition hh := mkHurwitz 1 0 0 0.
Definition hi := mkHurwitz 0 1 0 0.
Definition hj := mkHurwitz 0 0 1 0.
Definition hk := mkHurwitz 0 0 0 1. 

Definition divide (x y : Hurwitz) := { d | hmul x d = y }.

Definition is_H_unit (x : Hurwitz) := { y | hmul x y = IZH 1 }.

Inductive Z_unit := Z_one | Z_mone.

Definition halfsub (u v : Z_unit) : Z :=
  match u, v with
  | Z_one, Z_one => 0
  | Z_one, Z_mone => 1
  | Z_mone, Z_one => -1
  | Z_mone, Z_mone => 0
  end.

Definition Z_of_Z_unit (u : Z_unit) :=
  match u with
  | Z_one => 1
  | Z_mone => -1
  end.

Inductive H_unit : Hurwitz -> Type :=
  | H_unit_1 : forall u, let n := Z_of_Z_unit u in H_unit (mkHurwitz (2 * n) (- n) (- n) (- n))
  | H_unit_i : forall u, H_unit (mkHurwitz 0 (Z_of_Z_unit u) 0 0)
  | H_unit_j : forall u, H_unit (mkHurwitz 0 0 (Z_of_Z_unit u) 0)
  | H_unit_k : forall u, H_unit (mkHurwitz 0 0 0 (Z_of_Z_unit u))
  | H_unit_h : forall u v w z, H_unit (mkHurwitz
      (Z_of_Z_unit u)
      (halfsub v u)
      (halfsub w u)
      (halfsub z u)).
