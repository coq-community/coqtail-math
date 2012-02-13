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
     echo "let $x$y := $x h1 * $y h2 in"; done; done *)

Definition hmul (h1 h2 : Hurwitz) : Hurwitz :=
  let hh := h h1 * h h2 in
  let hi := h h1 * i h2 in
  let hj := h h1 * j h2 in
  let hk := h h1 * k h2 in
  let ih := i h1 * h h2 in
  let ii := i h1 * i h2 in
  let ij := i h1 * j h2 in
  let ik := i h1 * k h2 in
  let jh := j h1 * h h2 in
  let ji := j h1 * i h2 in
  let jj := j h1 * j h2 in
  let jk := j h1 * k h2 in
  let kh := k h1 * h h2 in
  let ki := k h1 * i h2 in
  let kj := k h1 * j h2 in
  let kk := k h1 * k h2 in
    mkHurwitz
      (- hh - hi - hj - hk - ih - 2 * ii - jh - 2 * jj - kh - 2 * kk)
      (hh + hi + hk + ih + ii + jh + jj + jk - kj + kk)
      (hh + hi + hj + ii - ik + jh + jj + kh + ki + kk)
      (hh + hj + hk + ih + ii + ij - ji + jj + kh + kk)
    .

Lemma rewh a b c d : h {| h := a; i := b; j := c; k := d |} = a.
auto.
Qed.

Lemma rewi a b c d : i {| h := a; i := b; j := c; k := d |} = b.
auto.
Qed.

Lemma rewj a b c d : j {| h := a; i := b; j := c; k := d |} = c.
auto.
Qed.

Lemma rewk a b c d : k {| h := a; i := b; j := c; k := d |} = d.
auto.
Qed.

Goal forall a b c, hmul a (hmul b c) = hmul (hmul a b) c.
intros [] [] [].
intros.
unfold hmul.
repeat rewrite rewh.
repeat rewrite rewi.
repeat rewrite rewj.
repeat rewrite rewk.
f_equal; ring.
Qed.