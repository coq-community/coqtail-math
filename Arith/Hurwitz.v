Require Import ZArith.

Open Scope Z_scope.

Record Hurwitz : Set := mkHurwitz { h : Z ; i : Z ; j : Z ; k : Z }.

Definition hadd (h1 h2 : Hurwitz) : Hurwitz :=
 mkHurwitz (h h1 + h h2) (i h1 + i h2) (j h1 + j h2) (k h1 + k h2).

Infix " h+ " := hadd (at level 50).

Ltac hastuce := unfold hadd ; simpl ; f_equal ; ring.

Section basic_lemmas.

Variable h1 h2 h3 : Hurwitz.

Lemma hadd_comm : h1 h+ h2 = h2 h+ h1.
Proof.
hastuce.
Qed.

Lemma hadd_assoc : h1 h+ h2 h+ h3 = h1 h+ (h2 h+ h3).
Proof.
hastuce.
Qed.
