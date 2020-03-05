Require Import ZArith.
Require Import Setoid.

Local Open Scope Z_scope.

Add Parametric Relation : Z Z.le
reflexivity proved by Z.le_refl
transitivity proved by Z.le_trans as le.

Lemma eq_Zle : forall (x y : Z), x = y -> x <= y.
Proof.
intros ; subst ; reflexivity.
Qed.
