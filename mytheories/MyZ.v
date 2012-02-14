Require Import ZArith.
Require Import Setoid.

Local Open Scope Z_scope.

Add Parametric Relation : Z Zle
reflexivity proved by Zle_refl
transitivity proved by Zle_trans as le.

Lemma eq_Zle : forall (x y : Z), x = y -> x <= y.
Proof.
intros ; subst ; reflexivity.
Qed.
