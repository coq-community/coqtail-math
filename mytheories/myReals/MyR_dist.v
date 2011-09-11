Require Import Reals.
Require Import MyRIneq.

Lemma R_dist_opp_compat: forall x y,
  R_dist (- x) (- y) = R_dist x y.
Proof.
intros ; unfold R_dist ; rewrite Rminus_opp, Rabs_minus_sym ;
 apply Rabs_eq_compat ; ring.
Qed.

Lemma R_dist_scal_compat: forall a x y,
  R_dist (a * x) (a * y) = Rabs a * R_dist x y.
Proof.
intros ; unfold R_dist ; rewrite <- Rabs_mult ;
 apply Rabs_eq_compat ; ring.
Qed.