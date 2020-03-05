Require Import Reals Ranalysis_def Rinterval.
Require Import MyRIneq Lra.

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

Lemma R_dist_minus_compat : forall x y z, R_dist (x - z) (y - z) = R_dist x y.
Proof.
intros ; apply Rabs_eq_compat ; ring.
Qed.

Lemma R_dist_Rplus_compat: forall x h, R_dist (x + h) x = Rabs h.
Proof.
intros ; apply Rabs_eq_compat ; ring.
Qed.

Lemma R_dist_Rminus_compat: forall x h, R_dist (x - h) x = Rabs h.
Proof.
intros ; rewrite <- Rabs_Ropp ; apply Rabs_eq_compat ; ring.
Qed.

Lemma Rlt_le_Rdist_compat : forall a b c, a < b -> b <= c -> R_dist c b < R_dist c a.
Proof.
intros a b c aleb alec ; unfold R_dist ; do 3 (rewrite Rabs_right || lra).
Qed.

Lemma Rle_lt_Rdist_compat : forall a b c, a <= b -> b < c -> R_dist b a < R_dist c a.
Proof.
intros a b c aleb alec ; unfold R_dist ; do 3 (rewrite Rabs_right || lra).
Qed.
