Require Import Reals Ranalysis_def Rinterval.
Require Import MyRIneq Fourier.

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

Lemma R_dist_Rplus_compat: forall x h, R_dist (x + h) x = Rabs h.
Proof.
intros ; apply Rabs_eq_compat ; ring.
Qed.

Lemma R_dist_Rminus_compat: forall x h, R_dist (x - h) x = Rabs h.
Proof.
intros ; rewrite <- Rabs_Ropp ; apply Rabs_eq_compat ; ring.
Qed.

Lemma dense_interval: forall lb ub x, lb < ub ->
  interval lb ub x -> dense (interval lb ub) x.
Proof.
intros lb ub x Hlt [xlb xub] eps eps_pos ; destruct xlb as [xlb | xeq].
 destruct xub as [xub | xeq].
  pose (h := Rmin (eps / 2) (interval_dist lb ub x)) ;
  assert (h_pos : 0 < h).
   apply Rmin_pos_lt, open_interval_dist_pos ;
   [fourier | split ; assumption].
  exists (x + h) ; split.
   split.
    apply interval_dist_bound ; [split ; left ; assumption |].
    rewrite Rabs_right ; [apply Rmin_r | left ; assumption].
    apply Rplus_pos_neq ; assumption.
   rewrite R_dist_Rplus_compat, Rabs_right ; [| left ; assumption].
    apply Rle_lt_trans with (eps / 2) ; [apply Rmin_l | fourier].
  pose (h := Rmin (eps / 2) (ub - lb)) ;
  assert (h_pos : 0 < h) by (apply Rmin_pos_lt ; fourier).
   exists (x - h) ; split. split. split.
    transitivity (x - (ub - lb)).
     right ; subst ; ring.
     apply Rplus_le_compat_l, Ropp_le_contravar, Rmin_r.
     left ; subst ; apply Rminus_pos_lt ; assumption.
     subst ; apply Rgt_not_eq, Rminus_pos_lt ; assumption.
     rewrite R_dist_Rminus_compat, Rabs_right ; [| left ; assumption].
     apply Rle_lt_trans with (eps / 2) ; [apply Rmin_l | fourier].
  pose (h := Rmin (eps / 2) (ub - lb)) ;
  assert (h_pos : 0 < h) by (apply Rmin_pos_lt ; fourier).
   exists (x + h) ; split. split. split.
    left ; rewrite xeq ; apply Rplus_pos_lt ; assumption.
    transitivity (x + (ub - lb)) ; [| right ; rewrite xeq ; ring].
     apply Rplus_le_compat_l, Rmin_r.
     apply Rlt_not_eq, Rplus_pos_lt ; assumption.
     rewrite R_dist_Rplus_compat, Rabs_right ; [| left ; assumption].
     apply Rle_lt_trans with (eps / 2) ; [apply Rmin_l | fourier].
Qed.  