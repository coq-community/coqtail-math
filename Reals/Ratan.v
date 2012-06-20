(*
(C) Copyright 2010, COQTAIL team

Project Info: http://sourceforge.net/projects/coqtail/

This library is free software; you can redistribute it and/or modify it
under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation; either version 2.1 of the License, or
(at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301,
USA.
*)

Require Import Rbase Rtactic.
Require Import PSeries_reg.
Require Import Fourier.
Require Import Ranalysis.
Require Import Rfunctions.
Require Import AltSeries Rtrigo_facts.
Require Import Rseries_def.
Require Import SeqProp.
Require Import Rinterval Ranalysis_def Ranalysis_def_simpl Ranalysis_facts Ranalysis5.
Require Import Rextensionality Rpser_usual.
Require Import RIVT.
Require Import Rseries_facts.
Require Import Rsequence_cv_facts.
Require Import MyRIneq.
Require Import Ass_handling.

Open Scope R_scope.

Lemma Zero_in : open_interval (- PI / 2) (PI / 2) 0.
Proof.
replace (- PI / 2) with (- (PI / 2)) by field ; split ;
 [apply _PI2_RLT_0 | apply PI2_RGT_0].
Qed.

Lemma PI6_in : open_interval (- PI / 2) (PI / 2) (PI / 6).
Proof.
replace (- PI / 2) with (- (PI / 2)) by field ; split.
 transitivity 0 ; [apply _PI2_RLT_0 | apply PI6_RGT_0].
 apply PI6_RLT_PI2.
Qed.

Lemma PI4_in : open_interval (- PI / 2) (PI / 2) (PI / 4).
Proof.
replace (- PI / 2) with (- (PI / 2)) by field ; split.
 transitivity 0 ; [apply _PI2_RLT_0 | apply PI4_RGT_0].
 apply PI4_RLT_PI2.
Qed.

Lemma _PI2_Rlt_PI2 : - PI / 2 < PI / 2.
replace (- PI / 2) with (- (PI / 2)) by field ;
 transitivity 0 ; [apply _PI2_RLT_0 | apply PI2_RGT_0].
Qed.

Lemma tan_reciprocal_image_open_interval : forall lb ub y,
  open_interval (- PI / 2) (PI / 2) lb ->
  open_interval (- PI / 2) (PI / 2) ub ->
  open_interval (tan lb) (tan ub) y ->
  { x | open_interval lb ub x /\ tan x = y }.
Proof.
intros lb ub y lb_in ub_in y_in ; apply IVT_open_interval.
 eapply continuity_in_contravariant ; try (eapply interval_open_restriction ; eassumption).
 apply continuity_open_interval_tan.
 eapply strictly_increasing_open_interval_order ; try eassumption.
  apply strictly_increasing_open_interval_tan.
  eapply open_interval_inhabited ; eassumption.
 assumption.
Qed.

Lemma tan_reciprocal_image_interval : forall lb ub y,
  open_interval (- PI / 2) (PI / 2) lb ->
  open_interval (- PI / 2) (PI / 2) ub ->
  interval (tan lb) (tan ub) y ->
  { x | interval lb ub x /\ tan x = y }.
Proof.
intros lb ub y lb_in ub_in y_bd.
 assert (Hbd: lb <= ub).
  eapply strictly_increasing_interval_order ; try eassumption.
  eapply strictly_increasing_open_interval_tan.
  eapply interval_inhabited ; eassumption.
 destruct (interval_open_interval_dec _ _ _ y_bd) as [l | yeq].
 destruct l as [yeq | y_in].
  exists lb ; split ; [apply interval_l | symmetry] ; assumption.
  destruct (tan_reciprocal_image_open_interval _ _ _ lb_in ub_in y_in) as [z [z_in Hz]] ;
   exists z ; split ; [apply open_interval_interval |] ; assumption.
  exists ub ; split ; [apply interval_r | symmetry] ; assumption.
Qed.

Lemma tan_cv_pos_infty_prelim : forall y , 0 < y ->
  { x | open_interval (- PI / 2) (PI / 2) x /\ y < tan x }.
Proof.
intros y y_pos ; destruct (cos_cv_0_left (/ (2 * y)) (PI / 6)) as [x [x_in Hx]].
 apply Rinv_0_lt_compat ; fourier.
 apply PI6_in.
 assert (x_bd : open_interval (- PI / 2) (PI / 2) x).
  eapply open_interval_restriction.
   eapply open_interval_interval, PI6_in.
   eapply interval_r ; left ; exact _PI2_Rlt_PI2.
   assumption.
 assert (cosx_pos : 0 < cos x) by (apply cos_pos ; assumption).
 exists x ; split ; [assumption |].
  apply Rlt_le_trans with (/ (2 * cos x)).
   rewrite <- Rinv_involutive with y ; [apply Rinv_lt_contravar | apply Rgt_not_eq ; fourier].
    apply Rlt_mult_inv_pos ; [apply Rmult_lt_0_compat |] ; (assumption || fourier).
    apply Rmult_Rinv_lt_compat_r_rev ; [| rewrite <- Rinv_mult_distr, Rmult_comm] ;
    (assumption || apply Rgt_not_eq || idtac) ; fourier.
   rewrite Rinv_mult_distr ; try (apply Rgt_not_eq ; (assumption || fourier)) ;
    apply Rmult_le_compat_r ; [left ; apply Rinv_0_lt_compat ; assumption |].
    transitivity (sin (PI / 6)).
     right ; rewrite sin_PI6 ; unfold Rdiv ; ring.
     left ; apply strictly_increasing_interval_sin ;
      try apply open_interval_interval ; (exact PI6_in || ass_apply).
Qed.

Lemma tan_cv_pos_infty : forall y ,
  { x | open_interval (- PI / 2) (PI / 2) x /\ y < tan x }.
Proof.
intro y ; destruct (Req_dec y 0) as [y_eq | y_neq].
 exists (PI / 4) ; split ; [exact PI4_in |] ; subst ; apply tan_gt_0 ;
  [apply PI4_RGT_0 | apply PI4_RLT_PI2].
 assert (y_pos : 0 < Rabs y) by (apply Rabs_pos_lt ; assumption) ;
  destruct (tan_cv_pos_infty_prelim _ y_pos) as [x [x_in Hx]] ;
  exists x ; split ; [| apply Rgt_ge_trans with (Rabs y), Rle_ge,
  Rle_abs] ; assumption.
Qed.

Lemma tan_cv_neg_infty : forall y,
  { x | open_interval (- PI / 2) (PI / 2) x /\ tan x < y }.
Proof.
intro y ; destruct (tan_cv_pos_infty (- y)) as [x [x_in Hx]] ;
 exists (- x) ; split.
  rewrite <- (Ropp_involutive (PI /2)), Ropp_Rdiv_compat_l ;
   [apply open_interval_opp_compat ; rewrite <- Ropp_Rdiv_compat_l |] ;
   (assumption || apply Rgt_not_eq ; fourier).
 rewrite tan_neg ; apply Ropp_lt_cancel ; rewrite Ropp_involutive ; assumption.
Qed.

Lemma strictly_increasing_open_interval_atan : forall x y,
  open_interval (- PI / 2) (PI / 2) x ->
  open_interval (- PI / 2) (PI / 2) y ->
  tan x < tan y -> x < y.
Proof.
intros x y x_in y_in Hxy ; destruct (total_order_T x y) as [[Hlt | Heq] | Hgt].
 assumption.
 subst ; destruct (Rlt_irrefl _ Hxy).
 destruct (Rlt_irrefl (tan x)) ; transitivity (tan y).
  assumption.
  apply strictly_increasing_open_interval_tan ; assumption.
Qed.

Lemma exists_atan : forall y : R, { x | open_interval (- PI / 2) (PI / 2) x /\ tan x = y }.
Proof.
intro y ;
 destruct (tan_cv_neg_infty y) as [lb [lb_in Hlb]] ;
 destruct (tan_cv_pos_infty y) as [ub [ub_in Hub]] ;
 assert (y_in : open_interval (tan lb) (tan ub) y) by (split ; assumption) ;
 destruct (tan_reciprocal_image_open_interval _ _ _ lb_in ub_in y_in) as [x [x_in Hx]] ;
 exists x ; split.
  eapply open_interval_restriction ; try eassumption ;
   eapply open_interval_interval ; assumption.
  assumption.
Qed.

Definition atan (y : R) : R := let (x, _) := exists_atan y in x.

Lemma reciprocal_tan_atan : reciprocal tan atan.
Proof.
intros y _ ; unfold atan ; destruct (exists_atan y) ; ass_apply.
Qed.

Lemma reciprocal_open_interval_atan_tan :
  reciprocal_open_interval (- PI / 2) (PI / 2) atan tan.
Proof.
intros x x_in ; unfold atan ; destruct (exists_atan (tan x)) as [x' [x'_in Hx']] ;
 apply injective_open_interval_tan ; assumption.
Qed.

Lemma atan_in : forall y, open_interval (- PI / 2) (PI / 2) (atan y).
Proof.
intro y ; unfold atan ; destruct (exists_atan y) as [x [x_in _]] ; exact x_in.
Qed.

Ltac fold_comp := match goal with
  | |- context G[?f (?g ?x)] => fold (comp f g x)
end.

Lemma strictly_increasing_atan : strictly_increasing atan.
Proof.
intros x y _ _ Hxy ; apply strictly_increasing_open_interval_atan ;
 try apply atan_in ; do 2 (rewrite reciprocal_tan_atan ; [| apply I]) ;
 assumption.
Qed.

Lemma increasing_atan : increasing atan.
Proof.
apply strictly_increasing_in_increasing_in, strictly_increasing_atan.
Qed.

Lemma injective_atan : injective atan.
Proof.
apply strictly_increasing_in_injective_in, strictly_increasing_atan.
Qed.

Lemma continuity_atan : continuity atan.
Proof.
intro y ; apply continuity_open_interval_continuity ; intros lb ub x x_in.
 rewrite <- (reciprocal_tan_atan lb), <- (reciprocal_tan_atan ub) ; try (exact I).
 apply continuity_reciprocal_strictly_increasing_open_interval.
  apply increasing_atan ; (exact I || left) ; eapply open_interval_inhabited ; eassumption.
  eapply strictly_increasing_in_contravariant, strictly_increasing_open_interval_tan.
   apply interval_open_restriction ; apply atan_in.
  eapply reciprocal_in_contravariant, reciprocal_open_interval_atan_tan.
   apply interval_open_restriction ; apply atan_in.
  eapply continuity_in_contravariant, continuity_open_interval_tan.
   apply interval_open_restriction ; apply atan_in.
  do 2 (rewrite reciprocal_tan_atan ; [| exact I]) ; apply x_in.
Qed.

Lemma derivable_pt_lim_atan : forall x, derivable_pt_lim atan x (/ (1 + x ^ 2)).
Proof.
intro x ; pose (d := interval_dist (- PI / 2) (PI / 2) (atan x)) ;
 assert (d_pos : 0 < d) by (apply open_interval_dist_pos, atan_in) ;
 pose (lb := atan x - d / 2) ; pose (ub := atan x + d / 2).
 assert (lb_in : open_interval (- PI / 2) (PI / 2) lb).
  apply open_interval_dist_bound ; [apply open_interval_interval, atan_in |].
  rewrite Rabs_Ropp, Rabs_right ; fold d ; fourier.
 assert (ub_in : open_interval (- PI / 2) (PI / 2) ub).
  apply open_interval_dist_bound ; [apply open_interval_interval, atan_in |].
  rewrite Rabs_right ; fold d ; fourier.
 assert (x_in : open_interval (tan lb) (tan ub) x).
 split.
  apply Rlt_le_trans with (tan (atan x)).
   apply strictly_increasing_open_interval_tan ;
    [assumption | apply atan_in | unfold lb ; fourier].
   right ; apply reciprocal_tan_atan ; exact I.
  apply Rle_lt_trans with (tan (atan x)).
   right ; symmetry ; apply reciprocal_tan_atan ; exact I.
   apply strictly_increasing_open_interval_tan ;
    [apply atan_in | assumption | unfold ub ; fourier].
 apply derivable_pt_lim_open_interval_pt_lim with (tan lb) (tan ub).
  assumption.
  replace (x ^ 2) with (tan (atan x) ^ 2) by (f_equal ; apply reciprocal_tan_atan ; exact I).
  assert (pr : derivable_open_interval (atan (tan lb)) (atan (tan ub)) tan).
   eapply derivable_in_contravariant, derivable_open_interval_tan.
    apply open_interval_restriction ; apply open_interval_interval, atan_in.
  rewrite <- derive_open_interval_tan_strong with (atan (tan lb)) (atan (tan ub)) (atan x) pr.
   eapply derivable_pt_lim_in_reciprocal_open_interval.
   eapply reciprocal_in_contravariant, reciprocal_tan_atan ; intros a b ; exact I.
   split ; apply strictly_increasing_atan ; (exact I || apply x_in).
   apply continuity_pt_continuity_pt_in, continuity_atan.
   assumption.
   rewrite derive_open_interval_tan_strong.
    apply Rgt_not_eq, One_plus_sqr_pos_lt.
    split ; apply strictly_increasing_atan ; (exact I || apply x_in).
    rewrite reciprocal_open_interval_atan_tan ; ass_apply.
    rewrite reciprocal_open_interval_atan_tan ; ass_apply.
    split ; apply strictly_increasing_atan ; (exact I || apply x_in).
    rewrite reciprocal_open_interval_atan_tan ; ass_apply.
    rewrite reciprocal_open_interval_atan_tan ; ass_apply.
Qed.

Lemma derivable_atan : derivable atan.
Proof.
intro x ; eexists ; eapply derivable_pt_lim_atan.
Qed.

Lemma derive_pt_atan : forall x (pr : derivable_pt atan x),
  derive_pt atan x pr = / (1 + x ^ 2).
Proof.
intros x pr ; apply derive_pt_eq_0, derivable_pt_lim_atan.
Qed.

Lemma atan_0 : atan 0 = 0.
Proof.
unfold atan ; destruct (exists_atan 0) as [x [x_in Hx]].
 apply injective_open_interval_tan ; [apply x_in | apply Zero_in |].
 rewrite tan_0 ; assumption.
Qed.

Lemma atan_PI4 : atan 1 = PI / 4.
Proof.
unfold atan ; destruct (exists_atan 1) as [x [x_in Hx]].
 apply injective_open_interval_tan ; [apply x_in | apply PI4_in |].
 rewrite tan_PI4 ; assumption.
Qed.

Lemma cos_atan : forall x, cos (atan x) = 1/ (sqrt (1 + x ^ 2)).
Proof.
intro x ; destruct (exists_atan x) as [a [a_in Ha]] ;
 assert (cosa_pos : 0 < cos a) by (apply cos_pos ; assumption).
 rewrite <- Ha ; rewrite reciprocal_open_interval_atan_tan ; [| assumption].
 unfold tan ; field_simplify (1 + (sin a / cos a) ^ 2).
replace ((sin a) ^ 2 + (cos a) ^2) with (Rsqr (sin a) + Rsqr (cos a)) by
(unfold Rsqr ; simpl ; ring).
 rewrite sin2_cos2.
 replace (1 / (cos a) ^ 2) with ((/cos a) * (/cos a)).
 rewrite sqrt_square.
  unfold Rdiv ; rewrite Rmult_1_l, Rinv_involutive.
  reflexivity.
 apply Rgt_not_eq ; assumption.
 left ; apply Rinv_0_lt_compat ; assumption.
field.
 apply Rgt_not_eq ; assumption.
 apply Rgt_not_eq ; assumption.
Qed.

Lemma sin_atan : forall x, sin (atan x) = x / (sqrt (1 + x ^ 2)).
Proof.
intro x ; destruct (exists_atan x) as [a [a_in Ha]] ;
 assert (cosa_pos : 0 < cos a) by (apply cos_pos ; assumption).
 rewrite <- Ha ; rewrite reciprocal_open_interval_atan_tan ;
 [| assumption].
 unfold tan ; field_simplify (1 + (sin a / cos a) ^ 2) ; [| apply Rgt_not_eq ; assumption].
 replace ((sin a) ^ 2 + (cos a) ^2) with (Rsqr (sin a) + Rsqr (cos a))
  by (unfold Rsqr ; simpl ; ring).
 rewrite sin2_cos2.
 replace (1 / (cos a) ^ 2) with ((/cos a) * (/cos a)).
 rewrite sqrt_square ; [unfold id ; field |].
  apply Rgt_not_eq ; assumption.
  left ; apply Rinv_0_lt_compat ; assumption.
 field ; apply Rgt_not_eq ; assumption.
Qed.

Lemma atan_inv_constant_pos : forall x, x <> 0 ->
  derivable_pt_lim (atan + comp atan (/ id))%F x 0.
Proof.
intros x x_pos ; replace 0 with (/ (1 + x ^ 2) - / (1 + x ^ 2)) by ring.
 apply derivable_pt_lim_plus.
  apply derivable_pt_lim_atan.
  replace (- / (1 + x ^ 2)) with (/ (1 + (/ id)%F x ^ 2) * (- 1 / (id x ^ 2))).
  apply derivable_pt_lim_comp.
   apply derivable_pt_lim_open_interval_pt_lim with (x - 1) (x + 1).
    apply center_in_open_interval, Rlt_0_1.
    apply derivable_pt_lim_in_inv.
    apply center_in_open_interval, Rlt_0_1.
     assumption.
     apply derivable_pt_lim_in_id.
     apply derivable_pt_lim_atan.
    unfold id, inv_fct ; field ; split ;
    [apply Rgt_not_eq ; apply One_plus_sqr_pos_lt | assumption].
Qed.

Lemma x_modulo_PI : forall x, { k : Z | 0 < IZR k * PI - x <= PI }.
Proof.
intro x ; pose (k := up (x / PI)) ; exists k.
 destruct (archimed (x / PI)) as [x_lb x_ub] ; fold k in x_lb, x_ub.
  split.
  apply Rlt_Rminus, Rmult_Rinv_lt_compat_l_rev, x_lb ; exact PI_RGT_0.
  apply Rminus_le_compat_l, Rminus_le_compat_l_rev.
  apply Rmult_le_reg_r with (/ PI).
   apply Rinv_0_lt_compat, PI_RGT_0.
   transitivity (IZR k - x / PI).
    right ; field ; apply Rgt_not_eq, PI_RGT_0.
    rewrite Rinv_r ; [assumption | apply Rgt_not_eq, PI_RGT_0].
Qed.

Lemma tan_period : forall x, cos x <> 0 -> tan x = tan (x + PI).
Proof.
intros x H.
unfold tan. 
rewrite sin_plus. rewrite cos_plus.
rewrite cos_PI. rewrite sin_PI.
do 2 rewrite Rmult_0_r. unfold Rminus. rewrite Ropp_0.
do 2 rewrite Rplus_0_r. unfold Rdiv.
rewrite Rinv_mult_distr. rewrite <- Ropp_inv_permute.
field. apply H. discrR. apply H. discrR.
Qed.
