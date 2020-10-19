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
Require Import Lra.
Require Import Ranalysis Rfunctions Rtrigo_facts.
Require Import Rseries_def.
Require Import SeqProp.
Require Import Rextensionality Rpser_usual.
Require Import RIVT.
Require Import Rseries_facts.
Require Import Rsequence_cv_facts.
Require Import MyRIneq.
Require Import Tactics.
Require Import Rinterval Ranalysis_def Ranalysis_def_simpl Ranalysis_facts Ranalysis5.

Open Scope R_scope.

(** TODO: move this! *)

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

(** * Definition of arctan as the reciprocal of tan *)

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
 apply Rinv_0_lt_compat ; lra.
 apply PI6_in.
 assert (x_bd : open_interval (- PI / 2) (PI / 2) x).
  eapply open_interval_restriction.
   eapply open_interval_interval, PI6_in.
   eapply interval_r ; left ; exact _PI2_Rlt_PI2.
   assumption.
 assert (cosx_pos : 0 < cos x) by (apply cos_pos ; assumption).
 exists x ; split ; [assumption |].
  apply Rlt_le_trans with (/ (2 * cos x)).
   rewrite <- Rinv_involutive with y ; [apply Rinv_lt_contravar | apply Rgt_not_eq ; lra].
    apply Rlt_mult_inv_pos ; [apply Rmult_lt_0_compat |] ; (assumption || lra).
    apply Rmult_Rinv_lt_compat_r_rev ; [| rewrite <- Rinv_mult_distr, Rmult_comm] ;
    (assumption || apply Rgt_not_eq || idtac) ; lra.
   rewrite Rinv_mult_distr ; try (apply Rgt_not_eq ; (assumption || lra)) ;
    apply Rmult_le_compat_r ; [left ; apply Rinv_0_lt_compat ; assumption |].
    transitivity (sin (PI / 6)).
     right ; rewrite sin_PI6 ; unfold Rdiv ; ring.
     left ; apply strictly_increasing_interval_sin ;
      try apply open_interval_interval ; (exact PI6_in || eapply_assumption).
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
   (assumption || apply Rgt_not_eq ; lra).
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

(** Proof that these really are reciprocal *)

Lemma reciprocal_tan_atan : reciprocal tan atan.
Proof.
intros y _ ; unfold atan ; destruct (exists_atan y) ; eapply_assumption.
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
apply strictly_increasing_increasing, strictly_increasing_atan.
Qed.

Lemma injective_atan : injective atan.
Proof.
apply strictly_increasing_injective, strictly_increasing_atan.
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
  rewrite Rabs_Ropp, Rabs_right ; fold d ; lra.
 assert (ub_in : open_interval (- PI / 2) (PI / 2) ub).
  apply open_interval_dist_bound ; [apply open_interval_interval, atan_in |].
  rewrite Rabs_right ; fold d ; lra.
 assert (x_in : open_interval (tan lb) (tan ub) x).
 split.
  apply Rlt_le_trans with (tan (atan x)).
   apply strictly_increasing_open_interval_tan ;
    [assumption | apply atan_in | unfold lb ; lra].
   right ; apply reciprocal_tan_atan ; exact I.
  apply Rle_lt_trans with (tan (atan x)).
   right ; symmetry ; apply reciprocal_tan_atan ; exact I.
   apply strictly_increasing_open_interval_tan ;
    [apply atan_in | assumption | unfold ub ; lra].
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
    rewrite reciprocal_open_interval_atan_tan ; eapply_assumption.
    rewrite reciprocal_open_interval_atan_tan ; eapply_assumption.
    split ; apply strictly_increasing_atan ; (exact I || apply x_in).
    rewrite reciprocal_open_interval_atan_tan ; eapply_assumption.
    rewrite reciprocal_open_interval_atan_tan ; eapply_assumption.
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

(* TODO: move this! *)

Lemma x_modulo_B : forall B (B_pos : 0 < B) x,
 { k : Z | 0 < IZR k * B - x <= B }.
Proof.
intros B B_pos x ; pose (k := up (x / B)) ; exists k.
 destruct (archimed (x / B)) as [x_lb x_ub] ; fold k in x_lb, x_ub.
  split.
  apply Rlt_Rminus, Rmult_Rinv_lt_compat_l_rev, x_lb ; assumption.
  apply Rminus_le_compat_l, Rminus_le_compat_l_rev.
  apply Rmult_le_reg_r with (/ B).
   apply Rinv_0_lt_compat ; assumption.
   transitivity (IZR k - x / B).
    right ; field ; apply Rgt_not_eq ; assumption.
    rewrite Rinv_r ; [assumption | apply Rgt_not_eq, B_pos].
Qed.

Lemma x_modulo_PI : forall x, { k : Z | 0 < IZR k * PI - x <= PI }.
Proof.
apply x_modulo_B ; apply PI_RGT_0.
Qed.

Lemma tan_period : forall x, cos x <> 0 -> tan x = tan (x + PI).
Proof.
intros x H.
unfold tan. 
rewrite sin_plus. rewrite cos_plus.
rewrite cos_PI. rewrite sin_PI.
do 2 rewrite Rmult_0_r. unfold Rminus. rewrite Ropp_0.
do 2 rewrite Rplus_0_r. unfold Rdiv.
rewrite Rinv_mult_distr. change (-1) with (-(1)). rewrite <- Ropp_inv_permute.
field. apply H. discrR. apply H. discrR.
Qed.

(* TODO: move this! *)

Lemma Ropp_eq_compat_rev : forall a b, - a = - b -> a = b.
Proof.
intros a b Heq ; rewrite <- Ropp_involutive, <- Heq, Ropp_involutive ;
 reflexivity.
Qed.

Lemma Rplus_eq_compat_l_rev_strong :
  forall a b c d, a + c = b + d -> a = b -> c = d.
Proof.
intros a b c d Heq Hab ;
 replace c with (a + c - a) by ring ;
 replace d with (b + d - b) by ring ;
 subst ; apply Rplus_eq_compat_r ; assumption.
Qed.

Lemma Rminus_eq_compat_rev_strong :
  forall a b c d, a - c = b - d -> c = d -> a = b.
Proof.
intros a b c d Heq Hcd ;
 replace a with (a - c + c) by ring ;
 replace b with (b - d + d) by ring ;
 subst ; apply Rplus_eq_compat_r ; assumption.
Qed.

Lemma Rmult_eq_compat_r_rev_strong :
  forall a b c d, a * c = b * d -> c = d -> d <> 0 -> a = b.
Proof.
intros a b c d Heq Hcd c_neq.
 replace a with (a * c * / c).
 replace b with (b * d * / d).
 subst ; apply Rmult_eq_compat_r ; assumption.
 field ; subst ; assumption.
 field ; subst ; assumption.
Qed.

Lemma Rmin_le_Rmax : forall a b, Rmin a b <= Rmax a b.
Proof.
intros a b ; unfold Rmin, Rmax ; destruct (Rle_dec a b).
 assumption.
 left ; apply Rnot_le_lt ; assumption.
Qed.

Lemma Rmin_lt_Rmax : forall a b, a <> b -> Rmin a b < Rmax a b.
Proof.
intros a b Hneq ; unfold Rmin, Rmax ; destruct (Rle_dec a b).
 apply Rneq_le_lt ; assumption.
 apply Rnot_le_lt ; assumption.
Qed.

(** * Definition of arctan as the sum of a power series. *)

(** *)
Definition arctan_pos (x : R) : R.
Proof.
destruct (Rlt_le_dec x 0).
 exact 0.
 destruct (Rle_lt_dec x 1).
  exact (arctan_sum x).
  exact (2 * arctan_sum 1 - arctan_sum (/ x)).
Defined.

Definition arctan (x : R) : R.
Proof.
destruct (Rlt_le_dec x 0).
 exact (- arctan_pos (- x)).
 exact (arctan_pos x).
Defined.

Lemma arctan_explicit_Rball : Rball_eq 0 1 arctan arctan_sum.
Proof.
intros x x_in ; unfold arctan, arctan_pos, arctan_sum.
 destruct (Rlt_le_dec x 0).
  destruct (Rlt_le_dec (- x) 0).
   apply False_ind ; lra.
   destruct (Rle_lt_dec (- x) 1).
    destruct (Req_dec (- x) 1).
     destruct (Req_dec x 1).
      apply False_ind ; lra.
      apply False_ind ; destruct (Rabs_def2 _ _ x_in) ; lra.
     destruct (Req_dec x 1).
      apply False_ind ; lra.
      symmetry ; apply sum_r_arctan_odd ; assumption.
     apply False_ind ; destruct (Rabs_def2 _ _ x_in) ; lra.
    destruct (Rle_lt_dec x 1).
     reflexivity.
     apply False_ind ; destruct (Rabs_def2 _ _ x_in) ; lra.
Qed.

Lemma arctan_explicit_pos : forall x, 1 <= x ->
  arctan x = 2 * arctan 1 - arctan_sum (/ x).
Proof.
intros x x_lb ; unfold arctan, arctan_sum, arctan_pos.
 destruct (Rlt_le_dec x 0).
  apply False_ind ; lra.
  destruct (Rle_lt_dec x 1).
   destruct (Rlt_le_dec 1 0).
    apply False_ind ; lra.
    destruct (Rle_lt_dec 1 1).
     destruct (Req_dec (/ x) 1) as [Heq | Hneq].
      assert (Hx : x = 1).
       rewrite <- (Rmult_1_r x), <- Heq, Rinv_r.
        symmetry ; assumption.
        apply Rgt_not_eq ; lra.
      rewrite Hx, arctan_sum_1_PI4 ; ring.
     assert (Hx : x = 1) by (apply Rle_antisym ; assumption).
      apply False_ind, Hneq ; rewrite Hx, Rinv_1 ; reflexivity.
    apply False_ind ; lra.
   destruct (Rlt_le_dec 1 0).
    apply False_ind ; lra.
    destruct (Rle_lt_dec 1 1).
     unfold arctan_sum ; destruct (Req_dec (/ x) 1) as [Heq | Hneq].
      assert (Hx : x = 1).
       rewrite <- (Rmult_1_r x), <- Heq, Rinv_r.
        symmetry ; assumption.
        apply Rgt_not_eq ; lra.
      apply False_ind ; lra.
     reflexivity.
    apply False_ind ; lra.
Qed.

Lemma derivable_arctan_pos : forall lb ub x,
  1 <= lb -> open_interval lb ub x ->
  derivable_pt_lim_in (open_interval lb ub) arctan x (/ (1 + x ^ 2)).
Proof.
intros lb ub x lb_lb x_in.
 assert (x_pos : 0 < x) by (transitivity 1 ; [lra | apply Rle_lt_trans with lb ; eapply_assumption]).
 assert (Rinvx_in : Rball 0 1 (/ x)).
  rewrite Rball_0_simpl, Rabs_Rinv_pos, <- Rinv_1 ; [| assumption].
  apply Rinv_1_lt_contravar ; [reflexivity | apply Rle_lt_trans with lb ; eapply_assumption].
 eapply derivable_pt_lim_in_ext_strong.
  assumption.
  intros y y_in ; symmetry ; apply arctan_explicit_pos ; transitivity lb ; [| left] ; eapply_assumption.
  replace (/ (1 + x ^ 2)) with (0 - ((- 1 / (x ^ 2)) * / (1 + (/ x) ^ 2))).
  apply derivable_pt_lim_in_minus.
   apply derivable_pt_lim_in_const.
   eapply derivable_pt_lim_in_contravariant ; [eapply included_open_interval_Rball |].
   apply derivable_pt_lim_Rball_comp with (cg := 0) (rg := 1) (f := Rinv).
    apply included_open_interval_Rball; assumption.
    assumption.
    apply derivable_pt_lim_in_inv.
     apply included_open_interval_Rball ; assumption.
     apply Rgt_not_eq ; assumption.
    apply derivable_pt_lim_in_id.
    apply derivable_pt_lim_Rball_arctan_sum ; assumption.
 field ; split.
  apply Rgt_not_eq, One_plus_sqr_pos_lt.
  apply Rgt_not_eq ; assumption.
Qed.

(** *)

Lemma Rball_eq_atan_arctan_sum : Rball_eq 0 1 atan arctan_sum.
Proof.
intros x x_in ; destruct (Req_dec x 0) as [x_eq | x_neq].
 subst ; rewrite atan_0, arctan_sum_0_0 ; reflexivity.
 pose (lb := Rmin 0 x) ; pose (ub := Rmax 0 x) ;
 assert (Hbs : lb < ub).
  apply Rmin_lt_Rmax ; symmetry ; assumption.
 assert (lb_lb : - 1 < lb).
  apply Rmin_glb_lt ; [| destruct (Rabs_def2 _ _ x_in)] ; lra.
 assert (ub_ub : ub < 1).
  apply Rmax_lub_lt ; [| destruct (Rabs_def2 _ _ x_in)] ; lra.
 assert (atan_der : forall c, lb < c < ub -> derivable_pt atan c).
  intros ; apply derivable_atan.
 assert (arctan_der1 : forall c, lb <= c <= ub -> derivable_pt arctan_sum c).
  intros ; eapply derivable_Rball_derivable_pt.
   eapply derivable_Rball_arctan_sum.
   rewrite Rball_0_simpl ; apply Rabs_def1.
    apply Rle_lt_trans with ub ; eapply_assumption.
    apply Rlt_le_trans with lb ; eapply_assumption.
 assert (arctan_der : forall  c, lb < c < ub -> derivable_pt arctan_sum c).
  intros ; apply arctan_der1 ; split ; left ; eapply_assumption.
 destruct (MVT arctan_sum atan lb ub) with arctan_der atan_der as [c [c_bd Hc]].
  assumption.
  intros c c_in ; eapply derivable_continuous_pt, arctan_der1 ; assumption.
  intros ; apply continuity_atan.
 assert (c_in : Rball 0 1 c).
  rewrite Rball_0_simpl ; apply Rabs_def1.
   transitivity ub ; eapply_assumption.
   transitivity lb ; eapply_assumption.
 assert (eq_in_0 : atan 0 = arctan_sum 0) by (rewrite atan_0, arctan_sum_0_0 ; reflexivity).
 assert (eq_in_c : derive_pt arctan_sum c (arctan_der c c_bd) = derive_pt atan c (atan_der c c_bd)).
  rewrite derive_pt_atan ; apply derive_pt_eq_0, derivable_pt_lim_Rball_pt_lim with 0 1.
  assumption.
  apply derivable_pt_lim_Rball_arctan_sum ; assumption.
 assert (der_neq : derive_pt atan c (atan_der c c_bd) <> 0).
  rewrite derive_pt_atan ; apply Rinv_neq_0_compat, Rgt_not_eq, One_plus_sqr_pos_lt.
 unfold ub, lb, Rmin, Rmax in Hc ; destruct (Rle_dec 0 x) as [x_pos | x_neg].
  eapply Rminus_eq_compat_rev_strong, eq_in_0.
   eapply Rmult_eq_compat_r_rev_strong, der_neq ; try eapply eq_in_c.
   exact Hc.
  eapply Ropp_eq_compat_rev, Rplus_eq_compat_l_rev_strong, eq_in_0.
   eapply Rmult_eq_compat_r_rev_strong, der_neq ; try eapply eq_in_c.
   exact Hc.
Qed.
