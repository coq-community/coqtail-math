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
Require Import AltSeries.
Require Import Rseries_def.
Require Import SeqProp.
Require Import Rinterval Ranalysis_def Ranalysis_facts.
Require Import Ranalysis5.
Require Import RIVT.
Require Import Rseries_facts.
Require Import Rsequence_cv_facts.

Open Scope R_scope.

Lemma cos_pos : forall x, open_interval (- PI/2) (PI/2) x -> 0 < cos x.
Proof.
intros x [xlb xub] ; apply cos_gt_0 ; unfold Rdiv ;
 ring_simplify ; assumption.
Qed.

Lemma derivable_derivable_open_interval : forall f lb ub,
  derivable f -> derivable_open_interval f lb ub.
Proof.
intros f lb ub pr x x_in ; apply derivable_pt_derivable_pt_in, pr.
Qed.

Lemma derivable_open_interval_id : forall lb ub, derivable_open_interval id lb ub.
Proof.
intros ; apply derivable_derivable_open_interval, derivable_id.
Qed.

Lemma derive_pt_id : forall x pr, derive_pt id x pr = 1.
Proof.
intros ; rewrite <- derive_pt_id with x ; apply pr_nu_var ; reflexivity.
Qed.

Lemma derivable_open_interval_tan : derivable_open_interval tan (- PI / 2) (PI / 2).
Proof.
intros x x_in ; apply derivable_pt_derivable_pt_in, derivable_pt_div ;
 try reg ; apply Rgt_not_eq, cos_pos ; assumption.
Qed.

Lemma continuity_open_interval_tan : continuity_open_interval tan (- PI / 2) (PI / 2).
Proof.
intros ; apply derivable_continuous_open_interval, derivable_open_interval_tan.
Qed.

Lemma derive_pt_tan : forall x (cosx_neq: cos x <> 0) (pr: derivable_pt tan x),
 derive_pt tan x pr = 1 + (tan x) ^ 2.
Proof.
intros ; unfold tan ; reg ; unfold Rsqr ; simpl ; field ; assumption.
Qed.

Lemma derive_pt_derive_open_interval : forall f lb ub x
  (pr1 : derivable_open_interval f lb ub) (pr2 : derivable_pt f x),
  open_interval lb ub x ->
  derive_open_interval f lb ub pr1 x = derive_pt f x pr2.
Proof.
intros f lb ub x pr1 [l Hl] Hx ; unfold derive_open_interval ;
 destruct (in_open_interval_dec lb ub x) as [x_in | x_out].
  destruct (pr1 x x_in) as [l' Hl'] ; apply uniqueness_limite with f x.
   eapply derivable_pt_lim_open_interval_derivable_pt_lim ; eassumption.
   assumption.
  contradiction.
Qed.

Lemma derive_open_interval_tan : forall x (x_in : open_interval (- PI / 2) (PI / 2) x)
 (pr : derivable_open_interval tan (- PI / 2) (PI / 2)),
 derive_open_interval tan (- PI / 2) (PI / 2) pr x = 1 + (tan x) ^ 2.
Proof.
intros x x_in pr.
 assert (cos_neq : cos x <> 0) by (apply Rgt_not_eq, cos_pos ; assumption).
 assert (pr' : derivable_pt tan x) by (apply derivable_pt_div ; (reg || assumption)).
 rewrite <- (derive_pt_tan _ cos_neq pr') ; apply derive_pt_derive_open_interval ;
 assumption.
Qed.

Lemma derive_open_interval_pos_strictly_increasing_open_interval :
  forall f lb ub (pr : derivable_open_interval f lb ub),
  (forall x (x_in : open_interval lb ub x), 0 < derive_open_interval f lb ub pr x) ->
  strictly_increasing_open_interval f lb ub.
Proof.
intros f lb ub pr Df_pos x y x_in y_in Hxy.
 assert (pr1 : forall c : R, x < c < y -> derivable_pt f c).
  intros ; eapply derivable_open_interval_derivable_pt ; [eapply pr |].
   eapply open_interval_restriction_compat ; try eassumption ;
   apply open_interval_interval ; eassumption.
 assert (pr2 : forall c : R, x < c < y -> derivable_pt id c) by (intros ; apply derivable_id).
 destruct (MVT f id x y pr1 pr2) as [c [c_in Hc]].
  assumption.
  intros ; eapply derivable_continuous_pt, derivable_open_interval_derivable_pt ;
   [eapply pr | apply interval_open_restriction_compat with x y ; assumption].
  intros ; reg.
  unfold id in Hc ; fold id in Hc ; replace (derive_pt id c (pr2 c c_in)) with 1 in Hc ;
   [rewrite Rmult_1_r in Hc |].
  apply Rminus_gt ; rewrite <- Hc ; apply Rmult_lt_0_compat ; [fourier |].
   erewrite <- derive_pt_derive_open_interval ; [eapply Df_pos |] ;
    eapply open_interval_restriction_compat ;
    try (eapply open_interval_interval || apply c_in) ; eassumption.
  symmetry ; apply derive_pt_id.
Qed.

Lemma sqr_pos : forall x, 0 <= x ^ 2.
Proof.
 intros ; rewrite <- Rsqr_pow2 ; apply Rle_0_sqr.
Qed.

Lemma One_plus_sqr_pos_lt : forall x, 0 < 1 + x ^ 2.
Proof.
intro x ; replace 0 with (0 + 0) by ring ;
 apply Rplus_lt_le_compat ; [fourier | apply sqr_pos].
Qed.

Lemma strictly_increasing_open_interval_tan :
  strictly_increasing_open_interval tan (- PI / 2) (PI / 2).
Proof.
apply derive_open_interval_pos_strictly_increasing_open_interval
 with (derivable_open_interval_tan).
intros x x_in ; rewrite derive_open_interval_tan ;
 [apply One_plus_sqr_pos_lt | assumption].
Qed.

Lemma strictly_increasing_injective_open_interval : forall f lb ub,
  strictly_increasing_open_interval f lb ub -> injective_open_interval f lb ub.
Proof.
intros f lb ub Hf x y x_in y_in Heq ; destruct (Rlt_le_dec x y) as [x_lt_y | y_le_x].
 destruct (Rlt_irrefl (f x)) ; apply Rlt_le_trans with (f y).
  apply Hf ; assumption.
  rewrite Heq ; reflexivity.
 destruct y_le_x as [y_lt_x | y_eq_x] ; [| symmetry ; trivial].
  destruct (Rlt_irrefl (f x)) ; apply Rle_lt_trans with (f y).
   right ; assumption.
   apply Hf ; assumption.
Qed.

Lemma strictly_increasing_open_interval_order : forall f lb ub a b,
  open_interval lb ub a -> open_interval lb ub b ->
  strictly_increasing_open_interval f lb ub ->
  f a < f b -> a < b.
Proof.
intros f lb ub a b a_in b_in Hf Hfafb ; destruct (Rlt_le_dec a b) as [altb | blea].
 assumption.
 destruct blea as [blta | beqa].
  destruct (Rlt_irrefl (f a)) ; transitivity (f b).
   assumption.
   apply Hf ; assumption.
  rewrite beqa in Hfafb ; destruct (Rlt_irrefl _ Hfafb).
Qed.

Lemma strictly_increasing_interval_order : forall f lb ub a b,
  open_interval lb ub a -> open_interval lb ub b ->
  strictly_increasing_open_interval f lb ub ->
  f a <= f b -> a <= b.
Proof.
intros f lb ub a b a_in b_in Hf Hfafb ; destruct (Rle_lt_dec a b) as [aleb | blta].
 assumption.
 destruct (Rlt_irrefl (f a)) ; apply Rle_lt_trans with (f b).
  assumption.
  apply Hf ; assumption.
Qed.

Lemma strictly_increasing_injective_interval : forall f lb ub,
  strictly_increasing_interval f lb ub -> injective_interval f lb ub.
Proof.
intros f lb ub Hf x y x_in y_in Heq ; destruct (Rlt_le_dec x y) as [x_lt_y | y_le_x].
 destruct (Rlt_irrefl (f x)) ; apply Rlt_le_trans with (f y).
  apply Hf ; assumption.
  rewrite Heq ; reflexivity.
 destruct y_le_x as [y_lt_x | y_eq_x] ; [| symmetry ; trivial].
  destruct (Rlt_irrefl (f x)) ; apply Rle_lt_trans with (f y).
   right ; assumption.
   apply Hf ; assumption.
Qed.

Lemma injective_open_interval_tan : injective_open_interval tan (- PI / 2) (PI / 2).
Proof.
apply strictly_increasing_injective_open_interval ;
apply strictly_increasing_open_interval_tan.
Qed.

Lemma continuity_open_interval_continuity_interval : forall f lb ub x y,
  continuity_open_interval f lb ub -> open_interval lb ub x ->
  open_interval lb ub y -> continuity_interval f x y.
Proof.
intros f lb ub x y Hf x_in y_in z z_in ; eapply limit1_imp, Hf.
 intros t t_in ; eapply interval_open_restriction_compat, t_in ; assumption.
 eapply interval_open_restriction_compat, z_in ; assumption.
Qed.

Lemma tan_reciprocal_image : forall lb ub y,
  open_interval (- PI / 2) (PI / 2) lb ->
  open_interval (- PI / 2) (PI / 2) ub ->
  open_interval (tan lb) (tan ub) y ->
  { x | open_interval lb ub x /\ tan x = y }.
Proof.
intros lb ub y lb_in ub_in y_in ; apply IVT_open_interval.
 eapply continuity_open_interval_continuity_interval ; try eassumption.
 apply continuity_open_interval_tan.
 eapply strictly_increasing_open_interval_order ; try eassumption.
  apply strictly_increasing_open_interval_tan.
  eapply open_interval_inhabited ; eassumption.
 assumption.
Qed.

Lemma exists_atan : forall lb ub y,
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
  destruct (tan_reciprocal_image _ _ _ lb_in ub_in y_in) as [z [z_in Hz]] ;
   exists z ; split ; [apply open_interval_interval |] ; assumption.
  exists ub ; split ; [apply interval_r | symmetry] ; assumption.
Qed.

Lemma lim_cos : limit1_in cos (fun x => PI/2 <> x) 0 (PI/2).
Proof.
generalize continuity_cos. intros.
unfold continuity in H.
generalize (H (PI/2)). intros.
unfold continuity_pt, continue_in in H0.
simpl in *. rewrite cos_PI2 in H0.
unfold D_x in H0.
unfold no_cond in *.
apply H0.
Qed.

Lemma sin_first_order : forall x, 0 <= x -> sin x <= x.
Proof.
intros x xpos.
pose (g := fun x => x - sin x).
cut (0 <= g x).
 intro; unfold g in *; fourier.
replace 0 with (g 0) by (unfold g; rewrite sin_0; field).
assert (Hg : derivable g) by (unfold g; reg).
apply (nonneg_derivative_1 g Hg); auto.
clear xpos x.
intro.
apply Rle_trans with (1 - cos x).
 pose proof COS_bound x; intuition; fourier.
 
 apply Req_le.
 pose proof derive_pt_id as Hid.
 pose proof derive_pt_sin as Hsin.
 rewrite <- Hid with x.
 rewrite <- Hsin.
 rewrite <- derive_pt_minus.
 apply pr_nu_var.
 trivial.
Qed.

Lemma sin_cv_0_right_sig : forall eps, eps > 0 -> {x | 0 < x /\ sin x < eps}.
Proof.
intros e epos.
exists (e / 2); split; [fourier | ].
eapply Rle_lt_trans.
 apply sin_first_order; fourier.
 fourier.
Qed.

Lemma sin_cv_0_right_sig_local : forall e a, e > 0 -> a > 0 -> {x | 0 < x < a /\ sin x < e}.
Proof.
intros e a epos apos.
destruct (Rle_lt_dec e a).
 exists (e / 2); repeat split; [fourier | | ].
 apply Rlt_le_trans with e; auto; fourier.
 eapply Rle_lt_trans.
  apply sin_first_order; fourier.
  fourier.
 
 exists (a / 2); repeat split; auto; try fourier.
 apply Rlt_le_trans with a; try fourier.
 eapply Rle_lt_trans.
  apply sin_first_order; fourier.
  fourier.
Qed.

Lemma cos_cv_0_left_sig_local : forall e a, e > 0 -> a < PI / 2 -> {x | a < x < PI / 2 /\ cos x < e}.
Proof.
intros e a epos ainf.
destruct (sin_cv_0_right_sig_local e (PI / 2 - a) epos) as [x Hx].
 fourier.
exists (PI / 2 - x); repeat split; intuition; try fourier.
rewrite cos_shift.
auto.
Qed.

Lemma tan_cv_pos_infty : forall y, {x | - PI / 2 < x < PI/2 /\ tan x > y}.
Proof.
intros y.
assert (__PI2_PI2 : - PI / 2 = - (PI / 2)) by field.
destruct (total_order_T 0 y) as [[Cy|Cy]|Cy].
 cut (forall e, e > 0 -> {x | PI / 6 < x < PI / 2 /\ 0 < cos x < e}).
  intro cos_small.
  destruct (cos_small (/ (2 * y))) as [x [[Hxi Hxs] Hx]].
   apply Rlt_gt.
   apply Rinv_0_lt_compat.
   fourier.
  assert (xpos : 0 < x).
   apply Rlt_trans with (PI / 6); auto.
   fourier.
  exists x; repeat split.
   apply Rlt_trans with 0.
    rewrite __PI2_PI2; apply _PI2_RLT_0.
    auto.
   auto.
   
   unfold tan.
   apply Rlt_le_trans with (/ (cos x * 2)).
    rewrite <- Rinv_involutive with y; [|apply Rgt_not_eq; fourier].
    apply Rinv_lt_contravar; intuition.
     apply Rlt_mult_inv_pos; fourier.
     
     replace (/ y) with (/ (2 * y) * 2) by (field; apply Rgt_not_eq; auto).
     apply Rmult_lt_compat_r; auto; fourier.
    
    replace (/ (cos x * 2)) with (/ 2 / cos x) by (field; apply Rgt_not_eq; intuition; fourier).
    unfold Rdiv.
    apply Rmult_le_compat_r.
     apply Rlt_le; apply Rinv_0_lt_compat; intuition.
     replace (/ 2) with (1 / 2) by field.
     rewrite <- sin_PI6.
     apply sin_incr_1; fourier.
  
  clear Cy y.
  intros e epos.
  destruct (cos_cv_0_left_sig_local e (PI / 6) epos) as [x Hx].
   exact PI6_RLT_PI2.
  exists x.
  intuition.
  apply cos_gt_0; fourier.
 
 exists (PI / 4); repeat split.
  apply Rlt_trans with 0.
   rewrite __PI2_PI2; apply _PI2_RLT_0.
   apply PI4_RGT_0.
  apply PI4_RLT_PI2.
  rewrite tan_PI4; subst.
  fourier.
  
 exists 0; repeat split.
  rewrite __PI2_PI2; apply _PI2_RLT_0.
  apply PI2_RGT_0.
  
  unfold tan.
  rewrite sin_0.
  unfold Rdiv; rewrite Rmult_0_l.
  intuition.
Qed.

Lemma tan_cv_neg_infty : forall y, {x | - PI / 2 < x < PI / 2 /\ tan x < y}.
Proof.
intros y.
assert (__PI2_PI2 : - PI / 2 = - (PI / 2)) by field.
destruct (tan_cv_pos_infty (- y)) as [x [Hxi Hxs] Hx].
exists (- x); repeat split.
 rewrite __PI2_PI2; apply Ropp_lt_contravar; intuition.
 apply Ropp_lt_cancel; rewrite Ropp_involutive; rewrite <- __PI2_PI2; intuition.
 rewrite tan_neg; apply Ropp_lt_cancel; rewrite Ropp_involutive; intuition.
Qed.

Lemma inv_lt : forall x y, x > 0 -> y > 0 -> /x < /y -> x > y.
Proof.
intros x y Hx Hy H.
assert ((- x) * / x > (- x) * / y) as H0.
apply Rmult_lt_gt_compat_neg_l ; intuition.
repeat rewrite Ropp_mult_distr_l_reverse in H0.
apply Ropp_lt_cancel in H0.
rewrite Rinv_r in H0.
assert ((-y) * 1 > (-y) * (x * /y)) as H3.
apply Rmult_lt_gt_compat_neg_l ; intuition.
repeat rewrite Ropp_mult_distr_l_reverse in H3.
apply Ropp_lt_cancel in H3.
rewrite Rmult_1_r in H3. rewrite Rmult_comm in H3.
rewrite Rmult_assoc in H3. rewrite Rinv_l in H3. 
rewrite Rmult_1_r in H3. assumption.
intro H5. rewrite H5 in Hy. fourier.
intro H5. rewrite H5 in Hx. fourier.
Qed.

Lemma Rgt_Rinv : forall x y : R, 0 < x -> 0 < y -> x > y -> / y > / x.
Proof.
intros x y H H1 H2.
rewrite <- Rmult_1_l.
replace (/y) with (1 * /y) by ring.
rewrite <- Rinv_r with y.
replace (y * / y * / y) with (/y * (y * /y)) by ring.
replace (y * / y * / x) with (/y * (y * /x)) by ring.
apply Rmult_gt_compat_l. intuition.
rewrite <- Rmult_1_l. 
rewrite Rinv_r.
rewrite <- Rinv_l with x.
replace (/x * x * (y * /x)) with (/x * ((x*/x)*y)) by ring.
apply Rmult_gt_compat_l. intuition.
rewrite Rinv_r. rewrite Rmult_1_l.
assumption. intro H10. rewrite H10 in *. fourier.
intro H10. rewrite H10 in *. fourier.
intro H10. rewrite H10 in *. fourier.
intro H10. rewrite H10 in *. fourier.
Qed.

Lemma sin_incr : forall x y, -(PI/2) <= x -> -(PI/2) <= y ->
x <= PI/2 -> y <= PI/2 -> sin x = sin y -> x = y.
Proof.
intros x y Hmx Hmy Hpx Hpy H.
destruct (total_order_T x y) as [[H1|H1]|H1].
apply sin_increasing_1 in H1 ; intuition.
rewrite H in H1. fourier. intuition.
apply sin_increasing_1 in H1 ; intuition.
rewrite H in H1. fourier.
Qed.

Lemma tan_increasing3 :
  forall x y:R,
    -PI/2 < x ->
    x < PI/2 -> -PI/2 < y -> y < PI/2 -> tan x < tan y -> x < y.
Proof.
intros.
destruct (total_order_T (x) (y)) as [[H4|H4]|H4].
assumption.
rewrite H4 in *.
fourier.
apply tan_increasing in H4.
fourier.
assumption.
assumption.
assumption.
assumption.
Qed.

Lemma M_PI2_MPI_2_same : forall x, - (PI / 2) < x <-> - PI / 2 < x.
Proof.
split; replace (- PI / 2) with (- (PI / 2)) by field; auto.
Qed.

Lemma tan_increasing_5 : forall lb ub y, 
- PI/2 < lb < PI/2 -> - PI/2 < ub < PI/2 ->
tan lb < y -> tan ub > y -> ub > lb.
Proof.
intros lb ub y H1 H2 H3 H4.
assert (H : tan ub > tan lb).
destruct H1. destruct H2.
eapply Rlt_trans ; eauto.
apply tan_increasing3; intuition.
Qed.
(*
Definition myatan2 (lb ub y:R) (lb_def : - PI / 2 < lb) (ub_def : ub < PI / 2)
 (lb_lt_ub : lb < ub) (Pr: tan lb <= y <= tan ub) :=
 let (a,_) := (exists_myatan lb ub y lb_def ub_def lb_lt_ub Pr) in a.

Definition myarctan : R -> R.
Proof.
intro y.
destruct (tan_cv_neg_infty y) as (lb, H).
destruct (tan_cv_pos_infty y) as (ub, H1).
destruct H as (lb_def, H).
destruct H1 as (ub_def, H1). 
assert (lb_lt_ub : lb < ub). 
apply Rgt_lt.
apply (tan_increasing_5 lb ub y); intuition; replace (- PI / 2) with (- (PI / 2)) by field; auto.
destruct lb_def as (lb_def, _).
destruct ub_def as (_, ub_def).
assert (Pr : tan lb <= y <= tan ub).
split ; fourier.
destruct (exists_myatan lb ub y lb_def ub_def lb_lt_ub Pr) as (x, atanx).
exact x.
Defined.
*)
Lemma exists_arctan : forall y : R, {x : R| -PI/2 < x < PI/2 /\ tan x = y }.
Proof.
intro y.
destruct (tan_cv_neg_infty y) as (lb, H).
destruct (tan_cv_pos_infty y) as (ub, H1).
destruct H as (lb_def, H).
destruct H1 as (ub_def, H1). 
assert (lb_lt_ub : lb < ub).
apply Rgt_lt. apply (tan_increasing_5 lb ub y); auto.
destruct lb_def as (lb_def, _).
destruct ub_def as (_, ub_def).
assert (Pr : tan lb <= y <= tan ub).
split ; fourier.
destruct (exists_myatan lb ub y lb_def ub_def lb_lt_ub Pr) as (x, atanx).
exists x.
destruct atanx. intuition.
eapply Rlt_le_trans. apply lb_def. assumption. 
eapply Rle_lt_trans; [|apply ub_def]; assumption.
Defined.

Definition arctan : R -> R.
Proof.
intro y.
destruct (exists_arctan y).
exact x.
Defined.

Lemma tanarctan : forall y, tan (arctan y) = y.
Proof.
intros y.
unfold arctan.
destruct (exists_arctan y).
intuition.
Qed.

Lemma arctantan : forall x, -PI/2 < x < PI/2 -> arctan (tan x) = x.
Proof.
intros x H.
unfold arctan. 
destruct (exists_arctan (tan x)).
apply tan_is_inj ; intuition.
Qed.

Lemma tanarctandev1 : forall x, derivable_pt (fun x => tan (arctan x)) x ->
 derivable_pt (fun y:R => y) x.
Proof.
intros x.
unfold derivable_pt.
unfold derivable_pt_abs.
unfold derivable_pt_lim.
intros H.
destruct H as (l, H).
exists l.
intros eps Heps.
generalize (H eps Heps). intro H1.
destruct H1 as (delta, H1).
exists delta.
intros h H0h Habsh.
replace (x + h - x) with (tan (arctan (x + h)) - tan (arctan x)).
apply H1. assumption. assumption.
do 2 rewrite tanarctan. reflexivity.
Qed.

Lemma tanarctandev2 : forall x, derivable_pt (fun y:R => y) x 
-> derivable_pt (fun x => tan (arctan x)) x.
Proof.
intros x.
unfold derivable_pt.
unfold derivable_pt_abs.
unfold derivable_pt_lim.
intros H.
destruct H as (l, H).
exists l.
intros eps Heps.
generalize (H eps Heps). intro H1.
destruct H1 as (delta, H1).
exists delta.
intros h H0h Habsh.
replace (x + h - x) with (tan (arctan (x + h)) - tan (arctan x)).
do 2 rewrite tanarctan.
apply H1. assumption. assumption.
do 2 rewrite tanarctan. reflexivity.
Qed.

Lemma arctan_lt_mPI2 : forall x, arctan x > -PI/2.
Proof.
intros x.
unfold arctan.
destruct (exists_arctan x).
intuition.
Qed.

Lemma arctan_lt_PI2 : forall x, arctan x < PI/2.
Proof.
intros x.
unfold arctan.
destruct (exists_arctan x).
intuition.
Qed.

Lemma arctan_increasing : forall x y, x < y -> arctan x < arctan y.
Proof.
intros x y H.
apply tan_increasing3.
apply arctan_lt_mPI2.
apply arctan_lt_PI2.
apply arctan_lt_mPI2.
apply arctan_lt_PI2.
do 2 rewrite tanarctan.
assumption.
Qed.

Lemma arctan_inj : forall x y, arctan x = arctan y -> x = y.
Proof.
intros x y H.
unfold arctan in H.
destruct (exists_arctan x) as (x1, H2).
destruct (exists_arctan y) as (y1, H3).
destruct H2 as (H2, H4).
destruct H3 as (H3, H5).
rewrite <- H4. rewrite <- H5.
rewrite H.
reflexivity.
Qed.

Lemma continuity_open_interval_tan : continuity_open_interval tan (-PI/2) (PI/2).
Proof.
intros x Hx.
apply derivable_continuous_pt.
apply derivable_pt_tan.
assumption.
Qed.

Lemma continuity_arctan : forall b, continuity_pt arctan b.
Proof.
intros y.
destruct (tan_cv_neg_infty y) as (lb, H).
destruct (tan_cv_pos_infty y) as (ub, H1).
destruct H as (lb_def, H).
destruct H1 as (ub_def, H1). 
assert (lb_lt_ub : lb < ub). 
apply Rgt_lt. apply (tan_increasing_5 lb ub y) ; auto.
destruct lb_def as (lb_def, _).
destruct ub_def as (_, ub_def).
assert (Pr : tan lb <= y <= tan ub).
split ; fourier.
apply continuity_reciprocal_strictly_increasing_interval with tan lb ub ; intuition.
intros a b a_in_I b_in_I a_lt_b ; apply tan_increasing2 ; unfold interval in * ; intuition.
eapply Rlt_le_trans. apply lb_def. assumption.
eapply Rle_lt_trans ; [| eassumption] ; assumption.
intros a a_in_I ; apply arctantan ; split ; unfold interval, id in *.
apply Rlt_le_trans with lb ; intuition.
apply Rle_lt_trans with ub ; intuition.
intros a a_in_I ; apply continuity_open_interval_tan ; split ;
 [apply Rlt_le_trans with lb | apply Rle_lt_trans with ub] ;
 unfold interval in a_in_I ; intuition.
split. eapply Rle_lt_trans ; [eapply Rmin_l |] ; assumption.
eapply Rlt_le_trans ; [| eapply RmaxLess2] ; assumption.
Qed.

Lemma arctan_increasing_le : forall x y, x <= y -> arctan x <= arctan y.
Proof.
intros x y H3.
destruct H3 as [H3|H3].
left. apply arctan_increasing. assumption.
right. rewrite H3. reflexivity.
Qed.

Lemma derivable_pt_arctan : forall x, derivable_pt arctan x.
Proof.
intros y.
destruct (tan_cv_neg_infty y) as (lb, H).
destruct (tan_cv_pos_infty y) as (ub, H1).
destruct H as (lb_def, H).
destruct H1 as (ub_def, H1). 
assert (lb_lt_ub : lb < ub). 
apply Rgt_lt. apply (tan_increasing_5 lb ub y) ; assumption.
destruct lb_def as (lb_def, _).
destruct ub_def as (_, ub_def).
assert (Pr : tan lb <= y <= tan ub).
split ; fourier.
destruct (exists_myatan lb ub y lb_def ub_def lb_lt_ub Pr) as (x, atanx).
assert (x_encad : open_interval (tan lb) (tan ub) y) by (unfold open_interval ; intuition).
assert (f_eq_g : reciprocal_interval tan arctan (tan lb) (tan ub)).
unfold reciprocal_interval ; intuition ; apply tanarctan.
assert (g_wf:forall x : R, interval (tan lb) (tan ub) x -> interval lb ub (arctan x)).
unfold interval ; intuition. rewrite <- (arctantan lb).
apply arctan_increasing_le. assumption.
split. assumption. eapply Rlt_trans. apply lb_lt_ub. assumption.
rewrite <- (arctantan ub). 
apply arctan_increasing_le. assumption.
split. eapply Rlt_trans. apply lb_def. assumption. assumption.
assert (f_incr : strictly_increasing_interval tan lb ub).
unfold strictly_increasing_interval ; intros. apply tan_increasing2 ; intuition.
eapply Rlt_le_trans. apply lb_def. apply (proj1 H0).
eapply Rle_lt_trans ; [| apply ub_def] ; apply (proj2 H2).
assert (fderivable : derivable_interval tan lb ub).
unfold derivable_interval ; intros. apply derivable_pt_tan. intuition.
eapply Rlt_le_trans. apply lb_def. apply (proj1 H0).
eapply Rle_lt_trans ; [| apply ub_def] ; apply (proj2 H0).
apply derivable_pt_recip_interv with tan lb ub lb_lt_ub x_encad f_eq_g g_wf f_incr fderivable.
destruct atanx as (atanx1, atanx2).
unfold derive_pt. unfold proj1_sig.
destruct derivable_pt_reciprocal_interval_rev as (x0, H10).
assert (PR : -PI/2 < x < PI/2).
destruct atanx1 as (atanx11, atanx12).
split. eapply Rlt_le_trans. apply lb_def. assumption.
eapply Rle_lt_trans. Focus 2. apply ub_def. assumption. 
rewrite <- atanx2 in H10. rewrite (arctantan x PR) in H10.
intro H20. rewrite H20 in H10.
generalize (derive_pt_tan x PR).
intros. unfold derive_pt in H0.
destruct derivable_pt_tan as (x1, H22) in H0.
unfold proj1_sig in H0. 
rewrite H0 in H22.
assert (1 + tan x ^ 2 = 0).
apply (uniqueness_limite tan x).
assumption.
assumption.
assert (1 + (tan x) ^ 2 > 0) by (apply plus_Rsqr_gt_0).
fourier.
Qed.

Lemma derive_pt_arctan : forall (x:R),  
forall (Pratan:derivable_pt arctan x), derive_pt arctan x Pratan = 1/(1 + x^2).
Proof.
intros y Pratan.
destruct (tan_cv_neg_infty y) as (lb, H).
destruct (tan_cv_pos_infty y) as (ub, H1).
destruct H as (lb_def, H).
destruct H1 as (ub_def, H1). 
assert (lb_lt_ub : lb < ub). 
apply Rgt_lt. apply (tan_increasing_5 lb ub y) ; assumption.
destruct lb_def as (lb_def, _).
destruct ub_def as (_, ub_def).
assert (Pr : tan lb <= y <= tan ub).
split ; fourier.
destruct (exists_myatan lb ub y lb_def ub_def lb_lt_ub Pr) as (x, atanx).
assert (x_encad : tan lb < y < tan ub) by intuition.
assert (f_eq_g : forall x, tan lb <= x -> x <= tan ub -> comp tan arctan x = id x).
intuition. apply tanarctan.
assert (g_wf:forall x : R, tan lb <= x -> x <= tan ub -> lb <= arctan x <= ub).
intuition. rewrite <- (arctantan lb).
apply arctan_increasing_le. assumption.
split. assumption. eapply Rlt_trans. apply lb_lt_ub. assumption.
rewrite <- (arctantan ub). 
apply arctan_increasing_le. assumption.
split. eapply Rlt_trans. apply lb_def. assumption. assumption.
assert (f_incr:forall x y : R, lb <= x -> x < y -> y <= ub -> tan x < tan y).
intros. apply tan_increasing2 ; intuition.
eapply Rlt_le_trans. apply lb_def. assumption.
eapply Rle_lt_trans. Focus 2. apply ub_def. assumption.
assert (fderivable : forall a : R, lb <= a <= ub -> derivable_pt tan a).
intros. apply derivable_pt_tan. intuition.
eapply Rlt_le_trans. apply lb_def. assumption.
eapply Rle_lt_trans. Focus 2. apply ub_def. assumption.
destruct atanx as (atanx1, atanx2).
assert (PR : -PI/2 < x < PI/2).
destruct atanx1 as (atanx11, atanx12).
split. eapply Rlt_le_trans. apply lb_def. assumption.
eapply Rle_lt_trans. Focus 2. apply ub_def. assumption.
assert (arctanx : x = arctan y).
rewrite <- (arctantan x). rewrite atanx2. reflexivity. assumption.
assert (Prf : derivable_pt tan (arctan y)).
apply derivable_pt_tan. rewrite <- arctanx. assumption.
assert (Prg : derivable_pt arctan y). apply derivable_pt_arctan.

rewrite <- atanx2 at 2. 
rewrite <- (derive_pt_tan x PR).
rewrite (derive_pt_recip_interv_prelim0 tan arctan (tan lb) (tan ub) y Prf).
destruct derivable_pt_tan.
destruct Prf.
unfold derive_pt.
simpl.
rewrite arctanx in *.
assert (x1 = x0). apply (uniqueness_limite tan (arctan y)).
assumption. assumption.
intuition. intuition. unfold reciprocal_open_interval ; intros ; apply f_eq_g ;
try (apply open_interval_interval ; assumption) ; intuition.
left ; apply (proj1 H0).
left ; apply (proj2 H0).
intro Hf.
assert (1 + tan (arctan y) ^ 2 > 0).
apply plus_Rsqr_gt_0.
rewrite derive_pt_tan2 in Hf.
fourier.
intro Hf2 ; apply cos_eq_0_0 in Hf2.
destruct Hf2 as (k, H11).
generalize (arctan_lt_PI2 y).
generalize (arctan_lt_mPI2 y).
intros H12 H14.
induction k. simpl in H11. rewrite Rmult_0_l in H11.
rewrite Rplus_0_l in H11. fourier.
simpl in H11. destruct (nat_of_P p).
simpl in H11. rewrite Rmult_0_l in H11.
rewrite Rplus_0_l in H11. fourier.
assert (INR (S n) * PI + PI/2 > arctan y).
intros. replace (arctan y) with ((arctan y) + 0) by ring.
rewrite Rplus_comm.
apply Rplus_gt_compat. assumption.
apply Rmult_gt_0_compat. intuition. apply PI_RGT_0.
fourier.
simpl in H11. destruct (nat_of_P p).
simpl in H11. ring_simplify in H11. fourier.
assert (-INR (S n) * PI + PI/2 < arctan y).
intros. rewrite S_INR. unfold Rdiv. ring_simplify. 
replace (- INR n * PI+PI */ 2 - PI) with (- INR n * PI + -PI * / 2).
replace (arctan y) with ((arctan y) + 0) by ring.
rewrite Rplus_comm. destruct n. simpl. ring_simplify. intuition.
apply Rplus_gt_compat. assumption.
rewrite Ropp_mult_distr_l_reverse. apply Ropp_0_lt_gt_contravar.
apply Rmult_gt_0_compat. intuition. apply PI_RGT_0.
field.
fourier.
Qed.

Lemma arctan0 : arctan 0 = 0.
Proof.
unfold arctan.
destruct exists_arctan as (x, H).
destruct H as (H1, H2).
apply tan_is_inj. assumption. intuition.
unfold Rdiv. rewrite  Ropp_mult_distr_l_reverse.
apply _PI2_RLT_0. apply PI2_RGT_0.
rewrite tan_0. assumption.
Qed.

Lemma arctanPI4 : arctan (1) = PI/4.
Proof.
unfold arctan.
destruct exists_arctan as (x, H).
destruct H as (H1, H2).
apply tan_is_inj. assumption.
intuition. eapply (Rlt_trans). 
unfold Rdiv. rewrite  Ropp_mult_distr_l_reverse.
apply _PI2_RLT_0. apply PI4_RGT_0. apply PI4_RLT_PI2.
rewrite tan_PI4. assumption.
Qed.

Lemma derivable_arctan : derivable arctan.
Proof.
intro x.
apply derivable_pt_arctan.
Qed.

Lemma arctancos : forall x, cos (arctan x) = 1/ (sqrt( 1 + x^2)).
Proof.
intro x.
destruct (exists_arctan x) as (a, H).
destruct H as (H1, H2).
generalize (cos_pos a). intros H10.
rewrite <- H2. rewrite arctantan.
unfold tan.
field_simplify (1 + (sin a / cos a) ^ 2).
replace ((sin a) ^ 2 + (cos a) ^2) with (Rsqr (sin a) + Rsqr (cos a)) by
(unfold Rsqr ; simpl ; ring).
rewrite (sin2_cos2 a).
replace (1 / (cos a) ^ 2) with ((/cos a) * (/cos a)).
rewrite sqrt_square. unfold Rdiv. rewrite Rmult_1_l.
rewrite Rinv_involutive. reflexivity.
intro H11. rewrite H11 in H10. intuition. fourier.
left. apply Rinv_0_lt_compat. apply H10. assumption.
field. 
intro H11. rewrite H11 in H10. intuition. fourier.
intro H11. rewrite H11 in H10. intuition. fourier.
assumption.
Qed.

Lemma arctansin : forall x, sin (arctan x) = x / (sqrt (1 + x ^ 2)).
Proof.
intro x.
destruct (exists_arctan x) as (a, H).
destruct H as (H1, H2).
generalize (cos_pos a). intros H10.
rewrite <- H2. rewrite arctantan.
unfold tan.
field_simplify (1 + (sin a / cos a) ^ 2).
replace ((sin a) ^ 2 + (cos a) ^2) with (Rsqr (sin a) + Rsqr (cos a)) by
(unfold Rsqr ; simpl ; ring).
rewrite (sin2_cos2 a).
replace (1 / (cos a) ^ 2) with ((/cos a) * (/cos a)).
rewrite sqrt_square. field.
intro H11. rewrite H11 in H10. intuition. fourier.
left. apply Rinv_0_lt_compat. apply H10. assumption.
field. 
intro H11. rewrite H11 in H10. intuition. fourier.
intro H11. rewrite H11 in H10. intuition. fourier.
assumption.
Qed.

Lemma arctan_inv_PI2_1 : forall x0, x0 > 0 -> 
forall Pf : derivable_pt (fun x : R => (arctan x + arctan (/ id x))%R) x0,
    derive_pt (fun x : R => (arctan x + arctan (/ id x))%R) x0 Pf = 0.
Proof.
intros x0 Hx.
replace (/x0) with (/ id x0). Focus 2. intuition.
assert (Pf : derivable_pt (fun x => arctan x + arctan (/ id x)) x0).
reg.
intro H1. replace (id x0) with x0 in H1 by intuition. rewrite H1 in Hx. fourier.
apply derivable_arctan.
apply derivable_arctan.
assert (forall (Pf : derivable_pt (fun x => arctan x + arctan (/ id x)) x0),
 derive_pt (fun x : R => (arctan x + arctan (/ id x))%R) x0 (Pf) = 0).
intros Pf0.
reg.
replace 0 with (1/ (1 + x0 ^ 2) + -1 / (1 + x0 ^ 2)). Focus 2. field. 
assert (1 + x0 ^ 2 > 0). apply plus_Rsqr_gt_0. intro H10. rewrite H10 in *. fourier.
assert (H3 : derivable_pt (fun x => arctan(/id x)) x0). reg.
replace (1/(1 + x0^2)) with (derive_pt arctan x0 H).
Focus 2. rewrite derive_pt_arctan. reflexivity.
replace (-1/(1 + x0^2)) with (derive_pt (fun x0 => arctan (/ id x0)) x0 H3).
Focus 2.
replace (-1 / (1 + x0 ^ 2)) with ((-1 / x0 ^ 2) * 1 / (1 + (1 / x0 ^ 2))).
Focus 2. field. split. assert (1 + x0 ^2 > 0) by (apply plus_Rsqr_gt_0). 
intro H10. rewrite H10 in *. fourier.
intuition.
Focus 2. assert (H4 : (derivable_pt (/id) x0)). reg.
replace (-1 / x0 ^2) with (derive_pt (/id) x0 H4). Focus 2. 
assert (H6 : derivable_pt id x0). reg.
replace 1 with (derive_pt id x0 H6). replace (x0 ^ 2) with (Rsqr (id x0)).
rewrite <- (derive_pt_inv id x0 H6 H1).
destruct derivable_pt_inv. simpl. unfold derive_pt. destruct H4.
simpl.
apply (uniqueness_limite (/id)%F x0 x1 x).
assumption. assumption. unfold Rsqr. simpl. intuition.
reg.
rewrite <- derive_pt_plus.
reg. destruct derivable_pt_plus. destruct Pf0. simpl.
apply (uniqueness_limite (fun x => arctan x + arctan (/id x)) x0 x1 x).
assumption. assumption.
unfold Rdiv. rewrite Rmult_assoc.
replace (1 */ (1 + 1 */ x0 ^ 2)) with (derive_pt arctan (/id x0) H0).
rewrite Rmult_comm.
reg. rewrite <- derive_pt_comp.
reg. destruct H3. destruct derivable_pt_comp. simpl.
apply (uniqueness_limite (fun x : R => arctan (/ id x)) x0).
assumption. assumption.
rewrite derive_pt_arctan. compute. field.
split. intuition. generalize (plus_Rsqr_gt_0 x0). intro H10.
intro H11. rewrite <- H11 in H10. ring_simplify in H10. fourier.
intro H10. rewrite H10 in Hx. fourier.
apply derivable_pt_arctan.
apply derivable_pt_arctan.
assumption.
Qed.

Lemma arctan_inv_mPI2_1 : forall x0, x0 < 0 -> 
forall Pf : derivable_pt (fun x : R => (arctan x + arctan (/ id x))%R) x0,
    derive_pt (fun x : R => (arctan x + arctan (/ id x))%R) x0 Pf = 0.
Proof.
intros x0 Hx.
assert (Pf : derivable_pt (fun x => arctan x + arctan (/ id x)) x0).
reg.
intro H1. replace (id x0) with x0 in H1 by intuition. rewrite H1 in Hx. fourier.
apply derivable_arctan.
apply derivable_arctan.
assert (forall (Pf : derivable_pt (fun x => arctan x + arctan (/ id x)) x0),
 derive_pt (fun x : R => (arctan x + arctan (/ id x))%R) x0 (Pf) = 0).
intros Pf0.
reg.
replace 0 with (1/ (1 + x0 ^ 2) + -1 / (1 + x0 ^ 2)). Focus 2. field. 
assert (1 + x0 ^ 2 > 0). apply plus_Rsqr_gt_0. intro H10. rewrite H10 in *. fourier.
assert (H3 : derivable_pt (fun x => arctan(/id x)) x0). reg.
replace (1/(1 + x0^2)) with (derive_pt arctan x0 H).
Focus 2. rewrite derive_pt_arctan. reflexivity.
replace (-1/(1 + x0^2)) with (derive_pt (fun x0 => arctan (/ id x0)) x0 H3).
Focus 2.
replace (-1 / (1 + x0 ^ 2)) with ((-1 / x0 ^ 2) * 1 / (1 + (1 / x0 ^ 2))).
Focus 2. field. split. assert (1 + x0 ^2 > 0) by (apply plus_Rsqr_gt_0). 
intro H10. rewrite H10 in *. fourier.
intuition.
Focus 2. assert (H4 : (derivable_pt (/id) x0)). reg.
replace (-1 / x0 ^2) with (derive_pt (/id) x0 H4). Focus 2. 
assert (H6 : derivable_pt id x0). reg.
replace 1 with (derive_pt id x0 H6). replace (x0 ^ 2) with (Rsqr (id x0)).
rewrite <- (derive_pt_inv id x0 H6 H1).
destruct derivable_pt_inv. simpl. unfold derive_pt. destruct H4.
simpl.
apply (uniqueness_limite (/id)%F x0 x1 x).
assumption. assumption. unfold Rsqr. simpl. intuition.
reg.
rewrite <- derive_pt_plus.
reg. destruct derivable_pt_plus. destruct Pf0. simpl.
apply (uniqueness_limite (fun x => arctan x + arctan (/id x)) x0 x1 x).
assumption. assumption.
unfold Rdiv. rewrite Rmult_assoc.
replace (1 */ (1 + 1 */ x0 ^ 2)) with (derive_pt arctan (/id x0) H0).
rewrite Rmult_comm.
reg. rewrite <- derive_pt_comp.
reg. destruct H3. destruct derivable_pt_comp. simpl.
apply (uniqueness_limite (fun x : R => arctan (/ id x)) x0).
assumption. assumption.
rewrite derive_pt_arctan. compute. field.
split. intuition. generalize (plus_Rsqr_gt_0 x0). intro H10.
intro H11. rewrite <- H11 in H10. ring_simplify in H10. fourier.
intro H10. rewrite H10 in Hx. fourier.
apply derivable_pt_arctan.
apply derivable_pt_arctan.
assumption.
Qed.

Lemma exist_0_mPI : forall x, 
  {k : Z| forall x1, (x1 = IZR k * PI - x) -> 
    0 < x1 <= PI}.
Proof.
intros x.
exists (up (x/PI)).
intros x1 H.
destruct (archimed (x/PI)).
apply (Rmult_gt_compat_r PI) in H0.
apply (Rmult_le_compat_r PI) in H1.
unfold Rdiv in *. rewrite Rmult_assoc in H0.
rewrite <- Rinv_l_sym in H0. unfold Rminus in *.
rewrite Rmult_plus_distr_r in H1. 
replace (-(x */PI) * PI) with (-x) in H1 by (field ; apply PI_neq0).
rewrite Rmult_1_l in H1. rewrite Rmult_1_r in H0.
apply Rgt_minus in H0.
rewrite H. intuition.
apply PI_neq0. left. assert (2 * PI > 0). apply Rgt_2PI_0.
fourier. 
assert (2 * PI > 0). apply Rgt_2PI_0. fourier.
Qed.

Lemma cos2PI_period : forall x k, cos x = cos (x + 2 * IZR ( k ) * PI).
Proof.
intros.
destruct (k). simpl. ring_simplify (x + 2 * 0 * PI).
reflexivity.
simpl. destruct (nat_of_P p). simpl. ring_simplify (x + 2 * 0 * PI).
reflexivity.
rewrite cos_period. reflexivity.
simpl. destruct (nat_of_P p). simpl. ring_simplify (x + 2 * - 0 * PI).
reflexivity.
replace (x + 2 * - INR (S n) * PI) with (x - (0 + 2 * INR (S n) * PI)) by ring.
rewrite cos_minus. rewrite cos_period. rewrite sin_period.
rewrite cos_0. rewrite sin_0. ring.
Qed.

Lemma sin2PI_period : forall x k, sin x = sin (x + 2 * IZR ( k ) * PI).
Proof.
intros.
destruct (k). simpl. ring_simplify (x + 2 * 0 * PI).
reflexivity.
simpl. destruct (nat_of_P p). simpl. ring_simplify (x + 2 * 0 * PI).
reflexivity.
rewrite sin_period. reflexivity.
simpl. destruct (nat_of_P p). simpl. ring_simplify (x + 2 * - 0 * PI).
reflexivity.
replace (x + 2 * - INR (S n) * PI) with (x - (0 + 2 * INR (S n) * PI)) by ring.
rewrite sin_minus. rewrite cos_period. rewrite sin_period.
rewrite cos_0. rewrite sin_0. ring.
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
