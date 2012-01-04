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

Lemma cos_pos : forall x, open_interval (- PI/2) (PI/2) x -> 0 < cos x.
Proof.
intros x [xlb xub] ; apply cos_gt_0 ; unfold Rdiv ;
 ring_simplify ; assumption.
Qed.

Lemma strictly_increasing_interval_sin :
  strictly_increasing_interval sin (- PI / 2) (PI / 2).
Proof.
 replace (- PI / 2) with (- (PI / 2)) by field.
 do 5 intro ; apply sin_increasing_1 ; ass_apply.
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

Lemma derive_open_interval_tan_strong :
 forall lb ub x (x_in : open_interval lb ub x)
 (pr : derivable_open_interval tan lb ub),
 open_interval (- PI / 2) (PI / 2) lb ->
 open_interval (- PI / 2) (PI / 2) ub ->
 derive_open_interval tan lb ub pr x = 1 + (tan x) ^ 2.
Proof.
intros lb ub x x_in pr lb_in ub_in.
 assert (cos_neq : cos x <> 0).
  apply Rgt_not_eq, cos_pos ; eapply open_interval_restriction_compat ;
   try eassumption ; apply open_interval_interval ; assumption.
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

Lemma tan_reciprocal_image_open_interval : forall lb ub y,
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

Lemma Rle_Rminus : forall a b, a <= b -> 0 <= b - a.
Proof.
intros ; fourier.
Qed.

Lemma Rle_Rminus_rev : forall a b, 0 <= b - a -> a <= b.
Proof.
intros ; fourier.
Qed.

Lemma Rlt_Rminus_rev : forall a b, 0 < b - a -> a < b.
Proof.
intros ; fourier.
Qed.

Lemma Rmult_Rinv_lt_compat_r : forall a b c, 0 < a -> a * b < c -> b < c * / a.
Proof.
intros a b c a_pos Habc ; apply Rle_lt_trans with (a * b * / a).
 right ; field ; apply Rgt_not_eq ; assumption.
 apply Rmult_lt_compat_r ; [apply Rinv_0_lt_compat |] ; assumption.
Qed.

Lemma Rmult_Rinv_lt_compat_r_rev : forall a b c, 0 < a -> b < c * / a -> a * b < c.
Proof.
intros a b c a_pos Habc ; apply Rlt_le_trans with (a * (c * / a)).
 apply Rmult_lt_compat_l ; assumption.
 right ; field ; apply Rgt_not_eq ; assumption.
Qed.

Lemma Rmult_Rinv_lt_compat_l : forall a b c, 0 < c -> a < b * c -> a * / c < b.
Proof.
intros a b c a_pos Habc ; apply Rlt_le_trans with (b * c * / c).
 apply Rmult_lt_compat_r ; [apply Rinv_0_lt_compat |] ; assumption.
 right ; field ; apply Rgt_not_eq ; assumption.
Qed.

Lemma Rmult_Rinv_lt_compat_l_rev : forall a b c, 0 < c -> a * / c < b -> a < b * c.
Proof.
intros a b c a_pos Habc ; apply Rle_lt_trans with (a * / c * c).
 right ; field ; apply Rgt_not_eq ; assumption.
 apply Rmult_lt_compat_r ; assumption.
Qed.

Lemma derive_pt_minus : forall f g x prf prg pr,
  derive_pt (f - g)%F x pr = derive_pt f x prf - derive_pt g x prg.
Proof.
intros f g x prf prg pr ; erewrite pr_nu_var with
 (pr2 := derivable_pt_minus _ _ x prf prg) ;
 [apply derive_pt_minus | reflexivity].
Qed.

Lemma derive_pt_cos : forall x pr, derive_pt cos x pr = - sin x.
Proof.
intros x pr ; erewrite pr_nu_var with (pr2 := derivable_pt_cos x) ;
 [apply derive_pt_cos | reflexivity].
Qed.

Lemma derive_pt_sin : forall x pr, derive_pt sin x pr = cos x.
Proof.
intros x pr ; erewrite pr_nu_var with (pr2 := derivable_pt_sin x) ;
 [apply derive_pt_sin | reflexivity].
Qed.

Lemma sin_first_order : forall x, 0 <= x -> sin x <= x.
Proof.
intros x xpos ; apply Rle_Rminus_rev ; pose (g := (id - sin)%F).
 transitivity (g 0) ; [unfold g, minus_fct, id ; rewrite sin_0, Rminus_0_r ; reflexivity |].
 transitivity (g x) ; [| reflexivity].
 assert (Hg : derivable g) by (unfold g ; reg).
 eapply nonneg_derivative_1 with Hg ; [| eassumption].
 clear ; intro x ; erewrite derive_pt_minus with (prg := derivable_pt_sin x)
 (prf := derivable_pt_id x), derive_pt_id, derive_pt_sin.
 apply Rle_Rminus, COS_bound.
Qed.

Lemma sin_cv_0_right : forall eps a, 0 < eps -> 0 < a ->
  { x | open_interval 0 a x /\ sin x < eps }.
Proof.
intros eps a eps_pos a_pos ; pose (f := Rmin eps a) ;
 assert (f_pos : 0 < f) by (apply Rmin_pos_lt ; assumption) ;
 exists (f / 2) ; repeat split.
  apply Rlt_mult_inv_pos ; [assumption | fourier].
 apply Rlt_le_trans with f ; [fourier | apply Rmin_r].
 apply Rle_lt_trans with (f / 2) ; [apply sin_first_order |
  apply Rlt_le_trans with f, Rmin_l] ; fourier.
Qed.

Lemma cos_cv_0_left : forall eps a, 0 < eps -> a < PI / 2 ->
  { x | open_interval a (PI / 2) x /\ cos x < eps }.
Proof.
intros eps a eps_pos a_ub ;
 destruct (sin_cv_0_right _ (PI / 2 - a) eps_pos) as [x [[x_lb x_ub] Hx]].
 fourier.
 exists (PI / 2 - x) ; rewrite cos_shift ; repeat split ; (trivial || fourier).
Qed.

Lemma tan_cv_pos_infty_prelim : forall y , 0 < y ->
  { x | open_interval (- PI / 2) (PI / 2) x /\ y < tan x }.
Proof.
intros y y_pos ; destruct (cos_cv_0_left (/ (2 * y)) (PI / 6)) as [x [x_in Hx]].
 apply Rinv_0_lt_compat ; fourier.
 apply PI6_in.
 assert (x_bd : open_interval (- PI / 2) (PI / 2) x).
  eapply open_interval_restriction_compat.
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

Lemma Ropp_Rdiv_compat_l : forall a b, b <> 0 -> - a / b = - (a / b).
Proof.
intros ; field ; assumption.
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

Lemma Rinv_lt_contravar_rev : forall x y, 0 < x -> 0 < y -> /x < /y -> y < x.
Proof.
intros x y x_pos y_pos Hxy ; rewrite <- (Rinv_involutive x), <- (Rinv_involutive y) ;
 try (apply Rgt_not_eq ; assumption).
 apply Rinv_lt_contravar ; [| assumption] ; apply Rmult_lt_0_compat ;
 apply Rinv_0_lt_compat ; assumption.
Qed.

Lemma injective_interval_sin : injective_interval sin (- PI / 2) (PI / 2).
Proof.
apply strictly_increasing_injective_interval, strictly_increasing_interval_sin.
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
  eapply open_interval_restriction_compat ; try eassumption ;
   eapply open_interval_interval ; assumption.
  assumption.
Qed.

Definition atan (y : R) : R := let (x, _) := exists_atan y in x.

Lemma reciprocal_tan_atan : reciprocal tan atan.
Proof.
intro y ; unfold comp, id, atan ; destruct (exists_atan y) ; ass_apply.
Qed.

Lemma reciprocal_open_interval_atan_tan :
  reciprocal_open_interval atan tan (- PI / 2) (PI / 2).
Proof.
intros x x_in ; unfold comp, id, atan ;
 destruct (exists_atan (tan x)) as [x' [x'_in Hx']] ;
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
intros x y Hxy ; apply strictly_increasing_open_interval_atan ;
 try apply atan_in ; repeat fold_comp ;
 do 2 rewrite reciprocal_tan_atan ; ass_apply.
Qed.

Lemma strictly_increasing_increasing : forall f,
  strictly_increasing f -> increasing f.
Proof.
intros f Hf x y [xy_lt | xy_eq].
 left ; apply Hf ; assumption.
 subst ; reflexivity.
Qed.

Lemma strictly_increasing_interval_restriction : forall f lb ub,
  strictly_increasing f -> strictly_increasing_interval f lb ub.
Proof.
intros f lb ub Hf x y x_in y_in Hxy ; apply Hf ; assumption.
Qed.

Lemma strictly_increasing_open_interval_restriction : forall f lb ub,
  strictly_increasing f -> strictly_increasing_open_interval f lb ub.
Proof.
intros f lb ub Hf x y x_in y_in Hxy ; apply Hf ; assumption.
Qed.

Lemma increasing_atan : increasing atan.
Proof.
apply strictly_increasing_increasing, strictly_increasing_atan.
Qed.

Lemma injective_atan : injective atan.
Proof.
unfold atan ; intros x y Hxy ;
 destruct (exists_atan x) as [z1 [_ Hz1]] ;
 destruct (exists_atan y) as [z2 [_ Hz2]] ;
 subst ; reflexivity.
Qed.

Lemma x_in_Rball1 : forall x, open_interval (x - 1) (x + 1) x.
Proof.
intro x ; split ; fourier.
Qed.

Lemma continuity_open_interval_continuity : forall f,
  (forall lb ub, continuity_open_interval f lb ub ) ->
  continuity f.
Proof.
intros f Hf x eps eps_pos ;
 destruct (Hf (x - 1) (x + 1) x (x_in_Rball1 x) _ eps_pos) as [delta [delta_pos Hdelta]] ;
 exists (Rmin delta 1) ; split.
  apply Rmin_pos_lt ; fourier.
  simpl ; intros y [[_ y_neq] y_b] ; apply Hdelta ; split.
   rewrite <- (Rball_rewrite _ _ Rle_0_1) ; eapply Rlt_le_trans ; [eassumption | apply Rmin_r].
   eapply Rlt_le_trans ; [eassumption | apply Rmin_l].
Qed.

Lemma derivable_open_interval_derivable : forall f,
  (forall lb ub, derivable_open_interval f lb ub ) ->
  derivable f.
Proof.
intros f Hf x ; eapply derivable_open_interval_derivable_pt,
 x_in_Rball1 ; apply Hf ; fourier.
Qed.

Lemma strictly_increasing_open_interval_restriction_compat :
  forall (f : R -> R) (a b a' b' : R),
  open_interval a b a' -> open_interval a b b' ->
  strictly_increasing_open_interval f a b ->
  strictly_increasing_interval f a' b'.
Proof.
intros f a b a' b' a'_in b'_in Hf x y x_in y_in Hxy ;
 apply Hf ; try (apply interval_open_restriction_compat with a' b') ;
 assumption.
Qed.

Lemma reciprocal_open_interval_restriction_compat :
  forall (f g : R -> R) (a b a' b' : R),
  open_interval a b a' -> open_interval a b b' ->
  reciprocal_open_interval f g a b ->
  reciprocal_interval f g a' b'.
Proof.
intros f g a b a' b' a'_in b'_in Hf x x_in ;
 eapply Hf, interval_open_restriction_compat ;
 try eapply x_in ; assumption.
Qed.

Lemma derivable_pt_lim_open_interval_restriction_compat :
  forall (f : R -> R) (a b a' b' : R) l x,
  interval a' b' x ->
  open_interval a b a' -> open_interval a b b' ->
  derivable_pt_lim_in f (open_interval a b) x l ->
  derivable_pt_lim_in f (interval a' b') x l.
Proof.
intros ; eapply derivable_pt_lim_in_imp_compat ; [| eassumption].
 intros y y_in ; eapply interval_open_restriction_compat ;
  try eapply y_in ; assumption.
Qed.

Lemma derivable_pt_lim_open_interval_restriction_compat' :
  forall (f : R -> R) (a b a' b' : R) l x,
  open_interval a' b' x ->
  open_interval a b a' -> open_interval a b b' ->
  derivable_pt_lim_in f (open_interval a b) x l ->
  derivable_pt_lim_in f (open_interval a' b') x l.
Proof.
intros ; eapply derivable_pt_lim_in_imp_compat ; [| eassumption].
 intros y y_in ; eapply open_interval_restriction_compat ; try eassumption ;
  eapply open_interval_interval ; eassumption.
Qed.

Lemma derivable_open_interval_restriction_compat :
  forall (f : R -> R) (a b a' b' : R),
  open_interval a b a' -> open_interval a b b' ->
  derivable_open_interval f a b ->
  derivable_interval f a' b'.
Proof.
intros f a b a' b' a'_in b'_in Hf x x_in ; destruct (Hf x) as [l Hl].
 eapply interval_open_restriction_compat ; try eapply x_in ; eassumption.
 exists l ; eapply derivable_pt_lim_open_interval_restriction_compat ;
  eassumption.
Qed.

Lemma derivable_open_interval_restriction_compat' :
  forall (f : R -> R) (a b a' b' : R),
  open_interval a b a' -> open_interval a b b' ->
  derivable_open_interval f a b ->
  derivable_open_interval f a' b'.
Proof.
intros f a b a' b' a'_in b'_in Hf x x_in ; destruct (Hf x) as [l Hl].
 eapply open_interval_restriction_compat ; try eapply x_in ;
  eapply open_interval_interval ; eassumption.
 exists l ; eapply derivable_pt_lim_open_interval_restriction_compat' ;
  eassumption.
Qed.

Lemma continuity_atan : continuity atan.
Proof.
intro y ; apply continuity_open_interval_continuity ; intros lb ub x x_in.
 replace lb with (id lb) by reflexivity ; replace ub with (id ub) by reflexivity ;
 do 2 rewrite <- (reciprocal_tan_atan) ; unfold comp.
 apply continuity_reciprocal_strictly_increasing_open_interval.
  apply increasing_atan ; left ; eapply open_interval_inhabited ; eassumption.
  eapply strictly_increasing_open_interval_restriction_compat ;
   (eapply atan_in || exact strictly_increasing_open_interval_tan).
  eapply reciprocal_open_interval_restriction_compat ;
   (eapply atan_in || exact reciprocal_open_interval_atan_tan).
  eapply continuity_open_interval_continuity_interval ;
   (eapply atan_in || apply continuity_open_interval_tan).
  do 2 (fold_comp ; rewrite reciprocal_tan_atan) ; apply x_in.
Qed.

Lemma reciprocal_reciprocal_interval : forall f g lb ub,
  reciprocal f g -> reciprocal_interval f g lb ub.
Proof.
intros f g lb ub Hfg x x_in ; apply Hfg.
Qed.

Lemma reciprocal_reciprocal_open_interval : forall f g lb ub,
  reciprocal f g -> reciprocal_open_interval f g lb ub.
Proof.
intros f g lb ub Hfg x x_in ; apply Hfg.
Qed.

Lemma derive_pt_in_uniqueness : forall f x lb ub pr pr',
  lb < ub -> interval lb ub x ->
  derive_pt_in f (interval lb ub) x pr = derive_pt_in f (interval lb ub) x pr'.
Proof.
intros f x lb ub [l Hl] [l' Hl'] Hlu x_in ;
 apply derivable_pt_lim_interval_uniqueness with f lb ub x ;
 ass_apply.
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
   right ; apply reciprocal_tan_atan.
  apply Rle_lt_trans with (tan (atan x)).
   right ; symmetry ; apply reciprocal_tan_atan.
   apply strictly_increasing_open_interval_tan ;
    [apply atan_in | assumption | unfold ub ; fourier].
 apply derivable_pt_lim_open_interval_derivable_pt_lim with (tan lb) (tan ub).
  assumption.
  replace (x ^ 2) with (tan (atan x) ^ 2) by (f_equal ; apply reciprocal_tan_atan).
  assert (pr : derivable_open_interval tan (atan (tan lb)) (atan (tan ub))).
   eapply derivable_open_interval_restriction_compat', derivable_open_interval_tan ;
    fold_comp ; rewrite reciprocal_open_interval_atan_tan ; ass_apply.
  rewrite <- derive_open_interval_tan_strong with (atan (tan lb)) (atan (tan ub)) (atan x) pr.
   eapply derivable_pt_lim_in_reciprocal_open_interval.
   apply reciprocal_reciprocal_interval, reciprocal_tan_atan.
   split ; apply strictly_increasing_atan ; apply x_in.
   apply continuity_pt_continue_in, continuity_atan.
   assumption.
   rewrite derive_open_interval_tan_strong.
    apply Rgt_not_eq, One_plus_sqr_pos_lt.
    split ; apply strictly_increasing_atan ; apply x_in.
    fold_comp ; rewrite reciprocal_open_interval_atan_tan ; ass_apply.
    fold_comp ; rewrite reciprocal_open_interval_atan_tan ; ass_apply.
    split ; apply strictly_increasing_atan ; apply x_in.
    fold_comp ; rewrite reciprocal_open_interval_atan_tan ; ass_apply.
    fold_comp ; rewrite reciprocal_open_interval_atan_tan ; ass_apply.
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
 rewrite <- Ha ; fold (comp atan tan a) ;
  rewrite reciprocal_open_interval_atan_tan ; [| assumption].
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
 rewrite <- Ha ; fold (comp atan tan a) ; rewrite reciprocal_open_interval_atan_tan ;
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

Lemma derivable_pt_lim_in_id : forall D x,
  derivable_pt_lim_in id D x 1.
Proof.
intros ; apply derivable_pt_lim_derivable_pt_lim_in,
 derivable_pt_lim_id.
Qed.

Lemma atan_inv_constant_pos : forall x, x <> 0 ->
  derivable_pt_lim (atan + comp atan (/ id))%F x 0.
Proof.
intros x x_pos ; replace 0 with (/ (1 + x ^ 2) - / (1 + x ^ 2)) by ring.
 apply derivable_pt_lim_plus.
  apply derivable_pt_lim_atan.
  replace (- / (1 + x ^ 2)) with (/ (1 + (/ id)%F x ^ 2) * (- 1 / (id x ^ 2))).
  apply derivable_pt_lim_comp.
   apply derivable_pt_lim_open_interval_derivable_pt_lim with (x - 1) (x + 1).
    apply x_in_Rball1.
    apply derivable_pt_lim_in_inv_compat.
     apply x_in_Rball1.
     assumption.
     apply derivable_pt_lim_in_id.
     apply derivable_pt_lim_atan.
    unfold id, inv_fct ; field ; split ;
    [apply Rgt_not_eq ; apply One_plus_sqr_pos_lt | assumption].
Qed.

Lemma Rminus_lt_compat_l : forall a b c, a < b + c -> a - b < c.
intros ; fourier.
Qed.

Lemma Rminus_le_compat_l : forall a b c, a <= b + c -> a - b <= c.
intros ; fourier.
Qed.

Lemma Rminus_le_compat_r : forall a b c, a + c <= b -> a <= b - c.
Proof.
intros ; fourier.
Qed.

Lemma Rminus_le_compat_l_rev : forall a b c, a - b <= c -> a <= b + c.
Proof.
intros ; fourier.
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
