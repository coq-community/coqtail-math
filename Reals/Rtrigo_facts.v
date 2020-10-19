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
Require Import Ranalysis Ranalysis5 Rtrigo AltSeries.
Require Import Rfunctions.
Require Import Rinterval Ranalysis_def Ranalysis_def_simpl Ranalysis_facts.
Require Import Rextensionality Rpser_usual.
Require Import Rsequence_cv_facts.
Require Import MyRIneq.
Require Import Tactics.

Open Scope R_scope.

Lemma sqr_pos : forall x, 0 <= x ^ 2.
Proof.
 intros ; rewrite <- Rsqr_pow2 ; apply Rle_0_sqr.
Qed.

Lemma One_plus_sqr_pos_lt : forall x, 0 < 1 + x ^ 2.
Proof.
intro x ; replace 0 with (0 + 0) by ring ;
 apply Rplus_lt_le_compat ; [lra | apply sqr_pos].
Qed.

Lemma cos_pos : forall x, open_interval (- PI/2) (PI/2) x -> 0 < cos x.
Proof.
intros x [xlb xub] ; apply cos_gt_0 ; unfold Rdiv ;
 ring_simplify ; assumption.
Qed.

Lemma derivable_open_interval_tan : derivable_open_interval (- PI / 2) (PI / 2) tan.
Proof.
intros x x_in ; apply derivable_pt_derivable_pt_in, derivable_pt_div ;
 try reg ; apply Rgt_not_eq, cos_pos ; assumption.
Qed.

Lemma continuity_open_interval_tan : continuity_open_interval (- PI / 2) (PI / 2) tan.
Proof.
intros ; apply derivable_in_continuity_in, derivable_open_interval_tan.
Qed.

Lemma derive_pt_tan : forall x (cosx_neq: cos x <> 0) (pr: derivable_pt tan x),
 derive_pt tan x pr = 1 + (tan x) ^ 2.
Proof.
intros ; unfold tan ; reg ; unfold Rsqr ; simpl ; field ; assumption.
Qed.

Lemma derive_open_interval_tan : forall x (x_in : open_interval (- PI / 2) (PI / 2) x)
 (pr : derivable_open_interval (- PI / 2) (PI / 2) tan),
 derive_open_interval (- PI / 2) (PI / 2) tan pr x = 1 + (tan x) ^ 2.
Proof.
intros x x_in pr.
 assert (cos_neq : cos x <> 0) by (apply Rgt_not_eq, cos_pos ; assumption).
 assert (pr' : derivable_pt tan x) by (apply derivable_pt_div ; (reg || assumption)).
 rewrite <- (derive_pt_tan _ cos_neq pr') ; apply derive_open_interval_derive_pt ;
 assumption.
Qed.

Lemma derive_open_interval_tan_strong :
 forall lb ub x (x_in : open_interval lb ub x)
 (pr : derivable_open_interval lb ub tan),
 open_interval (- PI / 2) (PI / 2) lb ->
 open_interval (- PI / 2) (PI / 2) ub ->
 derive_open_interval lb ub tan pr x = 1 + (tan x) ^ 2.
Proof.
intros lb ub x x_in pr lb_in ub_in.
 assert (cos_neq : cos x <> 0).
  apply Rgt_not_eq, cos_pos ; eapply open_interval_restriction ;
   try eassumption ; apply open_interval_interval ; assumption.
 assert (pr' : derivable_pt tan x) by (apply derivable_pt_div ; (reg || assumption)).
 rewrite <- (derive_pt_tan _ cos_neq pr') ; apply derive_open_interval_derive_pt ;
 assumption.
Qed.

Lemma strictly_increasing_open_interval_tan :
  strictly_increasing_open_interval (- PI / 2) (PI / 2) tan.
Proof.
apply derive_open_interval_pos_strictly_increasing_open_interval
 with (derivable_open_interval_tan).
intros x x_in ; rewrite derive_open_interval_tan ;
 [apply One_plus_sqr_pos_lt | assumption].
Qed.

Lemma injective_open_interval_tan : injective_open_interval (- PI / 2) (PI / 2) tan.
Proof.
apply strictly_increasing_in_injective_in, strictly_increasing_open_interval_tan.
Qed.

Lemma strictly_increasing_interval_sin :
  strictly_increasing_interval (- PI / 2) (PI / 2) sin.
Proof.
 replace (- PI / 2) with (- (PI / 2)) by field.
 do 5 intro ; apply sin_increasing_1 ; eapply_assumption.
Qed.

Lemma injective_interval_sin : injective_interval (- PI / 2) (PI / 2) sin.
Proof.
apply strictly_increasing_in_injective_in, strictly_increasing_interval_sin.
Qed.

Lemma sqr_lt_switch : forall x y, x < y -> y <= 0 -> y² < x².
Proof.
intros x y xlty yneg ; rewrite (Rsqr_neg x), (Rsqr_neg y) ;
 apply Rsqr_incrst_1 ; lra.
Qed.

Lemma sin_bound : forall x, interval (- 1) 1 (sin x).
Proof.
intro x ; destruct (Rle_lt_dec (sin x) 1) as [Hub | Hf].
 destruct (Rle_lt_dec (- 1) (sin x)) as [Hlb | Hf].
  split ; assumption.
  destruct (Rlt_irrefl 1) ; apply Rle_lt_trans with ((-(1))² + (cos x)²).
   rewrite <- Rsqr_neg, Rsqr_1 ; apply Rplus_le_simpl_l, Rle_0_sqr.
   apply Rlt_le_trans with ((sin x)² + (cos x)²).
    apply Rplus_lt_compat_r, sqr_lt_switch ; lra.
    right ; apply sin2_cos2.
  destruct (Rlt_irrefl 1) ; apply Rle_lt_trans with (1² + (cos x)²).
   rewrite Rsqr_1 ; apply Rplus_le_simpl_l, Rle_0_sqr.
   apply Rlt_le_trans with ((sin x)² + (cos x)²).
    apply Rplus_lt_compat_r, Rsqr_incrst_1 ; lra.
    right ; apply sin2_cos2.
Qed.

Lemma cos_bound : forall x, interval (- 1) 1 (cos x).
Proof.
intro x ; destruct (Rle_lt_dec (cos x) 1) as [Hub | Hf].
 destruct (Rle_lt_dec (- 1) (cos x)) as [Hlb | Hf].
  split ; assumption.
  destruct (Rlt_irrefl 1) ; apply Rle_lt_trans with ((sin x)² + (-(1))²).
   rewrite <- Rsqr_neg, Rsqr_1 ; apply Rplus_le_simpl_r, Rle_0_sqr.
   apply Rlt_le_trans with ((sin x)² + (cos x)²).
    apply Rplus_lt_compat_l, sqr_lt_switch ; lra.
    right ; apply sin2_cos2.
  destruct (Rlt_irrefl 1) ; apply Rle_lt_trans with ((sin x)² + 1²).
   rewrite Rsqr_1 ; apply Rplus_le_simpl_r, Rle_0_sqr.
   apply Rlt_le_trans with ((sin x)² + (cos x)²).
    apply Rplus_lt_compat_l, Rsqr_incrst_1 ; lra.
    right ; apply sin2_cos2.
Qed.

Lemma sin_derivable : derivable sin.
Proof.
eapply derivable_ext.
 intro x ; symmetry ; apply sin_sine.
 apply derivable_sine.
Qed.

Lemma cos_derivable : derivable cos.
Proof.
eapply derivable_ext.
 intro x ; symmetry ; apply cos_cosine.
 apply derivable_cosine.
Qed.

Lemma derive_pt_cos : forall x pr, derive_pt cos x pr = - sin x.
Proof.
intros x pr ; transitivity (- sine x).
 rewrite derive_pt_ext with (prg := derivable_cosine x).
 apply derive_pt_cosine_sine.
 apply cos_cosine.
 apply Ropp_eq_compat ; symmetry ; apply sin_sine.
Qed.

Lemma derive_pt_sin : forall x pr, derive_pt sin x pr = cos x.
Proof.
intros x pr ; transitivity (cosine x).
 rewrite derive_pt_ext with (prg := derivable_sine x).
 apply derive_pt_sine_cosine.
 apply sin_sine.
 symmetry ; apply cos_cosine.
Qed.

Lemma sin_first_order : forall x, 0 <= x -> sin x <= x.
Proof.
intros x xpos ; apply Rle_Rminus_rev ; pose (g := (id - sin)%F).
 transitivity (g 0) ; [unfold g, minus_fct, id ; rewrite sin_0, Rminus_0_r ; reflexivity |].
 transitivity (g x) ; [| reflexivity].
 assert (Hg : derivable g).
  unfold g ; apply derivable_minus ; [apply derivable_id | intro a ; apply sin_derivable].
 eapply nonneg_derivative_1 with Hg ; [| eassumption].
 clear ; intro x ; erewrite derive_pt_minus with (prg := sin_derivable x)
 (prf := derivable_pt_id x), derive_pt_id, derive_pt_sin.
 apply Rle_Rminus, cos_bound.
Qed.

Lemma sin_cv_0_right : forall eps a, 0 < eps -> 0 < a ->
  { x | open_interval 0 a x /\ sin x < eps }.
Proof.
intros eps a eps_pos a_pos ; pose (f := Rmin eps a) ;
 assert (f_pos : 0 < f) by (apply Rmin_pos_lt ; assumption) ;
 exists (f / 2) ; repeat split.
  apply Rlt_mult_inv_pos ; [assumption | lra].
 apply Rlt_le_trans with f ; [lra | apply Rmin_r].
 apply Rle_lt_trans with (f / 2) ; [apply sin_first_order |
  apply Rlt_le_trans with f, Rmin_l] ; lra.
Qed.

Lemma cos_cv_0_left : forall eps a, 0 < eps -> a < PI / 2 ->
  { x | open_interval a (PI / 2) x /\ cos x < eps }.
Proof.
intros eps a eps_pos a_ub ;
 destruct (sin_cv_0_right _ (PI / 2 - a) eps_pos) as [x [[x_lb x_ub] Hx]].
 lra.
 exists (PI / 2 - x) ; rewrite cos_shift ; repeat split ; (trivial || lra).
Qed.

Lemma cos2PI_period : forall x k, cos x = cos (x + 2 * IZR ( k ) * PI).
Proof.
intros; symmetry.
destruct k.

f_equal. ring.

unfold IZR.
rewrite <-2INR_IPR.
apply cos_period.

unfold IZR.
replace (x + IPR 2 * - IPR p * PI) with (x - (0 + IPR 2 * IPR p * PI)) by ring.
rewrite <-2INR_IPR.
rewrite cos_minus, cos_period, sin_period, cos_0, sin_0. ring.
Qed.

Lemma sin2PI_period : forall x k, sin x = sin (x + 2 * IZR ( k ) * PI).
Proof.
intros; symmetry.

destruct k.

f_equal. ring.

unfold IZR.
rewrite <-2INR_IPR.
apply sin_period.

unfold IZR.
replace (x + IPR 2 * - IPR p * PI) with (x - (0 + IPR 2 * IPR p * PI)) by ring.
rewrite <-2INR_IPR.
rewrite sin_minus, cos_period, sin_period, cos_0, sin_0. ring.
Qed.
