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

Require Export Reals.
Require Export MyReals.
Require Export Rsequence_def Rsequence_facts Rsequence_sums_facts.
Require Export Rseries_def.
Require Import Rpser_def Rpser_sums Rpser_sums_facts Rpser_derivative.
Require Import Rpser_radius_facts Rpser_taylor.
Require Import Lra.
Require Import Rintegral.
Require Import Rseries_facts.
Require Import Rseries_RiemannInt.
Require Import Rsequence_subsequence.
Require Import Rtactic.

(* begin hide *)
Lemma continuity_pt_eq_compat :
  forall f g x, (exists alp, alp > 0 /\ forall y, R_dist x y < alp -> f y = g y) ->
  continuity_pt f x -> continuity_pt g x.
Proof.
intros f g x [alp1 [Halp1 H1]] H.
intros eps Heps.
destruct (H eps Heps) as [alp2 [Halp2 H2]].
exists (Rmin alp1 alp2); split.
apply Rmin_pos_lt; assumption.
intros u Hu.
repeat rewrite <- H1.
apply H2.
split; intuition.
unfold Rmin in * |- ; destruct Rle_dec; lra.
rewrite R_dist_eq; assumption.
apply Rlt_le_trans with (Rmin alp1 alp2).
  destruct Hu as [_ Hu].
  rewrite R_dist_sym; apply Hu.
  apply Rmin_l.
Qed.
(* end hide *)

(** ** Taylor series of ln *)

(** * Taylor series of ln (1 - x) *)

Section ln_minus.

Let Un n :=
match n with
| 0 => 0
| _ => - / (INR n)
end.

Lemma ln_minus_cv_radius : Cv_radius_weak Un 1.
Proof.
exists 1; intros m [n Hn]; subst m.
unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult.
rewrite pow1; rewrite Rmult_1_r.
unfold Un; destruct n.
  rewrite Rabs_R0; apply Rle_0_1.
  assert (Hle : 1 <= INR (S n)).
    rewrite S_INR.
    pattern 1 at 1; rewrite <- Rplus_0_l.
    apply Rplus_le_compat_r.
    apply pos_INR.
  rewrite Rabs_Ropp.
  rewrite Rabs_Rinv; [|intros Hc; lra].
  rewrite Rabs_right; [|lra].
  apply (Rmult_le_reg_l (INR (S n))); [lra|].
  rewrite Rinv_r; [lra|intros Hc; lra].
Qed.
(* begin hide *)

Lemma sum_f_R0_Ropp_compat : forall An n, - sum_f_R0 An n = sum_f_R0 (-An)%Rseq n.
Proof.
intros An n ; induction n.
 reflexivity.
 simpl ; rewrite Ropp_plus_distr ; rewrite IHn ; reflexivity.
Qed.
(* end hide *)

Lemma ln_minus_finite_cv_radius : finite_cv_radius Un 1.
Proof.
 assert (Un_decr : Un_decreasing (- (fun n => Un (S n)))%Rseq).
  assert (Hrew : forall n, Un (S n) = -/ INR (S n)).
   intro ; reflexivity.
   intro n ; unfold Rseq_opp ; repeat rewrite Hrew, Ropp_involutive.
   apply Rle_Rinv ; intuition.
  assert (Un_cv_0 : Un_cv (fun n : nat => - Un (S n)) 0).
  replace (fun n : nat => Un (S n)) with (fun n => - / INR (S n)).
  rewrite <- Ropp_involutive ;  do 2 apply Rseq_cv_opp_compat.
  apply Rseq_cv_pos_infty_inv_compat.
  intro M.
  assert (lt_0_1 : (0 < 1)%nat) by auto ;
  destruct (Rseq_poly_cv 1 lt_0_1 M) as [N HN] ;
  exists N ; intros n n_gt_N ; apply Rlt_trans with (INR n).
  rewrite <- pow_1 ; apply HN ; assumption.
  intuition.
  reflexivity.
 destruct (alternated_series (fun n => - Un (S n)) Un_decr Un_cv_0) as [l Hl].

 rewrite <- Rabs_R1.
 rewrite <- Rabs_Ropp.
 apply Rpser_finite_cv_radius_caracterization with l.
 unfold Pser, infinite_sum.
 intros eps eps_pos ; destruct (Hl eps eps_pos) as [N HN] ; exists (S N) ;
 intros n n_lb ; unfold R_dist.
 rewrite <- Rabs_Ropp.
 rewrite Ropp_minus_distr.
 assert (Hrew := (Rseq_pps_opp_compat Un (-1) n)) ; unfold Rseq_opp in Hrew ;
 unfold Rminus . change (-(1)) with (-1). rewrite <- Hrew.
 apply Rle_lt_trans with (R_dist (sum_f_R0 (tg_alt (fun n0 : nat => - Un (S n0))) (pred n)) l).
 right ; rewrite <- Rabs_Ropp ; unfold R_dist ; apply Rabs_eq_compat.
 clear - n_lb; induction n ; unfold tg_alt.
 inversion n_lb.
 simpl pred.
 clear ; induction n.
  compute ; field.
  unfold Rseq_pps, Rseq_sum in *.
  rewrite tech5.
  repeat rewrite Ropp_plus_distr in *.
  rewrite <- Rplus_assoc.
  rewrite IHn.
  unfold Rminus ; rewrite tech5.
  repeat rewrite Rplus_assoc ; apply Rplus_eq_compat_l.
  rewrite Rplus_comm ; apply Rplus_eq_compat_r.
  unfold gt_pser. unfold Rseq_mult. simpl pow. ring.
  apply HN ; intuition.

 intros M Hconv.
 unfold Rpser_abs in *.
(*
 rewrite Rabs_Ropp; rewrite Rabs_R1.
 intros M Hconv.
*) pose (fun n => match n with O => 0 | S _ => / INR n end) as An.
 apply Rseq_cv_not_infty with (sum_f_R0 An); split.
  exists M.
  refine (proj1 (Rser_cv_ext _ An M _) Hconv).
  intros [|n].
   simpl. unfold gt_abs_pser. unfold Rseq_abs. unfold gt_pser. 
   unfold Rseq_mult. simpl. rewrite Rmult_0_l. rewrite Rabs_R0. reflexivity.
   
   unfold Un, An.
   unfold gt_abs_pser. unfold Rseq_abs. unfold gt_pser. 
   unfold Rseq_mult. rewrite Rabs_mult.
   rewrite pow_1_abs.
   rewrite Rabs_Ropp. 
   rewrite Rabs_pos_eq; [ | apply Rlt_le; apply Rinv_0_lt_compat; INR_solve].
   ring.
 
 apply Rseq_cv_pos_infty_shift_compat.
 eapply Rseq_cv_pos_infty_eq_compat.
  2:eapply Rseq_equiv_cv_pos_infty_compat.
   2:apply Rseq_equiv_sym.
   2:apply harmonic_series_equiv.
  
  intro n; unfold Rseq_shift.
   induction n.
    simpl; ring.
    
    rewrite tech5.
    rewrite IHn.
    reflexivity.
   
   apply Rseq_subseq_cv_pos_infty_compat with (fun n => ln (INR n)).
    exists (exist _ _ (extractor_Rseq_iter_S 2)).
    unfold extracted, is_extractor.
    reflexivity.
    
    apply Rseq_ln_cv.
Qed.

Let sum x := weaksum_r Un 1 ln_minus_cv_radius x.

Lemma ln_minus_taylor_sum :
  forall x, Rabs x < 1 -> sum x = (ln (1 - x)).
Proof.
intros x Hx.
pose (f := comp ln (fct_cte 1 - id)).
pose (df := fun u => / (1 - u) * (0 - 1)).
assert (Hb : forall u, Rmin 0 x <= u <= Rmax 0 x -> -1 < u < 1).
  destruct (Rabs_def2 x 1 Hx) as [Hmax Hmin].
  intros u [Hul Hur].
    unfold Rmin, Rmax in Hul, Hur.
    destruct Rle_dec; split; lra.
pose (Hcv := ln_minus_cv_radius).
pose (g := weaksum_r Un 1 Hcv).
pose (dg := weaksum_r_derive Un 1 Hcv).
destruct Rint_derive2
  with (f := f) (a := 0) (b := x) (d := df) as [pr HI].
  intros u Hu.
  apply derivable_pt_lim_comp.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_ln.
  apply Rgt_minus; apply (Hb u Hu).
  intros u Hu.
  apply continuity_pt_mult.
  apply continuity_pt_inv.
  apply continuity_pt_minus.
  apply continuity_pt_const; unfold constant; auto.
  apply derivable_continuous_pt; apply derivable_pt_id.
  apply Rgt_not_eq; apply Rgt_minus; apply (Hb u Hu).
  apply continuity_pt_minus.
  apply continuity_pt_const; unfold constant; auto.
  apply continuity_pt_const; unfold constant; auto.
assert (Heq : forall u, -1 < u < 1 -> dg u = df u).
  intros u [Hul Hur]; unfold df, dg.
  replace (/ (1 - u) * (0 - 1))
    with (- / (1 - u)) by (field; intros Hc; lra).
  assert (Habs : Rabs u < 1).
    unfold Rabs; destruct Rcase_abs; lra.
  assert (Hser1 := weaksum_r_derive_sums Un 1 Hcv u Habs).
  assert (Hser2 := GP_infinite u Habs).
  eapply Rseq_cv_unique.
    apply Hser1.
    assert (Hrw : - sum_f_R0 (fun n => 1 * u ^ n) ==
      sum_f_R0 (fun n => An_deriv Un n * u ^ n)).
      unfold An_deriv.
      unfold Rseq_opp; intros n; induction n.
        simpl; unfold Rseq_shift, Rseq_mult; simpl; field.
        simpl sum_f_R0 at 1; rewrite Ropp_plus_distr.
        rewrite IHn.
        simpl; apply Rplus_eq_compat_l; destruct n.
          simpl. unfold Rseq_shift, Rseq_mult; simpl; field.
          unfold Rseq_shift. unfold Rseq_mult. unfold Un.
          field; assert (H := pos_INR (S n)); intros Hc. do 2 rewrite S_INR in Hc.
          lra.
    eapply Rseq_cv_eq_compat; unfold Rseq_pps, Rseq_sum, gt_pser. 
    erewrite <- Hrw. reflexivity. apply Rseq_cv_opp_compat; apply Hser2.
edestruct Rint_eq_compat
  with (f := df) (g := dg) (a := 0) (b := x) as [pr2 HI2].
  intros u Hu.
  apply Heq; apply Hb; assumption.
  exists pr; apply HI.
destruct Rint_derive2
  with (f := g) (a := 0) (b := x) (d := dg) as [pr3 HI3].
  intros u Hu.
  apply derivable_pt_lim_weaksum_r.
  apply Hb in Hu.
  destruct Hu as [Hul Hur].
  unfold Rabs; destruct Rcase_abs; lra.
  intros u Hu.
  assert (Hu2 := Hb u Hu).
  destruct Hu2 as [Hul Hur].
  assert (Hct : continuity_pt df u).
    unfold df.
    apply continuity_pt_mult.
    apply continuity_pt_inv; [|intros Hc; lra].
    apply continuity_pt_minus.
    apply continuity_pt_const; unfold constant; auto.
    apply derivable_continuous_pt; apply derivable_pt_id.
    apply continuity_pt_const; unfold constant; auto.
  eapply continuity_pt_eq_compat; [|apply Hct].
    pose (alp1 := u / 2 + / 2).
    pose (alp2 := /2 - u / 2).
    exists (Rmin alp1 alp2); split.
    apply Rmin_pos_lt.
      unfold alp1; lra.
      unfold alp2; lra.
    intros y Hy; symmetry.
    apply Heq.
    unfold alp1, alp2, R_dist, Rabs, Rmin in *.
    destruct Rcase_abs as [Hc|Hc] in Hy;
    destruct Rle_dec as [Hl|Hl] in Hy;
    split; try lra;
      try apply Rnot_le_lt in Hl; lra.
assert (Hint : Rint dg 0 x (f x - f 0)).
  apply Rint_eq_compat with (f := df).
  intros u Hu.
  apply Heq; apply Hb; assumption.
  exists pr; assumption.
assert (Heq_fun : g x - g 0 = f x - f 0).
  eapply Rint_uniqueness.
    exists pr3; assumption.
    assumption.
replace (ln (1 - x)) with (weaksum_r Un 1 Hcv x).
  unfold sum, Hcv; reflexivity.
unfold f, g, comp, fct_cte, id, minus_fct in Heq_fun; hnf in Heq_fun.
replace (1 - 0) with 1 in Heq_fun by ring; rewrite ln_1 in Heq_fun.
rewrite Rminus_0_r in Heq_fun.
replace (weaksum_r Un 1 Hcv 0) with 0 in Heq_fun.
rewrite Rminus_0_r in Heq_fun; assumption.
symmetry.
eapply Rseq_cv_unique.
apply weaksum_r_sums; rewrite Rabs_R0; lra.
intros eps Heps; exists 0%nat; intros n _.
unfold Rseq_pps, gt_pser.
rewrite sum_eq_R0.
rewrite R_dist_eq; assumption.
intros m _; unfold Un; destruct m.
  unfold Rseq_mult.
  field.
  unfold Rseq_mult.
  rewrite pow_ne_zero; [field|].
    apply not_0_INR; auto.
    auto.
Qed.

Lemma ln_minus_taylor :
  forall x, Rabs x < 1 -> Pser Un x (ln (1 - x)).
Proof.
intros x Hx.
rewrite <- ln_minus_taylor_sum; [|assumption].
apply weaksum_r_sums; assumption.
Qed.

End ln_minus.


(** * Taylor series of ln (1 + x) *)

Section ln_plus.

Let Un n :=
match n with
| 0 => 0 
| _ => (- 1) ^ (S n) / (INR n)
end.

Lemma ln_plus_cv_radius : Cv_radius_weak Un 1.
Proof.
exists 1; intros m [n Hn]; subst m.
unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult.
rewrite pow1; rewrite Rmult_1_r.
unfold Un; destruct n.
  rewrite Rabs_R0; apply Rle_0_1.
  assert (Hle : 1 <= INR (S n)).
    rewrite S_INR.
    pattern 1 at 1; rewrite <- Rplus_0_l.
    apply Rplus_le_compat_r.
    apply pos_INR.
  unfold Rdiv; rewrite Rabs_mult.
  rewrite pow_1_abs; rewrite Rmult_1_l.
  rewrite Rabs_Rinv; [|intros Hc; lra].
  rewrite Rabs_right; [|lra].
  apply (Rmult_le_reg_l (INR (S n))); [lra|].
  rewrite Rinv_r; [lra|intros Hc; lra].
Qed.

Let sum x := weaksum_r Un 1 ln_plus_cv_radius x.

Lemma ln_plus_taylor_sum :
  forall x, Rabs x < 1 -> sum x = (ln (1 + x)).
Proof.
intros x Hx.
assert (Hmx : Rabs (- x) < 1).
  rewrite Rabs_Ropp; assumption.
replace (1 + x) with (1 - (- x)) by ring.
eapply trans_eq; [|apply ln_minus_taylor_sum; assumption].
eapply Rseq_cv_unique.
  apply weaksum_r_sums; assumption.
eapply Rseq_cv_eq_compat; [|apply weaksum_r_sums; assumption].
intros n; apply sum_eq; intros i Hi; unfold Un.
unfold gt_pser. unfold Rseq_mult.
destruct i; [field|].
replace (- x) with (- 1 * x) by ring.
rewrite Rpow_mult_distr.
repeat rewrite <- tech_pow_Rmult; field.
auto with real.
Qed.

Lemma ln_plus_taylor :
  forall x, Rabs x < 1 -> Pser Un x (ln (1 + x)).
Proof.
intros x Hx.
rewrite <- ln_plus_taylor_sum; [|assumption].
apply weaksum_r_sums; assumption.
Qed.

End ln_plus.
