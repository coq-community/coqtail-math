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

Require Import MyReals.
Require Import Max.
Require Import Rsequence_def.
Require Import Rsequence_facts.
Require Import Rsequence_base_facts.
Require Import Lia Lra.
Require Import Complex.
Require Import Csequence_def.

Open Scope C_scope.
Open Scope Cseq_scope.

Section Cseq_partial.

Variable Un : Cseq.

(**********)
Lemma Cseq_partial_bound : forall N, exists M, forall n,
  (n <= N)%nat -> Cnorm (Un n) <= M.
Proof.
intros N.
 destruct (Rseq_partial_bound_max (fun n => Cnorm (Un n)) N) as (M, HM) ;
 exists M ; apply HM.
Qed.

End Cseq_partial.

(** * Asymptotic properties. *)

Section Cseq_asymptotic.

(**********)
Definition Cseq_asymptotic P :=
  forall (Q : Cseq -> Prop) Un,
    (forall Vn, Q Vn -> P Vn) -> Cseq_eventually Q Un -> P Un.

(**********)
Definition Cseq_asymptotic2 P :=
  forall (Q : Cseq -> Cseq -> Prop) Un Vn,
    (forall Wn Xn, Q Wn Xn -> P Wn Xn) -> Cseq_eventually2 Q Un Vn -> P Un Vn.

(** Convergence is asymptotic. *)

(**********)
Lemma Cseq_cv_asymptotic : forall l, Cseq_asymptotic (fun Un => Cseq_cv Un l).
Proof.
intros l Q Un HQ He eps Heps.
destruct He as [Ne HNe].
edestruct HQ as [N HN]; [eexact HNe|eexact Heps|].
exists (Ne + N)%nat; intros n Hn.
assert (Hn0 : exists n0, (n = Ne + n0)%nat).
induction Hn.
exists N; reflexivity.
destruct IHHn as [n0 H]; exists (S n0).
rewrite <- plus_Snm_nSm; simpl; rewrite H; reflexivity.
destruct Hn0 as [n0 Hn0].
rewrite Hn0; apply HN; lia.
Qed.

End Cseq_asymptotic.

(** * Convergence compatibilities *)

Section Cseq_cv_R_to_C.

Variable Un : Cseq.
Variable lu : C.

Lemma Cseq_Rseq_Rseq_equiv : Cseq_cv Un lu
 <-> (Rseq_cv (fun n => Cre (Un n)) (Cre lu) /\ Rseq_cv (fun n => Cim (Un n)) (Cim lu)).
Proof.
split ; intro H.
 split ; intros eps eps_pos.
 destruct (H _ eps_pos) as [N HN] ; exists N ; intros n Hn.
 unfold R_dist ; rewrite Cre_minus_compat.
 assert (Hrew := Cadd_conj (Un n - lu)).
 assert (HN_conj : forall n : nat, (n >= N)%nat -> Cnorm (Cconj (Un n - lu)) < eps).
  intros ; rewrite Cnorm_conj_compat ; apply HN ; assumption.
 apply Rle_lt_trans with (Rabs (2 / 2 * Cre (Un n - lu))).
 right ; apply Rabs_eq_compat ; field.
 replace (2 / 2 * Cre (Un n - lu))%R with (/2 * (2 * Cre (Un n - lu)))%R by field.
 replace (2 * Cre (Un n - lu))%R with (Cre (Un n - lu + Cconj (Un n - lu)))%R.
 rewrite Rabs_mult ; rewrite Rabs_right by lra ; apply Rlt_le_trans with
 (/2 * (2 * eps))%R.
 apply Rmult_lt_compat_l ; [lra |] ; apply Rle_lt_trans with
 (Rabs (Cre (Un n - lu)) + Rabs (Cre (Cconj (Un n - lu))))%R.
 rewrite <- Cre_add_compat ; apply Rabs_triang.
 apply Rle_lt_trans with (Cnorm (Un n - lu) + Rabs (Cre (Cconj (Un n - lu))))%R.
 apply Rplus_le_compat_r ; apply Cre_le_Cnorm.
 apply Rle_lt_trans with (Cnorm (Un n - lu) + Cnorm (Cconj (Un n - lu)))%R.
 apply Rplus_le_compat_l ; apply Cre_le_Cnorm.
 apply Rlt_trans with (eps + Cnorm (Cconj (Un n - lu)))%R.
 apply Rplus_lt_compat_r ; apply HN ; assumption.
 replace (2 * eps)%R with (eps + eps)%R by field ; apply Rplus_lt_compat_l ;
 apply HN_conj ; assumption.
 right ; field.
 rewrite Hrew ; simpl ; replace ((0 + 0) * 0)%R with 0%R.
 rewrite Rminus_0_r ; reflexivity.
 field.
 destruct (H _ eps_pos) as [N HN] ; exists N ; intros n Hn.
 unfold R_dist ; rewrite Cim_minus_compat.
 assert (Hrew := Cminus_conj (Un n - lu)).
 assert (HN_conj : forall n : nat, (n >= N)%nat -> Cnorm (Cconj (Un n - lu)) < eps).
  intros ; rewrite Cnorm_conj_compat ; apply HN ; assumption.
 apply Rle_lt_trans with (Rabs (2 / 2 * Cim (Un n - lu))).
 right ; apply Rabs_eq_compat ; field.
 replace (2 / 2 * Cim (Un n - lu))%R with (/2 * (2 * Cim (Un n - lu)))%R by field.
 replace (2 * Cim (Un n - lu))%R with (Cim (Un n - lu - Cconj (Un n - lu)))%R.
 rewrite Rabs_mult ; rewrite Rabs_right by lra ; apply Rlt_le_trans with
 (/2 * (2 * eps))%R.
 apply Rmult_lt_compat_l ; [lra |] ; apply Rle_lt_trans with
 (Rabs (Cim (Un n - lu)) + Rabs (- Cim (Cconj (Un n - lu))))%R.
 rewrite <- Cim_minus_compat ; unfold Rminus ; apply Rabs_triang.
 apply Rle_lt_trans with (Cnorm (Un n - lu) + Rabs (Cim (Cconj (Un n - lu))))%R.
 rewrite Rabs_Ropp ; apply Rplus_le_compat_r ; apply Cim_le_Cnorm.
 apply Rle_lt_trans with (Cnorm (Un n - lu) + Cnorm (Cconj (Un n - lu)))%R.
 apply Rplus_le_compat_l ; apply Cim_le_Cnorm.
 apply Rlt_trans with (eps + Cnorm (Cconj (Un n - lu)))%R.
 apply Rplus_lt_compat_r ; apply HN ; assumption.
 replace (2 * eps)%R with (eps + eps)%R by field ; apply Rplus_lt_compat_l ;
 apply HN_conj ; assumption.
 right ; field.
 rewrite Hrew ; simpl ; replace ((0 + 0) * 0)%R with 0%R.
 rewrite Rplus_0_r ; reflexivity.
 field.
 destruct H as [Hre Him] ; intros eps eps_pos ;
 assert (eps_2_pos : 0 < eps/2) by lra ; destruct (Hre _ eps_2_pos) as (N1, HN1) ;
 destruct (Him _ eps_2_pos) as (N2, HN2) ; exists (max N1 N2) ; intros n Hn.
 apply Rle_lt_trans with (Rabs (Cre (Un n - lu)) + Rabs (Cim (Un n - lu)))%R.
 apply Cnorm_le_Cre_Cim.
 unfold R_dist in * ; apply Rlt_trans with (Rabs (Cre (Un n - lu)) + eps/2)%R.
 apply Rplus_lt_compat_l ; rewrite <- Cim_minus_compat ; apply HN2.
 apply le_trans with (max N1 N2)%nat.
 apply le_max_r.
 assumption.
 apply Rlt_le_trans with (eps/2 + eps/2)%R.
 apply Rplus_lt_compat_r ; rewrite <- Cre_minus_compat ; apply HN1.
 apply le_trans with (max N1 N2)%nat.
 apply le_max_l.
 assumption.
 right ; field.
Qed.

Lemma Cauchy_equiv : Cauchy_crit Un <->
 (Rseries.Cauchy_crit (fun n => Cre (Un n)) /\ Rseries.Cauchy_crit (fun n => Cim (Un n)))%R.
Proof.
split.
intro Un_cauchy ; split ; intros eps eps_pos ;
 destruct (Un_cauchy eps eps_pos) as [N HN] ;
 exists N ; intros m n m_lb n_lb.
 apply Rle_lt_trans with (Cnorm (Cre (Un m - Un n))%C)%R ;
 [right |].
 unfold R_dist ; rewrite Cnorm_IRC_Rabs ; apply Rabs_eq_compat ;
 apply Cre_minus_compat.
 rewrite Cnorm_IRC_Rabs ; apply Rle_lt_trans with (Cnorm (Un m - Un n))%R ;
 [apply Cre_le_Cnorm | apply HN] ; assumption.
 apply Rle_lt_trans with (Cnorm (Cim (Un m - Un n))%C)%R ;
 [right |].
 unfold R_dist ; rewrite Cnorm_IRC_Rabs ; apply Rabs_eq_compat ;
 apply Cim_minus_compat.
 rewrite Cnorm_IRC_Rabs ; apply Rle_lt_trans with (Cnorm (Un m - Un n))%R ;
 [apply Cim_le_Cnorm | apply HN] ; assumption.
 intros [Cre_cauchy Cim_cauchy] ; intros eps eps_pos ;
 assert (eps_2_pos : 0 < eps / 2) by lra ;
 destruct (Cre_cauchy (eps / 2)%R eps_2_pos) as [N1 HN1] ;
 destruct (Cim_cauchy (eps / 2)%R eps_2_pos) as [N2 HN2] ;
 unfold R_dist in * ; exists (max N1 N2) ; intros m n m_ub n_ub.
 apply Rle_lt_trans with (Rabs (Cre (Un m - Un n)) + Rabs (Cim (Un m - Un n)))%R ;
 [apply Cnorm_le_Cre_Cim | apply Rlt_le_trans with (eps / 2 + eps / 2)%R ;
 [| right ; field]].
 apply Rlt_trans with (Rabs (Cre (Un m - Un n)) + eps / 2)%R.
 apply Rplus_lt_compat_l ; rewrite <- Cim_minus_compat ; apply HN2 ;
 apply le_trans with (max N1 N2) ; [apply le_max_r | assumption |
 apply le_max_r | assumption].
 apply Rplus_lt_compat_r.
 rewrite <- Cre_minus_compat ; apply HN1 ;
 apply le_trans with (max N1 N2) ; [apply le_max_l | assumption |
 apply le_max_l | assumption].
Qed.

End Cseq_cv_R_to_C.


Section Cseq_cv_simpl.

Variable Un Vn : Cseq.
Variable lu lv : C.
Hypothesis Hu : Cseq_cv Un lu.
Hypothesis Hv : Cseq_cv Vn lv.


(**********)
Lemma Cseq_cv_bound : exists M, 0 < M /\ Cseq_bound Un M.
Proof.
destruct (Hu 1%R) as [N HN]; [lra|].
destruct (Cseq_partial_bound Un N) as [M HM].
exists (Rmax (1 + (Cnorm lu)) M).
split.
eapply Rlt_le_trans; [|apply RmaxLess1].
apply Rplus_lt_le_0_compat; [lra|apply Cnorm_pos].
intros n.
destruct (le_ge_dec n N) as [He|He].
eapply Rle_trans; [apply HM; assumption|apply RmaxLess2].
eapply Rle_trans; [|apply RmaxLess1].
replace (Un n) with ((Un n - lu) + lu)%C by field.
eapply Rle_trans; [apply Cnorm_triang|].
apply Rplus_le_compat.
left; apply HN; assumption.
apply Rle_refl.
Qed.

(**********)
Lemma Cseq_cv_eq_compat : forall l,
    (forall n, Un n = Vn n) -> Cseq_cv Un l -> Cseq_cv Vn l.
Proof.
intros l H Hl eps Heps.
destruct (Hl eps Heps) as [N HN]; exists N;
intros n Hn; rewrite <- H; apply HN; apply Hn.
Qed.

(**********)
Lemma Cseq_cst_cv : forall (c : C), Cseq_cv (fun _ => c) c.
intros c eps Heps; exists O; intros n Hn.
unfold R_dist.
assert (c - c = C0)%C.
ring.
rewrite H.
change (Cnorm C0 < eps).
rewrite Cnorm_C0; apply Heps.
Qed.

(**********)
Lemma Cseq_cv_cnorm_compat : Rseq_cv (fun k => Cnorm (Un k)) (Cnorm lu).
Proof.
intros eps Heps ; destruct (Hu eps Heps) as [N HN].
exists N.
intros n Hn.
unfold R_dist.
apply Rle_lt_trans with (Cnorm (Un n - lu)).
apply Cnorm_triang_rev.
apply HN; apply Hn.
Qed.

(**********)
Lemma Cseq_cv_add_compat : Cseq_cv (Un + Vn) (lu + lv).
Proof.
intros eps Heps.
destruct (Hu (eps/2)%R) as [Nu HNu]; [lra|].
destruct (Hv (eps/2)%R) as [Nv HNv]; [lra|].
exists (Max.max Nu Nv).
intros n Hn.
unfold R_dist; unfold Cseq_add.
replace (Un n + Vn n - (lu + lv))%C
  with ((Un n - lu) + (Vn n - lv))%C by field.
eapply Rle_lt_trans; [apply Cnorm_triang|].
replace eps with (eps/2 + eps/2)%R by field.
apply Rplus_lt_compat.
apply (HNu n); eapply le_trans; [apply Max.le_max_l|eexact Hn].
apply (HNv n); eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

(**********)
Lemma Cseq_cv_opp_compat : Cseq_cv (- Un) (- lu).
Proof.
intros eps Heps.
destruct (Hu eps) as [Nu HNu]; [assumption|].
exists Nu; intros n Hn.
unfold R_dist; unfold Cseq_opp.
replace (- Un n - - lu)%C with (- (Un n - lu))%C by field.
rewrite Cnorm_opp.
apply HNu; exact Hn.
Qed.

End Cseq_cv_simpl.

Section Cseq_cv.

Variable Un Vn : nat -> C.
Variable lu lv : C.
Hypothesis Hu : Cseq_cv Un lu.
Hypothesis Hv : Cseq_cv Vn lv.

(**********)
Lemma Cseq_cv_minus_compat : Cseq_cv (Un - Vn) (lu - lv).
Proof.
apply Cseq_cv_eq_compat with (Un + (-Vn)).
reflexivity.
apply Cseq_cv_add_compat.
apply Hu.
apply Cseq_cv_opp_compat.
apply Hv.
Qed.

(**********)
Lemma Cseq_cv_mult_compat : Cseq_cv (Un * Vn) (lu * lv).
Proof.
intros eps Heps.
destruct Cseq_cv_bound with Un lu%C as [Mb [HMb Hb]] ; [assumption |].
pose (eps1 := (eps / 2 / (Rmax 1 (Cnorm lv)))%R).
pose (eps2 := (eps / 2 / Mb)%R).
assert (Heps1 : eps1 > 0).
unfold eps1; repeat apply Rmult_gt_0_compat; try lra.
apply Rinv_0_lt_compat; eapply Rlt_le_trans; [apply Rlt_0_1|apply RmaxLess1].
assert (Heps2 : eps2 > 0).
unfold eps2; repeat apply Rmult_gt_0_compat; try lra.
apply Rinv_0_lt_compat; assumption.
destruct (Hu eps1) as [Nu HNu]; [assumption|].
destruct (Hv eps2) as [Nv HNv]; [assumption|].
exists (Max.max Nu Nv); intros n Hn.
unfold R_dist; unfold Cseq_mult.
replace (Un n * Vn n - lu * lv)%C
  with ((Un n * Vn n - Un n * lv) + (Un n * lv - lu * lv))%C by field.
eapply Rle_lt_trans; [apply Cnorm_triang|].
replace eps with (eps / 2 + eps / 2)%R by field.
apply Rplus_lt_compat.
rewrite <- Cmult_minus_distr_l ; rewrite Cnorm_Cmult.
eapply Rle_lt_trans.
  apply Rmult_le_compat_r; [apply Cnorm_pos|].
  apply Hb.
replace (eps / 2)%R with (Mb * (eps / 2 / Mb))%R
  by (field; apply Rgt_not_eq; assumption).
apply Rmult_lt_compat_l; [assumption|].
apply HNv; eapply le_trans; [apply Max.le_max_r|eexact Hn].
unfold Cminus ; rewrite <- Copp_mult_distr_l_reverse.
rewrite <- Cmult_add_distr_r.
rewrite Cnorm_Cmult.
destruct (Ceq_dec lv C0) as [Hlv|Hlv].
  rewrite Hlv ; rewrite Cnorm_C0 ; rewrite Rmult_0_r; lra.
eapply Rlt_le_trans.
  apply Rmult_lt_compat_r; [apply Cnorm_pos_lt; assumption|].
  apply HNu; eapply le_trans; [apply Max.le_max_l|eexact Hn].
unfold eps1.
unfold Rdiv; rewrite Rmult_assoc; rewrite <- Rmult_1_r.
apply Rmult_le_compat_l; [lra|].
assert (Hmax : Rmax 1 (Cnorm lv) > 0%R).
eapply Rlt_le_trans with 1%R; [lra|apply RmaxLess1].
pattern 1%R at 2; rewrite <- (Rinv_l (Rmax 1 (Cnorm lv))).
  apply Rmult_le_compat_l.
    left; apply Rinv_0_lt_compat; assumption.
    apply RmaxLess2.
apply Rgt_not_eq; assumption.
Qed.

(**********)

Lemma Cseq_cv_inv_compat : lu <> 0 -> Cseq_cv (/ Un) (/ lu).
Proof.
intros H eps Heps.
destruct (Hu (Cnorm lu / 2))%R as [Ninf Hinf].
apply Rmult_lt_0_compat; [apply Cnorm_pos_lt|lra]; assumption.
destruct (Hu (/2 * Cnorm lu * Cnorm lu * eps))%R as [N HN].
repeat apply Rmult_lt_0_compat; (apply Cnorm_pos_lt || lra); assumption.
exists (Max.max Ninf N).
intros n Hn.
unfold R_dist; unfold Cseq_inv.
assert (Habs : Cnorm lu / 2 <= Cnorm (Un n)).
replace (Cnorm lu / 2)%R with
  (Cnorm lu - Cnorm lu / 2)%R by field.
assert (Hr : Cnorm (Un n - lu) < Cnorm lu / 2).
apply Hinf; eapply le_trans; [apply Max.le_max_l|eexact Hn].
 rewrite Cnorm_minus_sym in Hr.
 assert (Temp := Cnorm_triang_rev_r (lu - Un n) lu).
 replace (Cnorm (Un n)) with (Cnorm (- Un n)) by (apply Cnorm_opp) ;
 replace (- Un n)%C with (lu - Un n - lu)%C by field.
lra.
assert (Hpos : Un n <> 0).
case (Ceq_or_neq_C0 (Un n)) ; intro HUn.
apply False_ind ; elim (Rlt_irrefl 0).
apply Rlt_le_trans with (Cnorm lu / 2)%R.
unfold Rdiv ; rewrite Rmult_comm ; replace (/2)%R with (Rabs (/2)) by
  (apply Rabs_right ; lra) ; rewrite <- Cnorm_mult ; apply Cnorm_pos_lt ;
  apply Cnorm_gt_not_eq ; rewrite Cnorm_mult ; apply Rmult_lt_0_compat.
  rewrite Rabs_right ; lra.
  apply Cnorm_pos_lt ; assumption.
Set Printing All.
  apply Rle_trans with (Cnorm (Un n)) ; [assumption | rewrite HUn ;
  rewrite Cnorm_C0 ; right ; trivial].
  assumption.
replace (/ Un n - / lu)%C with
  (/ lu * / Un n * (lu - Un n))%C by (field; tauto).
repeat (rewrite Cnorm_Cmult).
repeat rewrite Cnorm_inv; try assumption.
rewrite Cnorm_minus_sym.
eapply Rlt_le_trans.
apply Rmult_lt_compat_l.
apply Rmult_lt_0_compat; apply Rinv_0_lt_compat;
apply Cnorm_pos_lt; assumption.
apply HN; eapply le_trans; [apply Max.le_max_r|eexact Hn].
replace (/ Cnorm lu * / Cnorm (Un n) * (/2 * Cnorm lu * Cnorm lu * eps))%R
  with (/ Cnorm (Un n) * (/2 * Cnorm lu) * eps)%R by (field; split ;
  apply Cnorm_no_R0 ; assumption).
rewrite <- Rmult_1_l.
apply Rmult_le_compat_r; auto with real.
eapply Rle_trans.
apply Rmult_le_compat_r.
replace 0%R with (0 * 0)%R by field.
apply Rmult_le_compat; auto with real; apply Cnorm_pos.
destruct Habs as [Habs|Habs].
left; apply Rinv_lt_contravar; [|eassumption].
repeat apply Rmult_lt_0_compat; auto with real; apply Cnorm_pos_lt; assumption.
rewrite Habs; right; reflexivity.
right; field.
apply Cnorm_no_R0; assumption.
Qed.

End Cseq_cv.

(** Compatibility with Cre and Cim *)
Lemma Cseq_cv_re_compat : forall Un l, Cseq_cv Un l -> 
  Rseq_cv (fun n : nat => Cre (Un n)) (Cre l).
Proof.
intros Un l HC e epos.
destruct (HC e epos) as [N HN]; exists N.
intros n Hn.
pose proof HN n Hn.
unfold R_dist.
rewrite Cre_minus_compat.
eapply Rle_lt_trans.
 apply Cre_le_Cnorm.
 auto.
Qed.

Lemma Cseq_cv_im_compat : forall Un l, Cseq_cv Un l -> 
  Rseq_cv (fun n : nat => Cim (Un n)) (Cim l).
Proof.
intros Un l HC e epos.
destruct (HC e epos) as [N HN]; exists N.
intros n Hn.
pose proof HN n Hn.
unfold R_dist.
rewrite Cim_minus_compat.
eapply Rle_lt_trans.
 apply Cim_le_Cnorm.
 auto.
Qed.

Lemma Cseq_cv_re_im_compat : forall Un l,
  Rseq_cv (fun n => Cre (Un n)) (Cre l) ->
  Rseq_cv (fun n => Cim (Un n)) (Cim l) ->
  Cseq_cv Un l.
Proof.
intros Un l Hre Him e epos.
pose (e / 2)%R as e'.
assert (e'pos : e' > 0) by (unfold e'; lra).
destruct (Hre e' e'pos) as [Nre HNre].
destruct (Him e' e'pos) as [Nim HNim].
exists (max Nre Nim).
intros n Hn.
replace e with (e' + e')%R by (unfold e'; field).
eapply Rle_lt_trans.
 apply Cnorm_le_Cre_Cim.
 apply Rplus_lt_compat.
  rewrite <- Cre_minus_compat.
  apply HNre.
  eapply le_trans.
   apply le_max_l.
   apply Hn.
  rewrite <- Cim_minus_compat.
  apply HNim.
  eapply le_trans.
   apply le_max_r.
   apply Hn.
Qed.

(** Limit uniquess *)
Lemma Cseq_cv_unique : forall Un lu1 lu2, Cseq_cv Un lu1 -> Cseq_cv Un lu2 -> lu1 = lu2.
Proof.
intros Un l1 l2 Hl1 Hl2.
rewrite <- Cproj_right with l1.
rewrite <- Cproj_right with l2.
cut (Cre l1 = Cre l2 /\ Cim l1 = Cim l2).
 intros [H I]; rewrite H; rewrite I; trivial.
split.
 apply Rseq_cv_unique with (fun n => Cre (Un n));
  apply Cseq_cv_re_compat; assumption.
 apply Rseq_cv_unique with (fun n => Cim (Un n));
  apply Cseq_cv_im_compat; assumption.
Qed.

Section Cseq_cv_bonus.

Variable Un Vn : nat -> C.
Variable lu lv : C.
Hypothesis Hu : Cseq_cv Un lu.
Hypothesis Hv : Cseq_cv Vn lv.

Lemma Cseq_cv_div_compat : lv <> 0 -> Cseq_cv (Un /Vn) (lu/lv).
Proof.
intro Hlu ; unfold Cseq_div, Rdiv.
 apply Cseq_cv_eq_compat with (Un *(/Vn)).
 reflexivity.
 apply Cseq_cv_mult_compat.
 assumption.
 apply Cseq_cv_inv_compat ; assumption.
Qed.

End Cseq_cv_bonus.
