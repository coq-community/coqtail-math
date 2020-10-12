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

Require Import Lia.
Require Import Rsequence_def.
Require Import Rsequence_base_facts.
Require Import Max Rinterval MyRIneq Ranalysis_def Lra.

Open Scope R_scope.
Open Scope Rseq_scope.

(** printing ~	~ *)
(** * Convergence compatibility. *)

Section Rseq_cv.

(**********)
Lemma Rseq_cv_bound :
  forall Un lu, Rseq_cv Un lu -> exists M, 0 < M /\ Rseq_bound Un M.
Proof.
intros Un lu Hu.
destruct (Hu 1) as [N HN]; [lra|].
destruct (Rseq_partial_bound Un N) as [M HM].
exists (Rmax (1 + (Rabs lu))%R M).
split.
eapply Rlt_le_trans; [|apply RmaxLess1].
apply Rplus_lt_le_0_compat; [lra|apply Rabs_pos].
intros n.
destruct (le_ge_dec n N) as [He|He].
eapply Rle_trans; [apply HM; assumption|apply RmaxLess2].
eapply Rle_trans; [|apply RmaxLess1].
replace (Un n) with ((Un n - lu) + lu)%R by field.
eapply Rle_trans; [apply Rabs_triang|].
apply Rplus_le_compat.
left; apply HN; assumption.
apply Rle_refl.
Qed.

(**********)
Lemma Rseq_constant_cv : forall r, Rseq_cv (Rseq_constant r) r.
intros r eps Heps; exists O; intros n Hn.
unfold R_dist; unfold Rseq_constant.
replace (r - r)%R with 0 by ring.
rewrite Rabs_R0; apply Heps.
Qed.

(**********)
Lemma Rseq_cv_plus_compat :
  forall Un Vn lu lv,
    Rseq_cv Un lu -> Rseq_cv Vn lv -> Rseq_cv (Un + Vn) (lu + lv).
Proof.
intros Un Vn lu lv Hu Hv eps Heps.
destruct (Hu (eps/2)%R) as [Nu HNu]; [lra|].
destruct (Hv (eps/2)%R) as [Nv HNv]; [lra|].
exists (Max.max Nu Nv).
intros n Hn.
unfold R_dist; unfold Rseq_plus.
replace (Un n + Vn n - (lu + lv))%R
  with ((Un n - lu) + (Vn n - lv))%R by field.
eapply Rle_lt_trans; [apply Rabs_triang|].
replace eps with (eps/2 + eps/2)%R by field.
apply Rplus_lt_compat.
apply (HNu n); eapply le_trans; [apply Max.le_max_l|eexact Hn].
apply (HNv n); eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

(**********)
Lemma Rseq_cv_opp_compat :
  forall Un lu, Rseq_cv Un lu -> Rseq_cv (- Un) (- lu).
Proof.
intros Un lu Hu eps Heps.
destruct (Hu eps) as [Nu HNu]; [assumption|].
exists Nu; intros n Hn.
unfold R_dist; unfold Rseq_opp.
replace (- Un n - - lu)%R with (- (Un n - lu))%R by field.
rewrite Rabs_Ropp.
apply HNu; exact Hn.
Qed.

(**********)
Lemma Rseq_cv_mult_compat :
  forall Un Vn lu lv,
    Rseq_cv Un lu -> Rseq_cv Vn lv -> Rseq_cv (Un * Vn) (lu * lv).
Proof.
intros Un Vn lu lv Hu Hv eps Heps.
destruct (Rseq_cv_bound Un lu) as [Mb [HMb Hb]]; [assumption|].
pose (eps1 := (eps / 2 / (Rmax 1 (Rabs lv)))%R).
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
unfold R_dist; unfold Rseq_mult.
replace (Un n * Vn n - lu * lv)%R
  with ((Un n * Vn n - Un n * lv) + (Un n * lv - lu * lv))%R
  by field.
eapply Rle_lt_trans; [apply Rabs_triang|].
replace eps with (eps / 2 + eps / 2)%R by field.
apply Rplus_lt_compat.
rewrite <- Rmult_minus_distr_l; rewrite Rabs_mult.
eapply Rle_lt_trans.
  apply Rmult_le_compat_r; [apply Rabs_pos|].
  apply Hb.
replace (eps / 2)%R with (Mb * (eps / 2 / Mb))%R
  by (field; apply Rgt_not_eq; assumption).
apply Rmult_lt_compat_l; [assumption|].
apply HNv; eapply le_trans; [apply Max.le_max_r|eexact Hn].
unfold Rminus; rewrite <- Ropp_mult_distr_l_reverse.
rewrite <- Rmult_plus_distr_r.
rewrite Rabs_mult.
destruct (Req_dec lv 0) as [Hlv|Hlv].
  rewrite Hlv; rewrite Rabs_R0; rewrite Rmult_0_r; lra.
  eapply Rlt_le_trans.
  apply Rmult_lt_compat_r; [apply Rabs_pos_lt; assumption|].
  apply HNu; eapply le_trans; [apply Max.le_max_l|eexact Hn].
unfold eps1.
unfold Rdiv; rewrite Rmult_assoc; rewrite <- Rmult_1_r.
apply Rmult_le_compat_l; [lra|].
assert (Hmax : Rmax 1 (Rabs lv) > 0).
eapply Rlt_le_trans with 1; [lra|apply RmaxLess1].
pattern 1 at 2; rewrite <- (Rinv_l (Rmax 1 (Rabs lv))).
  apply Rmult_le_compat_l.
    left; apply Rinv_0_lt_compat; assumption.
    apply RmaxLess2.
apply Rgt_not_eq; assumption.
Qed.

(**********)
Lemma Rseq_cv_pow_compat : forall An d l,
  Rseq_cv An l -> Rseq_cv (fun n => An n ^ d) (l ^ d).
Proof.
intros An d ; revert An ; induction d ; intros An l HAn.
 simpl ; apply Rseq_constant_cv.
 simpl ; apply Rseq_cv_mult_compat ; [| apply IHd] ; assumption.
Qed.

(**********)
Lemma Rseq_cv_inv_compat :
  forall Un lu, Rseq_cv Un lu -> lu <> 0 -> Rseq_cv (/ Un) (/ lu).
Proof.
intros Un lu Hu H eps Heps.
destruct (Hu (Rabs lu / 2))%R as [Ninf Hinf].
apply Rmult_lt_0_compat; [apply Rabs_pos_lt|lra]; assumption.
destruct (Hu (/2 * Rabs lu * Rabs lu * eps))%R as [N HN].
repeat apply Rmult_lt_0_compat; (apply Rabs_pos_lt || lra); assumption.
exists (Max.max Ninf N).
intros n Hn.
unfold R_dist; unfold Rseq_inv.
assert (Habs : Rabs lu / 2 <= Rabs (Un n)).
replace (Rabs lu / 2)%R with
  (Rabs lu - Rabs lu / 2)%R by field.
assert (Hr : Rabs (Un n - lu) < Rabs lu / 2).
apply Hinf; eapply le_trans; [apply Max.le_max_l|eexact Hn].
unfold Rabs; repeat destruct Rcase_abs;
unfold Rabs in Hr; repeat destruct Rcase_abs in Hr; lra.
assert (Hpos : Un n <> 0).
unfold Rabs in Habs; repeat destruct Rcase_abs in Habs;
try (apply Rlt_not_eq || apply Rgt_not_eq; lra).
apply Rgt_not_eq; eapply Rlt_le_trans; [|eexact Habs].
unfold Rdiv; rewrite Ropp_mult_distr_l_reverse; lra.
apply Rgt_not_eq; eapply Rlt_le_trans; [|eexact Habs].
unfold Rdiv; apply Rmult_lt_0_compat; auto with real.
destruct (Rle_lt_or_eq_dec 0 lu); auto with real.
subst; elim H; reflexivity.
replace (/ Un n - / lu)%R with
  (/ lu * / Un n * (lu - Un n))%R by (field; tauto).
repeat rewrite Rabs_mult.
repeat rewrite Rabs_Rinv; try assumption.
rewrite Rabs_minus_sym.
eapply Rlt_le_trans.
apply Rmult_lt_compat_l.
apply Rmult_lt_0_compat; apply Rinv_0_lt_compat;
apply Rabs_pos_lt; assumption.
apply HN; eapply le_trans; [apply Max.le_max_r|eexact Hn].
replace (/ Rabs lu * / Rabs (Un n) * (/2 * Rabs lu * Rabs lu * eps))%R
  with (/ Rabs (Un n) * (/2 * Rabs lu) * eps)%R
  by (field; split; apply Rabs_no_R0; assumption).
rewrite <- Rmult_1_l.
apply Rmult_le_compat_r; auto with real.
eapply Rle_trans.
apply Rmult_le_compat_r.
replace 0%R with (0 * 0)%R by field.
apply Rmult_le_compat; auto with real; apply Rabs_pos.
destruct Habs as [Habs|Habs].
left; apply Rinv_lt_contravar; [|eassumption].
repeat apply Rmult_lt_0_compat; auto with real; apply Rabs_pos_lt; assumption.
rewrite Habs; right; reflexivity.
right; field.
apply Rabs_no_R0; assumption.
Qed.

(**********)
Lemma Rseq_cv_minus_compat : forall Un Vn lu lv,
    Rseq_cv Un lu -> Rseq_cv Vn lv -> Rseq_cv (Un - Vn) (lu - lv).
Proof.
intros Un Vn lu lv Hlu Hlv.
apply Rseq_cv_eq_compat with (Un + (-Vn)).
intros n; reflexivity.
apply Rseq_cv_plus_compat; [apply Hlu|].
apply Rseq_cv_opp_compat; apply Hlv.
Qed.

(**********)
Lemma Rseq_cv_div_compat : 
  forall Un Vn lu lv,
    Rseq_cv Un lu -> Rseq_cv Vn lv -> lv <> 0 -> Rseq_cv (Un / Vn) (lu / lv).
Proof.
intros Un Vn lu lv Hu Hv H.
unfold Rseq_div, Rdiv.
apply Rseq_cv_eq_compat with (Un * (/ Vn)).
intros n; reflexivity.
apply Rseq_cv_mult_compat; [apply Hu|].
apply Rseq_cv_inv_compat; [apply Hv|apply H].
Qed.

(**********)
Lemma Rseq_cv_continuity_compat :
  forall Un lu f, Rseq_cv Un lu -> continuity_pt f lu -> Rseq_cv (fun n => f (Un n)) (f lu).
Proof.
intros Un lu f Hu Hf eps Heps.
destruct (Hf eps) as [h [Hh H]]; [assumption|simpl in H].
destruct (Hu h) as [N HN]; [assumption|].
exists N; intros n Hn.
destruct (Req_dec lu (Un n)) as [Heq|Heq].
rewrite Heq; rewrite R_dist_eq; assumption.
apply H; split; [compute; tauto|].
apply HN; assumption.
Qed.

(**********)
Lemma Rseq_cv_continuity_interval_compat : forall Un lu f a b,
  interval a b lu -> (forall n, interval a b (Un n)) ->
  Rseq_cv Un lu -> continuity_interval a b f ->
  Rseq_cv (fun n => f (Un n)) (f lu).
Proof.
intros Un lu f a b lu_in Un_in Hu Hf eps eps_pos.
 destruct (Hf _ lu_in _ eps_pos) as [h [h_pos Hh]] ; simpl in Hh.
 destruct (Hu _ h_pos) as [N HN] ; exists N ; intros n n_lb.
  destruct (Req_dec lu (Un n)) as [Heq | Hneq].
   rewrite Heq, R_dist_eq ; assumption.
   apply Hh ; split ; [apply Un_in | apply HN ; assumption].
Qed.

(**********)
Lemma Rseq_cv_abs_compat : forall (Un : nat -> R) (l : R), 
    Rseq_cv Un l -> Rseq_cv (|Un|) (Rabs l).
Proof.
intros Un l Hl eps Heps.
destruct (Hl eps Heps) as [N HN].
exists N.
intros n Hn.
unfold R_dist.
apply Rle_lt_trans with (Rabs (Un n - l)).
apply Rabs_triang_inv2.
apply HN; apply Hn.
Qed.

Lemma Rseq_cv_even_odd_compat : forall (Un : Rseq) (l : R),
  Rseq_cv (fun i => Un (2 * i)%nat) l ->
  Rseq_cv (fun i => Un (S (2 * i))%nat) l ->
  Rseq_cv Un l.
Proof.
intros Un l Heven Hodd eps eps_pos ;
 destruct (Heven _ eps_pos) as [N1 HN1] ;
 destruct (Hodd _ eps_pos) as [N2 HN2] ;
 exists (max (2 * N1) (S (2 * N2))) ; intros n n_lb ;
 destruct (n_modulo_2 n) as [[p Hp] | [p Hp]] ; subst.
  apply HN1 ; assert (H := max_lub_l _ _ _ n_lb) ; lia.
  apply HN2 ; assert (H := max_lub_r _ _ _ n_lb) ; lia.
Qed.

End Rseq_cv.

(** * Infinite convergence compatibility. *)

Section Rseq_cv_infty.

Variable Un Vn : nat -> R.

(**********)
Lemma Rseq_cv_pos_infty_plus_compat :
  Rseq_cv_pos_infty Un -> Rseq_cv_pos_infty Vn ->
    Rseq_cv_pos_infty (Un + Vn).
Proof.
intros Hu Hv M.
destruct (Hu (M / 2)%R) as [Nu HNu].
destruct (Hv (M / 2)%R) as [Nv HNv].
exists (Max.max Nu Nv); intros n Hn.
unfold Rseq_plus.
replace M with (M / 2 + M / 2)%R by field.
apply Rplus_lt_compat.
apply HNu; eapply le_trans; [apply Max.le_max_l|eexact Hn].
apply HNv; eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

(**********)
Lemma Rseq_cv_finite_plus_pos_infty_r : forall l,
  Rseq_cv Un l -> Rseq_cv_pos_infty Vn ->
  Rseq_cv_pos_infty (Un + Vn).
Proof.
intros l Hl Hf m.
destruct (Hl 1 ltac:(lra)) as [N HN].
destruct (Hf (m-(l -1))%R) as [N0 HN0].
exists (N+N0)%nat.
intros n Hn.
apply Rle_lt_trans with ((l-1)+ (m-(l-1)))%R.
ring_simplify; apply Rle_refl.
apply Rplus_lt_compat.
apply Rminus_lt.
unfold Rminus.
rewrite Rplus_comm.
rewrite <- Rplus_assoc.
rewrite Rplus_comm.
replace 0 with (-1 + 1)%R by ring.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (Rabs (- Un n+ l)).
apply RRle_abs.
rewrite Rplus_comm.
fold (Rminus l (Un n)).
fold (R_dist l (Un n)).
rewrite R_dist_sym.
apply HN; lia.
apply HN0; lia.
Qed.

(**********)
Lemma Rseq_cv_finite_plus_pos_infty_l : forall l,
  Rseq_cv_pos_infty Vn -> Rseq_cv Un l -> 
  Rseq_cv_pos_infty (Vn + Un).
Proof.
intros l Hf Hl m.
destruct (Hl 1 ltac:(lra)) as [N HN].
destruct (Hf (m-(l -1))%R) as [N0 HN0].
exists (N+N0)%nat.
intros n Hn.
apply Rle_lt_trans with ((m-(l-1))+ (l-1))%R.
ring_simplify; apply Rle_refl.
apply Rplus_lt_compat.
apply HN0; lia.
apply Rminus_lt.
unfold Rminus.
rewrite Rplus_comm.
rewrite <- Rplus_assoc.
rewrite Rplus_comm.
replace 0 with (-1 + 1)%R by ring.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (Rabs (- Un n+ l)).
apply RRle_abs.
rewrite Rplus_comm.
fold (Rminus l (Un n)).
fold (R_dist l (Un n)).
rewrite R_dist_sym.
apply HN; lia.
Qed.

(**********)
Lemma Rseq_cv_pos_pos_infty_mult :
  Rseq_cv_pos_infty Un -> Rseq_cv_pos_infty Vn ->
  Rseq_cv_pos_infty (Un * Vn).
Proof.
intros Hu Hv M.
destruct (Hu (Rabs M)) as [Nu HNu].
destruct (Hv 1) as [Nv HNv].
exists (Max.max Nu Nv); intros n Hn.
unfold Rseq_mult.
apply Rle_lt_trans with (Rabs M).
apply RRle_abs.
replace (Rabs M) with ((Rabs M)*1)%R by apply Rmult_1_r.
apply Rmult_le_0_lt_compat.
apply Rabs_pos.
apply Rle_0_1.
apply HNu; eapply le_trans; [apply Max.le_max_l|eexact Hn].
apply HNv; eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.


(**********)
Lemma Rseq_cv_neg_neg_infty_mult :
  Rseq_cv_neg_infty Un -> Rseq_cv_neg_infty Vn ->
    Rseq_cv_pos_infty (Un * Vn).
Proof.
intros Hu Hv M.
destruct (Hu (- (Rabs M))%R) as [Nu HNu].
destruct (Hv (-1)) as [Nv HNv].
exists (Max.max Nu Nv); intros n Hn.
unfold Rseq_mult.
apply Rle_lt_trans with (Rabs M).
apply RRle_abs.
replace (Un n * Vn n)%R with ((- Un n) *( - Vn n))%R by ring.
replace (Rabs M)%R with (( - -Rabs M) *( - - 1))%R by ring.
apply Rmult_le_0_lt_compat.
rewrite Ropp_involutive; apply Rabs_pos.
lra.
apply Ropp_lt_contravar; apply HNu; eapply le_trans; [apply Max.le_max_l|eexact Hn].
apply Ropp_lt_contravar; apply HNv; eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

(**********)
Lemma Rseq_cv_pos_neg_infty_mult :
  Rseq_cv_pos_infty Un -> Rseq_cv_neg_infty Vn ->
    Rseq_cv_neg_infty (Un * Vn).
Proof.
intros Hu Hv M.
destruct (Hu (Rabs M)%R) as [Nu HNu].
destruct (Hv (-1)) as [Nv HNv].
exists (Max.max Nu Nv); intros n Hn.
unfold Rseq_mult.
apply Rlt_le_trans with (- Rabs M)%R.
replace (Un n * Vn n)%R with (-(Un n * (- Vn n)))%R by ring.
apply Ropp_lt_contravar.
replace (Rabs M)%R with ((Rabs M) * (- - 1))%R by ring.
apply Rmult_le_0_lt_compat.
apply Rabs_pos.
lra.
apply HNu; eapply le_trans; [apply Max.le_max_l|eexact Hn].
apply Ropp_lt_contravar; apply HNv; eapply le_trans; [apply Max.le_max_r|eexact Hn].
replace M with (- -M)%R by ring; apply Ropp_le_contravar; rewrite Ropp_involutive.
rewrite <- Rabs_Ropp.
apply RRle_abs.
Qed.

Lemma Rseq_cv_neg_pos_infty_mult :
  Rseq_cv_pos_infty Un -> Rseq_cv_neg_infty Vn ->
    Rseq_cv_neg_infty (Vn * Un).
Proof.
intros Hu Hv M.
destruct (Rseq_cv_pos_neg_infty_mult Hu Hv M) as [N HN].
exists N; intros n Hn.
unfold Rseq_mult; rewrite Rmult_comm.
apply HN; apply Hn.
Qed.

(**********)
Lemma Rseq_cv_finite_plus_neg_infty_r : forall l, 
  Rseq_cv Un l -> Rseq_cv_neg_infty Vn ->
  Rseq_cv_neg_infty (Un + Vn).
Proof.
intros l Hl Hf M.
destruct (Hl 1 ltac:(lra)) as [N HN].
destruct (Hf (M-(l +1))%R) as [N0 HN0].
exists (N+N0)%nat.
intros n Hn.
apply Rlt_le_trans with ((l+1)+ (M-(l+1)))%R.
apply Rplus_lt_compat.
apply Rminus_lt.
unfold Rminus.
rewrite Ropp_plus_distr.
rewrite <- Rplus_assoc.
rewrite Rplus_comm.
replace 0 with (-1 + 1)%R by ring.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (Rabs (Un n+ - l)).
apply RRle_abs.
apply HN; lia.
apply HN0; lia.
ring_simplify; apply Rle_refl.
Qed.

(**********)
Lemma Rseq_cv_finite_plus_neg_infty_l : forall l, 
  Rseq_cv_neg_infty Vn -> Rseq_cv Un l ->
  Rseq_cv_neg_infty (Vn + Un).
Proof.
intros l Hf Hl M.
destruct (Hl 1 ltac:(lra)) as [N HN].
destruct (Hf (M-(l +1))%R) as [N0 HN0].
exists (N+N0)%nat.
intros n Hn.
apply Rlt_le_trans with ((M-(l+1)) +(l+1))%R.
apply Rplus_lt_compat.
apply HN0; lia.
apply Rminus_lt.
unfold Rminus.
rewrite Ropp_plus_distr.
rewrite <- Rplus_assoc.
rewrite Rplus_comm.
replace 0 with (-1 + 1)%R by ring.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (Rabs (Un n+ - l)).
apply RRle_abs.
apply HN; lia.
ring_simplify; apply Rle_refl.
Qed.

(**********)
Lemma Rseq_cv_finite_minus_neg_infty : forall l, 
  Rseq_cv Un l -> Rseq_cv_neg_infty Vn ->
    Rseq_cv_pos_infty (Un - Vn).
Proof.
intros l Hl Hf M.
destruct (Hl 1 ltac:(lra)) as [N HN].
destruct (Hf (-M+(l -1))%R) as [N0 HN0].
exists (N+N0)%nat.
intros n Hn.
apply Rle_lt_trans with ((l-1)+ -(-M+(l -1)))%R.
ring_simplify; apply Rle_refl.
apply Rplus_lt_compat.
apply Rminus_lt.
unfold Rminus.
rewrite Rplus_comm.
rewrite <- Rplus_assoc.
rewrite Rplus_comm.
replace 0 with (-1 + 1)%R by ring.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (Rabs (- Un n+ l)).
apply RRle_abs.
rewrite Rplus_comm.
fold (Rminus l (Un n)).
fold (R_dist l (Un n)).
rewrite R_dist_sym.
apply HN; lia.
apply Ropp_gt_lt_contravar.
apply HN0; lia.
Qed.

(**********)
Lemma Rseq_cv_finite_minus_pos_infty : forall l, 
  Rseq_cv Un l -> Rseq_cv_pos_infty Vn ->
    Rseq_cv_neg_infty (Un - Vn).
Proof.
intros l Hl Hf M.
destruct (Hl 1 ltac:(lra)) as [N HN].
destruct (Hf ((l +1)+ -M)%R) as [N0 HN0].
exists (N+N0)%nat.
intros n Hn.
apply Rlt_le_trans with ((l+1)+ -((l +1)+-M))%R.
apply Rplus_lt_compat.
apply Rminus_lt.
unfold Rminus.
rewrite Ropp_plus_distr.
rewrite <- Rplus_assoc.
rewrite Rplus_comm.
replace 0 with (-1 + 1)%R by ring.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (Rabs (Un n+ - l)).
apply RRle_abs.
apply HN; lia.
apply Ropp_gt_lt_contravar.
apply HN0; lia.
ring_simplify; apply Rle_refl.
Qed.

(**********)
Lemma Rseq_cv_pos_minus_neg_infty :
  Rseq_cv_pos_infty Un -> Rseq_cv_neg_infty Vn -> Rseq_cv_pos_infty (Un - Vn).
Proof.
intros Hl Hf M.
destruct (Hl M) as [N HN].
destruct (Hf 0%R) as [N0 HN0].
exists (N+N0)%nat.
intros n Hn.
apply Rle_lt_trans with (M+-0)%R.
ring_simplify; apply Rle_refl.
apply Rplus_lt_compat.
apply HN; lia.
apply Ropp_gt_lt_contravar.
apply HN0; lia.
Qed.

(**********)
Lemma Rseq_cv_neg_minus_pos_infty :
  Rseq_cv_neg_infty Un -> Rseq_cv_pos_infty Vn -> Rseq_cv_neg_infty (Un - Vn).
Proof.
intros Hl Hf M.
destruct (Hl M) as [N HN].
destruct (Hf 0%R) as [N0 HN0].
exists (N+N0)%nat.
intros n Hn.
apply Rlt_le_trans with (M+-0)%R.
apply Rplus_lt_compat.
apply HN; lia.
apply Ropp_gt_lt_contravar.
apply HN0; lia.
ring_simplify; apply Rle_refl.
Qed.

(**********)
Lemma Rseq_cv_finite_pos_mult_pos_infty_r : forall l, 
  0 < l -> Rseq_cv Un l -> Rseq_cv_pos_infty Vn ->
    Rseq_cv_pos_infty (Un * Vn).
Proof.
intros l Hl Hu Hv M.
destruct (Hu (l*/2)%R) as [N HN].
repeat apply Rmult_gt_0_compat; try lra.
destruct (Hv ((Rabs M)*(/l*2))%R) as [N0 HN0].
exists (N+N0)%nat; intros n Hn.
apply Rle_lt_trans with ((l*/2)*((Rabs M)*(2*/l)))%R.
replace ((l*/2)*((Rabs M)*(2*/l)))%R with (Rabs M).
apply RRle_abs.
field.
apply Rgt_not_eq; exact Hl.
apply Rmult_le_0_lt_compat.
repeat apply Rmult_gt_0_compat; try lra.
replace 0%R with (Rabs M * 0)%R by field.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Rlt_le.
repeat apply Rmult_gt_0_compat; try lra.
apply Rinv_0_lt_compat.
exact Hl.
replace (l * /2)%R with (l - (l * /2))%R by field.
apply Rminus_lt.
unfold Rminus.
rewrite Rplus_comm.
rewrite <- Rplus_assoc.
rewrite Rplus_comm.
replace 0 with (- (l * /2) + (l * /2))%R by ring.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (Rabs (Un n+ - l)).
rewrite <- Rabs_Ropp.
rewrite Ropp_plus_distr, Ropp_involutive.
apply RRle_abs.
apply HN; lia.
rewrite (Rmult_comm 2 (/l)).
apply HN0; lia.
Qed.

(**********)
Lemma Rseq_cv_finite_neg_mult_pos_infty_r : forall l, 
  l < 0 -> Rseq_cv Un l -> Rseq_cv_pos_infty Vn ->
    Rseq_cv_neg_infty (Un * Vn).
Proof.
intros l Hl Hu Hv M.
destruct (Hu (-(l*/2))%R) as [N HN].
repeat apply Rmult_gt_0_compat; try lra.
destruct (Hv (-(Rabs M)*(/l*2))%R) as [N0 HN0].
exists (N+N0)%nat; intros n Hn.
apply Rlt_le_trans with ((l*/2)*(-(Rabs M)*(2*/l)))%R.
replace ((Un * Vn)%Rseq n) with (Un n * Vn n)%R by reflexivity.
apply Ropp_lt_cancel.
rewrite <- Ropp_mult_distr_l_reverse, <- (Ropp_mult_distr_l_reverse (Un n) (Vn n)).
apply Rmult_le_0_lt_compat.
repeat apply Rmult_gt_0_compat; try lra.
replace (-(Rabs M)*(2*/l))%R with ((Rabs M)*(- 2*/l))%R by ring.
replace (IZR 0) with (Rabs M * 0)%R by field.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Rlt_le.
Set Printing All.
change (IZR (-2)) with (- (IZR 2))%R.
rewrite Ropp_mult_distr_l_reverse, <- Ropp_mult_distr_r_reverse.
repeat apply Rmult_gt_0_compat; try lra.
apply Ropp_0_gt_lt_contravar.
apply Rinv_lt_0_compat.
exact Hl.
apply Ropp_gt_lt_contravar.
replace (l * /2)%R with (l - (l * /2))%R by field.
apply Rminus_lt.
unfold Rminus.
rewrite Ropp_plus_distr, Ropp_involutive, <- Rplus_assoc.
replace 0 with (- (l * /2) + (l * /2))%R by ring.
apply Rplus_lt_compat_r.
apply Rle_lt_trans with (Rabs (Un n+ - l)).
apply RRle_abs.
apply HN; lia.
rewrite (Rmult_comm 2 (/l)).
apply HN0; lia.
replace (l * /2 * (- Rabs M *(2 * /l)))%R with (- Rabs M)%R.
rewrite <- (Ropp_involutive M).
apply Ropp_ge_le_contravar.
rewrite Rabs_Ropp.
apply Rle_ge.
apply RRle_abs.
field.
apply Rlt_not_eq.
exact Hl.
Qed.

(**********)
Lemma Rseq_cv_finite_pos_mult_neg_infty_r : forall l,
  0 < l -> Rseq_cv Un l -> Rseq_cv_neg_infty Vn ->
    Rseq_cv_neg_infty (Un * Vn).
Proof.
intros l Hl Hu Hv M.
destruct (Hu (l*/2)%R) as [N HN].
repeat apply Rmult_gt_0_compat; try lra.
destruct (Hv (-(Rabs M)*(/l*2))%R) as [N0 HN0].
exists (N+N0)%nat; intros n Hn.
apply Rlt_le_trans with ((l*/2)*(-(Rabs M)*(2*/l)))%R.
replace ((Un * Vn)%Rseq n)%R with (Un n * Vn n)%R by reflexivity.
apply Ropp_lt_cancel.
replace (- (l */2  *(- Rabs M * (2 * /l))))%R 
    with (l */2  *( Rabs M * (2 * /l)))%R by ring.
rewrite <- (Ropp_mult_distr_r_reverse (Un n) (Vn n)).
apply Rmult_le_0_lt_compat.
repeat apply Rmult_gt_0_compat; try lra.
replace 0%R with (Rabs M * 0)%R by field.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Rlt_le.
repeat apply Rmult_gt_0_compat; try lra.
apply Rinv_0_lt_compat.
exact Hl.
replace (l * /2)%R with (l - (l * /2))%R by field.
apply Rminus_lt.
unfold Rminus.
rewrite Rplus_comm, <- Rplus_assoc, Rplus_comm.
replace 0 with (- (l * /2) + (l * /2))%R by ring.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (Rabs (Un n+ - l)).
rewrite <- Rabs_Ropp, Ropp_plus_distr, Ropp_involutive.
apply RRle_abs.
apply HN; lia.
apply Ropp_lt_cancel.
rewrite (Rmult_comm 2 (/l)), <- Ropp_mult_distr_l_reverse, Ropp_involutive.
apply HN0; lia.
replace (l * /2 * (- Rabs M *(2 * /l)))%R with (- Rabs M)%R.
rewrite <- (Ropp_involutive M).
apply Ropp_ge_le_contravar.
rewrite Rabs_Ropp.
apply Rle_ge.
apply RRle_abs.
field.
apply Rgt_not_eq.
exact Hl.
Qed.

(**********)
Lemma Rseq_cv_finite_neg_mult_neg_infty_r : forall l,
  l < 0 -> Rseq_cv Un l -> Rseq_cv_neg_infty Vn ->
    Rseq_cv_pos_infty (Un * Vn).
Proof.
intros l Hl Hu Hv M.
destruct (Hu (-(l*/2))%R) as [N HN].
repeat apply Rmult_gt_0_compat; try lra.
destruct (Hv ((Rabs M)*(/l*2))%R) as [N0 HN0].
exists (N+N0)%nat; intros n Hn.
apply Rle_lt_trans with (-(l*/2)*(-(Rabs M)*(2*/l)))%R.
replace (-(l*/2)*(-(Rabs M)*(2*/l)))%R with (Rabs M).
apply RRle_abs.
field.
apply Rlt_not_eq.
exact Hl.
replace ((Un * Vn)%Rseq n) with (Un n * Vn n)%R by reflexivity.
replace (Un n * Vn n)%R with ((- Un n) * (- Vn n))%R by ring.
apply Rmult_le_0_lt_compat.
repeat apply Rmult_gt_0_compat; try lra.
replace (-(Rabs M)*(2*/l))%R with ((Rabs M)*(- 2*/l))%R by ring.
replace 0%R with (Rabs M * 0)%R by field.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Rlt_le.
change (IZR (-2)) with (- (IZR 2))%R.
rewrite Ropp_mult_distr_l_reverse, <- Ropp_mult_distr_r_reverse.
repeat apply Rmult_gt_0_compat; try lra.
apply Ropp_0_gt_lt_contravar.
apply Rinv_lt_0_compat.
exact Hl.
apply Ropp_lt_contravar.
replace (l * /2)%R with (l - (l * /2))%R by field.
apply Rminus_lt.
unfold Rminus.
rewrite Ropp_plus_distr, Ropp_involutive, <- Rplus_assoc.
replace 0 with (- (l * /2) + (l * /2))%R by ring.
apply Rplus_lt_compat_r.
apply Rle_lt_trans with (Rabs (Un n+ - l)).
apply RRle_abs.
apply HN; lia.
rewrite Ropp_mult_distr_l_reverse.
apply Ropp_gt_lt_contravar.
apply Rlt_gt.
rewrite (Rmult_comm 2 (/l)).
apply HN0; lia.
Qed.


(**********)
Lemma Rseq_cv_finite_pos_mult_pos_infty_l : forall l,
  0 < l -> Rseq_cv Un l -> Rseq_cv_pos_infty Vn ->
    Rseq_cv_pos_infty (Vn * Un).
Proof.
intros l Hl Hu Hv M.
destruct (Hu (l*/2)%R) as [N HN].
repeat apply Rmult_gt_0_compat; try lra.
destruct (Hv ((Rabs M)*(/l*2))%R) as [N0 HN0].
exists (N+N0)%nat; intros n Hn.
apply Rle_lt_trans with ((l*/2)*((Rabs M)*(2*/l)))%R.
replace (l */2 * (Rabs M * (2 * /l)))%R with (Rabs M).
apply RRle_abs.
field.
apply Rgt_not_eq.
exact Hl.
replace ((Vn * Un)%Rseq n) with (Vn n * Un n)%R by reflexivity.
rewrite (Rmult_comm (Vn n) (Un n)).
apply Rmult_le_0_lt_compat.
repeat apply Rmult_gt_0_compat; try lra.
replace 0%R with (Rabs M * 0)%R by field.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Rlt_le.
repeat apply Rmult_gt_0_compat; try lra.
apply Rinv_0_lt_compat.
exact Hl.
replace (l * /2)%R with (l - (l * /2))%R by field.
apply Rminus_lt.
unfold Rminus.
rewrite Rplus_comm.
rewrite <- Rplus_assoc.
rewrite Rplus_comm.
replace 0 with (- (l * /2) + (l * /2))%R by ring.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (Rabs (Un n+ - l)).
rewrite <- Rabs_Ropp.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
apply RRle_abs.
apply HN; lia.
rewrite (Rmult_comm 2 (/l)).
apply HN0; lia.
Qed.

(**********)
Lemma Rseq_cv_finite_neg_mult_pos_infty_l : forall l,
  l < 0 -> Rseq_cv Un l -> Rseq_cv_pos_infty Vn ->
    Rseq_cv_neg_infty (Vn * Un).
Proof.
intros l Hl Hu Hv M.
destruct (Hu (-(l*/2))%R) as [N HN].
repeat apply Rmult_gt_0_compat; try lra.
destruct (Hv (-(Rabs M)*(/l*2))%R) as [N0 HN0].
exists (N+N0)%nat; intros n Hn.
apply Rlt_le_trans with ((l*/2)*(-(Rabs M)*(2*/l)))%R.
apply Ropp_lt_cancel.
rewrite <- Ropp_mult_distr_l_reverse.
replace ((Vn * Un)%Rseq n) with (Vn n * Un n)%R by reflexivity.
rewrite (Rmult_comm (Vn n) (Un n)).
rewrite <- (Ropp_mult_distr_l_reverse (Un n) (Vn n)).
apply Rmult_le_0_lt_compat.
apply Rlt_le.
repeat apply Rmult_gt_0_compat; try lra.
replace (-(Rabs M)*(2*/l))%R with ((Rabs M)*(- 2*/l))%R by ring.
replace 0%R with (Rabs M * 0)%R by field.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Rlt_le.
change (IZR (-2)) with (- (IZR 2))%R.
rewrite Ropp_mult_distr_l_reverse, <- Ropp_mult_distr_r_reverse.
repeat apply Rmult_gt_0_compat; try lra.
apply Ropp_0_gt_lt_contravar.
apply Rinv_lt_0_compat.
exact Hl.
apply Ropp_gt_lt_contravar.
replace (l * /2)%R with (l - (l * /2))%R by field.
apply Rminus_lt.
unfold Rminus.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
rewrite <- Rplus_assoc.
replace 0 with (- (l * /2) + (l * /2))%R by ring.
apply Rplus_lt_compat_r.
apply Rle_lt_trans with (Rabs (Un n+ - l)).
apply RRle_abs.
apply HN; lia.
rewrite (Rmult_comm 2 (/l)).
apply HN0; lia.
replace (l * /2 * (- Rabs M *(2 * /l)))%R with (- Rabs M)%R.
rewrite <- (Ropp_involutive M).
apply Ropp_ge_le_contravar.
rewrite Rabs_Ropp.
apply Rle_ge.
apply RRle_abs.
field.
apply Rlt_not_eq.
exact Hl.
Qed.


(**********)
Lemma Rseq_cv_finite_pos_mult_neg_infty_l : forall l,
  0 < l -> Rseq_cv Un l -> Rseq_cv_neg_infty Vn ->
    Rseq_cv_neg_infty (Vn * Un).
Proof.
intros l Hl Hu Hv M.
destruct (Hu (l*/2)%R) as [N HN].
repeat apply Rmult_gt_0_compat; try lra.
destruct (Hv (-(Rabs M)*(/l*2))%R) as [N0 HN0].
exists (N+N0)%nat; intros n Hn.
apply Rlt_le_trans with ((l*/2)*(-(Rabs M)*(2*/l)))%R.
replace ((Vn * Un)%Rseq n) with (Vn n * Un n)%R by reflexivity.
rewrite (Rmult_comm (Vn n) (Un n)).
apply Ropp_lt_cancel.
rewrite <- (Ropp_mult_distr_r_reverse (Un n) (Vn n)).
rewrite <- Ropp_mult_distr_r_reverse, <- Ropp_mult_distr_l_reverse, Ropp_involutive.
replace (- (l * /2 * (- Rabs M * (2 * /l))))%R with (l * /2 * (Rabs M * (2 * /l)))%R by ring.
apply Rmult_le_0_lt_compat.
repeat apply Rmult_gt_0_compat; try lra.
replace 0%R with (Rabs M * 0)%R by field.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Rlt_le.
repeat apply Rmult_gt_0_compat; try lra.
apply Rinv_0_lt_compat.
exact Hl.
replace (l * /2)%R with (l - (l * /2))%R by field.
apply Rminus_lt.
unfold Rminus.
rewrite Rplus_comm, <- Rplus_assoc, Rplus_comm.
replace 0 with (- (l * /2) + (l * /2))%R by ring.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (Rabs (Un n+ - l)).
rewrite <- Rabs_Ropp, Ropp_plus_distr, Ropp_involutive.
apply RRle_abs.
apply HN; lia.
apply Ropp_lt_cancel.
rewrite (Rmult_comm 2 (/l)), <- Ropp_mult_distr_l_reverse, Ropp_involutive.
apply HN0; lia.
replace (l * /2 * (- Rabs M *(2 * /l)))%R with (- Rabs M)%R.
rewrite <- (Ropp_involutive M).
apply Ropp_ge_le_contravar.
rewrite Rabs_Ropp.
apply Rle_ge.
apply RRle_abs.
field.
apply Rgt_not_eq.
exact Hl.
Qed.

(**********)
Lemma Rseq_cv_finite_neg_mult_neg_infty_l : forall l, 
  l < 0 -> Rseq_cv Un l -> Rseq_cv_neg_infty Vn ->
    Rseq_cv_pos_infty (Vn * Un).
Proof.
intros l Hl Hu Hv M.
destruct (Hu (-(l*/2))%R) as [N HN].
repeat apply Rmult_gt_0_compat; try lra.
destruct (Hv ((Rabs M)*(/l*2))%R) as [N0 HN0].
exists (N+N0)%nat; intros n Hn.
apply Rle_lt_trans with (-(l*/2)*(-(Rabs M)*(2*/l)))%R.
replace (-(l*/2)*(-(Rabs M)*(2*/l)))%R with (Rabs M)%R.
apply RRle_abs.
field.
apply Rlt_not_eq.
exact Hl.
replace ((Vn * Un)%Rseq n) with (Vn n * Un n)%R by reflexivity.
replace (Vn n * Un n)%R with (-Un n * -Vn n)%R by ring.
apply Rmult_le_0_lt_compat.
repeat apply Rmult_gt_0_compat; try lra.
replace (- Rabs M * (2 * /l))%R with ( Rabs M * (- 2 * /l))%R by ring.
replace 0%R with (Rabs M * 0)%R by field.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Rlt_le.
change (IZR (-2)) with (- (IZR 2))%R.
rewrite Ropp_mult_distr_l_reverse, <- Ropp_mult_distr_r_reverse.
repeat apply Rmult_gt_0_compat; try lra.
apply Ropp_0_gt_lt_contravar.
apply Rinv_lt_0_compat.
exact Hl.
apply Ropp_gt_lt_contravar.
replace (l * /2)%R with (l - (l * /2))%R by field.
apply Rminus_lt.
unfold Rminus.
rewrite Ropp_plus_distr, Ropp_involutive, <- Rplus_assoc.
replace 0 with (- (l * /2) + (l * /2))%R by ring.
apply Rplus_lt_compat_r.
apply Rle_lt_trans with (Rabs (Un n+ - l)).
apply RRle_abs.
apply HN; lia.
rewrite Ropp_mult_distr_l_reverse.
apply Ropp_gt_lt_contravar.
apply Rlt_gt.
rewrite (Rmult_comm 2 (/l)).
apply HN0; lia.
Qed.

(**********)
Lemma Rseq_cv_neg_infty_plus_compat :
  Rseq_cv_neg_infty Un -> Rseq_cv_neg_infty Vn ->
    Rseq_cv_neg_infty (Un + Vn).
Proof.
intros Hu Hv M.
destruct (Hu (M / 2)%R) as [Nu HNu].
destruct (Hv (M / 2)%R) as [Nv HNv].
exists (Max.max Nu Nv); intros n Hn.
unfold Rseq_plus.
replace M with (M / 2 + M / 2)%R by field.
apply Rplus_lt_compat.
apply HNu; eapply le_trans; [apply Max.le_max_l|eexact Hn].
apply HNv; eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

(**********)
Lemma Rseq_cv_pos_infty_opp_compat : Rseq_cv_pos_infty Un -> Rseq_cv_neg_infty (- Un).
Proof.
intros H M.
destruct (H (- M)%R) as [N HN].
exists N; intros n Hn.
unfold Rseq_opp.
rewrite <- Ropp_involutive.
apply Ropp_gt_lt_contravar.
apply HN; assumption.
Qed.

(**********)
Lemma Rseq_cv_neg_infty_opp_compat : Rseq_cv_neg_infty Un -> Rseq_cv_pos_infty (- Un).
Proof.
intros H M.
destruct (H (- M)%R) as [N HN].
exists N; intros n Hn.
unfold Rseq_opp.
pattern M; rewrite <- Ropp_involutive.
apply Ropp_lt_gt_contravar.
apply HN; assumption.
Qed.

(**********)
Lemma Rseq_cv_pos_infty_inv_compat : Rseq_cv_pos_infty Un -> Rseq_cv (/ Un) 0.
Proof.
intros H eps Heps.
destruct (H (/eps)%R) as [N HN].
exists N; intros n Hn.
assert (Hpos : Un n > 0).
eapply Rlt_trans; [|apply HN; assumption].
apply Rinv_0_lt_compat; assumption.
unfold R_dist; unfold Rseq_inv.
replace (/Un n - 0)%R with (/ Un n)%R; [|field; auto with real].
rewrite <- Rinv_involutive; [|apply Rgt_not_eq; assumption].
rewrite Rabs_Rinv; [|auto with real].
apply Rinv_lt_contravar.
apply Rmult_gt_0_compat.
apply Rinv_0_lt_compat; assumption.
rewrite Rabs_right; [|left]; assumption.
rewrite Rabs_right; [apply HN|left]; assumption.
Qed.


(**********)
Lemma Rseq_cv_pos_infty_div_compat : forall l, 
    Rseq_cv_pos_infty Un -> Rseq_cv Vn l -> Rseq_cv (Vn / Un) 0.
Proof.
intros l HU HV.
assert (H : Rseq_cv (Vn*(/Un)) 0).
rewrite <- Rmult_0_r with l.
apply Rseq_cv_mult_compat.
apply HV.
apply Rseq_cv_pos_infty_inv_compat; apply HU.
unfold Rseq_mult in H.
unfold Rseq_div, Rdiv.
apply H.
Qed.

(**********)
Lemma Rseq_cv_neg_infty_inv_compat : Rseq_cv_neg_infty Un -> Rseq_cv (/ Un) 0.
intros H eps Heps.
destruct (H (-/eps)%R) as [N HN].
exists N; intros n Hn.
assert (Hpos : Un n < 0).
eapply Rlt_trans; [apply HN; assumption|].
apply Ropp_lt_gt_0_contravar; apply Rinv_0_lt_compat; assumption.
unfold R_dist; unfold Rseq_inv.
replace (/ Un n - 0)%R with (/ Un n)%R; [|field; auto with real].
rewrite <- Rinv_involutive; [|apply Rgt_not_eq; assumption].
rewrite Rabs_Rinv; [|auto with real].
apply Rinv_lt_contravar.
apply Rmult_gt_0_compat.
apply Rinv_0_lt_compat; assumption.
apply Rabs_pos_lt; apply Rlt_not_eq; assumption.
rewrite Rabs_left; [|assumption].
pattern (/ eps)%R; rewrite <- Ropp_involutive.
apply Ropp_gt_lt_contravar.
apply HN; assumption.
Qed.

(**********)
Lemma Rseq_cv_neg_infty_div_compat : forall l, 
    Rseq_cv_neg_infty Un -> Rseq_cv Vn l -> Rseq_cv (Vn / Un) 0.
Proof.
intros l HU HV.
assert (H : Rseq_cv (Vn*(/Un)) 0).
rewrite <- Rmult_0_r with l.
apply Rseq_cv_mult_compat.
apply HV.
apply Rseq_cv_neg_infty_inv_compat; apply HU.
unfold Rseq_mult in H.
unfold Rseq_div, Rdiv.
apply H.
Qed.

(**********)
Lemma Rseq_cv_0_inv_compat :
  Rseq_cv Un 0 -> Rseq_neq_0 Un ->
    Rseq_cv_pos_infty (|/ Un|).
Proof.
intros Hcv He M.
pose (Mp := Rmax 1 M).
assert (Hp : Mp > 0).
eapply Rlt_le_trans; [apply Rlt_0_1|apply RmaxLess1].
destruct (Hcv (/ Mp)%R) as [N HN].
apply Rinv_0_lt_compat; assumption.
exists N; intros n Hn.
apply Rle_lt_trans with Mp; [apply RmaxLess2|].
pattern Mp; rewrite <- Rinv_involutive; [|auto with real].
assert (Hd : Un n <> 0).
apply He.
unfold Rseq_abs, Rseq_inv.
rewrite Rabs_Rinv; [|assumption].
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat; [|auto with real].
apply Rabs_pos_lt; assumption.
replace (Un n) with (Un n - 0)%R by field.
apply HN; assumption.
Qed.

(**********)
Lemma Rseq_cv_abs_pos_infty : Rseq_cv_pos_infty Un -> Rseq_cv_pos_infty (|Un|).
Proof.
intros HU M.
destruct (HU (Rabs M)) as [N HN].
exists N.
intros n Hn.
apply Rle_lt_trans with (Rabs M).
apply RRle_abs.
apply Rlt_le_trans with (Un n).
apply (HN _ Hn).
apply RRle_abs.
Qed.

(**********)
Lemma Rseq_cv_abs_neg_infty : Rseq_cv_neg_infty Un -> Rseq_cv_pos_infty (|Un|).
Proof.
intros HU M.
assert (H : Rseq_cv_pos_infty (-Un)).
apply Rseq_cv_neg_infty_opp_compat.
apply HU.
destruct (H (Rabs M)) as [N HN].
exists N.
intros n Hn.
apply Rle_lt_trans with (Rabs M).
apply RRle_abs.
apply Rlt_le_trans with (- (Un n))%R.
apply (HN _ Hn).
unfold Rseq_abs.
rewrite <- Rabs_Ropp.
apply RRle_abs.
Qed.

End Rseq_cv_infty.

Section Rseq_cv_others.

(** * Uniqueness of limit. *)

(**********)
Lemma Rseq_cv_unique : forall Un lu1 lu2, Rseq_cv Un lu1 -> Rseq_cv Un lu2 -> lu1 = lu2.
Proof.
intros Un lu1 lu2 H1 H2.
assert (H: forall eps, eps > 0 -> Rabs (lu1 - lu2) <= eps).
  intros eps Heps.
  destruct (H1 (eps / 2)%R) as [N1 HN1]; [lra|].
  destruct (H2 (eps / 2)%R) as [N2 HN2]; [lra|].
  pose (N := Max.max N1 N2).
  replace (lu1 - lu2)%R
    with ((lu1 - Un N) + (Un N - lu2))%R by field.
  replace eps with (eps / 2 + eps / 2)%R by field.
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rplus_le_compat.
    left; rewrite Rabs_minus_sym; apply HN1; apply Max.le_max_l.
    left; apply HN2; apply Max.le_max_r.
apply Rle_antisym; apply le_epsilon;
intros eps Heps; apply H in Heps;
unfold Rabs in Heps; destruct Rcase_abs; lra.
Qed.

Lemma Rseq_cv_Rseq_cv_pos_infty_incompat : forall An l,
  Rseq_cv An l -> Rseq_cv_pos_infty An -> False.
Proof.
intros An l Hl Hinfty ; destruct (Hl _ Rlt_0_1) as [M HM] ;
 destruct (Hinfty (Rabs l + 1)%R) as [N HN] ;
 apply (Rlt_irrefl (An (max M N))) ; transitivity (Rabs l + 1)%R.
 rewrite <- (Rabs_right (An _)).
 apply Rminus_lt_compat_l_rev, Rle_lt_trans with (R_dist (An (max M N)) l).
  apply Rabs_triang_inv.
  apply HM, le_max_l.
  apply Rle_ge ; transitivity (Rabs l + 1)%R.
   apply Rplus_le_le_0_compat ; [apply Rabs_pos | lra].
   left ; apply HN, le_max_r.
  apply HN, le_max_r.
Qed.

Lemma Rseq_cv_Rseq_cv_neg_infty_incompat : forall An l,
  Rseq_cv An l -> Rseq_cv_neg_infty An -> False.
Proof.
intros ; eapply Rseq_cv_Rseq_cv_pos_infty_incompat.
 eapply Rseq_cv_opp_compat ; eassumption.
 eapply Rseq_cv_neg_infty_opp_compat ; eassumption.
Qed.

(** * Sandwich theorem. *)

(**********)
Lemma Rseq_sandwich_theorem :
  forall Un Vn Wn l,
    (Rseq_cv Un l) -> (Rseq_cv Wn l) -> (forall n, Un n <= Vn n <= Wn n) -> Rseq_cv Vn l.
Proof.
intros Un Vn Wn l Hu Hw H eps Heps.
destruct (Hu eps Heps) as [Nu HNu].
destruct (Hw eps Heps) as [Nw HNw].
exists (Max.max Nu Nw); intros n Hn.
eapply Rle_lt_trans.
  apply RmaxAbs; apply Rplus_le_compat_r; apply (H n).
  unfold Rmax; destruct Rle_dec as [_|_].
  apply HNw; eapply le_trans; [apply Max.le_max_r|eassumption].
  apply HNu; eapply le_trans; [apply Max.le_max_l|eassumption].
Qed.

(** * Limit of (non) negative terms *)

(**********)
Lemma Rseq_positive_limit : forall (An : nat -> R) (a : R),
      (forall n, 0 <= An n) ->
       Rseq_cv An a ->
       0 <= a.
Proof.
intros An a Hpos Ha.
apply Rnot_lt_le; intro Na.
destruct (Ha (Ropp (Rdiv a 2))) as [N HN]; [lra | ].
pose proof (HN N (le_n N)).
generalize dependent H.
unfold R_dist, Rabs.
pose proof Hpos N as Hposn.
destruct (Rcase_abs (An N - a)); intro; lra.
Qed.

(**********)
Lemma Rseq_negative_limit : forall (An : nat -> R) (a : R),
  (forall n, An n <= 0) -> Rseq_cv An a -> a <= 0.
Proof.
intros An a Hneg Ha ; apply Ropp_le_cancel ; rewrite Ropp_0 ;
 eapply Rseq_positive_limit, Rseq_cv_opp_compat, Ha.
 intro n ; apply Ropp_0_ge_le_contravar, Rle_ge, Hneg.
Qed.

(** * Compatibility of Rle and interval with the limit *)

(**********)
Lemma Rseq_limit_comparison: forall (An Bn : nat -> R) (a b : R),
      (forall n, An n <= Bn n) ->
       Rseq_cv An a -> Rseq_cv Bn b ->
       a <= b.
Proof.
intros An Bn a b Hcomp Ha Hb.
assert (0 <= b - a).
 apply Rseq_positive_limit with (fun n => (Bn n - An n)%R).
  intro n; pose proof Hcomp n; lra.
  apply Rseq_cv_minus_compat; auto.
 lra.
Qed.

Lemma Rseq_interval_compat : forall (An : Rseq) (a lb ub : R),
  (forall n, interval lb ub (An n)) -> Rseq_cv An a ->
  interval lb ub a.
Proof.
intros An a lb ub Hcomp Ha ; split ; eapply Rseq_limit_comparison.
 intro ; apply (proj1 (Hcomp n)).
  apply Rseq_constant_cv.
  assumption.
 intro n ; apply (proj2 (Hcomp n)).
  assumption.
  apply Rseq_constant_cv.
Qed. 

End Rseq_cv_others.

(* begin hide *)
Hint Resolve Rseq_constant_cv : Rseq.
Hint Resolve Rseq_cv_0_inv_compat : Rseq.
Hint Resolve Rseq_cv_abs_compat: Rseq.
Hint Resolve Rseq_cv_abs_neg_infty : Rseq.
Hint Resolve Rseq_cv_abs_pos_infty : Rseq.
Hint Resolve Rseq_cv_continuity_compat : Rseq.
Hint Resolve Rseq_cv_div_compat : Rseq.
Hint Resolve Rseq_cv_finite_minus_neg_infty : Rseq.
Hint Resolve Rseq_cv_finite_minus_pos_infty : Rseq.
Hint Resolve Rseq_cv_finite_neg_mult_neg_infty_l : Rseq.
Hint Resolve Rseq_cv_finite_neg_mult_neg_infty_r : Rseq.
Hint Resolve Rseq_cv_finite_neg_mult_pos_infty_l : Rseq.
Hint Resolve Rseq_cv_finite_neg_mult_pos_infty_r : Rseq.
Hint Resolve Rseq_cv_finite_plus_neg_infty_l : Rseq.
Hint Resolve Rseq_cv_finite_plus_neg_infty_l: Rseq.
Hint Resolve Rseq_cv_finite_plus_neg_infty_r : Rseq.
Hint Resolve Rseq_cv_finite_plus_neg_infty_r: Rseq.
Hint Resolve Rseq_cv_finite_plus_pos_infty_l : Rseq.
Hint Resolve Rseq_cv_finite_plus_pos_infty_r : Rseq.
Hint Resolve Rseq_cv_finite_pos_mult_neg_infty_l : Rseq.
Hint Resolve Rseq_cv_finite_pos_mult_neg_infty_r : Rseq.
Hint Resolve Rseq_cv_finite_pos_mult_pos_infty_l : Rseq.
Hint Resolve Rseq_cv_finite_pos_mult_pos_infty_r : Rseq.
Hint Resolve Rseq_cv_inv_compat : Rseq.
Hint Resolve Rseq_cv_minus_compat : Rseq.
Hint Resolve Rseq_cv_mult_compat : Rseq.
Hint Resolve Rseq_cv_neg_infty_div_compat : Rseq.
Hint Resolve Rseq_cv_neg_infty_inv_compat : Rseq.
Hint Resolve Rseq_cv_neg_infty_opp_compat : Rseq.
Hint Resolve Rseq_cv_neg_infty_plus_compat : Rseq.
Hint Resolve Rseq_cv_neg_infty_plus_compat : Rseq.
Hint Resolve Rseq_cv_neg_minus_pos_infty : Rseq.
Hint Resolve Rseq_cv_neg_neg_infty_mult : Rseq.
Hint Resolve Rseq_cv_neg_pos_infty_mult : Rseq.
Hint Resolve Rseq_cv_opp_compat : Rseq.
Hint Resolve Rseq_cv_plus_compat : Rseq.
Hint Resolve Rseq_cv_pos_infty_inv_compat : Rseq.
Hint Resolve Rseq_cv_pos_infty_opp_compat : Rseq.
Hint Resolve Rseq_cv_pos_infty_plus_compat : Rseq.
Hint Resolve Rseq_cv_pos_minus_neg_infty : Rseq.
Hint Resolve Rseq_cv_pos_neg_infty_mult : Rseq.
Hint Resolve Rseq_cv_pos_pos_infty_mult : Rseq.
(* end hide *)
