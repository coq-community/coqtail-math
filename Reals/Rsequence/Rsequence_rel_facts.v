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
Require Import Max.
Require Import Reals.
Require Export Setoid Morphisms.
Require Import Rsequence_def.
Require Import Rsequence_base_facts.
Require Import Rsequence_cv_facts.
Require Import Lra.

Open Scope R_scope.
Open Scope Rseq_scope.
(** printing ~	~ *)
(** * Big-O, little-O and equivalence relations. *)

(** Big-O is reflexive and transitive. *)

(**********)
Lemma Rseq_big_O_refl : forall Un, Un = O(Un).
Proof.
exists 1; split; [|exists 0%nat; intros n H]; lra.
Qed.

(**********)
Lemma Rseq_big_O_trans : forall Un Vn Wn, Un = O(Vn) -> Vn = O(Wn) -> Un = O(Wn).
Proof.
intros Un Vn Wn Hu Hv.
destruct Hu as [Mu [HMu Hu]];
destruct Hv as [Mv [HMv Hv]].
exists (Mu * Mv)%R; split.
replace 0 with (0 * 0)%R by field.
apply Rmult_ge_compat; (assumption || apply Rge_refl).
destruct Hu as [Nu Hu];
destruct Hv as [Nv Hv].
exists (Max.max Nu Nv); intros n Hn.
apply Rle_trans with (r2 := (Mu * Rabs (Vn n))%R).
apply (Hu n); eapply le_trans; [apply Max.le_max_l|eexact Hn].
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rge_le; assumption.
apply (Hv n); eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

(**********)
Instance Rseq_big_O_PreOrder : PreOrder Rseq_big_O.
Proof.
split.
  exact Rseq_big_O_refl.
  exact Rseq_big_O_trans.
Qed.

(** Little-O is transitive. *)

(**********)
Lemma Rseq_little_O_trans : forall Un Vn Wn, Un = o(Vn) -> Vn = o(Wn) -> Un = o(Wn).
Proof.
intros Un Vn Wn Hu Hv eps Heps.
destruct (Hu 1) as [Nu HNu]; [lra|].
destruct (Hv eps) as [Nv Hnv]; [assumption|].
exists (Max.max Nu Nv).
intros n Hn.
apply Rle_trans with (r2 := (Rabs (Vn n))%R).
rewrite <- Rmult_1_l; apply (HNu n).
eapply le_trans; [apply Max.le_max_l|eexact Hn].
apply (Hnv n).
eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

(**********)
Instance Rseq_little_O_Transitive : Transitive Rseq_little_O.
Proof.
exact Rseq_little_O_trans.
Qed.

(** Equivalence is an equivalence relation. *)

(**********)
Lemma Rseq_equiv_refl : forall Un, Un ~ Un.
Proof.
intros Un eps Heps.
exists 0%nat; intros n Hn.
unfold Rseq_minus; unfold Rminus.
rewrite Rplus_opp_r; rewrite Rabs_R0.
replace 0%R with (0 * 0)%R by field.
apply Rmult_le_compat; auto with real.
apply Rabs_pos.
Qed.

(**********)
Lemma Rseq_equiv_sym : forall Un Vn, Un ~ Vn -> Vn ~ Un.
Proof.
intros Un Vn H eps Heps.
pose (eps' := (eps / (1 + eps))%R).
assert (Heps' : eps' > 0).
apply Rmult_gt_0_compat; [assumption|apply Rinv_0_lt_compat; lra].
destruct (H eps') as [N HN]; [assumption|].
exists N; intros n Hn.
unfold Rseq_minus; rewrite Rabs_minus_sym.
apply Rmult_le_reg_l with (/(1 + eps))%R;
  [apply Rinv_0_lt_compat; lra|].
rewrite <- Rmult_assoc.
replace (/(1 + eps))%R with (1 - eps')%R
  by (unfold eps'; field; apply Rgt_not_eq; lra).
replace ((1 - eps') * eps)%R with eps'
  by (unfold eps'; field; apply Rgt_not_eq; lra).
rewrite <- Rplus_0_r.
rewrite <- Rplus_opp_r with (eps' * Rabs (Un n - Vn n))%R.
unfold Rminus; rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
rewrite <- Rplus_assoc.
rewrite <- Ropp_mult_distr_l_reverse.
apply Rplus_le_compat_r.
eapply Rle_trans.
apply HN; assumption.
rewrite <- Rmult_plus_distr_l.
apply Rmult_le_compat_l; [left; assumption|].
replace (Rabs (Vn n) + Rabs (Un n + - Vn n))%R
  with (Rabs (Un n + - Vn n) + Rabs (Vn n))%R by field.
pattern Un at 2; replace (Un n) with (Un n - Vn n + Vn n)%R by field.
apply Rabs_triang.
Qed.

(**********)
Lemma Rseq_equiv_trans : forall Un Vn Wn, Un ~ Vn -> Vn ~ Wn -> Un ~ Wn.
Proof.
intros Un Vn Wn Hu Hv eps Heps.
pose (eps' := Rmin 1 (eps / 3)).
assert (Heps' : 0 < eps').
compute; destruct Rle_dec; lra.
assert (Heps2 : eps' * eps' <= eps').
pattern eps' at 3; replace eps' with (1 * eps')%R by field.
apply Rmult_le_compat; (auto with real || apply Rmin_l).
destruct (Hu eps') as [Nu HNu]; [assumption|].
destruct (Hv eps') as [Nv HNv]; [assumption|].
exists (Max.max Nu Nv); intros n Hn.
replace eps
  with (eps / 3 + (eps / 3 + eps / 3))%R by field.
do 2 rewrite Rmult_plus_distr_r. 
unfold Rseq_minus.
eapply Rle_trans; [apply R_dist_tri with (z := Vn n)|].
apply Rplus_le_compat.
eapply Rle_trans.
apply HNu; eapply le_trans; [apply Max.le_max_l|eexact Hn].
apply Rmult_le_compat_r; [apply Rabs_pos|apply Rmin_r].
eapply Rle_trans.
apply HNv; eapply le_trans; [apply Max.le_max_r|eexact Hn].
replace (Vn n) with ((Vn n - Un n) + Un n)%R by field.
eapply Rle_trans.
apply Rmult_le_compat_l; [lra|apply Rabs_triang].
rewrite Rmult_plus_distr_l.
apply Rplus_le_compat.
eapply Rle_trans.
apply Rmult_le_compat_l; [left; assumption|].
rewrite Rabs_minus_sym.
apply HNu; eapply le_trans; [apply Max.le_max_l|eexact Hn].
rewrite <- Rmult_assoc; apply Rmult_le_compat_r; [apply Rabs_pos|].
eapply Rle_trans; [eexact Heps2|apply Rmin_r].
apply Rmult_le_compat_r; [apply Rabs_pos|apply Rmin_r].
Qed.

(**********)
Instance Rseq_equiv_Equivalence : Equivalence Rseq_equiv.
Proof.
split.
  exact Rseq_equiv_refl.
  exact Rseq_equiv_sym.
  exact Rseq_equiv_trans.
Qed.

(** Big-O contains little-O and equivalence. *)

(**********)
Lemma Rseq_little_O_big_O_incl : forall Un Vn, Un = o(Vn) -> Un = O(Vn).
Proof.
intros Un Vn H.
destruct (H 1) as [N HN]; [lra|].
exists 1; split; [lra|].
exists N; intros n Hn.
apply HN; assumption.
Qed.

(**********)
Lemma Rseq_equiv_big_O_incl : forall Un Vn, Un ~ Vn -> Un = O(Vn).
Proof.
intros Un Vn H.
apply Rseq_equiv_sym in H.
destruct (H 1) as [N HN]; [lra|].
exists 2; split; [lra|].
exists N; intros n Hn.
replace (Un n) with (Un n - Vn n + Vn n)%R by field.
eapply Rle_trans; [apply Rabs_triang|].
change 2 with (1 + 1)%R.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat; [|rewrite Rmult_1_l; apply Rle_refl].
rewrite Rabs_minus_sym; apply HN; assumption.
Qed.

(** Compatibility of relations. *)

(**********)
Lemma Rseq_big_O_little_O_trans : forall Un Vn Wn, Un = O(Vn) -> Vn = o(Wn) -> Un = o(Wn).
Proof.
intros Un Vn Wn HO Ho eps Heps.
destruct HO as [M [HM [NO HNO]]].
assert (Hm : Rmax 1 M > 0).
eapply Rlt_le_trans; [apply Rlt_0_1|apply RmaxLess1].
destruct (Ho (eps * / Rmax 1 M))%R as [No HNo].
apply Rmult_lt_0_compat; [lra|].
apply Rinv_0_lt_compat; assumption.
exists (Max.max No NO); intros n Hn.
eapply Rle_trans.
apply HNO; eapply le_trans; [apply Max.le_max_r|eexact Hn].
replace eps with ((Rmax 1 M) * eps * / (Rmax 1 M))%R
  by (field; apply Rgt_not_eq; assumption).
do 2 rewrite Rmult_assoc.
apply Rmult_le_compat; [apply Rge_le; assumption|apply Rabs_pos|apply RmaxLess2|].
eapply Rle_trans.
apply HNo; eapply le_trans; [apply Max.le_max_l|eexact Hn].
rewrite Rmult_assoc; apply Rmult_le_compat_r; [|apply Rle_refl].
replace 0%R with (0 * 0)%R by field.
apply Rmult_le_compat; try apply Rle_refl.
left; apply Rinv_0_lt_compat; assumption.
apply Rabs_pos.
Qed.

(**********)
Lemma Rseq_little_O_big_O_trans : forall Un Vn Wn, Un = o(Vn) -> Vn = O(Wn) -> Un = o(Wn).
Proof.
intros Un Vn Wn Hu Hv eps Heps.
destruct Hv as [M [HM [NO HNO]]].
destruct (Hu (eps * / Rmax 1 M)%R) as [No HNo].
apply Rmult_gt_0_compat; [lra|].
apply Rinv_0_lt_compat; eapply Rlt_le_trans; [apply Rlt_0_1|apply RmaxLess1].
exists (Max.max NO No); intros n Hn.
eapply Rle_trans.
apply HNo; eapply le_trans; [apply Max.le_max_r|eexact Hn].
rewrite Rmult_assoc.
apply Rmult_le_compat_l; [lra|].
eapply Rle_trans.
apply Rmult_le_compat_l.
left; apply Rinv_0_lt_compat.
eapply Rlt_le_trans; [apply Rlt_0_1|apply RmaxLess1].
apply HNO; eapply le_trans; [apply Max.le_max_l|eexact Hn].
rewrite <- Rmult_assoc.
rewrite <- Rmult_1_l; apply Rmult_le_compat_r; [apply Rabs_pos|].
pattern 1 at 2; rewrite <- (Rinv_l (Rmax 1 M)).
apply Rmult_le_compat_l.
left; apply Rinv_0_lt_compat; eapply Rlt_le_trans; [apply Rlt_0_1|apply RmaxLess1].
apply RmaxLess2.
apply Rgt_not_eq.
eapply Rlt_le_trans; [apply Rlt_0_1|apply RmaxLess1].
Qed.

(**********)
Lemma Rseq_equiv_big_O_compat_l : forall Un Vn Wn, Un ~ Vn -> Un = O(Wn) -> Vn = O(Wn).
Proof.
intros Un Vn Wn He HO.
destruct HO as [M [HM [NO HNO]]].
destruct (He 1) as [Ne HNe]; [lra|].
exists (2 * M)%R; split; [lra|].
exists (Max.max Ne NO); intros n Hn.
replace (Vn n) with (Vn n - Un n + Un n)%R by field.
eapply Rle_trans; [apply Rabs_triang|].
change 2 with (1 + 1)%R.
rewrite Rmult_assoc; rewrite Rmult_plus_distr_r.
apply Rplus_le_compat; rewrite Rmult_1_l.
rewrite Rabs_minus_sym.
eapply Rle_trans.
apply HNe; eapply le_trans; [apply Max.le_max_l|eexact Hn].
rewrite Rmult_1_l.
apply HNO; eapply le_trans; [apply Max.le_max_r|eexact Hn].
apply HNO; eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

(**********)
Lemma Rseq_equiv_big_O_compat_r : forall Un Vn Wn, Un ~ Vn -> Wn = O(Un) -> Wn = O(Vn).
Proof.
intros Un Vn Wn He HO.
apply Rseq_equiv_sym in He.
destruct HO as [M [HM [NO HNO]]].
destruct (He 1) as [Ne HNe]; [lra|].
exists (M * 2)%R; split; [lra|].
exists (Max.max Ne NO); intros n Hn.
eapply Rle_trans.
apply HNO; eapply le_trans; [apply Max.le_max_r|eexact Hn].
rewrite Rmult_assoc.
apply Rmult_le_compat_l; [lra|].
replace (Un n) with (Un n - Vn n + Vn n)%R by field.
eapply Rle_trans; [apply Rabs_triang|].
change 2 with (1 + 1)%R.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat.
rewrite Rabs_minus_sym.
apply HNe; eapply le_trans; [apply Max.le_max_l|eexact Hn].
rewrite Rmult_1_l; apply Rle_refl.
Qed.

(**********)
Lemma Rseq_equiv_little_O_compat_l : forall Un Vn Wn, Un ~ Vn -> Un = o(Wn) -> Vn = o(Wn).
Proof.
intros Un Vn Wn He Ho eps Heps.
pose (eps' := Rmin 1 eps).
assert (Heps' : eps' > 0).
unfold eps'; unfold Rmin; destruct Rle_dec; lra.
destruct (He (eps' / 2)%R) as [Ne HNe]; [lra|].
destruct (Ho (eps' / 2)%R) as [No HNo]; [lra|].
exists (Max.max Ne No); intros n Hn.
replace (Vn n) with (Vn n - Un n + Un n)%R by field.
replace eps with (eps / 2 + eps / 2)%R by field.
eapply Rle_trans; [apply Rabs_triang|].
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat.
rewrite Rabs_minus_sym.
eapply Rle_trans.
apply HNe; eapply le_trans; [apply Max.le_max_l|eexact Hn].
eapply Rle_trans with (eps / 2 * Rabs (Un n))%R.
apply Rmult_le_compat_r; [apply Rabs_pos|].
unfold eps'; unfold Rmin; destruct Rle_dec; lra.
apply Rmult_le_compat_l; [lra|].
eapply Rle_trans.
apply HNo; eapply le_trans; [apply Max.le_max_r|eexact Hn].
rewrite <- Rmult_1_l.
apply Rmult_le_compat_r; [apply Rabs_pos|].
rewrite <- Rmult_1_l.
apply Rmult_le_compat; try lra; apply Rmin_l.
eapply Rle_trans.
apply HNo; eapply le_trans; [apply Max.le_max_r|eexact Hn].
apply Rmult_le_compat_r; [apply Rabs_pos|].
apply Rmult_le_compat_r; [lra|apply Rmin_r].
Qed.

(**********)
Lemma Rseq_equiv_little_O_compat_r : forall Un Vn Wn, Un ~ Vn -> Wn = o(Un) -> Wn = o(Vn).
intros Un Vn Wn He Ho eps Heps.
apply Rseq_equiv_sym in He.
pose (eps1 := (eps / (2 + eps))%R).
pose (eps2 := (eps / 2)%R).
assert (Heps1 : eps1 > 0).
unfold eps1; unfold Rdiv; apply Rmult_lt_0_compat;
[|apply Rinv_0_lt_compat]; lra.
assert (Heps2 : eps2 > 0).
unfold eps2; lra.
destruct (Ho eps1) as [No HNo]; [assumption|].
destruct (He eps2) as [Ne HNe]; [assumption|].
exists (Max.max No Ne); intros n Hn.
eapply Rle_trans.
apply HNo; eapply le_trans; [apply Max.le_max_l|eexact Hn].
unfold eps1; unfold Rdiv.
rewrite Rmult_assoc; apply Rmult_le_compat_l; [lra|].
rewrite <- Rmult_1_l.
pattern 1 at 1.
replace 1%R with (/ (2 + eps) * (2 + eps))%R
  by (field; apply Rgt_not_eq; lra).
rewrite Rmult_assoc; apply Rmult_le_compat_l.
left; apply Rinv_0_lt_compat; lra.
replace (Un n) with (Un n - Vn n + Vn n)%R by field.
replace (2 + eps)%R with (eps + 1 + 1)%R by field.
eapply Rle_trans; [apply Rabs_triang|].
rewrite Rmult_plus_distr_r; rewrite Rmult_1_l.
apply Rplus_le_compat_r.
rewrite Rabs_minus_sym.
eapply Rle_trans.
apply HNe; eapply le_trans; [apply Max.le_max_r|eexact Hn].
apply Rmult_le_compat_r; [apply Rabs_pos|].
unfold eps2; lra.
Qed.

(** * Big-O and common operations. *)

Section Rseq_big_O_compat.

Variable Un Vn Wn Xn : nat -> R.
Variable r : R.

(** Scalar compatibility. *)

(**********)
Lemma Rseq_big_O_Rmult_compat_l : Un = O(Vn) -> (r * Un) = O(Vn).
Proof.
intros Hu.
destruct Hu as [M [HM [N HN]]].
exists (Rabs r * M)%R; split.
rewrite <- (Rmult_0_l 0).
apply Rmult_ge_compat; apply Rle_refl || (apply Rle_ge; apply Rabs_pos) || assumption.
exists N; intros n Hn.
unfold Rseq_mult.
rewrite Rabs_mult; rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply HN; assumption.
Qed.

(**********)
Lemma Rseq_big_O_Rmult_compat_r : Un = O(Vn) -> r <> 0 -> Un = O(r * Vn).
Proof.
intros Hu Hr.
destruct Hu as [M [HM [N HN]]].
exists (/ Rabs r * M)%R; split.
rewrite <- (Rmult_0_l 0).
apply Rmult_ge_compat; apply Rle_refl || assumption || idtac.
left; apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption.
exists N; intros n Hn.
unfold Rseq_mult; rewrite Rabs_mult.
change (r n) with r.
field_simplify; [|apply Rabs_no_R0; assumption].
unfold Rdiv; repeat rewrite Rinv_1; repeat rewrite Rmult_1_r.
apply HN; assumption.
Qed.

(** Additive compatibility. *)

(**********)
Lemma Rseq_big_O_plus_compat_l : Un = O(Wn) -> Vn = O(Wn) -> (Un + Vn) = O(Wn).
Proof.
intros Hu Hv.
destruct Hu as [Mu [HMu [Nu Hu]]].
destruct Hv as [Mv [HMv [Nv Hv]]].
exists (Mu + Mv)%R; split; [lra|].
exists (Max.max Nu Nv).
intros n Hn.
unfold Rseq_plus.
eapply Rle_trans; [apply Rabs_triang|].
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat.
apply (Hu n); eapply le_trans; [apply Max.le_max_l|eexact Hn].
apply (Hv n); eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

(** Multiplicative compatibility. *)

(**********)
Lemma Rseq_big_O_opp_compat_l : Un = O(Vn) -> - Un = O(Vn).
intros H.
destruct H as [M [HM [N H]]]. 
exists M; split; [exact HM|].
exists N; intros n Hn.
unfold Rseq_opp; rewrite Rabs_Ropp.
apply (H n); apply Hn.
Qed.

(**********)
Lemma Rseq_big_O_opp_compat_r : Un = O(Vn) -> Un = O(- Vn).
intros H.
destruct H as [M [HM [N H]]]. 
exists M; split; [exact HM|].
exists N; intros n Hn.
unfold Rseq_opp; rewrite Rabs_Ropp.
apply (H n); apply Hn.
Qed.

(**********)
Lemma Rseq_big_O_mult_compat : Un = O(Wn) -> Vn = O(Xn) -> (Un * Vn) = O(Wn * Xn).
Proof.
intros Hu Hv.
destruct Hu as [Mu [HMu [Nu Hu]]].
destruct Hv as [Mv [HMv [Nv Hv]]].
exists (Mu * Mv)%R; split.
replace 0 with (0 * 0)%R by field.
apply Rmult_ge_compat; auto with real.
exists (Max.max Nu Nv).
intros n Hn.
unfold Rseq_mult.
do 2 (rewrite Rabs_mult).
replace (Mu * Mv * (Rabs (Wn n) * Rabs (Xn n)))%R
  with ((Mu * Rabs (Wn n)) * (Mv * Rabs (Xn n)))%R by field.
apply Rmult_le_compat; try (apply Rabs_pos).
apply (Hu n); eapply le_trans; [apply Max.le_max_l|eexact Hn].
apply (Hv n); eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

End Rseq_big_O_compat.

(** * Little-O and common operations. *)

Section Rseq_little_O_compat.

Variable Un Vn Wn Xn : nat -> R.
Variable r : R.

(** Scalar compatibility. *)

(**********)
Lemma Rseq_little_O_Rmult_compat_l : Un = o(Vn) -> (r * Un) = o(Vn).
Proof.
intros Hu eps Heps.
destruct (Req_dec r 0) as [He|He].
exists 0%nat; intros n Hn.
unfold Rseq_mult; rewrite He.
rewrite Rmult_0_l; rewrite Rabs_R0.
rewrite <- (Rmult_0_l 0).
apply Rmult_le_compat;
(apply Rle_refl || lra || apply Rabs_pos).
destruct (Hu (eps * / Rabs r)%R) as [N HN].
apply Rmult_gt_0_compat; [|apply Rinv_0_lt_compat; apply Rabs_pos_lt];
assumption.
exists N; intros n Hn.
unfold Rseq_mult; rewrite Rabs_mult.
eapply Rle_trans.
apply Rmult_le_compat_l; [apply Rabs_pos|].
apply HN; assumption.
change (r n) with r.
right; field; apply Rabs_no_R0; assumption.
Qed.

(**********)
Lemma Rseq_little_O_Rmult_compat_r : Un = o(Vn) -> r <> 0 -> Un = o(r * Vn).
Proof.
intros Hu Hr eps Heps.
destruct (Hu (eps * Rabs r)%R) as [N HN].
apply Rmult_gt_0_compat; [|apply Rabs_pos_lt]; assumption.
exists N; intros n Hn.
unfold Rseq_mult; rewrite Rabs_mult.
rewrite <- Rmult_assoc.
apply HN; assumption.
Qed.

(** Additive compatibility. *)

(**********)
Lemma Rseq_little_O_plus_compat_l : Un = o(Wn) -> Vn = o(Wn) -> (Un + Vn) = o(Wn).
Proof.
intros Hu Hv.
intros eps Heps.
destruct (Hu (eps/2)%R) as [Nu HNu]; [lra|].
destruct (Hv (eps/2)%R) as [Nv HNv]; [lra|].
exists (Max.max Nu Nv).
intros n Hn.
unfold Rseq_plus.
eapply Rle_trans; [apply Rabs_triang|].
replace eps with (eps / 2 + eps / 2)%R by field.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat.
apply (HNu n); eapply le_trans; [apply Max.le_max_l|eexact Hn].
apply (HNv n); eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

(** Multiplicative compatibility. *)

(**********)
Lemma Rseq_little_O_opp_compat_l : Un = o(Vn) -> - Un = o(Vn).
Proof.
intros H eps Heps.
destruct (H eps) as [N HN]; [assumption|].
exists N; intros n Hn.
unfold Rseq_opp.
rewrite Rabs_Ropp.
apply HN; assumption.
Qed.

(**********)
Lemma Rseq_little_O_opp_compat_r : Un = o(Vn) -> Un = o(- Vn).
Proof.
intros H eps Heps.
destruct (H eps) as [N HN]; [assumption|].
exists N; intros n Hn.
unfold Rseq_opp.
rewrite Rabs_Ropp.
apply HN; assumption.
Qed.

(**********)
Lemma Rseq_little_O_mult_compat : Un = o(Wn) -> Vn = o(Xn) -> (Un * Vn) = o(Wn * Xn).
Proof.
intros Hu Hv eps Heps.
destruct (Hu (sqrt eps)) as [Nu HNu];
[apply sqrt_lt_R0; assumption|].
destruct (Hv (sqrt eps)) as [Nv HNv];
[apply sqrt_lt_R0; assumption|].
exists (Max.max Nu Nv); intros n Hn.
unfold Rseq_mult.
repeat rewrite Rabs_mult.
rewrite <- (sqrt_def eps); [|left; assumption].
replace (sqrt eps * sqrt eps * (Rabs (Wn n) * Rabs (Xn n)))%R
  with ((sqrt eps * Rabs (Wn n)) * (sqrt eps * Rabs (Xn n)))%R by field.
apply Rmult_le_compat; try apply Rabs_pos.
apply (HNu n); eapply le_trans; [apply Max.le_max_l|eexact Hn].
apply (HNv n); eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

(** Inverse contravariance. *)

(**********)
Lemma Rseq_little_O_inv_contravar : Un = o(Vn) -> Rseq_neq_0 Un -> Rseq_neq_0 Vn -> (/ Vn) = o(/ Un).
Proof.
intros Hu Hnu Hnv.
intros eps Heps.
destruct (Hu eps) as [N HN]; [assumption|].
exists N; intros n Hn.
unfold Rseq_inv.
rewrite Rabs_Rinv; [|apply Hnv].
rewrite Rabs_Rinv; [|apply Hnu].
apply (Rmult_le_reg_l (Rabs (Un n))); [apply Rabs_pos_lt; apply Hnu|].
apply (Rmult_le_reg_l (Rabs (Vn n))); [apply Rabs_pos_lt; apply Hnv|].
field_simplify.
try (unfold Rdiv; rewrite Rinv_1; repeat rewrite Rmult_1_r).
rewrite Rmult_comm; apply HN; apply Hn.
apply Rabs_no_R0; apply Hnu.
apply Rabs_no_R0; apply Hnv.
Qed.

End Rseq_little_O_compat.

(** * Equivalence and common operations. *)

Section Rseq_equiv_compat.

Variable Un Vn Wn Xn En : nat -> R.
Variable r : R.

(** Scalar compatibility. *)

(**********)
Lemma Rseq_equiv_Rmult_compat : Un ~ Vn -> (r * Un) ~ (r * Vn).
Proof.
intros Hu eps Heps.
unfold Rseq_mult; unfold Rseq_minus.
destruct (Req_dec r 0) as [He|He].
exists 0%nat; intros n Hn.
rewrite He; rewrite <- Rmult_minus_distr_l.
do 2 rewrite Rabs_mult.
change ((IZR 0) n) with (IZR 0); rewrite Rabs_R0.
right; field.
destruct (Hu eps) as [N HN]; [assumption|].
exists N; intros n Hn.
rewrite <- Rmult_minus_distr_l.
do 2 rewrite Rabs_mult.
rewrite <- Rmult_assoc.
pattern (eps * Rabs (r n))%R; rewrite Rmult_comm.
rewrite -> Rmult_assoc.
apply Rmult_le_compat_l; [apply Rabs_pos|].
apply HN; assumption.
Qed.

(**********)
Lemma Rseq_equiv_opp_compat : Un ~ Vn -> (- Un) ~ (- Vn).
Proof.
intros Hu eps Heps.
destruct (Hu eps) as [N HN]; [assumption|].
exists N; intros n Hn.
unfold Rseq_minus; unfold Rseq_opp.
unfold Rminus; rewrite <- Ropp_plus_distr.
repeat rewrite Rabs_Ropp.
apply HN; assumption.
Qed.

(** Multiplicative compatibility. *)

(**********)
Lemma Rseq_equiv_mult_compat : Un ~ Wn -> Vn ~ Xn -> (Un * Vn) ~ (Wn * Xn).
Proof.
intros Hu Hv eps Heps.
pose (eps1 := (eps / 2)%R).
pose (eps2 := (eps / (eps + 2))%R).
assert (Heps1 : eps1 > 0).
unfold eps1; lra.
assert (Heps2 : eps2 > 0).
unfold eps2; unfold Rdiv.
apply Rmult_gt_0_compat; [assumption|].
apply Rinv_0_lt_compat; lra.
destruct (Hu eps1) as [Nu HNu]; [assumption|].
destruct (Hv eps2) as [Nv HNv]; [assumption|].
exists (Max.max Nu Nv); intros n Hn.
unfold Rseq_minus; unfold Rseq_mult.
replace (Un n * Vn n - Wn n * Xn n)%R
  with ((Un n * Vn n - Wn n * Vn n) + (Wn n * Vn n - Wn n * Xn n))%R
  by ring.
replace (eps * Rabs (Un n * Vn n))%R
  with (eps / 2 * Rabs (Un n * Vn n) + eps / 2 * Rabs (Un n * Vn n))%R
  by field.
eapply Rle_trans; [apply Rabs_triang|].
apply Rplus_le_compat.
replace (Un n * Vn n - Wn n * Vn n)%R
  with ((Un n - Wn n) * Vn n)%R by ring.
repeat rewrite Rabs_mult; rewrite <- Rmult_assoc.
apply Rmult_le_compat_r; [apply Rabs_pos|].
apply HNu; eapply le_trans; [apply Max.le_max_l|eexact Hn].
replace (Wn n * Vn n - Wn n * Xn n)%R
  with (Wn n * (Vn n - Xn n))%R by field.
repeat rewrite Rabs_mult.
replace (eps / 2)%R with (eps2 * (eps1 + 1))%R
  by (unfold eps1; unfold eps2; field; apply Rgt_not_eq; lra).
replace (eps2 * (eps1 + 1) * (Rabs (Un n) * Rabs (Vn n)))%R
  with ((eps1 * Rabs (Un n) + Rabs (Un n)) * ((eps2 * Rabs (Vn n))))%R
  by field.
apply Rmult_le_compat; try apply Rabs_pos.
replace (Wn n) with ((Wn n - Un n) + Un n)%R by field.
eapply Rle_trans; [apply Rabs_triang|].
apply Rplus_le_compat_r; rewrite Rabs_minus_sym.
apply HNu; eapply le_trans; [apply Max.le_max_l|eexact Hn].
apply HNv; eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

(** Addition and little-O. *)

(**********)
Lemma Rseq_equiv_plus_little_O_compat_l : Un ~ Wn -> En = o(Un) -> (Un + En) ~ Wn.
Proof.
intros Hu Ho.
apply Rseq_equiv_sym; apply Rseq_equiv_sym in Hu.
intros eps Heps.
assert (Hpos : (eps * / (2 + eps) > 0)%R).
apply Rmult_lt_0_compat; [lra|].
apply Rinv_0_lt_compat; lra.
destruct (Hu (eps / 2)%R) as [N HN]; [lra|].
destruct (Ho (eps * / (2 + eps))%R) as [No HNo]; [assumption|].
exists (Max.max N No); intros n Hn.
unfold Rseq_plus; unfold Rseq_minus.
replace (Wn n - (Un n + En n))%R
  with (Wn n + - Un n + - En n)%R by field.
replace eps with (eps / 2 + eps / 2)%R by field.
eapply Rle_trans; [apply Rabs_triang|].
rewrite Rmult_plus_distr_r; apply Rplus_le_compat.
apply HN; eapply le_trans; [apply Max.le_max_l|eexact Hn].
rewrite Rabs_Ropp.
eapply Rle_trans.
apply HNo; eapply le_trans; [apply Max.le_max_r|eexact Hn].
replace (Un n) with (Un n - Wn n + Wn n)%R by field.
eapply Rle_trans.
apply Rmult_le_compat_l; [left; assumption|apply Rabs_triang].
eapply Rle_trans.
apply Rmult_le_compat_l; [left; assumption|].
apply Rplus_le_compat_r.
rewrite Rabs_minus_sym.
apply HN; eapply le_trans; [apply Max.le_max_l|eexact Hn].
right; field; apply Rgt_not_eq; lra.
Qed.

End Rseq_equiv_compat.

(** * Convergence and little-O. *)

Section Rseq_little_O_cv.

Variable Un Vn : nat -> R.
Variable l : R.
Hypothesis Ho : Un = o(Vn).

(**********)
Lemma Rseq_little_O_cv : Rseq_cv Vn l -> Rseq_cv Un 0.
Proof.
intros H eps Heps.
assert (Hpos : / (1 + Rabs l) > 0).
apply Rinv_0_lt_compat.
eapply Rlt_le_trans with (r2 := 1); [lra|].
pattern 1 at 1; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l; apply Rabs_pos.
destruct (H 1) as [Ncv HNcv]; [lra|].
destruct (Ho (/ (1 + Rabs l) * eps))%R as [No HNo].
apply Rmult_gt_0_compat; assumption.
exists (Max.max Ncv No).
intros n Hn.
unfold R_dist; rewrite Rminus_0_r.
eapply Rle_lt_trans; [apply HNo|].
eapply le_trans; [apply Max.le_max_r|eexact Hn].
rewrite Rmult_comm; rewrite <- Rmult_assoc.
rewrite <- Rmult_1_l; apply Rmult_lt_compat_r; [assumption|].
eapply Rlt_le_trans.
apply Rmult_lt_compat_r; [assumption|].
replace (Vn n) with (Vn n - l + l)%R by field.
eapply Rle_lt_trans.
apply Rabs_triang.
apply Rplus_lt_compat_r.
apply HNcv; eapply le_trans; [apply Max.le_max_l|eexact Hn].
right; apply Rinv_r; apply Rgt_not_eq.
eapply Rlt_le_trans with (r2 := 1); [lra|].
pattern 1 at 1; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l; apply Rabs_pos.
Qed.

(**********)
Lemma Rseq_little_O_cv_pos_infty :
  Rseq_cv_pos_infty Un -> Rseq_cv_pos_infty (|Vn|).
Proof.
intros H M.
destruct (H M) as [N HN].
destruct (Ho 1) as [No HNo]; [lra|].
exists (Max.max N No); intros n Hn.
eapply Rlt_le_trans.
apply (HN n); eapply le_trans; [apply Max.le_max_l|eexact Hn].
rewrite <- Rmult_1_l.
apply Rle_trans with (Rabs (Un n)).
unfold Rabs; repeat destruct Rcase_abs; lra.
apply HNo; eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

End Rseq_little_O_cv.

(** * Divergence and little-O. *)

Section Rseq_little_O_pos_infty.

Variable Un Vn : nat -> R.
Variable l : R.

(**********)
Lemma Rseq_cv_little_O_cv_pos_infty : (Rseq_cv Un l) -> (Rseq_cv_pos_infty Vn) -> Un = o(Vn).
Proof.
intros Un_cv Vn_cv_pos_infty eps epspos.
destruct (Rseq_cv_bound Un l Un_cv) as [M [Mpos Mbound]].
destruct (Vn_cv_pos_infty (M/eps)%R) as [N Vnlowerbound].
exists N.
intros n HnN.
apply Rle_trans with M.
 apply Mbound.
 
 apply Rlt_le.
 assert (REW : (M = eps * (M / eps))%R).
  field.
  intro zero; subst; apply (Rlt_irrefl _ epspos).
 
 rewrite REW.
 apply Rmult_lt_compat_l; [assumption|].
 apply Rlt_le_trans with (Vn n).
 apply (Vnlowerbound _ HnN).
 apply RRle_abs.
Qed.

End Rseq_little_O_pos_infty.

(** * Convergence and equivalence. *)

Section Rseq_equiv_cv.

(**********)
Instance Rseq_equiv_cv_compat : Proper (Rseq_equiv ==> @eq R ==> iff) Rseq_cv.
Proof.
assert (Hcompat : forall Un Vn l, Un ~ Vn -> Rseq_cv Un l -> Rseq_cv Vn l).
  intros Un Vn l Heq H eps Heps.
  destruct (Rseq_cv_bound Un l H) as [M [HM Hb]].
  destruct (H (eps / 2))%R as [Ncv HNcv]; [lra|].
  destruct (Heq (eps / 2 * /(M + 1)))%R as [Neq HNeq].
  repeat apply Rmult_gt_0_compat; try (assumption || lra).
  apply Rinv_0_lt_compat; lra.
  exists (Max.max Ncv Neq); intros n Hn.
  unfold R_dist.
  replace (Vn n - l)%R
    with ((Vn n - Un n) + (Un n - l))%R by field. 
  eapply Rle_lt_trans; [apply Rabs_triang|].
  replace eps with (eps / 2 + eps / 2)%R by field.
  apply Rplus_lt_compat.
  rewrite Rabs_minus_sym.
  eapply Rle_lt_trans.
  apply HNeq; eapply le_trans; [apply Max.le_max_r|eexact Hn].
  rewrite <- Rmult_1_r; rewrite Rmult_assoc.
  apply Rmult_lt_compat_l; [lra|].
  apply Rmult_lt_reg_l with (r := (M + 1)%R); [lra|].
  rewrite <- Rmult_assoc; rewrite Rmult_1_r.
  rewrite Rinv_r; [|apply Rgt_not_eq; lra].
  rewrite Rmult_1_l.
  pattern (Rabs (Un n)); rewrite <- Rplus_0_r.
  apply Rplus_le_lt_compat; [apply Hb|lra].
  apply HNcv; eapply le_trans; [apply Max.le_max_l|eexact Hn].
intros Un Vn Heq l l' Hl; subst l'.
split; apply Hcompat; auto; symmetry; auto.
Qed.

Variable Un Vn : nat -> R.
Variable l : R.
Hypothesis Heq : Un ~ Vn.

(**********)
Lemma Rseq_equiv_cv_pos_infty_compat : Rseq_cv_pos_infty Un -> Rseq_cv_pos_infty Vn.
Proof.
intros H M.
pose (Mp := Rmax 1 M).
destruct (Heq (/2)%R) as [N HN]; [lra|].
destruct (H (2 * Mp)%R) as [Nm HNm].
exists (Max.max N Nm); intros n Hn.
assert (HMp : 0 < Mp).
eapply Rlt_le_trans with 1%R; [lra|apply RmaxLess1].
assert (Hpos : 0 < Un n).
eapply Rlt_trans with (2 * Mp)%R.
apply Rmult_gt_0_compat; [lra|assumption].
apply HNm; eapply le_trans; [apply Max.le_max_r|eexact Hn].
assert (Hq : Rabs (Un n - Vn n) <= /2 * Rabs (Un n)).
apply HN; eapply le_trans; [apply Max.le_max_l|eexact Hn].
assert (Hp : /2 * Rabs (Un n) <= Rabs (Vn n)).
replace (/2)%R with (1 + - /2)%R by field.
replace (Vn n)%R with (Un n - (Un n - Vn n))%R by field.
rewrite Rmult_plus_distr_r; rewrite Rmult_1_l.
eapply Rle_trans; [|apply Rabs_triang_inv].
apply Rplus_le_compat_l ; rewrite Ropp_mult_distr_l_reverse.
apply Ropp_ge_le_contravar; apply Rle_ge; assumption.
assert (Hm : Vn n  >= /2 * Un n).
unfold Rabs in Hq; repeat destruct Rcase_abs in Hq; lra.
apply Rle_lt_trans with Mp; [apply RmaxLess2|].
apply Rlt_le_trans with (/ 2 * Un n)%R.
apply Rmult_lt_reg_l with 2%R; [lra|].
rewrite <- Rmult_assoc.
rewrite Rinv_r; [|apply Rgt_not_eq; lra].
rewrite Rmult_1_l.
apply HNm; eapply le_trans; [apply Max.le_max_r|eexact Hn].
apply Rge_le; assumption.
Qed.

(**********)
Lemma Rseq_equiv_cv_neg_infty_compat : Rseq_cv_neg_infty Un -> Rseq_cv_neg_infty Vn.
Proof.
intros H M.
pose (Mp := Rmin (-1) M).
destruct (Heq (/2)%R) as [N HN]; [lra|].
destruct (H (2 * Mp)%R) as [Nm HNm].
exists (Max.max N Nm); intros n Hn.
assert (HMp : Mp < 0).
eapply Rle_lt_trans with (-1)%R; [apply Rmin_l|lra].
assert (Hpos : Un n < 0).
eapply Rlt_trans with (2 * Mp)%R; [|lra].
apply HNm; eapply le_trans; [apply Max.le_max_r|eexact Hn].
assert (Hq : Rabs (Un n - Vn n) <= /2 * Rabs (Un n)).
apply HN; eapply le_trans; [apply Max.le_max_l|eexact Hn].
assert (Hp : /2 * Rabs (Un n) <= Rabs (Vn n)).
replace (/2)%R with (1 + - /2)%R by field.
replace (Vn n)%R with (Un n - (Un n - Vn n))%R by field.
rewrite Rmult_plus_distr_r; rewrite Rmult_1_l.
eapply Rle_trans; [|apply Rabs_triang_inv].
apply Rplus_le_compat_l ; rewrite Ropp_mult_distr_l_reverse.
apply Ropp_ge_le_contravar; apply Rle_ge; assumption.
assert (Hm : Vn n <= /2 * Un n).
unfold Rabs in Hq; repeat destruct Rcase_abs in Hq;
try rewrite Ropp_mult_distr_r_reverse in Hq; lra.
apply Rlt_le_trans with Mp; [|apply Rmin_r].
apply Rle_lt_trans with (/ 2 * Un n)%R; [assumption|].
apply Rmult_lt_reg_l with 2%R; [lra|].
rewrite <- Rmult_assoc.
rewrite Rinv_r; [|apply Rgt_not_eq; lra].
rewrite Rmult_1_l.
apply HNm; eapply le_trans; [apply Max.le_max_r|eexact Hn].
Qed.

(**********)
Lemma Rseq_equiv_cv_div : (forall n, Vn n <> 0) -> Rseq_cv (Un / Vn) 1.
Proof.
intros Hv eps Heps.
apply Rseq_equiv_sym in Heq.
destruct (Heq (eps / 2))%R as [N HN]; [lra|].
exists N; intros n Hn.
unfold R_dist, Rseq_div.
replace (Un n / Vn n - 1)%R
  with ((Un n - Vn n) / Vn n)%R by (field; apply Hv).
unfold Rdiv.
rewrite Rabs_mult; rewrite Rabs_Rinv; [|apply Hv].
rewrite Rabs_minus_sym.
rewrite Rmult_comm.
apply (Rmult_lt_reg_l (Rabs (Vn n))).
  apply Rabs_pos_lt; apply Hv.
rewrite <- Rmult_assoc.
rewrite Rinv_r; [|apply Rabs_no_R0; apply Hv].
rewrite Rmult_1_l.
eapply Rle_lt_trans.
  apply HN; exact Hn.
  rewrite Rmult_comm.
  apply Rmult_lt_compat_l.
    apply Rabs_pos_lt; apply Hv.
    lra.
Qed.

End Rseq_equiv_cv.

(**********)
Lemma Rseq_equiv_cv_constant : forall Un l,
  Un ~ (Rseq_constant l) -> Rseq_cv Un l.
Proof.
intros Un l H.
apply Rseq_equiv_sym in H.
assert(Rseq_cv (Un - l) 0).
apply Rseq_little_O_cv with (Vn := l) (l := l).
intros eps Heps.
destruct (H eps Heps) as [N HN].
exists N.
intros n Hn; unfold Rseq_minus, Rseq_constant.
replace (Un n - l)%R with (-(l - Un n))%R by ring.
rewrite Rabs_Ropp.
apply HN; assumption.
apply Rseq_constant_cv.
replace l with (0 + l)%R by ring.
apply Rseq_cv_eq_compat with ((Un - l) + l).
intro n; unfold Rseq_minus, Rseq_constant, Rseq_plus; ring.
auto with Rseq.
Qed.

(**********)
Lemma Rseq_cv_equiv_constant : forall Un l,
  l <> 0 -> Rseq_cv Un l -> Un ~ (Rseq_constant l).
Proof.
intros Un l Hl H.
apply Rseq_equiv_sym.
intros eps Heps.
assert(Hpos : 0 < eps* Rabs l).
  pose proof (Rabs_pos_lt l Hl).
  apply Rmult_lt_0_compat; assumption. 
destruct (H (eps * (Rabs l))%R Hpos) as [N HN].
exists N.
intros n Hn.
unfold Rseq_minus, Rseq_constant.
replace (l - Un n)%R with (- (Un n - l))%R by ring.
rewrite Rabs_Ropp.
left; apply HN; assumption.
Qed.

(**********)
Lemma Rseq_equiv_1 : forall Un Vn, (forall n, Vn n <> 0) -> (Rseq_div Un  Vn) ~ 1 -> Un ~ Vn.
Proof.
intros Un Vn Hneq H.
apply Rseq_equiv_sym in H.
apply Rseq_equiv_sym.
intros eps Heps.
destruct (H eps Heps) as [N HN].
exists N.
intros n Hn.
unfold Rseq_minus, Rseq_div, Rseq_constant in *.
replace (eps * Rabs (IZR 1))%R with eps in HN by (rewrite Rabs_R1; ring).
replace (Vn n - Un n)%R with ((1 - Un n / Vn n)* (Vn n))%R by (field; trivial).
rewrite Rabs_mult.
apply Rmult_le_compat_r.
  apply Rabs_pos.
  apply HN; assumption.
Qed.

(**********)
Lemma Rseq_equiv_inv_compat : forall Un Vn, 
  {m | forall n, (n >= m)%nat -> Un n <> 0} -> 
  {m | forall n, (n >= m)%nat -> Vn n <> 0} -> 
  Un ~ Vn -> (Rseq_inv Un) ~ (Rseq_inv Vn).
Proof.
intros Un Vn Upos Vpos H eps Heps.
apply Rseq_equiv_sym in H.
destruct (H eps Heps) as [N HN].
destruct Upos as (m1, Upos).
destruct Vpos as (m2, Vpos).
exists (max (max N m1) m2); intros n Hn.
unfold Rseq_minus, Rseq_inv in *.
assert (Hm1 : (n >= m1)%nat).
 apply le_trans with (max (max N m1) m2). apply le_trans with (max N m1). intuition. intuition. intuition.
assert (Hm2 : (n >= m2)%nat).
 apply le_trans with (max (max N m1) m2). intuition. intuition.
assert (HN1 : (n >= N)%nat).
 apply le_trans with (max (max N m1) m2). apply le_trans with (max N m1). intuition. intuition. intuition.
replace (/ Un n - / Vn n)%R with ((Vn n - Un n) */ (Un n * Vn n))%R by (field; auto).
rewrite Rabs_mult.
replace (Rabs (/Un n))%R with (Rabs (Vn n) * (Rabs (/ (Un n * Vn n))))%R.
  rewrite <- Rmult_assoc.
  apply Rmult_le_compat_r.
  apply Rabs_pos.
  auto.
rewrite <- Rabs_mult.
replace (Vn n * / (Un n * Vn n))%R with (/ Un n)%R by (field; auto);
  reflexivity.
Qed.
