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

(** Properties of real series *)

Require Export Reals.
Require Export Rsequence.
Require Export Rseries_def.
Require Import Rsequence_facts.
Require Export Rsequence_subsequence.
Require Import Fourier.
Require Import Max.
Open Scope R_scope.
Open Scope Rseq_scope.
(** printing ~	~ *)
(** Uniqueness of the limit. *)

Lemma Rser_cv_unique : forall Un lu1 lu2, Rser_cv Un lu1 -> Rser_cv Un lu2 -> lu1 = lu2.
Proof.
intros Un lu1 lu2 H H'.
apply Rseq_cv_unique with (sum_f_R0 Un); assumption.
Qed.
(* begin hide *)
(*TODO*)
(* simplification lemma : to put at the right place *)
Lemma Rplus_le_simpl_l : forall a b, 0<= b -> a <= a+b.
Proof.
intros a b Hb.
replace a with (a+ 0)%R by intuition ; rewrite Rplus_0_r at 2.
apply Rplus_le_compat_l.
exact Hb.
Qed.

Lemma Rplus_le_simpl_r : forall a b, 0<= b -> a <= b+a.
Proof.
intros a b Hb.
replace a with (0+a)%R by intuition ; rewrite Rplus_0_l at 2.
apply Rplus_le_compat_r.
exact Hb.
Qed.
(* end hide *)

(** * Properties about positive term series *)

Section Rser_pos_prop.

Variables Un Vn : nat -> R.
Hypothesis Un_pos : forall n : nat, 0 <= Un n.

Lemma Rser_pos_growing : Rseq_growing (sum_f_R0 Un).
intro n.
simpl.
rewrite <- (Rplus_0_r (sum_f_R0 Un n)) at 1.
apply Rplus_le_compat_l.
apply Un_pos.
Qed.

(* reciprocal : sum_incr : rename *)
(** Positive term series convergence caracterization *)

Lemma Rser_pos_bound_cv M: Rser_bound_max Un M -> { l | Rser_cv Un l }.
Proof.
intros M Hb.
destruct ub_to_lub with (sum_f_R0 Un). (*rename?*)
exists M.
intros x Hx; destruct Hx as (i, Hi); rewrite Hi.
apply Hb.
exists x.
apply tech10. (*rename*)
apply Rser_pos_growing.
exact i.
Qed.

End Rser_pos_prop.

(** * Properties using classical logic *)

Section Classical_facts.

Variables Un Vn : nat -> R.
Hypothesis Un_pos : forall n : nat, 0 <= Un n.
Hypothesis NNPP : forall p : Prop, ~ ~ p -> p.
Hypothesis classic: forall P : Prop, P \/ ~ P.

(** Positive series are either convergent or go to infinity *)

Lemma Rser_pos_cv_dec : (exists l, Rser_cv Un l) \/ (Rser_cv_pos_infty Un).
Proof.
assert((exists M, Rser_bound_max Un M) \/ ~(exists M, Rser_bound_max Un M)) as Hdec.
apply classic.
case Hdec.
intro H; left.
destruct H as [ M HM].
assert ({l : R | Rser_cv Un l}).
apply (Rser_pos_bound_cv Un Un_pos M); apply HM.
destruct H as [l Hl].
exists l; apply Hl.
intro H; right.
apply Rseq_unbounded_growing.
apply NNPP.
apply Rser_pos_growing; apply Un_pos.
apply H.
Qed.

End Classical_facts.


(** * Extensionnal equality compatibility *)

Lemma Rsum_eq_compat Un Vn : Un == Vn -> sum_f_R0 Un == sum_f_R0 Vn.
Proof.
intros Un Vn H n.
induction n; simpl; rewrite (H _); [|rewrite IHn]; reflexivity.
Qed.

Lemma Rser_cv_eq_compat Un Vn l : Un == Vn -> Rser_cv Un l -> Rser_cv Vn l.
Proof.
intros Un Vn l H n.
apply Rseq_cv_eq_compat with (sum_f_R0 Un); [apply Rsum_eq_compat | ]; assumption.
Qed.


(** * Compatibility between convergence and common operations *)

Section Rser_operations.

Lemma Rser_cv_plus_compat :
  forall Un Vn lu lv,
    Rser_cv Un lu -> Rser_cv Vn lv -> Rser_cv (Un + Vn) (lu + lv).
Proof.
intros.
unfold Rser_cv.
apply Rseq_cv_eq_compat with (sum_f_R0 Un + sum_f_R0 Vn).
unfold Rseq_eq.
unfold Rseq_plus.
intro n; rewrite sum_plus; reflexivity.
apply Rseq_cv_plus_compat.
apply H.
apply H0.
Qed.

Lemma Rser_cv_opp_compat :
  forall Un lu,
    Rser_cv Un lu -> Rser_cv (-Un) (-lu).
Proof.
intros Un lu Hu.
apply Rseq_cv_eq_compat with (- sum_f_R0 Un).
unfold Rseq_eq, Rseq_opp.
induction n.
trivial.
simpl.
ring_simplify.
rewrite IHn.
unfold Rminus.
auto with *.
apply Rseq_cv_opp_compat.
apply Hu.
Qed.

Lemma Rser_cv_minus_compat :
  forall Un Vn lu lv,
    Rser_cv Un lu -> Rser_cv Vn lv -> Rser_cv (Un - Vn) (lu - lv).
Proof.
intros.
apply Rseq_cv_eq_compat with (sum_f_R0 Un - sum_f_R0 Vn).
unfold Rseq_eq, Rseq_minus.
intro n.
rewrite <- tech11 with (Un - Vn) Un Vn n.
trivial.
trivial.
apply Rseq_cv_minus_compat.
apply H.
apply H0.
Qed.

(*Lemma Rser_cv_sig_eq_compat Un Vn : Un == Vn -> { l | Rser_cv Un l } -> { l | Rser_cv Vn l }.
Proof.
intros Un Vn E H.
destruct H as [l H]; exists l.
apply Rser_cv_eq_compat with Un; assumption.
Qed.*)

Lemma Rser_cv_scal_mult_compat :
  forall Un lu (x:R),
    Rser_cv Un lu -> Rser_cv (x * Un) (x * lu).
Proof.
intros.
apply Rseq_cv_eq_compat with (x * (sum_f_R0 Un)).
 intro n.
 unfold Rseq_mult.
 rewrite scal_sum.
 apply Rsum_eq_compat; intro; unfold Rseq_constant; ring.
 
 apply Rseq_cv_mult_compat.
  apply Rseq_constant_cv.
  assumption.
Qed.

(** If a series converges absolutely, then it converges *)

Lemma Rser_abs_cv_cv Un : {l | Rser_abs_cv Un l} -> { lu | Rser_cv Un lu}.
Proof.
unfold Rser_cv, Rser_abs_cv.
intros Un Habs.
apply (cv_cauchy_2 Un).
apply cauchy_abs.
apply cv_cauchy_1.
apply Habs.
Qed.

End Rser_operations.

Section Rser_partition.

(** If a gt-positive series converges on an extractor, then it converges *)

Lemma Rser_cv_growing_subseq_compat Un :
  forall (phi : extractor) l, 0 <= Un ->
    Rseq_cv ((sum_f_R0 Un) ⋅ phi)%Rseq l -> Rser_cv Un l.
Proof.
intros Un phi l ephi Unpos Uncv.
apply Rseq_subseq_growing_cv_compat with ((sum_f_R0 Un) ⋅ phi).
 exists phi; reflexivity.
  assumption.
 intro; apply Rplus_le_simpl_l; assumption.
Qed.

(** If a gt-positive series converges on even integers, then it converges *)

Lemma Rser_cv_growing_even_compat Un : forall l, 0 <= Un ->
  Rseq_cv (fun n => (sum_f_R0 Un (2*n))) l ->
  Rser_cv Un l.
Proof.
intros Un phi l Unpos.
assert (Hex : is_extractor (mult 2)).
  intros n; omega.
apply Rser_cv_growing_subseq_compat with (exist _ (mult 2) Hex).
 assumption.
 assumption.
Qed.

(** Finite sum of even and odd terms *)

Lemma sum_even_odd_split : forall an n,
  ((sum_f_R0 (fun i => an (2 * i)%nat) n) + 
  (sum_f_R0 (fun i => an (S (2 * i))) n) =
  (sum_f_R0 an (S (2 * n))))%R.
Proof.
intros an n.
induction n.
 reflexivity.
 
 replace (2 * S n)%nat with (S (S (2 * n))) by ring.
 do 4 rewrite tech5.
 replace (2 * S n)%nat with (S (S (2 * n))) by ring.
 rewrite <- IHn.
 ring.
Qed.

Lemma sum_even_odd_split_s : forall an n,
  ((sum_f_R0 (fun i => an (2 * i)%nat) (S n)) + 
  (sum_f_R0 (fun i => an (S (2 * i))) n) =
  (sum_f_R0 an (2 * (S n))))%R.
Proof.
intros an n.
induction n.
 simpl; field.
 
 replace (2 * (S (S n)))%nat with (S (S (S (S (2 * n))))) by ring.
 do 5 rewrite tech5.
 rewrite <- tech5.
 
 replace (2 * S n)%nat with (S (S (2 * n))) in IHn by ring.
 replace (2 * S n)%nat with (S (S (2 * n))) by ring.
 replace (2 * S (S n))%nat with (S (S (S (S (2 * n))))) by ring.
 rewrite <- IHn.
 ring.
Qed.

(** Sum of series of even and odd terms *)

Lemma Rser_even_odd_split : forall an le lo, 
  Rser_cv (fun n => an (2*n)%nat) le ->
  Rser_cv (fun n => an (S(2*n))%nat) lo ->
  Rser_cv an (le+lo).
Proof.
intros an le lo CVE CVO eps epspos.
assert (epssplit: (eps/2 > 0)%R) by fourier.
destruct (CVO (eps/2)%R epssplit) as [No Ho].
destruct (CVE (eps/2)%R epssplit) as [Ne He].
exists (mult 2 (S (plus No Ne))).
intros n nN.
destruct (even_odd_cor n) as [p [Hne|Hno]].
 rewrite Hne.
 destruct p; [ rewrite Hne in nN; simpl in nN; inversion nN | ].
 rewrite <- sum_even_odd_split_s.
 replace eps with (eps / 2 + eps / 2)%R by field.
 eapply Rle_lt_trans.
  eapply R_dist_plus.
  apply Rplus_lt_compat; [apply He|apply Ho]; omega.

 rewrite Hno.
 rewrite <- sum_even_odd_split.
 replace eps with (eps / 2 + eps / 2)%R by field.
 eapply Rle_lt_trans.
  eapply R_dist_plus.
  apply Rplus_lt_compat; [apply He|apply Ho]; omega.
Qed.

End Rser_partition.

(** * Convergence and comparisons between sequences*)

Section Rser_pos_comp.

Lemma Rser_pos_maj_cv (Un Vn : nat -> R) : 
    (forall n : nat, 0 <= Un n) -> (forall n : nat, 0 <= Vn n) ->
        Rseq_le Un Vn ->  {lv | Rser_cv Vn lv } -> {lu | Rser_cv Un lu}.
Proof.
intros Un Vn Un_pos Vn_pos Hmaj Hlv.
destruct Hlv as (lv, Hlv).
apply Rser_pos_bound_cv with lv.
exact Un_pos.
intro n.
apply Rle_trans with (sum_f_R0 Vn n).
apply sum_Rle.
intros p _; apply Hmaj.
apply growing_ineq. (* rename*)
apply Rser_pos_growing.
apply Vn_pos.
exact Hlv.
Qed.

(** Big-O and bound *)

Lemma Rser_big_O_maj (Un Vn : nat -> R) : 
    (forall n : nat, 0 <= Vn n) -> Un = O (Vn) ->
        exists K, exists SN, 0<= K /\ 
            forall n : nat, sum_f_R0 (|Un|) n <= K* (sum_f_R0 Vn n) + SN.
Proof.
intros Un Vn Vn_pos HO.
destruct HO as [K [HK [N HN]]].
apply Rge_le in HK.
exists K; exists (sum_f_R0 (fun k => Rabs (Un k)) N).
split.
apply HK.
intro n; case (le_lt_dec n N); intro Hn.
apply Rle_trans with (sum_f_R0 (fun k => Rabs (Un k)) N).
assert (n = N \/ n < N)%nat.
omega.
case H ; intro HnN.
rewrite HnN; apply Rle_refl.
rewrite tech2 with (fun k => Rabs (Un k)) n N. (* rename!*)
apply Rplus_le_simpl_l.
apply cond_pos_sum. (* rename!*)
intro k; apply Rabs_pos.
apply HnN.
apply Rplus_le_simpl_r.
apply Rmult_le_pos; [apply HK | apply cond_pos_sum; apply Vn_pos].
rewrite tech2 with (|Un|) N n.
rewrite Rplus_comm.
apply Rplus_le_compat_r.
rewrite tech2 with Vn N n.
rewrite Rmult_plus_distr_l.
apply Rle_trans with (K * sum_f_R0 (fun i : nat => Vn (S N + i)%nat) (n- (S N)))%R.
rewrite scal_sum. (* rename*)
apply sum_Rle. (*rename*)
intros n0 Hn0.
rewrite <- Rabs_pos_eq.
rewrite Rmult_comm; rewrite Rabs_mult.
rewrite Rabs_pos_eq with K.
apply HN; omega.
apply HK.
apply Rmult_le_pos; [apply Vn_pos | apply HK].
apply Rplus_le_simpl_r.
apply Rmult_le_pos; [apply HK | apply cond_pos_sum; apply Vn_pos].
apply Hn.
apply Hn.
Qed.

(** Convergence and big-O *)

Lemma Rser_big_O_cv_weak (Un Vn : nat -> R) : 
    (forall n : nat, 0 <= Un n) -> (forall n : nat, 0 <= Vn n) ->
        Un = O(Vn) -> {lv | Rser_cv Vn lv} -> {lu | Rser_cv Un lu}.
Proof.
intros Un Vn Un_pos Vn_pos HO Hlv; destruct Hlv as [lv Hlv].
assert ({M | Rser_bound_max Un M}) as HM.
assert ({M : R | is_lub (EUn (sum_f_R0 Un))M})as HMub.
apply ub_to_lub.
destruct (Rser_big_O_maj Un Vn  Vn_pos HO) as [K [SN [K_pos Hmaj]]].
exists (K*lv+SN)%R.
intros x Hx; destruct Hx as [n Hn]; rewrite Hn.
apply Rle_trans with (K * sum_f_R0 Vn n + SN)%R.
rewrite (sum_eq Un (fun k => Rabs (Un k))).
apply Hmaj.
intros i Hi; rewrite Rabs_pos_eq; [reflexivity | apply Un_pos].
apply Rplus_le_compat_r.
apply Rmult_le_compat_l.
apply K_pos.
apply growing_ineq. (*rename*)
apply Rser_pos_growing; apply Vn_pos.
apply Hlv.
destruct HMub as [M [HM _]]; exists M.
intro n; apply HM.
exists n; reflexivity.
destruct HM as [M HM].
apply Rser_pos_bound_cv with M.
apply Un_pos.
apply HM.
Qed.

Lemma Rser_big_O_cv (Un Vn : nat -> R) : 
  Un = O(Vn) -> {lv | Rser_abs_cv Vn lv} -> {lu | Rser_abs_cv Un lu}.
Proof.
intros Un Vn HO Hlv.
apply Rser_big_O_cv_weak with (|Vn|); intros; apply Rabs_pos || auto.
destruct HO as [M [HM [N HN]]]; exists M.
split; auto.
exists N; intros.
unfold Rseq_abs; rewrite Rabs_Rabsolu; auto.
rewrite Rabs_Rabsolu; apply HN; assumption.
Qed.

(** Little-O and bound *)

Lemma Rser_little_O_maj (Un Vn : nat -> R) : 
    (forall n : nat, 0 <= Vn n) -> Un = o (Vn) ->
        forall eps, 0< eps -> exists SN,
            forall n : nat, sum_f_R0 (|Un|) n <= eps* (sum_f_R0 Vn n) + SN.
Proof.
intros Un Vn Vn_pos HO eps Heps.
assert (0<= eps) as Heps_pos.
apply Rlt_le; apply Heps.
destruct (HO eps Heps) as [N HN].
exists (sum_f_R0 (|Un|) N).
intro n; case (le_lt_dec n N); intro Hn.
apply Rle_trans with (sum_f_R0 (|Un|) N).
assert (n = N \/ n < N)%nat.
omega.
case H ; intro HnN.
rewrite HnN; apply Rle_refl.
rewrite tech2 with (|Un|) n N. (* rename!*)
apply Rplus_le_simpl_l.
apply cond_pos_sum. (* rename!*)
intro k; apply Rabs_pos.
apply HnN.
apply Rplus_le_simpl_r.
apply Rmult_le_pos; [apply Heps_pos | apply cond_pos_sum; apply Vn_pos].
rewrite tech2 with (|Un|) N n.
rewrite Rplus_comm.
apply Rplus_le_compat_r.
rewrite tech2 with Vn N n.
rewrite Rmult_plus_distr_l.
apply Rle_trans with (eps * sum_f_R0 (fun i : nat => Vn (S N + i)%nat) (n- (S N)))%R.
rewrite scal_sum. (* rename*)
apply sum_Rle. (*rename*)
intros n0 Hn0.
rewrite <- Rabs_pos_eq.
rewrite Rmult_comm; rewrite Rabs_mult.
rewrite Rabs_pos_eq with eps.
apply HN; omega.
apply Heps_pos.
apply Rmult_le_pos; [apply Vn_pos | apply Heps_pos].
apply Rplus_le_simpl_r.
apply Rmult_le_pos; [apply Heps_pos | apply cond_pos_sum; apply Vn_pos].
apply Hn.
apply Hn.
Qed.

(** Convergence and little-O*)

Lemma Rser_little_O_cv (Un Vn : nat -> R) : 
  Un = o(Vn) -> {lv | Rser_abs_cv Vn lv} -> {lu | Rser_abs_cv Un lu}.
Proof.
intros Un Vn Ho Hcv.
apply (Rser_big_O_cv Un Vn); [|assumption].
apply Rseq_little_O_big_O_incl; assumption.
Qed.

(** Convergence and equivalence *)

Lemma Rser_equiv_cv (Un Vn : nat -> R) : 
    (forall n : nat, 0 <= Un n) -> (forall n : nat, 0 <= Vn n) ->
        Un ~ Vn -> {lv | Rser_cv Vn lv} -> {lu | Rser_cv Un lu}.
Proof.
intros Un Vn Un_pos Vn_pos Heq Hlv.
apply Rseq_equiv_sym in Heq.
assert  ({luv | Rser_cv (fun n => Rabs (Vn n - Un n)) luv}) as Hluv.
apply Rser_little_O_cv with Vn.
unfold Rseq_little_O.
intros eps Heps.
destruct (Heq eps Heps) as [N HN]; exists N.
intro n; apply HN.
destruct Hlv as [lv Hlv].
exists lv; apply Rser_cv_eq_compat with Vn.
  intros n; unfold Rseq_abs; rewrite Rabs_right; auto with real.
assumption.
destruct Hlv as [lv Hlv].
destruct Hluv as [luv Hluv].
apply Rser_pos_bound_cv with (lv + luv)%R.
apply Un_pos.
intro n.
apply Rle_trans with (sum_f_R0 Vn n + sum_f_R0 (fun n : nat => Rabs (Vn n - Un n)) n)%R.
apply Rle_trans with (sum_f_R0 (fun n0 : nat => Vn n0 + Rabs (Vn n0 - Un n0)) n)%R.
apply sum_Rle. (*rename?*)
intros n0 Hn0.
rewrite <- ( Rabs_pos_eq)  with (Vn n0).
rewrite Rabs_pos_eq with (Vn n0) at 2.
rewrite <- Rabs_pos_eq  with (Un n0).
rewrite  Rabs_pos_eq  with (Un n0) at 2.
rewrite <-  Rabs_Ropp.
rewrite <-  Rabs_Ropp with (Vn n0).
replace (- Un n0)%R with  (- Vn n0 + (Vn n0 - Un n0))%R by ring.
apply Rabs_triang.
apply Un_pos .
apply Un_pos.
apply Vn_pos.
apply Vn_pos.
rewrite plus_sum. (* rename*)
apply Rplus_le_compat_l.
apply Rle_refl.
apply Rplus_le_compat; [ | ]; apply growing_ineq.
apply Rser_pos_growing.
apply Vn_pos.
apply Hlv.
apply Rser_pos_growing.
intro k; apply Rabs_pos.
apply Hluv.
Qed.

(** classical is needed? *)
Hypothesis NNPP : forall p : Prop, ~ ~ p -> p.
Hypothesis classic: forall P : Prop, P \/ ~ P.


Lemma Rser_equiv_cv_infty (Un Vn : nat -> R) : 
    (forall n : nat, 0 <= Un n) -> (forall n : nat, 0 <= Vn n) ->
        Un ~ Vn -> Rser_cv_pos_infty Vn -> Rser_cv_pos_infty Un.
Proof.
intros Un Vn Un_pos Vn_pos Heq Hv.
case (Rser_pos_cv_dec Un Un_pos NNPP classic); intro Hcase.
apply Rseq_growing_constructive_limit in Hcase.
apply (Rser_equiv_cv Vn Un) in Hcase.
assert ((exists l, Rser_cv Vn l)/\ Rser_cv_pos_infty Vn).
split.
destruct Hcase as [ l Hl].
exists l; apply Hl.
apply Hv.
elim Rseq_cv_not_infty with (sum_f_R0 Vn).
apply H.
apply Vn_pos.
apply Un_pos.
apply Rseq_equiv_sym.
apply Heq.
apply Rser_pos_growing.
apply Un_pos.
apply Hcase.
Qed.

End Rser_pos_comp.

(** * Summing Landau's relations when the series go to infinity*)

Section Rser_landau_infty.

Variables Vn : nat -> R.
Hypothesis Vn_pos : (forall n : nat, 0 <= Vn n).
Hypothesis Vn_infty : Rser_cv_pos_infty Vn.

Lemma Rser_partial_big_O_compat (Un : nat -> R): 
    Un = O(Vn) -> sum_f_R0 Un = O(sum_f_R0 Vn).
Proof.
intros Un HO.
assert (forall n, 0<= Rabs(Un n)) as RUn_pos.
intro n; apply Rabs_pos.
destruct (Rser_big_O_maj Un Vn Vn_pos HO) as [K [SN [K_pos Hmaj]]].
destruct (Vn_infty SN) as [N HN].
exists (K+1)%R.
split.
auto with *.
exists N; intros n Hn.
apply Rle_trans with (K * sum_f_R0 Vn n + SN)%R.
apply Rle_trans with (sum_f_R0 (fun k : nat => Rabs (Un k)) n).
apply sum_f_R0_triangle.
apply Hmaj.
rewrite Rmult_plus_distr_r.
rewrite Rabs_pos_eq.
ring_simplify.
apply Rplus_le_compat_l.
apply Rlt_le; apply HN; apply Hn.
apply (cond_pos_sum _ _ Vn_pos).
Qed.

Lemma Rser_partial_little_O_compat (Un : nat -> R): 
    Un = o(Vn) -> sum_f_R0 Un = o(sum_f_R0 Vn).
Proof.
intros Un Ho eps Heps.
assert (0<eps/2) as Heps2; [fourier|].
destruct (Rser_little_O_maj _ _ Vn_pos Ho (eps /2)) as [C HC].
apply Heps2.
destruct (Vn_infty (C/(eps/2))%R) as [N HN].
exists N.
intros n Hn.
rewrite Rabs_pos_eq with (sum_f_R0 Vn n).
apply Rle_trans with (sum_f_R0 (fun k : nat => Rabs (Un k)) n).
apply sum_f_R0_triangle.
apply Rle_trans with ((eps / 2) * sum_f_R0 Vn n + C)%R.
apply HC.
rewrite double_var with eps .
rewrite <- double_var with eps at 1.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat_l.
assert (C = (eps/2)*(/(eps/2))*C)%R as HCr.
field.
intro Hf; apply Rlt_irrefl with 0; rewrite Hf in Heps; apply Heps.
rewrite HCr.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le; apply Heps2.
rewrite Rmult_comm.
apply Rlt_le.
apply HN; apply Hn.
apply (cond_pos_sum Vn n Vn_pos).
Qed.

Lemma Rser_partial_equiv_compat (Un : nat -> R): 
    Un ~ Vn -> (sum_f_R0 Un) ~ (sum_f_R0 Vn).
Proof.
intros Un Heq.
apply Rseq_equiv_sym.
apply Rseq_equiv_sym in Heq.
assert((sum_f_R0 (Vn -Un)) = o(sum_f_R0 Vn)).
apply (Rser_partial_little_O_compat (Vn - Un) Heq ).
intros eps Heps.
destruct (H eps Heps) as [N HN].
exists N; intros n Hn.
unfold Rseq_minus.
rewrite <- minus_sum.
apply HN; apply Hn.
Qed.

End Rser_landau_infty.

(** Properties of remainder *)
Section Rser_rem.

(** Remainder caracterization *)

Lemma Rser_rem_cv (Un : nat -> R) (lu : R) (Hlu : Rser_cv Un lu )(n : nat) : 
    Rser_cv (fun k => Un (S n+ k)%nat) (Rser_rem Un lu Hlu n).
Proof.
intros Un lu Hlu n eps Heps.
destruct (Hlu eps Heps) as [N HN].
exists (S n+N)%nat.
unfold R_dist; unfold Rser_rem.
intros p Hp.
replace (sum_f_R0 (fun k : nat => Un (S n + k)%nat) p - (lu - sum_f_R0 Un n))%R with
    (sum_f_R0 Un n + sum_f_R0 (fun k : nat => Un (S n +k)%nat) p - lu)%R by ring.
replace p with ((p + S n) - S n)%nat by intuition.
rewrite  <- tech2 with Un n (p+ S n)%nat.
apply HN.
apply le_trans with p; intuition.
apply le_trans with p; intuition.
Qed.

(** Compatibility between remainder and usual operations *)

Lemma Rser_rem_plus_compat Un Vn lu lv Hlu Hlv :
    Rser_rem Un lu Hlu + Rser_rem Vn lv Hlv == Rser_rem (Un+Vn) (lu+lv) (Rser_cv_plus_compat Un Vn lu lv Hlu Hlv).
Proof.
intros Un Vn lu lv Hlu hlv.
unfold Rser_rem, Rseq_plus, Rseq_eq.
intro n.
rewrite sum_plus.
ring.
Qed.

(* TODO to place *)
Lemma sum_opp_compat Un : sum_f_R0 (-Un) == - sum_f_R0 Un.
Proof.
intro Un.
unfold Rseq_eq.
induction n.
trivial.
simpl.
rewrite IHn.
unfold Rseq_opp.
rewrite <- Ropp_plus_distr.
reflexivity.
Qed.

Lemma sum_minus_compat Un Vn : sum_f_R0 (Un - Vn) == sum_f_R0 Un - sum_f_R0 Vn.
Proof.
intros Un Vn.
unfold Rseq_eq, Rseq_minus.
induction n.
trivial.
simpl.
rewrite IHn.
ring.
Qed.

Lemma Rser_rem_opp_compat Un lu Hlu :
    - Rser_rem Un lu Hlu == Rser_rem (-Un) (-lu) (Rser_cv_opp_compat Un lu Hlu).
Proof.
intros Un lu Hlu.
unfold Rser_rem, Rseq_eq.
intro  n.
rewrite sum_opp_compat.
unfold Rseq_opp.
ring.
Qed.

Lemma Rser_rem_minus_compat Un Vn lu lv Hlu Hlv :
    Rser_rem Un lu Hlu - Rser_rem Vn lv Hlv == Rser_rem (Un-Vn) (lu-lv) (Rser_cv_minus_compat Un Vn lu lv Hlu Hlv).
Proof.
intros Un Vn lu lv Hlu hlv.
unfold Rser_rem, Rseq_eq.
intro n.
rewrite sum_minus_compat.
unfold Rseq_minus.
ring.
Qed.

Lemma Rser_rem_scal : forall x (Un : Rseq) lu n (Vn := (fun n => x * Un n )%R)  
  (Hlu : Rser_cv Un lu) (Hlv : Rser_cv Vn (x * lu)),
   (x * Rser_rem Un lu Hlu n = Rser_rem Vn (x * lu) Hlv n)%R.
Proof.
intros x Un lu n Vn Hlu Hlv.
unfold Rser_rem.
rewrite Rmult_minus_distr_l. rewrite scal_sum.
unfold Vn.
induction n. 
 simpl. ring.

 repeat rewrite tech5. unfold Rminus in *. 
 repeat rewrite Ropp_plus_distr. rewrite <- Rplus_assoc. rewrite IHn. ring.
Qed.

End Rser_rem.




(** * Summing Landau's relations when the series converge*)
Section Rser_landau_cv.

Variables Un Vn : nat-> R.
Hypothesis Vn_pos : (forall n : nat, 0 <= Vn n).
Variable lu lv : R.
Hypothesis Hlv : Rser_cv Vn lv.
Hypothesis Hlu : Rser_cv Un lu.


Lemma Rser_rem_big_O_compat :
    Un = O(Vn) -> (Rser_rem Un lu Hlu) = O(Rser_rem Vn lv Hlv).
Proof.
intro HO.
destruct HO as [K [K_pos [N HN]]].
exists K.
split.
apply K_pos.
exists N.
intros n Hn.
rewrite <- Rabs_pos_eq with K.
rewrite <- Rabs_mult.
apply Rle_cv_lim with (fun p : nat => Rabs (sum_f_R0 (fun k => (Un (S n+k))) p))%R
                                    (fun p : nat => Rabs (sum_f_R0 (fun k => (Vn (S n+k))*K) p))%R.
intro p.
apply Rle_trans with (sum_f_R0 (fun k : nat =>(Rabs (Un (S n + k)))) p)%R.
apply Rabs_triang_gen.
rewrite Rabs_pos_eq.
apply sum_Rle.
intros k Hk.
 rewrite <- Rabs_pos_eq with (Vn (S n + k)).
rewrite Rmult_comm.
apply HN; omega.
apply Vn_pos.
apply cond_pos_sum; intro.
apply Rge_le in K_pos.
rewrite Rmult_comm.
apply Rmult_le_pos; [apply K_pos | apply Vn_pos].
apply Rseq_cv_abs_compat; apply Rser_rem_cv.
apply Rseq_cv_abs_compat.
apply Rseq_cv_eq_compat with (fun p : nat => K * sum_f_R0 (fun k : nat => ( Vn (S n + k))) p)%R.
intro; rewrite (scal_sum _ _ K); reflexivity.
apply CV_mult.
apply Rseq_constant_cv.
apply Rser_rem_cv.
apply Rge_le.
apply K_pos; apply K_pos.
Qed.

Lemma Rser_rem_little_O_compat :
    Un = o(Vn) -> (Rser_rem Un lu Hlu) = o(Rser_rem Vn lv Hlv).
Proof.
intros Ho eps Heps.
destruct (Ho eps Heps) as  [N HN].
exists N.
intros n Hn.
assert (0<= eps) as eps_pos.
apply Rlt_le; apply Heps.
rewrite <- Rabs_pos_eq with eps.
rewrite <- Rabs_mult.
apply Rle_cv_lim with (fun p : nat => Rabs (sum_f_R0 (fun k => (Un (S n+k))) p))%R
                                    (fun p : nat => Rabs (sum_f_R0 (fun k => (Vn (S n+k))*eps) p))%R.
intro p.
apply Rle_trans with (sum_f_R0 (fun k : nat =>(Rabs (Un (S n + k)))) p)%R.
apply Rabs_triang_gen.
rewrite Rabs_pos_eq.
apply sum_Rle.
intros k Hk.
 rewrite <- Rabs_pos_eq with (Vn (S n + k)).
rewrite Rmult_comm.
apply HN; omega.
apply Vn_pos.
apply cond_pos_sum; intro.
apply Rmult_le_pos; [ apply Vn_pos| apply eps_pos].
apply Rseq_cv_abs_compat; apply Rser_rem_cv.
apply Rseq_cv_abs_compat.
apply Rseq_cv_eq_compat with (fun p : nat => eps * sum_f_R0 (fun k : nat => ( Vn (S n + k))) p)%R.
intro; rewrite (scal_sum _ _ eps); reflexivity.
apply CV_mult.
apply Rseq_constant_cv.
apply Rser_rem_cv.
apply eps_pos.
Qed.

End Rser_landau_cv.

Section Rser_equiv_cv.

Variables Un Vn : nat-> R.
Hypothesis Vn_pos : (forall n : nat, 0 <= Vn n).
Variable lu lv : R.
Hypothesis Hlv : Rser_cv Vn lv.
Hypothesis Hlu : Rser_cv Un lu.


Lemma Rser_rem_equiv_compat :
    Un ~ Vn -> (Rser_rem Un lu Hlu) ~ (Rser_rem Vn lv Hlv).
Proof.
intro Heq.
apply Rseq_equiv_sym.
apply Rseq_equiv_sym in Heq.
unfold Rseq_equiv in *.
assert(Hrew : (Rser_rem Vn lv Hlv - Rser_rem Un lu Hlu)== Rser_rem (Vn-Un) (lv-lu) (Rser_cv_minus_compat Vn Un lv lu Hlv Hlu)).
apply Rser_rem_minus_compat.
intros eps Heps.
destruct(Rser_rem_little_O_compat (Vn -Un) Vn Vn_pos (lv-lu) lv Hlv (Rser_cv_minus_compat Vn Un lv lu Hlv Hlu) Heq eps Heps) as [N HN].
exists N.
intro n.
rewrite Hrew.
apply HN.
Qed.

End Rser_equiv_cv.

Lemma Rser_cv_zero Un l : Rser_cv Un l -> Rseq_cv Un 0.
Proof.
intros Un l Hu.
apply Rseq_cv_asymptotic_eq_compat with ((sum_f_R0 Un) - (fun n => sum_f_R0 Un (pred n))%R).
exists 1%nat.
intros n Hn ; simpl; unfold Rseq_minus.
rewrite  sum_N_predN.
ring.
apply Hn.
replace R0 with (l -l)%R by ring.
apply Rseq_cv_minus_compat.
apply Hu.
intros eps Heps.
destruct (Hu eps Heps) as [N HN].
exists (S N).
intros n Hn; unfold R_dist.
apply HN; intuition.
Qed.

(* begin hide *)
Open Scope R_scope.
(* end hide *)
Local Notation sum := sum_f_R0 (only parsing).

Lemma Rsum_shift Un : sum_f_R0 (Rseq_shift Un) == ((Rseq_shift (sum_f_R0 Un)) - (Un O))%Rseq.
Proof.
intros Un n.
assert (REW : forall a b c, c + a = b -> a = b - c) by (intros; subst; field).
apply REW.
induction n.
 compute; field.
 
 unfold Rseq_shift in *.
 do 2 rewrite tech5.
 rewrite <- IHn.
 unfold Rseq_constant.
 field.
Qed.

(** Series convergence shifting compatibility *)

Lemma Rser_cv_shift Un l : Rser_cv Un l -> Rser_cv (Rseq_shift Un) (l - (Un O)).
Proof.
intros Un l H.
apply Rseq_cv_shift_compat.
assert (EC : forall a b x, Rseq_cv (a + b - b)%Rseq x -> Rseq_cv a x).
 intros; apply Rseq_cv_eq_compat with (a + b - b)%Rseq.
  intro; compute; field.
  assumption.
 
 apply EC with (Un O)%Rseq.
  apply Rseq_cv_minus_compat.
  intros e ep; destruct (H e ep) as [N He]; exists N; intros n nN.
  unfold Rseq_plus; unfold Rseq_shift.
  replace (sum_f_R0 (fun n0 : nat => Un (S n0)) (S n)) with (sum_f_R0 (Rseq_shift Un) (S n)) by reflexivity.
  rewrite Rsum_shift with Un (S n).
  unfold Rseq_minus.
  assert (REW:forall a b, a - b + b = a) by (intros; field); rewrite REW; clear REW.
  apply He; omega.
  
  apply Rseq_constant_cv.
Qed.

Lemma Rser_cv_shift_rev : forall (Un : nat -> R) (l : R),
  Rser_cv (Rseq_shift Un) l ->
   Rser_cv Un (l + Un 0%nat).
Proof.
intros Un l H.
apply Rseq_cv_shift_compat.
assert (EC : forall a b x, Rseq_cv (a - b + b)%Rseq x -> Rseq_cv a x).
 intros; apply Rseq_cv_eq_compat with (a - b + b)%Rseq.
  intro; compute; field.
  assumption.
 
 apply EC with (Un O)%Rseq.
  intros e1 ep; destruct (H e1 ep) as [N He]; exists N; intros n nN.
  unfold Rseq_plus; unfold Rseq_shift. unfold Rseq_constant. unfold Rseq_minus.
  generalize (He n nN) ; intros H1.
  rewrite Rsum_shift in H1.
  unfold Rseq_shift, Rseq_minus, Rseq_constant, Rseq_plus, Rseq_shift, Rseq_constant in H1.
  unfold R_dist in *. ring_simplify (sum_f_R0 Un (S n) - Un 0%nat + Un 0%nat - (l + Un 0%nat)).
  apply H1.
Qed.

(* TODO hide and/or move *)
Lemma sum_minus: forall Un n n2, 
- sum_f_R0 Un n + sum_f_R0 Un (S (n2 + n)) =
sum_f_R0 (fun k : nat => Un (S n + k)%nat) n2.
Proof.
intros Un n n2.
induction n2.
 simpl. ring_simplify. rewrite plus_0_r. reflexivity.
 
 repeat rewrite tech5. rewrite <- IHn2. 
 rewrite <- plus_n_Sm. do 2 rewrite plus_Sn_m.
 rewrite plus_comm.
 ring.
Qed.

Lemma Rser_cv_shift_n : forall n (Un : nat -> R) (l : R),
  Rser_cv (fun k : nat => Un (S n + k)%nat) (l) ->
    Rser_cv Un (l + sum_f_R0 Un n).
Proof.
intros n Un l Hun.
unfold Rser_cv in *. unfold Rseq_cv in *.
intros eps Heps. destruct (Hun eps Heps) as (N, Hun1). clear Hun.
exists (S n + N)%nat. intros n1 Hn1.
pose (n2 := (n1 - S n)%nat).
assert (H3 : (n2 >= N)%nat). unfold n2. intuition. 
generalize (Hun1 n2 H3). intros Hun. clear Hun1.
unfold R_dist in *. unfold Rminus. rewrite Ropp_plus_distr.
rewrite Rplus_comm. rewrite Rplus_assoc.
destruct n1.
 simpl. unfold n2 in *. destruct n. inversion Hn1.
 inversion H3. unfold minus in *. inversion Hn1.

 replace (S n1) with (n2 + S n)%nat in * by (unfold n2 ; intuition).
 rewrite <- plus_n_Sm. rewrite sum_minus.
 rewrite Rplus_comm. apply Hun.
Qed.

Lemma Rser_cv_shift_n_rev : forall n (Un : nat -> R) (l : R),
  Rser_cv Un (l + sum_f_R0 Un n) ->
   Rser_cv (fun k : nat => Un (S n + k)%nat) (l).
Proof.
intros n Un l Hun.
unfold Rser_cv, Rseq_cv in *. 
intros eps Heps. destruct (Hun eps Heps) as (N, Hun1). clear Hun.
exists (N - n)%nat. intros n1 Hn1.
pose (n2 := S (n1 + n)%nat).
assert (H3 : (n2 >= N)%nat). unfold n2. intuition. 
generalize (Hun1 n2 H3). intros Hun. clear Hun1.
unfold R_dist in *. unfold Rminus in Hun. rewrite Ropp_plus_distr in Hun.
rewrite Rplus_comm in Hun. rewrite Rplus_assoc in Hun.
rewrite <- sum_minus. fold n2.
rewrite Rplus_comm in Hun. assumption.
Qed.


Lemma Rser_cv_sig_shift_compat Un : {l | Rser_cv Un l} -> {l | Rser_cv (Rseq_shift Un) l}.
Proof.
intros Un [l H].
exists (l - (Un O)).
apply Rser_cv_shift; assumption.
Qed.

Lemma Rser_cv_shift_reciprocal Un l : Rser_cv (Rseq_shift Un) (l - (Un O)) -> Rser_cv Un l.
Proof.
intros Un l H.
assert (EC : forall (a:Rseq) (b x:R), Rseq_cv (a - b)%Rseq (x - b) -> Rseq_cv a x).
 intros; apply Rseq_cv_eq_compat with (a - b + b)%Rseq.
  intro; compute; field.
  replace x with (x - b + b) by field.
  apply Rseq_cv_plus_compat.
   assumption.
   apply Rseq_constant_cv.
 
 eapply EC with (Un O).
 apply Rseq_cv_shift_compat.
 apply Rseq_cv_eq_compat with (sum_f_R0 (Rseq_shift Un)).
 apply Rsum_shift.
 apply H.
Qed.

Lemma Rser_cv_sig_shift_reciprocal_compat Un : {l | Rser_cv (Rseq_shift Un) l} -> {l | Rser_cv Un l}.
Proof.
intros Un [l H].
exists (l + (Un O)).
apply Rser_cv_shift_reciprocal.
replace (l + Un 0%nat - Un 0%nat) with l by ring; assumption.
Qed.

(* TODO : rename *)
Lemma Rseq_decomp An p n : sum An (S (p + n)) = sum An p + sum (fun i => An (plus i (S p))) n.
Proof.
intros.
induction n.
 replace (p + 0)%nat with p by omega.
 trivial.
 
 simpl sum.
 replace (p + S n)%nat with (S (p + n)) by auto.
 rewrite IHn.
 replace (S (n + S p)) with (S (S (p + n))) by omega.
 ring.
Qed.

Lemma Rseq_reverse An n : sum (fun i => An (n - i)%nat) n = sum An n.
Proof.
intros An n; generalize dependent An.
induction n.
 trivial.
 
 intros.
 repeat rewrite tech5.
 pose (fun j => An (S j)) as Asn.
 replace (sum (fun i => An (S n - i)%nat) n)
   with (sum (fun i => (Rseq_shift An) (n - i)%nat) n)
   by (unfold Rseq_shift; apply sum_eq; intros; replace (S (n - i)) with (S n - i)%nat by omega; trivial).
 rewrite IHn.
 replace (S n - S n)%nat with O by intuition.
 rewrite Rsum_shift.
 unfold Rseq_shift, Rseq_minus, Rseq_constant.
 simpl.
 ring.
Qed.

Lemma scal_sum_l : forall (An : nat -> R) (N : nat) (x : R),
       x * sum_f_R0 An N = sum_f_R0 (fun i : nat => x * An i ) N.
Proof.
intros.
induction N; simpl; ring_simplify; trivial.
rewrite IHN; ring.
Qed.

Lemma scal_sum_r : forall (An : nat -> R) (N : nat) (x : R),
       sum_f_R0 An N * x = sum_f_R0 (fun i : nat => An i * x) N.
Proof.
intros.
induction N; simpl; ring_simplify; trivial.
rewrite IHN; ring.
Qed.

(** * Cauchy Product **)

Lemma cauchy_product_subproof_rearrangement1 An Bn n :
  sum (fun i => (sum Bn i * An (n - i)%nat)%R) n =
  sum (fun i => sum (fun k => (An (n - i)%nat * Bn (k)%nat)%R) i) n.
Proof.
intros.
apply Rsum_eq_compat; intro.
rewrite Rmult_comm; rewrite scal_sum_l; trivial.
Qed.

Lemma cauchy_product_subproof_rearrangement An Bn n :
  sum (fun i => (sum Bn i * An (n - i)%nat)%R) n =
  sum (fun i => sum (fun k => (An k * Bn (i - k)%nat)%R) i) n.
Proof.
intros f g n.
rewrite cauchy_product_subproof_rearrangement1.
rewrite <- Rseq_reverse.
induction n.
 simpl; ring.
 
 do 2 rewrite tech5.
 rewrite <- IHn.
 replace (S n - S n)%nat with O by intuition.
 replace ( (sum (fun i => sum (fun k => f (S n - (S n - i))%nat * g k) (S n - i)) n)%R)
   with    (sum (fun i => sum (fun k => f (S n - (S n - i))%nat * g k) (n - i) +
     f ((S n - (S n - i)))%nat * g (S n - i)%nat) n)%R.
  rewrite sum_plus.
  assert (forall n, sum (fun l => f ((S n - (S n - l)))%nat * g (S n - l)%nat) n +
    sum (fun k => f (S n - 0)%nat * g k) 0 =
    sum (fun k => f k * g (S n - k)%nat) (S n)).
   intros n0.
   rewrite tech5.
   replace (S n0 - S n0)%nat with O by intuition.
   replace (
     sum (fun l => f (S n0 - (S n0 - l))%nat * g (S n0 - l)%nat) n0)
     with
     (sum (fun k => f k * g (S n0 - k)%nat) n0).
   trivial.
   apply sum_eq.
   intros n1 Hn1.
   replace (S n0 - (S n0 - n1))%nat with n1 by omega; trivial.
  
  rewrite <- H.
  replace (sum (fun l => sum (fun k => f (S n - (S n - l))%nat * g k) (n - l)) n)
    with (sum (fun i => sum (fun k => f (n - (n - i))%nat * g k) (n - i)) n).
  ring.
  apply sum_eq; intros i Hi.
  apply sum_eq; intros i0 Hi0.
  replace (S n - (S n - i))%nat with (n - (n-i))%nat by omega; trivial.
 
 apply sum_eq; intros i Hi.
 replace (S n - i)%nat with (S (n - i)) by intuition.
 trivial.
Qed.

(** Mertens' theorem *)

Lemma cauchy_product : forall An Bn la lb lna,
 Rser_cv An la -> 
 Rser_cv Bn lb -> 
 Rser_abs_cv An lna ->
 Rser_cv ((fun k:nat => sum_f_R0 (fun p:nat => An p * Bn (k - p)%nat) k)%R)
   (la * lb)%R.
Proof.
intros An Bn la lb lna HA HB HNA e epos.

pose (e * / 4 * / (lna + 1))%R as eN.
assert (lnapos : lna + 1 > 0).
 apply Rle_lt_0_plus_1.
 apply Rle_trans with (Rabs (An O)).
  apply Rabs_pos.
  apply (sum_incr (|An|) O lna HNA).
  intro; apply Rabs_pos.
assert (eNpos : eN > 0) by (apply Rlt_mult_inv_pos; auto; fourier).
destruct (HB eN eNpos) as [N HN].

destruct (maj_by_pos (sum_f_R0 Bn)) as [supBn[]]; [exists lb; apply HB|].
pose (supBn + Rabs lb)%R as supBnB.
assert (HsupBnB : forall n, (Rabs ((sum_f_R0 Bn n) - lb) <= supBnB)%R).
 intro n.
 replace ((sum_f_R0 Bn n) - lb)%R with (sum_f_R0 Bn n + - lb)%R by auto.
 eapply Rle_trans.
  apply Rabs_triang.
  apply Rplus_le_compat.
   apply H0.
   rewrite Rabs_Ropp; apply Rle_refl.
pose (e * / 8 * / (INR (S N)) * / (supBnB + 1))%R as eM.
assert (eMpos : eM > 0).
 repeat apply Rlt_mult_inv_pos; try fourier.
  replace 0 with (INR O) by trivial; apply lt_INR; omega.
  apply Rle_lt_0_plus_1; apply Rplus_le_le_0_compat; try fourier; apply Rabs_pos.
destruct (Rser_cv_zero An la HA eM eMpos) as [M' HM'].
pose (plus M' N) as M.

pose (e * / 2 * / (Rabs lb + 1))%R as eL.
assert (eLpos : eL > 0).
 repeat apply Rlt_mult_inv_pos; try fourier.
 apply Rle_lt_0_plus_1; try fourier; apply Rabs_pos.
destruct (HA eL eLpos) as [L HL].

clear H H0 eLpos epos.

pose (max (max (S N) M) L) as K.

pose (sum_f_R0 An) as SAn.
pose (sum_f_R0 Bn) as SBn.
pose (sum_f_R0 (fun i => sum_f_R0 (fun k => (An k * Bn (minus i k))%R) i)) as Cn.
fold Cn.

exists K; intros n Hn.
replace (Cn n) with (sum (fun i => SBn i * (An (n - i)%nat))%R n) by
  (unfold SBn, Cn; apply cauchy_product_subproof_rearrangement).

replace (sum (fun i => (SBn i * An (n - i)%nat)%R) n)
  with (sum (fun i => ((SBn i - lb) * An (n - i)%nat) + An (n - i)%nat * lb)%R n)
  by (apply Rsum_eq_compat; intro; ring).

rewrite sum_plus.
rewrite <- scal_sum.
rewrite Rseq_reverse.
fold SAn.

unfold R_dist.
assert (RE : forall x y z t, x + t * y - z * t = x + t * (y - z))
  by (intros; ring); rewrite RE; clear RE.

eapply Rle_lt_trans; [apply Rabs_triang|].
replace e with (e/4 + e/4 + e/2) by field.
apply Rplus_lt_compat.
 eapply Rle_lt_trans; [apply Rsum_abs |].
 pose (fun l => (fun l0 : nat => (SBn l0 - lb) * An (n - l0)%nat) l) as dab.
 fold dab.
 
 pose (minus n (S N)) as p.
 assert (HnN : (n >= S N)%nat).
  apply le_trans with K; auto.
  eapply le_trans; apply le_max_l.
 replace n with (S (N + p)) by (unfold p; omega).
 rewrite Rseq_decomp.
 
 apply Rplus_lt_compat.
  unfold dab.
  replace (e / 4) with (eM * 2 * INR (S N) * (supBnB + 1))
    by (unfold eM; field; split; replace 0 with (INR O) by auto; try (apply not_INR; omega);
    apply Rgt_not_eq; apply Rle_lt_0_plus_1; apply Rle_trans with (Rabs (SBn O - lb)); apply Rabs_pos || apply HsupBnB).
  apply Rle_lt_trans with (sum (fun l => Rabs (An (n - l)%nat) * supBnB) N).
   apply sum_Rle; intros.
   rewrite Rmult_comm.
   rewrite Rabs_mult.
   apply Rmult_le_compat_l.
    apply Rabs_pos.
    apply HsupBnB.
   
   rewrite <- scal_sum.
   rewrite Rmult_comm.
   apply Rmult_le_0_lt_compat; [
    apply cond_pos_sum; intro; apply Rabs_pos|
    apply Rle_trans with (Rabs (SBn O - lb)); apply Rabs_pos || apply HsupBnB | |
    auto with * ].
   apply Rle_lt_trans with (eM * INR (S N)); [|
    replace (eM * INR (S N)) with (eM * 1 * INR (S N)) by ring;
    apply Rmult_lt_compat_r; replace 0 with (INR O) by auto; try (apply lt_INR; omega);
    apply Rmult_lt_compat_l; auto; fourier].
   
   apply Rle_trans with (sum (fun i => eM) N); [|rewrite sum_cte; auto with *].
   apply sum_Rle; intros.
   unfold R_dist in HM'.
   rewrite <- Rminus_0_r with (An (n - n0)%nat).
   apply Rlt_le.
   apply HM'.
   replace n with (S p + N)%nat by (unfold p; omega).
   replace (S p + N - n0)%nat with (S p + (N - n0))%nat by omega.
   apply le_trans with (S p); [|omega].
   unfold p.
   apply le_trans with (K - N)%nat; [|omega].
   replace M' with (M - N)%nat by (unfold M; omega).
   apply minus_le_compat_r.
   unfold K; apply le_trans with (max (S N) M); auto with *.
  
  replace (e / 4) with (eN * (lna + 1)) by (unfold eN; field; auto with *).
  unfold dab.
  apply Rle_lt_trans with (sum (fun i => Rabs (An (n - (i + S N))%nat) * eN) p).
   apply sum_Rle; intros.
   rewrite Rmult_comm.
   rewrite Rabs_mult.
   apply Rmult_le_compat_l; [apply Rabs_pos|].
   apply Rlt_le; apply HN; omega.
   
   rewrite <- scal_sum.
   apply (Rmult_lt_compat_l _ _ _ eNpos).
   eapply Rle_lt_trans; [|apply Rlt_plus_1].
   replace (sum (fun i => Rabs (An (n - (i + S N))%nat)) p)
     with (sum (fun i => Rseq_abs An (p - i)%nat) p)
     by (apply Rsum_eq_compat; intro; replace (n - (n0 + S N))%nat with (n - S N - n0)%nat by omega; trivial).
   rewrite Rseq_reverse.
   apply growing_ineq.
    intro i; simpl sum; apply Rplus_le_simpl_l; apply Rabs_pos.
    apply HNA.
 
 rewrite Rabs_mult.
 replace e with (eL * 2 * (Rabs lb + 1)) by (unfold eL; field;
   apply Rgt_not_eq; apply Rle_lt_0_plus_1; apply Rabs_pos).
 cut (Rabs (SAn n - la) < eL).
  intro.
  replace (eL * 2 * (Rabs lb + 1) / 2) with (eL * (Rabs lb + 1)) by field.
  rewrite Rmult_comm.
  apply Rmult_le_0_lt_compat; auto || apply Rabs_pos || apply Rlt_plus_1.
 apply HL.
 apply le_trans with K; auto.
 unfold K; auto with *.
Qed.

(*
Lemma Rser_cv_square_compat Un : {lu | Rser_cv Un lu} -> { luu | Rser_cv (Un*Un) luu}.
Proof.
intros Un Hcv.
*)
(* TODO: 
riemann series : sigma 1/n^a cvg ssi a>1

order rule : n^a un cvg /\ a>1 -> sigma un cvg
sigma un cvg -> sigma un² cvg
sigma un² cvg -> sigma un/n cvg
Stirling
*)

Lemma Rser_pos_maj_cv_shift : forall Un Vn : nat -> R,
  (forall n, 0 <= Un (S n) <= Vn n) -> {lv : R | Rser_cv Vn lv} -> {lu : R | Rser_cv Un lu}.
Proof.
intros Un Vn uposmaj Vncv.
apply Rser_cv_sig_shift_reciprocal_compat.
eapply Rser_pos_maj_cv.
 intro; unfold Rseq_shift; apply (uposmaj n).
 intro; eapply Rle_trans; apply (uposmaj n).
 intro; apply (uposmaj n).
 assumption.
Qed.

(* begin hide *)
Ltac INR_group term := match term with
  | 0 => replace 0 with (INR 0) by trivial
  | 1 => replace 1 with (INR 1) by trivial
  | 2 => replace 2 with (INR 2) by trivial
  | INR ?a * INR ?b => rewrite <- mult_INR
  | INR ?a + INR ?b => rewrite <- plus_INR
  | INR ?a - INR ?b => rewrite <- minus_INR
  | ?a * ?b => try INR_group a; try INR_group b; try rewrite <- mult_INR
  | ?a + ?b => try INR_group a; try INR_group b; try rewrite <- plus_INR
  | ?a - ?b => try INR_group a; try INR_group b; try rewrite <- minus_INR; [|omega]
  | INR ?a => idtac
end.

Ltac INR_solve := match goal with
  | |- INR ?a <> INR ?b => apply not_INR
  | |- INR ?a = INR ?b => let H := fresh in cut (H : a = b); [rewrite H; reflexivity | ]
  | |- ?a <> ?b => try INR_group a; try INR_group b; try apply not_INR
  | |- ?a < ?b => try INR_group a; try INR_group b; try apply lt_INR
  | |- ?a <= ?b => try INR_group a; try INR_group b; apply le_INR
  | |- ?a = ?b => INR_group a; INR_group b; try reflexivity
  | |- ?a = ?b => INR_group a; INR_group b; let H := fresh in cut (H : a = b); [rewrite H; reflexivity | ]
  | |- ?a ?op ?b => INR_group a; INR_group b
  | |- ?a /\ ?b => split; try INR_solve
end; try omega.
(* end hide *)

Lemma Rser_cv_square_inv : {l | Rser_cv (fun i => / INR (S i) ^ 2) l}.
Proof.
eapply Rser_pos_maj_cv_shift with (fun n => / (INR ((S n) * (S (S n))))).
intro n; split.
 apply Rlt_le; apply Rinv_0_lt_compat; apply pow_lt; INR_solve.
 
 apply Rlt_le; apply Rinv_lt_contravar.
  unfold pow; INR_solve; simpl.
  assert (AP : forall a, (O < S a)%nat) by (intro; omega); apply AP.
  
  unfold pow; rewrite Rmult_1_r.
  INR_solve; simpl; omega.
 
 cut ({lv : R | Rser_cv (fun n => / INR (S n) - / (INR (S (S n)))) lv}).
  intros [lv H]; exists lv.
  eapply Rser_cv_eq_compat.
   2: apply H.
   intro n.
   replace (INR (S n * S (S n))) with ((INR (S n)) * (1 + (INR (S n)))) by INR_solve.
   replace (INR (S (S n))) with (1 + (INR (S n))) by INR_solve.
   field; split; INR_solve.
 
 exists 1.
 unfold Rser_cv.
 apply Rseq_cv_eq_compat with (1 - (fun n => (/ (INR (S (S n))))%R))%Rseq.
  intro n.
  unfold Rseq_minus.
  induction n.
   simpl; unfold Rseq_constant; field.
   
   rewrite tech5; rewrite <- IHn.
   repeat rewrite plus_1_S.
   unfold Rseq_constant.
   field; INR_solve.
 
 replace 1 with (1 - 0) by field.
 apply Rseq_cv_minus_compat.
 eapply Rseq_cv_eq_compat.
  2:apply Rseq_constant_cv.
  
  intro n; unfold Rseq_constant; ring.
 
 apply Rseq_cv_pos_infty_inv_compat.
 apply Rseq_subseq_cv_pos_infty_compat with INR.
  assert (Hex : is_extractor (fun i => S (S i))).
    intros n; omega.
  exists (exist _ (fun i => S (S i)) Hex).
   trivial.
  
  eapply Rseq_cv_pos_infty_eq_compat.
   2: apply Rseq_poly_cv.
   2: constructor.
   
   intro n; unfold Rseq_poly.
   field.
Qed.

Lemma Rser_cv_inv_poly d : (2 <= d)%nat -> {l | Rser_abs_cv (Rseq_inv_poly d) l}.
Proof.
intros d Hd.
unfold Rser_abs_cv.
cut ({l | Rser_cv (Rseq_inv_poly d) l}).
 intros [l Hl]; exists l.
 eapply Rser_cv_eq_compat; [|apply Hl]; intro i.
 destruct i; unfold Rseq_abs; symmetry; apply Rabs_right.
  apply Rle_refl.
  
  unfold Rseq_inv_poly.
  apply Rle_ge; apply pow_le.
  apply Rlt_le; apply Rinv_0_lt_compat; INR_solve.
apply Rser_pos_maj_cv_shift with (fun i => / INR (S i) ^ 2).
 unfold Rseq_inv_poly; intro n; rewrite <- Rinv_pow; [|INR_solve].
 split.
  apply Rlt_le; apply Rinv_0_lt_compat; apply pow_lt; INR_solve.
  apply Rle_Rinv.
   unfold pow; INR_solve; simpl mult; apply lt_O_Sn.
   apply pow_lt; INR_solve.
  apply Rle_pow; auto; INR_solve.
apply Rser_cv_square_inv.
Qed.

(*TODO to move and rename *)
Lemma sum_lt : forall Un Vn n, (forall k, Un k < Vn k) ->  
sum_f_R0 Un n < sum_f_R0 Vn n.
Proof.
intros Un Vn n Hlt.
induction n.
 simpl. apply Hlt.

 do 2 rewrite tech5.
 apply Rplus_lt_compat.
  apply IHn.

  apply Hlt.
Qed.

Lemma Rser_Rser_rem_equiv : forall Un Vn x l (H : Rser_cv Vn l) n,
  (forall k, (k > n)%nat -> Un (k - S n)%nat = Vn k) -> 
   Rser_cv Un x -> x = Rser_rem Vn l H n.
Proof.
intros Un Vn x l Hv n Heq Hu.
assert ( Hucv : Rseq_cv Un 0). apply Rser_cv_zero with x. assumption.
unfold Rser_rem.
assert (forall k, (k > n)%nat -> sum_f_R0 Un (k - S n)%nat 
+ sum_f_R0 Vn n = sum_f_R0 Vn k).
 intros k Hk.
 induction Hk. 
  rewrite <- minus_diag_reverse. simpl.
  rewrite (minus_diag_reverse (S n)). rewrite Heq. ring. intuition.
  
  rewrite tech5. rewrite <- IHHk. rewrite <- minus_Sn_m.
  rewrite tech5. repeat rewrite Rplus_assoc. apply Rplus_eq_compat_l.
  rewrite minus_Sn_m. rewrite Heq. ring. intuition. apply Hk. apply Hk.
assert (Rser_cv (Vn - Un)%Rseq (l - x)).
 apply Rser_cv_minus_compat ; assumption.
assert (Rser_cv (Vn - Un)%Rseq (sum_f_R0 Vn n)).
 intros eps Heps. 
 assert (Heps1 : eps / INR (S n) > 0). 
  assert (/INR (S n) > 0) by intuition.
  unfold Rdiv. apply Rmult_gt_0_compat ; assumption.
 destruct (Hucv (eps/INR (S n)) Heps1) as (N, HucvN).
 exists (2 * S n + N)%nat. intros n1 Hn1.
 unfold R_dist, Rseq_minus.
 rewrite minus_sum. rewrite <- H.
  ring_simplify ( sum_f_R0 Un (n1 - S n) + sum_f_R0 Vn n - sum_f_R0 Un n1 - sum_f_R0 Vn n).
  apply Rlt_le_trans with (INR (S n) * (eps / INR (S n))).
   eapply Rlt_le_trans with (sum_f_R0 (fun n0 => eps / INR (S n)) (n)).
    assert (n1 >= 2 * S n)%nat. intuition.
    pose (n2 := (n1 - S n)%nat). fold n2. replace n1 with (n2 + S n)%nat by (unfold n2 ; intuition).
    rewrite <- Rabs_Ropp. rewrite Ropp_minus_distr. unfold Rminus. 
    rewrite Rplus_comm. rewrite <- plus_n_Sm. rewrite plus_comm. 
    rewrite sum_minus. eapply Rle_lt_trans with (sum_f_R0 (fun k : nat => Rabs (Un (S n2 + k)%nat)) n ).
     apply Rsum_abs.

     apply sum_lt. unfold R_dist in HucvN.
     intros k. rewrite <- (Rminus_0_r (Un (S n2 + k)%nat)). apply HucvN.
     unfold n2. assert (n1 - S n >= S n + N)%nat. intuition. intuition.
    
    rewrite sum_cte. right. unfold Rdiv. ring.
   right. field. apply not_0_INR ; intuition.
  intuition.
assert (H2 : l - x = sum_f_R0 Vn n) by (apply (Rseq_cv_unique (sum_f_R0 (Vn - Un)%Rseq)) ; intuition).
rewrite <- H2. ring.
Qed.

(* TODO to move and rename *)
Lemma sum_pos_minus : forall Un n k, (n >= k)%nat ->
  (forall i, (i > k)%nat -> Un i >= 0) ->
    sum_f_R0 Un n - sum_f_R0 Un k >= 0.
Proof.
intros Un n k Hnk Hpos.
induction Hnk.
 right. ring.

 rewrite tech5. rewrite Rplus_comm. unfold Rminus in *. rewrite Rplus_assoc.
 replace 0 with (0 + 0) by intuition.
 apply Rle_ge. apply Rplus_le_compat ; intuition.
Qed.

Lemma Rser_rem_pos : forall Un k lu (Hlu : Rser_cv Un lu) , 
  (forall n, (n > k)%nat -> Un n >= 0) ->
   {n | (n > k)%nat /\ Un n > 0} ->
    Rser_rem Un lu Hlu k > 0.
Proof.
intros Un k lu Hlu Hpos Hstrict.
unfold Rser_cv, Rseq_cv in Hlu.
unfold Rser_rem.
destruct Hstrict as [n1 [Hn1k Heps]].
destruct (Hlu (Un n1) Heps) as (N, Hlu1).
assert (H2 : {n | n >= N /\ n >= S n1}%nat) by (exists (max N (S n1)) ; intuition).
destruct H2 as [n [HnN Hnk]].
generalize (Hlu1 n HnN). intros H5.
replace (lu - sum_f_R0 Un k) with ((lu - sum_f_R0 Un n) + (sum_f_R0 Un n - sum_f_R0 Un k)) by ring.
replace 0 with (-Un (n1) + Un (n1)) by intuition.
apply Rplus_lt_le_compat.
 unfold R_dist, Rabs in *. destruct (Rcase_abs (sum_f_R0 Un n - lu)) ; fourier.
 
 intuition. clear HnN H5. 
 induction Hnk.
  rewrite tech5. rewrite sum_N_predN ; [|inversion Hn1k ; intuition].
  unfold Rminus. rewrite Rplus_comm. repeat rewrite <- Rplus_assoc.
  replace (Un n1) with (0 + Un n1) by intuition. rewrite Rplus_assoc.
  apply Rplus_le_compat.
   rewrite Rplus_comm. apply Rge_le. apply sum_pos_minus ; intuition.
   
   ring_simplify. replace (Un n1) with (Un n1 + 0) by intuition.
   apply Rplus_le_compat ; intuition.
 
 apply Rle_trans with (sum_f_R0 Un m - sum_f_R0 Un k).
  apply IHHnk.

  rewrite tech5. ring_simplify.
  assert (Un (S m) >= 0) by intuition. fourier.
Qed.

Lemma Rser_rem_lt_le : forall Un lu lv (n : nat) Vn 
  (Hlu : Rser_cv Un lu) (Hlv : Rser_cv Vn lv),
   (forall k, (k > n)%nat -> Un k <= Vn k) ->
    {k | (k > n)%nat /\ Un k < Vn k} ->
     Rser_rem Un lu Hlu n < Rser_rem Vn lv Hlv n.
Proof.
intros Un lu lv n Vn Hlu Hlv Hle Hlt.
assert (Rser_cv (Vn - Un)%Rseq (lv - lu)).
 apply Rser_cv_minus_compat ; assumption.

assert (Hpos : (forall k, (k > n)%nat -> Vn k - Un k >= 0)). 
 intros. apply Rge_minus. apply Rle_ge. apply Hle. assumption.

apply Rminus_gt. generalize (Rser_rem_minus_compat Vn Un lv lu Hlv Hlu n).
intros Hrewrite. unfold Rseq_minus in Hrewrite. rewrite Hrewrite.
apply Rser_rem_pos. 
 apply Hpos. 

 destruct Hlt as [k [Hkn Hlt]].
exists k. 
split. 
 apply Hkn.

 apply Rgt_minus. apply Hlt.
Qed.

(* begin hide *)
Lemma seq_exist_subproof :  forall Un Vn n, 
  (forall k, (k > n)%nat -> Vn k <= Un (k - S n)%nat) ->
    {k | (k > n)%nat /\ Vn k < Un (k - S n)%nat} ->
      {Wn : (nat -> R)&{k | (forall k1, Vn k1 + Wn k1 = Un (k1 - S n)%nat /\ 
        ((k1 > n)%nat -> Wn k1 >= 0)) /\
          (k > n)%nat /\ Wn k > 0}}.
Proof.
intros Un Vn n Hle Hlt.
pose (Un1 := fun k => Un (k - S n)%nat).
pose (Wn := (Un1 - Vn)%Rseq).
destruct Hlt as [k [Hnk Hlt]].
exists Wn. exists k.
split. 
 unfold Wn. unfold Rseq_minus, Un1; intuition.
 apply Rge_minus. apply Rle_ge. apply Hle. assumption.

 split ; [assumption|unfold Wn, Rseq_minus, Un1].
 apply Rgt_minus. assumption.
Qed.

Lemma Rsum_eq_compat1 :  forall Un Vn n, 
  (forall k, (k <= n)%nat -> Un k = Vn k) ->
    sum_f_R0 Un n = sum_f_R0 Vn n.
Proof.
intros Un Vn n Hk.
induction n.
 simpl. apply Hk ; intuition.

 do 2 rewrite tech5.
 rewrite IHn. rewrite Hk. ring.
  intuition.
  intuition.
Qed.

Lemma sum_reorder_0 : forall Un n N, (n <= N)%nat -> 
  sum_f_R0 (fun k0 : nat => Un (k0 - N)%nat) n =
    INR (S n) * Un O.
Proof.
intros Un n N HnN.
induction n.
 simpl ; ring.

 rewrite tech5. rewrite IHn ; intuition.
 do 3 rewrite S_INR.
 inversion HnN.
  rewrite minus_diag. ring.
   
  rewrite not_le_minus_0. 
   ring.
   intuition.
Qed.   

Lemma Rser_cv_reorder : forall n Un l, 
  Rser_cv Un l ->
    Rser_cv (fun k => Un (k - S n)%nat) (l + INR (S n) * (Un O)).
Proof.
intros n Un l Uncv.
intros eps Heps.
destruct (Uncv eps Heps) as (N, Hn).
exists (S n + N)%nat.
intros k Hk.
assert (HkN : (k >= N)%nat) by intuition.
generalize (Hn k HkN) ; intros Hcv.
unfold R_dist in *.
assert (forall k n, (k >= S n)%nat -> sum_f_R0 (fun k0 : nat => Un (k0 - S n)%nat) k =
  sum_f_R0 Un (k - S n) + INR (S n) * Un O).
 intros m n0 Hmn0.
 induction Hmn0.
  induction n0.
   simpl. ring.
   
   rewrite sum_reorder_0. repeat rewrite S_INR.
    rewrite <- minus_diag_reverse.
    simpl. ring.
    
    intuition.
   rewrite tech5. rewrite IHHmn0. rewrite <- minus_Sn_m.
    rewrite tech5. ring.

    intuition.
  rewrite H. ring_simplify (sum_f_R0 Un (k - S n) + INR (S n) * Un 0%nat - (l + INR (S n) * Un 0%nat)).
   assert (k - S n >= N)%nat by intuition. 
   generalize (Hn (k - S n)%nat H0). intuition.
   
   intuition.
Qed.
(* end hide *)

Lemma Rser_Rser_rem_lt_le : forall Un Vn x l (H : Rser_cv Vn l) n,
  (forall k, (k > n)%nat -> Vn k <= Un (k - S n)%nat) ->
   {k | (k > n)%nat /\ Vn k < Un (k - S n)%nat} ->
    Rser_cv Un x -> Rser_rem Vn l H n < x.
Proof.
intros Un Vn x l Hv n Hle Hlt Hu.
destruct (seq_exist_subproof Un Vn n Hle Hlt) as (Wn, [k2 [Hwn11 [Hwn2 Hwn3]]]).
assert (Hwn :  Rser_cv Wn (x + INR (S n) * (Un O) - l)).
 assert (H1 : Rser_cv (fun k => Un (k - S n)%nat) (x + INR (S n) * (Un O))).
  apply Rser_cv_reorder. assumption.
 
 apply Rser_cv_eq_compat with ((fun k => Un (k - S n)%nat) - Vn)%Rseq.
  intros k. generalize (Hwn11 k) ; intros Hwn1. destruct Hwn1 as (Hwn1, _).
  unfold Rseq_minus. rewrite <- Hwn1. ring.

  apply Rser_cv_minus_compat ; intuition.
pose (l1 := x + INR (S n) * Un 0%nat - l).
assert (H1 : Rser_cv (Vn + Wn)%Rseq (l + l1)).
 apply Rser_cv_plus_compat ; assumption.

rewrite (Rser_Rser_rem_equiv Un (Vn + Wn)%Rseq x (l + l1) H1 n).
 apply Rser_rem_lt_le. 
  unfold Rseq_plus. intuition.
  replace (Vn k) with (Vn k + 0) by intuition.
  apply Rplus_le_compat.
   intuition. 

   destruct (Hwn11 k) as (_, Hwn1). destruct (Hwn1 H) ; intuition.

  destruct Hlt as (k, H2). exists k ; intuition.
  destruct (Hwn11 k) as (Hwn1, Hwn5). unfold Rseq_plus. rewrite Hwn1. intuition.

 intros k Hkn.
 destruct (Hwn11 k) as (Hwn1, Hwn5). unfold Rseq_plus. rewrite Hwn1. intuition.

 assumption.
Qed.


