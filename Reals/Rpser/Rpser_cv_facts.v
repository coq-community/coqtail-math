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

Require Import Reals.
Require Import Rsequence_def.
Require Import Rpser_def Rpser_def_simpl Rpser_base_facts Rsequence_facts.
Require Import Rsequence_sums_facts Rsequence_rewrite_facts.
Require Import Rpow_facts.
Require Import Lra.

Require Import Max Min.
Require Import MyRIneq MyNeq.
Require Import Rinterval.
Require Import RFsequence RFsequence_facts.

Require Import Tactics.

Open Scope Rseq_scope.
Open Scope R_scope.

(** * Abel's lemma : convergence of the power serie inside the cv-disc *)

Lemma Cauchy_crit_Rseq_pps : forall An r, Cv_radius_weak An r ->
  forall x, Rabs x < r -> Cauchy_crit (Rseq_pps An x).
Proof.
intros An r rho x x_ub eps eps_pos.
assert (r_pos : 0 < r).
 apply Rle_lt_trans with (Rabs x) ; [apply Rabs_pos | assumption].
assert (r_neq : 0 <> r) by (apply Rlt_not_eq ; assumption).
assert (Hrew_abs : Rabs (x / r) = Rabs x / r).
 unfold Rdiv ; rewrite Rabs_mult ; apply Rmult_eq_compat_l ; apply Rabs_right ;
 apply Rgt_ge ; apply Rlt_gt ; apply Rinv_0_lt_compat ; apply Rle_lt_trans with (Rabs x) ;
 [apply Rabs_pos | assumption].
assert (Rabsx_r_lt_1 : Rabs x / r < 1).
 rewrite <- (Rinv_r r) ; [| symmetry ; assumption] ; unfold Rdiv ;
 apply Rmult_lt_compat_r ; [apply Rinv_0_lt_compat |] ; assumption.
destruct (Req_or_neq x) as [x_eq | x_neq].
 exists O ; intros ; subst ; do 2 rewrite Rseq_pps_0_simpl ; rewrite R_dist_eq ;
  assumption.
 assert (Temp : forall m n, (m < n)%nat -> R_dist (Rseq_pps An x n) (Rseq_pps An x m)
  = Rabs (Rseq_sum (Rseq_shifts (gt_pser An x) (S (min m n))) ((max m n) - S (min m n)))).
  intros m n m_neq_n ; unfold R_dist ; apply Rabs_eq_compat ;
   replace (max m n) with n. replace (min m n) with m.
   rewrite Rseq_sum_shifts_compat ; unfold Rseq_shifts ;
   replace (S m + (n - S m))%nat with n by lia ; reflexivity.
   symmetry ; apply min_l ; intuition.
   symmetry ; apply max_r ; intuition.
 assert (Hrew : forall m n, m <> n -> R_dist (Rseq_pps An x n) (Rseq_pps An x m)
  = Rabs (Rseq_sum (Rseq_shifts (gt_pser An x) (S (min m n))) ((max m n) - S (min m n)))).
  intros m n m_neq_n ; unfold R_dist ; destruct (le_lt_dec m n) as [mlen | nltm].
   assert (mltn : (m < n)%nat) by (clear -m_neq_n mlen ; lia) ;
    apply Temp ; assumption.
   rewrite Rabs_minus_sym, min_comm, max_comm ; apply Temp ; assumption.
 clear Temp.
 assert (Hineq : exists M, forall m n, m <> n ->
  R_dist (Rseq_pps An x n) (Rseq_pps An x m) <= M *
  Rseq_sum (Rseq_shifts (pow (Rabs x / r)) (S (min m n))) ((max m n) - S (min m n))).
  destruct rho as [B HB] ; exists B ; intros m n m_neq_n ;
   rewrite Hrew ; [| assumption].
   assert (Temp : forall k n, Rabs (Rseq_sum (Rseq_shifts (gt_pser An x) k) n) <=
    B * Rseq_sum (Rseq_shifts (pow (Rabs x / r)) k) n).
    clear - r_neq r_pos Hrew_abs HB; intros k n ; induction n.
    simpl ; do 2 rewrite Rseq_shifts_O ; rewrite <- (Rmult_1_r (gt_pser An x k)),
    <- (Rinv_r (r ^ k)), <- Rmult_assoc, Rabs_mult, Rinv_pow ;
    [| symmetry ; assumption | apply pow_nonzero ; symmetry ; assumption].
    apply Rle_trans with (Rabs (gt_pser An r k) * Rabs (x ^ k) * Rabs ((/ r) ^ k)).
    right ; repeat rewrite <- Rabs_mult ; apply Rabs_eq_compat ;
    unfold gt_pser, Rseq_mult ; ring.
    apply Rle_trans with ((gt_abs_pser An r k) * (Rabs x / r) ^ k).
    right ; rewrite Rmult_assoc ; apply Rmult_eq_compat_l ;
    rewrite <- Hrew_abs, <- Rabs_mult, <- Rpow_mult_distr, RPow_abs ;
    reflexivity.
    apply Rmult_le_compat_r ; [| apply HB ; exists k ; reflexivity].
    apply pow_le ; unfold Rdiv ; apply Rle_mult_inv_pos ; [apply Rabs_pos | assumption].
    apply Rle_trans with (Rabs (Rseq_sum (Rseq_shifts (gt_pser An x) k) n)
      + Rabs (Rseq_shifts (gt_pser An x) k (S n))).
    simpl ; apply Rabs_triang.
    apply Rle_trans with (B * Rseq_sum (Rseq_shifts (pow (Rabs x / r)) k) n
     + B * (Rseq_shifts (pow (Rabs x / r)) k) (S n)).
    apply Rplus_le_compat ; [apply IHn |].
    apply Rle_trans with (gt_abs_pser An r (k + S n) * ((Rabs x / r) ^ (k + S n))).
    right ; unfold Rseq_shifts, gt_abs_pser, gt_pser, Rseq_mult, Rseq_abs.
    repeat rewrite Rabs_mult ; repeat rewrite Rmult_assoc ; apply Rmult_eq_compat_l ;
    rewrite <- Hrew_abs, RPow_abs, <- Rabs_mult ; apply Rabs_eq_compat ; unfold Rdiv ;
    rewrite Rpow_mult_distr, <- Rinv_pow ; [field |] ; [apply pow_nonzero |] ;
    symmetry ; assumption.
    apply Rmult_le_compat_r ; [| apply HB ; exists (k + S n)%nat ; reflexivity].
    unfold Rseq_shifts, Rdiv ; apply pow_le ; apply Rle_mult_inv_pos ;
    [apply Rabs_pos | assumption].
    right ; simpl ; symmetry ; apply Rmult_plus_distr_l.
  apply Temp.
  assert (Main :  exists M : R, forall m n : nat, m <> n ->
        R_dist (Rseq_pps An x n) (Rseq_pps An x m) <=
        M * ((Rabs x / r) ^ (S (min m n)) * (1 - (Rabs x / r)
        ^ (S (max m n - S (min m n)))) / (1 - (Rabs x / r)))).
   destruct Hineq as [B HB] ; exists B ; intros m n m_neq_n.
   specialize (HB m n m_neq_n) ; unfold Rseq_shifts in HB ; rewrite sum_pow in HB ;
   [apply HB | apply Rlt_not_eq ; assumption].
 clear Hineq Hrew.
  assert (Final : exists M : R, 0 < M /\ forall m n : nat, m <> n ->
       R_dist (Rseq_pps An x n) (Rseq_pps An x m) <=
       (Rabs x / r) ^ S (min m n) * (M * 2 / (1 - Rabs x / r))).
   destruct Main as [B HB] ; exists (Rmax B 1) ; split ;
   [apply Rlt_le_trans with 1 ; [lra | apply RmaxLess2] | intros m n m_neq_n].
    assert (Temp : (1 - (Rabs x / r) ^ S (max m n - S (min m n))) <= 2).
    apply Rle_trans with (Rabs (1 - (Rabs x / r) ^ S (max m n - S (min m n)))) ;
    [apply RRle_abs |].
    apply Rle_trans with (Rabs 1 + Rabs (- (Rabs x / r) ^ S (max m n - S (min m n)))) ;
    [apply Rabs_triang | rewrite Rabs_R1 ; apply Rplus_le_compat_l].
    rewrite Rabs_Ropp ; rewrite <- RPow_abs ; rewrite <- Hrew_abs ; rewrite Rabs_Rabsolu ;
    replace R1 with (1 ^  S (max m n - S (min m n))) ; [apply pow_le_compat | apply pow1].
    apply Rabs_pos.
    apply Rlt_le ; rewrite Hrew_abs ; assumption.
   apply Rle_trans with (B * ((Rabs x / r) ^ S (min m n) *
      (1 - (Rabs x / r) ^ S (max m n - S (min m n))) / (1 - Rabs x / r))) ; [apply HB ; assumption |].
  clear HB ; rewrite Rmult_comm ; unfold Rdiv ; repeat (rewrite Rmult_assoc) ;
  apply Rmult_le_compat_l ; [ unfold Rdiv in Hrew_abs ; rewrite <- Hrew_abs ;
  rewrite RPow_abs ; apply Rabs_pos |].
  apply Rle_trans with ((1 - (Rabs x * / r) ^ S (max m n - S (min m n))) * (/ (1 - Rabs x * / r) * (Rmax B 1))).
  apply Rmult_le_compat_l.
  unfold Rdiv in Hrew_abs ; rewrite <- Hrew_abs, RPow_abs.
  apply Rlt_le ; apply Rgt_minus.
  rewrite <- RPow_abs.
  case (Req_or_neq x) ; intro H.
  rewrite H ; rewrite Rmult_0_l ; rewrite Rabs_R0 ; rewrite pow_i ; intuition.
  replace 1 with (1 ^ S (max m n - S (min m n))).
  apply pow_lt_compat.
  apply Rabs_pos.
  unfold Rdiv in Rabsx_r_lt_1 ; rewrite Hrew_abs ; assumption.
  intuition.
  apply pow1.
  apply Rmult_le_compat_l.
  apply Rlt_le ; apply Rinv_0_lt_compat.
  apply Rgt_minus ; intuition.
  apply RmaxLess1.
  rewrite <- Rmult_assoc.
  rewrite Rmult_comm.
  apply Rmult_le_compat_l ; [apply Rle_trans with 1 ; [intuition | apply RmaxLess2] |].
  apply Rmult_le_compat_r.
  apply Rlt_le ; apply Rinv_0_lt_compat.
  apply Rgt_minus ; intuition.
  assumption.
  elim Final ; intros M HM ; destruct HM as (M_pos, HM).
  rewrite <- Hrew_abs in Rabsx_r_lt_1.
  assert (y_pos : 0 < eps / (4 * M) * (1 - Rabs x / r)).
  apply Rmult_lt_0_compat.
  unfold Rdiv ; apply Rmult_lt_0_compat.
  assumption.
  apply Rinv_0_lt_compat ; lra.
  apply Rgt_minus ; rewrite <- Hrew_abs ; assumption.
  elim (pow_lt_1_zero (x/r) Rabsx_r_lt_1 (eps / (4 * M) * (1 - (Rabs x / r))) y_pos) ; intros N HN ;
  exists N ; intros n m n_lb m_lb.
  case (eq_nat_dec m n); intro s.
  rewrite s ; rewrite R_dist_eq ; assumption.
  apply Rle_lt_trans with ((Rabs x / r) ^ S (min m n) * (M * 2 / (1 - Rabs x / r))).
  apply HM ; intuition.
  assert (Temp : (S (min m n) >= N)%nat).
   destruct N.
   intuition.
   apply le_n_S.
   case (min_dec m n) ; intro H ; rewrite H ; apply le_trans with (S N) ; intuition.
   apply Rlt_trans with ((eps / (4 * M) * (1 - Rabs x / r)) * ((M * 2 / (1 - Rabs x / r)))).
   apply Rmult_lt_compat_r.
   apply Rmult_lt_0_compat.
   lra.
   apply Rinv_0_lt_compat.
   apply Rgt_minus ; rewrite <- Hrew_abs ; assumption.
   rewrite <- Hrew_abs ; rewrite RPow_abs ; rewrite Hrew_abs ; apply HN ; assumption.
   replace (eps / (4 * M) * (1 - Rabs x / r) * (M * 2 / (1 - Rabs x / r))) with
       (eps * (/2 * (/(2*M) * (2*M) * ((1 - Rabs x / r) / (1 - Rabs x / r))))).
   replace (/ (2 * M) * (2 * M)) with 1.
   rewrite Rmult_1_l ; unfold Rdiv ; rewrite Rinv_r.
   lra.
   apply Rgt_not_eq ; apply Rgt_minus ; unfold Rdiv in Hrew_abs ; rewrite <- Hrew_abs ; assumption.
   symmetry ; apply Rinv_l ; apply Rgt_not_eq ; lra.
   field ; split ; [|split].
   apply Rgt_not_eq ; apply Rle_lt_trans with (Rabs x) ; [apply Rabs_pos | assumption].
   apply Rgt_not_eq ; apply Rgt_minus ; assumption.
   apply Rgt_not_eq ; assumption.
Qed.

Lemma Rpser_abel : forall (An : nat -> R) (r : R), 
     Cv_radius_weak An r -> forall x, Rabs x < r -> {l | Rpser An x l}.
Proof.
intros An r Rho x x_ub.
  apply R_complete ; apply Cauchy_crit_Rseq_pps with r ; assumption.
Qed.

(** * D'Alembert's criterion *)

Lemma Rpser_alembert_prelim : forall (An : nat -> R) (M : R),
       0 < M -> (forall n : nat, An n <> 0) ->
       Rseq_bound (fun n => (An (S n) / An n)) M -> forall r,
       Rabs r < / M -> Cv_radius_weak An r.
Proof.
intros An M M_pos An_neq An_frac_ub r r_bd.
 assert (r_lb := Rabs_pos r) ; case r_lb ; clear r_lb ; intro rabs_lb.
 assert (my_lam : 0 < /Rabs r - M).
 apply Rgt_minus ; rewrite <- Rinv_involutive.
 apply Rinv_lt_contravar.
 apply Rmult_lt_0_compat ; [| apply Rlt_trans with (Rabs r)] ; assumption.
 assumption.
 apply Rgt_not_eq ; assumption.
 exists (Rabs (An 0%nat)) ; intros x Hyp ;
  elim Hyp ; intros n Hn ; rewrite Hn ;
  unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult ; rewrite Rabs_mult.
  clear Hn ; induction n.
  simpl ; rewrite Rabs_R1 ; rewrite Rmult_1_r ; right ; reflexivity.
  apply Rle_trans with (Rabs (An (S n) / (An n)) * Rabs (An n) * Rabs (r ^ S n)).
  right ; repeat rewrite <- Rabs_mult ; apply Rabs_eq_compat ;
  field ; apply An_neq.
  apply Rle_trans with (M * Rabs (An n) * Rabs (r ^ S n)).
  repeat apply Rmult_le_compat_r ; [| | apply An_frac_ub] ; apply Rabs_pos.
  simpl ; rewrite Rabs_mult.
  apply Rle_trans with (M * Rabs (An n) * (/M * Rabs (r ^ n))).
  repeat rewrite <- Rmult_assoc ; apply Rmult_le_compat_r ; [apply Rabs_pos |
  repeat rewrite Rmult_assoc ; repeat apply Rmult_le_compat_l].
  left ; assumption.
  apply Rabs_pos.
  left ; assumption.
  apply Rle_trans with (Rabs (An n) * Rabs (r ^ n))%R ; [right ; field ;
  apply Rgt_not_eq |] ; assumption.
 exists (Rabs (An 0%nat)).
  intros x Hx ; destruct Hx as (n,Hn) ; rewrite Hn ; destruct n.
  apply gt_abs_pser_0_ub.
  destruct (Req_dec r 0) as [Hr | Hf].
  rewrite Hr ; apply gt_abs_pser_0_ub.
  apply False_ind ; assert (T := Rabs_no_R0 _ Hf) ;
  apply T ; symmetry ; assumption.
Qed.

Lemma Rseq_cv_bounded : forall Un l, l <> 0 ->
  Rseq_cv Un l -> forall k, 1 < k ->
  Rseq_eventually (fun un => forall n, (Rabs l) / k < Rabs (un n)) Un.
Proof.
intros Un l l_neq Hl k k_lb.
pose (eps := (k - 1) / k * Rabs l).
assert (eps_pos : 0 < eps).
 unfold eps ; apply Rmult_lt_0_compat ;
 [unfold Rdiv ; apply Rlt_mult_inv_pos ;
 [ | apply Rlt_trans with 1] | apply Rabs_pos_lt] ;
 intuition ; lra.
destruct (Hl _ eps_pos) as [N HN] ; exists N ; intros n.
apply Rle_lt_trans with (Rabs l - eps).
unfold eps, Rdiv ; right ; field ; apply Rgt_not_eq ;
 apply Rlt_trans with 1 ; lra.
apply R_dist_gt_r ; apply HN ; intuition.
Qed.


(* TODO: move *)
Lemma Rseq_cv_pos_infty_le_compat : forall Un Vn,
  (forall n, Un n <= Vn n) -> Rseq_cv_pos_infty Un ->
  Rseq_cv_pos_infty Vn.
Proof.
intros Un Vn Hle Un_inf M ; destruct (Un_inf M) as [N HN] ; exists N ;
 intros n n_lb ; apply Rlt_le_trans with (Un n) ;
 [apply HN | apply Hle] ; assumption.
Qed.

Lemma Rpser_alembert_prelim2 : forall (An : nat -> R) (M : R),
       0 < M -> (forall n : nat, An n <> 0) ->
       Rseq_eventually (fun Un => Rseq_bound Un M) (fun n => (An (S n) / An n)) ->
       forall r, Rabs r < / M -> Cv_radius_weak An r.
Proof.
intros An M M_pos An_neq An_frac_event r r_bd.
destruct An_frac_event as [N HN].
 assert (Rho : Cv_radius_weak (Rseq_shifts An N) r).
  apply Rpser_alembert_prelim with M.
  assumption.
  intro n ; apply An_neq.
  intro n ; unfold Rseq_shifts ; replace (N + S n)%nat
   with (S (N + n)) by intuition ; apply HN.
  assumption.
  rewrite Cv_radius_weak_shifts_compat.
 destruct Rho as [T HT] ; exists T ; intros u Hu ; destruct Hu as [n Hn] ;
 rewrite Hn ; apply HT ; exists n ; reflexivity.
Qed.

Lemma Rpser_alembert_weak : forall (An : Rseq) (lambda : R),
  lambda <> 0 -> (forall n : nat, An n <> 0) ->
  Rseq_cv (fun n : nat => Rabs (An (S n) / An n)) lambda -> forall r,
  Rabs r < / lambda -> Cv_radius_weak An r.
Proof.
intros An lam lam_neq An_neq An_frac_cv r r_bd.
 assert (lam_pos : 0 < lam).
  apply Rle_neq_lt ; [| symmetry ; exact lam_neq].
  eapply Rseq_positive_limit ; [| eassumption] ; intro n ; compute ;
  (* TODO: BUG? [; simpl] does not reduce [(fun n0 => ...) n] but [. simpl.]
  does. Using [compute] to avoid the problem. *)
  apply Rabs_pos.
 assert (middle_lb := proj1 (middle_is_in_the_middle _ _ r_bd)).
 assert (middle_ub := proj2 (middle_is_in_the_middle _ _ r_bd)).
 assert (middle_pos : 0 < middle (Rabs r) (/ lam)).
  apply Rle_lt_trans with (Rabs r) ; [apply Rabs_pos | assumption].
 pose (eps := (/ (middle (Rabs r) (/ lam)) - lam)%R).
 assert (eps_pos : 0 < eps).
  apply Rgt_minus ; rewrite <- Rinv_involutive.
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat ; [| apply Rinv_0_lt_compat] ; assumption.
  assumption.
  apply Rgt_not_eq ; assumption.
 apply Rpser_alembert_prelim2 with (lam + eps)%R.
 lra.
 apply An_neq.
 destruct (An_frac_cv (/ (middle (Rabs r) (/ lam)) - lam))%R as [N HN].
 assumption.
 exists N ; intro n ; unfold Rseq_shifts.
 transitivity (lam + (Rabs (An (S (N + n)) / An (N + n)%nat) - lam))%R.
 right ; ring.
 apply Rplus_le_compat_l ; apply Rle_trans with
   (R_dist (Rabs (An (S (N + n)) / An (N + n)%nat)) lam)%R.
 apply RRle_abs.
 left ; apply HN ; intuition.
 replace (lam + eps)%R with (/ (middle (Rabs r) (/ lam)))%R.
 rewrite Rinv_involutive ; [| apply Rgt_not_eq] ; assumption.
 unfold eps ; ring.
Qed.

Lemma Rpser_alembert_weak_reciprocal : forall (An : nat -> R) (lambda : R),
       lambda <> 0 -> (forall n : nat, An n <> 0) ->
       Rseq_cv (fun n => Rabs (An (S n) / An n)) lambda -> forall r,
       / lambda < Rabs r -> ~ Cv_radius_weak An r.
Proof.
intros An lam lam_neq An_neq An_frac_ub r r_ld Hf ;
pose (l' := middle 1 (Rabs r * lam)).
assert (lam_pos : 0 < lam).
 apply Rle_neq_lt ; [| symmetry ; exact lam_neq].
 eapply Rseq_positive_limit ; [| eassumption] ; intro n ; compute ;
  (* TODO: BUG? [; simpl] does not reduce [(fun n0 => ...) n] but [. simpl.]
  does. Using [compute] to avoid the problem. *)
 apply Rabs_pos.
assert (rlam_lb : 1 < Rabs r * lam).
 apply Rle_lt_trans with (/ lam * lam).
 right ; field ; apply Rgt_not_eq ; assumption.
 apply Rmult_lt_compat_r ; assumption.
assert (lam_l'_pos : 0 <= lam / l').
 apply Rle_mult_inv_pos ; [| apply Rlt_trans with 1;
 [| apply middle_is_in_the_middle]] ; lra.
destruct (Rseq_cv_bounded _ _ lam_neq An_frac_ub l') as [N H].
 apply middle_is_in_the_middle ; assumption. 
assert (HN : forall n, Rabs (An N) * (lam / l') ^ n <= Rabs (An (N + n)%nat)).
 clear -H lam_pos lam_l'_pos An_neq ; intro n ; induction n.
  simpl ; rewrite plus_0_r, Rmult_1_r ; reflexivity.
  apply Rle_trans with (Rabs (An N) * (lam / l') ^ n * (lam / l')).
  right ; simpl ; ring.
  apply Rle_trans with (Rabs (An (N + n)%nat) * (lam / l')).
  apply Rmult_le_compat_r ; assumption.
  apply Rle_trans with (Rabs (An (N + n)%nat) *
   Rabs (An (N + S n)%nat) * / Rabs (An (N + n)%nat)).
  rewrite Rmult_assoc ; apply Rmult_le_compat_l ; [apply Rabs_pos |].
  rewrite <- Rabs_Rinv, <- Rabs_mult ; [| apply An_neq].
  rewrite <- (Rabs_pos_eq lam), <- (Rabs_Rabsolu ((An (N + S n)%nat)
   * / An (N + n)%nat)), <-plus_n_Sm ; left ; [apply H | assumption].
  right ; field ; apply Rabs_no_R0 ; apply An_neq.
clear H.
assert (r_gt_1: 1 < (lam / l') * Rabs r).
 apply Rlt_le_trans with (Rabs r * lam * / l') ; [| right ; unfold Rdiv ; ring].
 apply Rlt_1_mult_inv ; [apply Rlt_trans with 1 ; [lra |]|] ;
 apply middle_is_in_the_middle ; assumption.
assert (Hinfty : Rseq_cv_pos_infty (gt_abs_pser An r)).
 apply Rseq_cv_pos_infty_shifts_compat with N.
 apply Rseq_cv_pos_infty_le_compat with (Rseq_mult (Rseq_constant (Rabs (An N) * Rabs r ^ N))
  (Rseq_pow (lam / l' * Rabs r))).
 intro n ; unfold Rseq_pow, Rseq_shifts, Rseq_mult, Rseq_constant,
 gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult.
 apply Rle_trans with ((Rabs (An N) * (lam / l') ^ n) * Rabs r ^ (n + N)).
 right; repeat rewrite Rmult_assoc ; apply Rmult_eq_compat_l.
 rewrite Rpow_mult_distr, pow_add ; ring.
 rewrite Rabs_mult, RPow_abs ; rewrite plus_comm ; apply Rmult_le_compat_r ;
 [apply Rabs_pos |] ; apply HN.
 apply Rseq_cv_finite_pos_mult_pos_infty_r with (Rabs (An N) * Rabs r ^ N).
 rewrite RPow_abs, <- Rabs_mult ; apply Rabs_pos_lt ;
 apply Rmult_integral_contrapositive_currified ; [apply An_neq | apply pow_nonzero].
 intro r_eq ; rewrite r_eq, Rabs_R0, Rmult_0_l in rlam_lb ; clear -rlam_lb ; lra.
 apply Rseq_constant_cv.
 apply Rseq_pow_gt_1_cv ; assumption.
destruct Hf as [B HB].
destruct (Hinfty B) as [M HM].
apply (Rlt_irrefl (gt_abs_pser An r M)).
apply Rle_lt_trans with B ; [apply HB ; exists M | apply HM] ; auto.
Qed.

Theorem Rpser_alembert_weak_eventually : forall (An : Rseq) (lambda : R),
  lambda <> 0 -> Rseq_eventually (fun un => forall n : nat, un n <> 0) An ->
  Rseq_cv (fun n : nat => Rabs (An (S n) / An n)) lambda -> forall r,
  Rabs r < / lambda -> Cv_radius_weak An r.
Proof.
intros An lam lam_neq [N An_neq] An_frac_cv r r_bd.
 rewrite Cv_radius_weak_shifts_compat ;
 apply Rpser_alembert_weak with lam ; try (assumption || apply An_neq).
 apply Rseq_cv_eq_compat with (Rseq_shifts (fun n => Rabs (An (S n) / An n)) N).
 intro n ; unfold Rseq_shifts ; rewrite plus_n_Sm ; reflexivity.
 apply Rseq_cv_shifts_compat_reciprocal ; assumption.
Qed.

Theorem Rpser_alembert_weak_reciprocal_eventually : forall (An : Rseq) (lambda : R),
  lambda <> 0 -> Rseq_eventually (fun un => forall n : nat, un n <> 0) An ->
  Rseq_cv (fun n : nat => Rabs (An (S n) / An n)) lambda -> forall r,
  / lambda < Rabs r -> ~ Cv_radius_weak An r.
Proof.
intros An lam lam_neq [N An_neq] An_frac_cv r r_bd Hf.
 assert (H := proj1 (Cv_radius_weak_shifts_compat _ _ N) Hf).
 revert H.
 apply Rpser_alembert_weak_reciprocal with lam ; try assumption.
 apply Rseq_cv_eq_compat with (Rseq_shifts (fun n => Rabs (An (S n) / An n)) N).
 intro n ; unfold Rseq_shifts ; rewrite plus_n_Sm ; reflexivity.
 apply Rseq_cv_shifts_compat_reciprocal ; assumption.
Qed.

Lemma Rpser_alembert_finite : forall (An : Rseq) (lambda : R),
  lambda <> 0 -> (forall n, An n <> 0) ->
  Rseq_cv (| (Rseq_shift An / An) |) lambda ->
  finite_cv_radius An (/ lambda).
Proof.
intros An lam lam_neq An_neq An_l.
assert (lam_pos : 0 < / lam).
 apply Rinv_0_lt_compat ; apply Rle_neq_lt ; [| symmetry ; exact lam_neq].
 eapply Rseq_positive_limit ; [| eassumption] ; intro n ; compute ;
  (* TODO: BUG? [; simpl] does not reduce [(fun n0 => ...) n] but [. simpl.]
  does. Using [compute] to avoid the problem. *)
 apply Rabs_pos.
split.
 intros r' [r'_pos r'_bd] ; apply Rpser_alembert_weak with lam ;
  [| | | rewrite Rabs_pos_eq] ; assumption.
 intros r' r'_lb ; apply Rpser_alembert_weak_reciprocal with lam ;
  [| | | rewrite Rabs_pos_eq ; [| left ; apply Rlt_trans with (/ lam)] ] ; assumption.
Qed.

Lemma Rpser_alembert_finite_eventually : forall (An : Rseq) (lambda : R),
  lambda <> 0 -> Rseq_eventually (fun un => forall n, un n <> 0) An ->
  Rseq_cv (fun n => Rabs (An (S n) / An n)) lambda ->
  finite_cv_radius An (/ lambda).
Proof.
intros An lam lam_neq An_neq An_l.
assert (lam_pos : 0 < / lam).
 apply Rinv_0_lt_compat ; apply Rle_neq_lt ; [| symmetry ; exact lam_neq].
 eapply Rseq_positive_limit ; [| eassumption] ; intro n ; compute ;
  (* TODO: BUG? [; simpl] does not reduce [(fun n0 => ...) n] but [. simpl.]
  does. Using [compute] to avoid the problem. *)
 apply Rabs_pos.
split.
 intros r' [r'_pos r'_bd] ; apply Rpser_alembert_weak_eventually with lam ;
  [| | | rewrite Rabs_pos_eq] ; assumption.
 intros r' r'_lb ; apply Rpser_alembert_weak_reciprocal_eventually with lam ;
  [| | | rewrite Rabs_pos_eq ; [| left ; apply Rlt_trans with (/ lam)] ] ; assumption.
Qed.

(* TODO: move *)
Lemma max_explicit : forall m n, { p | max m n = (m + p)%nat}.
Proof.
intros m n ; destruct (lt_dec m n) ;
 [exists (n - m)%nat | exists 0%nat] ;
 destruct (max_spec m n) ; lia.
Qed.

Lemma Rpser_alembert_infinite : forall (An : Rseq),
       Rseq_eventually (fun un => forall n, un n <> 0) An ->
       Rseq_cv (fun n : nat => Rabs (An (S n) / An n)) R0 ->
       infinite_cv_radius An.
Proof.
intros An [N1 HN1] An_frac_0 r.
assert (eps_pos : 0 < /(Rabs r + 1)).
 apply Rinv_0_lt_compat ; apply Rplus_le_lt_0_compat ; [apply Rabs_pos |
 apply Rlt_0_1].
destruct (An_frac_0 (/ (Rabs r + 1))%R eps_pos) as [N2 HN2].
rewrite (Cv_radius_weak_shifts_compat _ _ (max N1 N2)).
apply Rpser_alembert_prelim with (/ (Rabs r + 1)).
assumption.
intro n ; unfold Rseq_shifts.
destruct (max_explicit N1 N2) as [p Hp] ; rewrite Hp, <- plus_assoc ; apply HN1.
intro n ; unfold Rseq_shifts ; rewrite max_comm ;
 destruct (max_explicit N2 N1) as [p Hp] ; rewrite Hp, <- Rabs_Rabsolu ;
 replace (N2 + p + S n)%nat with (S (N2 + p + n)) by ring ;
 assert (Hyp := HN2 (N2 + p + n)%nat) ; unfold R_dist, Rminus in Hyp ;
 change R0 with (IZR 0) in Hyp;
 rewrite Ropp_0, Rplus_0_r in Hyp ; left ; apply Hyp.
lia.
rewrite Rinv_involutive ; [intuition |].
apply Rgt_not_eq ; apply Rlt_le_trans with (0 + 1) ;
 [| apply Rplus_le_compat_r ; apply Rabs_pos] ; intuition.
Qed.

(** A kind of reciprocal for the Abel's lemma*)
Lemma Rpser_bound_criteria : forall (An : nat -> R) (x l : R),
    Rpser An x l -> Cv_radius_weak An x.
Proof.
intros An x l Hxl.
 destruct (Hxl 1) as [N HN] ; [lra |] ; unfold R_dist in HN.
 assert (H1: forall n, (S N <= n)%nat -> gt_abs_pser An x n <= Rmax 2 (Rabs (An O))).
  intros n n_lb ; destruct n ; unfold gt_abs_pser, Rseq_abs.
   unfold gt_pser, Rseq_mult ; simpl ; rewrite Rmult_1_r ; apply RmaxLess2.
   transitivity (Rabs ((Rseq_pps An x (S n) - l) - (Rseq_pps An x n - l))).
    right ; rewrite Rseq_pps_simpl ; apply Rabs_eq_compat ;
    unfold gt_pser, Rseq_mult ; ring.
   transitivity (Rabs (Rseq_pps An x (S n) - l) + Rabs (- (Rseq_pps An x n - l))).
    apply Rabs_triang.
   transitivity 2 ; [| apply RmaxLess1] ; rewrite Rabs_Ropp.
    apply Rplus_le_compat ; left ; apply HN ; lia.
   destruct (Rseq_partial_bound (gt_pser An x) (S N)) as (B,HB).
   exists (Rmax B (Rmax 2 (Rabs (An O)))).
   intros y [i Hi] ; subst ; destruct (le_lt_dec i (S N)) as [Hi_b | Hi_b].
   apply Rle_trans with B ; [apply HB | apply RmaxLess1] ; intuition.
   apply Rle_trans with (Rmax 2 (Rabs (An O))) ; [apply H1 | apply RmaxLess2] ; intuition.
Qed.
