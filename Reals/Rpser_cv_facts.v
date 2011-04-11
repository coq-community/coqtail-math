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
Require Import Rpser_def Rpser_base_facts Rsequence_facts.
Require Import Rpow_facts.
Require Import Fourier.

Require Import Max Min.
Require Import RIneq.
Require Import Ranalysis_def.
Require Import RFsequence RFsequence_facts.

Open Scope Rseq_scope.
Open Scope R_scope.

(** * Abel's lemma : convergence of the power serie inside the cv-disc *)

Lemma Cauchy_crit_partial_sum : forall (An : nat -> R) (r : R), 
     Cv_radius_weak An r -> forall x, Rabs x < r ->
     Cauchy_crit (sum_f_R0 (gt_Pser An x)).
Proof.
intros An r Rho x x_ub eps eps_pos.
 case (Req_or_neq r) ; intro r_0.
 exists 0%nat ; apply False_ind ; rewrite r_0 in x_ub ; assert (0 <= Rabs x). apply Rabs_pos. fourier.
assert (Hrew_abs : Rabs (x / r) = Rabs x / r).
 unfold Rdiv ; rewrite Rabs_mult ; apply Rmult_eq_compat_l ; apply Rabs_right ;
 apply Rgt_ge ; apply Rlt_gt ; apply Rinv_0_lt_compat ; apply Rle_lt_trans with (Rabs x) ;
 [apply Rabs_pos | assumption].
assert (Rabsx_r_lt_1 : Rabs x / r < 1).
 assert (Temp : forall a b, b > 0 -> a < b -> a / b < 1).
  clear ; intros a b b_neq a_lt_b ; replace 1 with (b * / b).
  unfold Rdiv ; apply Rmult_lt_compat_r ; [apply Rinv_0_lt_compat |] ; assumption.
  apply Rinv_r ; apply Rgt_not_eq ; assumption.
 case (Req_or_neq x) ; intro H.
 rewrite H ; rewrite Rabs_R0 ; unfold Rdiv ; rewrite Rmult_0_l ; intuition.
 apply Temp ; [apply Rle_lt_trans with (Rabs x) ; [apply Rabs_pos |] |] ; assumption.
 assert (Hrew : forall m n, m <> n -> R_dist (sum_f_R0 (gt_Pser An x) n) (sum_f_R0 (gt_Pser An x) m)
               = Rabs (sum_f_R0 (fun i => (gt_Pser An x) (S (min m n) + i)%nat) ((max m n) - S (min m n)))).
  intros m n m_neq_n ; unfold R_dist.
   case (le_lt_dec m n) ; intro s.
   assert (H := le_lt_or_eq _ _ s) ; case H ; clear H s ; intro s.
   apply Rabs_eq_compat ; replace (min m n) with m.
   replace (max m n) with n. 
   rewrite tech2 with (m:=m).
   assert (Temp : forall a b, a + b - a = b).
    intros a b ; field.
   apply Temp.
   assumption.
   symmetry ; apply max_r ; intuition.
   symmetry ; apply min_l ; intuition.
   apply False_ind ; exact (m_neq_n s).
   rewrite <- Rabs_Ropp ; apply Rabs_eq_compat ; replace (min m n) with n.
   replace (max m n) with m.
   assert (Hrew := tech2 (gt_Pser An x) n m s) ; rewrite Hrew.
   unfold Rminus ; rewrite Ropp_plus_distr.
   rewrite Ropp_involutive ; rewrite <- Rplus_assoc ; rewrite Rplus_opp_l.
   intuition.
   symmetry ; apply max_l ; intuition.
   symmetry ; apply min_r ; intuition.
 assert (Hineq : exists M, forall m n, m <> n -> R_dist (sum_f_R0 (gt_Pser An x) n) (sum_f_R0 (gt_Pser An x) m)
        <= M * sum_f_R0 (fun i : nat => pow (Rabs x / r) (S (min m n) + i)) ((max m n) - S (min m n))).
  elim Rho ; intros M HM ; exists M ; intros m n m_neq_n.
  rewrite Hrew ; [| assumption].
  assert (H : forall n, Rabs (An n * r^n) <= M).
   intro u ; apply HM ; exists u ; unfold gt_abs_Pser ; reflexivity.
  assert (Temp : forall k n, Rabs (sum_f_R0 (fun i : nat => gt_Pser An x (k + i)) n) <=
       M * sum_f_R0 (fun i : nat => pow (Rabs x / r) (k + i)) n).
   clear -H Hrew_abs r_0 ; intros k n ; induction n.
   simpl ; replace (k+0)%nat with k%nat by intuition ; unfold gt_Pser.
   replace (An k * x ^ k) with ((An k * r ^ k) * (x / r) ^ k).
   rewrite Rabs_mult ; rewrite <- Hrew_abs ; rewrite RPow_abs ; apply Rmult_le_compat_r ;
   [apply Rabs_pos | apply H].
   repeat (rewrite Rmult_assoc) ; apply Rmult_eq_compat_l.
   unfold Rdiv ; rewrite Rpow_mult_distr ; rewrite Rmult_comm ; rewrite Rmult_assoc ;
   rewrite <- Rmult_1_r ; apply Rmult_eq_compat_l.
   rewrite <- Rpow_mult_distr ; rewrite Rinv_l ; [apply pow1 | assumption].
   simpl ; apply Rle_trans with (M * sum_f_R0 (fun i : nat => pow (Rabs x / r) (k + i)) n
          + Rabs (gt_Pser An x (k + S n))).
   apply Rle_trans with (Rabs (sum_f_R0 (fun i : nat => gt_Pser An x (k + i)) n)
          + Rabs (gt_Pser An x (k + S n))) ; [apply Rabs_triang | apply Rplus_le_compat_r ;
   assumption].
   rewrite Rmult_plus_distr_l ; apply Rplus_le_compat_l. 
   unfold gt_Pser ; replace (An (k + S n)%nat * x ^ (k + S n)) with
          ((An (k + S n)%nat * r ^ (k + S n)) * (x / r) ^ (k + S n)).
   rewrite Rabs_mult ; rewrite <- RPow_abs ; rewrite <- Hrew_abs ;
   apply Rmult_le_compat_r ; [rewrite RPow_abs ; apply Rabs_pos | apply H].
   repeat (rewrite Rmult_assoc) ; apply Rmult_eq_compat_l.
   unfold Rdiv ; rewrite Rpow_mult_distr ; rewrite Rmult_comm ; rewrite Rmult_assoc ;
   rewrite <- Rmult_1_r ; apply Rmult_eq_compat_l.
   rewrite <- Rpow_mult_distr ; rewrite Rinv_l ; [apply pow1 | assumption].
   apply Temp.
  assert (Main :  exists M : R, forall m n : nat, m <> n ->
        R_dist (sum_f_R0 (gt_Pser An x) n) (sum_f_R0 (gt_Pser An x) m) <=
        M * ((Rabs x / r) ^ (S (min m n)) * (1 - (Rabs x / r) ^ (S (max m n - S (min m n)))) / (1 - (Rabs x / r)))).
   elim Hineq ; intros M HM ; exists M ; intros m n m_neq_n.
   assert (HM' := HM m n m_neq_n).
   rewrite sum_pow in HM'. apply HM'.
    apply Rlt_not_eq ; assumption.
 clear Hineq Hrew.
  assert (Final : exists M : R, 0 < M /\ forall m n : nat,
       m <> n ->
       R_dist (sum_f_R0 (gt_Pser An x) n) (sum_f_R0 (gt_Pser An x) m) <=
       (Rabs x / r) ^ S (min m n) * (M * 2 / (1 - Rabs x / r))).
    elim Main ; intros M HM ; exists (Rmax M 1) ; split ; [apply Rlt_le_trans with 1 ;
    [intuition | apply RmaxLess2 ] | intros m n m_neq_n].
    assert (Temp : (1 - (Rabs x / r) ^ S (max m n - S (min m n))) <= 2).
    apply Rle_trans with (Rabs (1 - (Rabs x / r) ^ S (max m n - S (min m n)))) ;
    [apply RRle_abs |].
    apply Rle_trans with (Rabs 1 + Rabs (- (Rabs x / r) ^ S (max m n - S (min m n)))) ;
    [apply Rabs_triang | rewrite Rabs_R1 ; apply Rplus_le_compat_l].
    rewrite Rabs_Ropp ; rewrite <- RPow_abs ; rewrite <- Hrew_abs ; rewrite Rabs_Rabsolu ;
    replace 1 with (1 ^  S (max m n - S (min m n))) ; [apply pow_le_compat | apply pow1].
    apply Rabs_pos.
    apply Rlt_le ; rewrite Hrew_abs ; assumption.
   apply Rle_trans with (M * ((Rabs x / r) ^ S (min m n) *
      (1 - (Rabs x / r) ^ S (max m n - S (min m n))) / (1 - Rabs x / r))) ; [apply HM ; assumption |].
  clear Main HM ; rewrite Rmult_comm ; unfold Rdiv ; repeat (rewrite Rmult_assoc) ;
  apply Rmult_le_compat_l ; [ unfold Rdiv in Hrew_abs ; rewrite <- Hrew_abs ;
  rewrite RPow_abs ; apply Rabs_pos |].
  apply Rle_trans with ((1 - (Rabs x * / r) ^ S (max m n - S (min m n))) * (/ (1 - Rabs x * / r) * (Rmax M 1))).
  apply Rmult_le_compat_l.
  unfold Rdiv in Hrew_abs ; rewrite <- Hrew_abs, RPow_abs.
  apply Rlt_le ; apply Rgt_minus.
  rewrite <- RPow_abs.
  case (Req_or_neq x) ; intro H.
  rewrite H ; rewrite Rmult_0_l ; rewrite Rabs_R0 ; rewrite pow_i ; intuition.
  replace 1 with (1 ^ S (max m n - S (min m n))).
  apply pow_lt_compat.
  apply Rabs_pos_lt.
  apply Rmult_integral_contrapositive_currified ; [assumption |].
  apply Rgt_not_eq ; apply Rinv_0_lt_compat ; apply Rle_lt_trans with (Rabs x) ;
  [apply Rabs_pos | assumption].
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
  apply Rinv_0_lt_compat ; fourier.
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
   fourier.
   apply Rinv_0_lt_compat.
   apply Rgt_minus ; rewrite <- Hrew_abs ; assumption.
   rewrite <- Hrew_abs ; rewrite RPow_abs ; rewrite Hrew_abs ; apply HN ; assumption.
   replace (eps / (4 * M) * (1 - Rabs x / r) * (M * 2 / (1 - Rabs x / r))) with
       (eps * (/2 * (/(2*M) * (2*M) * ((1 - Rabs x / r) / (1 - Rabs x / r))))).
   replace (/ (2 * M) * (2 * M)) with 1.
   rewrite Rmult_1_l ; unfold Rdiv ; rewrite Rinv_r.
   fourier.
   apply Rgt_not_eq ; apply Rgt_minus ; unfold Rdiv in Hrew_abs ; rewrite <- Hrew_abs ; assumption.
   symmetry ; apply Rinv_l ; apply Rgt_not_eq ; fourier.
   field ; split ; [|split].
   apply Rgt_not_eq ; apply Rle_lt_trans with (Rabs x) ; [apply Rabs_pos | assumption].
   apply Rgt_not_eq ; apply Rgt_minus ; assumption.
   apply Rgt_not_eq ; assumption.
Qed.

Lemma Rpser_abel : forall (An : nat -> R) (r : R), 
     Cv_radius_weak An r -> forall x, Rabs x < r -> {l | Pser An x l}.
Proof.
intros An r Rho x x_ub.
  apply R_complete ; apply Cauchy_crit_partial_sum with r ; assumption.
Qed.

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
  unfold gt_abs_Pser ; rewrite Rabs_mult.
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
  intros x Hx ; destruct Hx as (n,Hn) ; rewrite Hn ; unfold gt_abs_Pser ; destruct n.
  right ; apply Rabs_eq_compat ; ring.
  destruct (Req_dec r 0) as [Hr | Hf].
  rewrite Hr ; unfold gt_abs_Pser ; rewrite Rabs_mult, <- RPow_abs,
  Rabs_R0, pow_i, Rmult_0_r ; [apply Rabs_pos | intuition].
  apply False_ind ; assert (T := Rabs_no_R0 _ Hf) ;
  apply T ; symmetry ; assumption.
Qed.

Lemma Rpser_alembert_prelim2 : forall (An : nat -> R) (M : R),
       0 < M -> (forall n : nat, An n <> 0) ->
       Rseq_eventually (fun Un => Rseq_bound Un M) (fun n => (An (S n) / An n)) ->
       forall r, Rabs r < / M -> Cv_radius_weak An r.
Proof.
intros An M M_pos An_neq An_frac_event r r_bd.
destruct An_frac_event as [N HN].
 assert (Rho : Cv_radius_weak (fun n => (An (N + n)%nat)) r).
  apply Rpser_alembert_prelim with M.
  assumption.
  intro n ; apply An_neq.
  intro n ; replace (N + S n)%nat with (S (N + n)) by intuition ; apply HN.
  assumption.
  apply Cv_radius_weak_padding_neg_compat with N ;
 destruct Rho as [T HT] ; exists T ; intros u Hu ; destruct Hu as [n Hn] ;
 rewrite Hn ; unfold gt_abs_Pser ; rewrite plus_comm ; apply HT ;
 exists n ; reflexivity.
Qed.

Lemma Rpser_alembert_prelim3 : forall (An : nat -> R) (lambda : R),
       0 < Rabs (lambda) -> (forall n : nat, An n <> 0) ->
       Rseq_cv (fun n : nat => Rabs (An (S n) / An n)) (Rabs lambda) -> forall r,
       Rabs r < / (Rabs lambda) -> Cv_radius_weak An r.
Proof.
intros An lam lam_pos An_neq An_frac_cv r r_bd.
 assert (middle_lb := proj1 (middle_is_in_the_middle _ _ r_bd)).
 assert (middle_ub := proj2 (middle_is_in_the_middle _ _ r_bd)).
 assert (middle_pos : 0 < middle (Rabs r) (/ Rabs lam)).
  apply Rle_lt_trans with (Rabs r) ; [apply Rabs_pos | assumption].
 pose (eps := (/ (middle (Rabs r) (/ Rabs lam)) - Rabs lam)%R).
 assert (eps_pos : 0 < eps).
  apply Rgt_minus ; rewrite <- Rinv_involutive.
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat ; [| apply Rinv_0_lt_compat] ; assumption.
  assumption.
  apply Rgt_not_eq ; assumption.
 apply Rpser_alembert_prelim2 with (Rabs lam + eps)%R.
 fourier.
 apply An_neq.
 destruct (An_frac_cv (/ (middle (Rabs r) (/ Rabs lam)) - Rabs lam))%R as [N HN].
 assumption.
 exists N ; intro n.
 apply Rle_trans with (Rabs lam + (Rabs (An (S (N + n)) / An (N + n)%nat)
      - Rabs lam))%R.
 right ; ring.
 apply Rplus_le_compat_l ; apply Rle_trans with
   (R_dist (Rabs (An (S (N + n)) / An (N + n)%nat)) (Rabs lam))%R.
 apply RRle_abs.
 left ; apply HN ; intuition.
 replace (Rabs lam + eps)%R with (/ (middle (Rabs r) (/ Rabs lam)))%R.
 rewrite Rinv_involutive ; [| apply Rgt_not_eq] ; assumption.
 unfold eps ; ring.
Qed.

Lemma Rpser_alembert_prelim4 : forall (An : nat -> R),
       (forall n : nat, An n <> 0) ->
       Rseq_cv (fun n : nat => Rabs (An (S n) / An n)) R0 ->
       infinite_cv_radius An.
Proof.
intros An An_neq An_frac_0 r.
 assert (eps_pos : 0 < /(Rabs r + 1)).
  apply Rinv_0_lt_compat ; apply Rplus_le_lt_0_compat ; [apply Rabs_pos |
  apply Rlt_0_1].
 apply Rpser_alembert_prelim2 with (/(Rabs r + 1))%R.
 assumption.
 apply An_neq.
 destruct (An_frac_0 (/ (Rabs r + 1))%R eps_pos) as [N HN] ; exists N ; intro n.
 apply Rle_trans with (R_dist (Rabs (An (S (N + n)) / An (N + n)%nat)) 0) ; [right |].
 unfold R_dist in |-* ; rewrite Rminus_0_r, Rabs_Rabsolu ; reflexivity.
 left ; apply HN ; intuition.
 rewrite Rinv_involutive ; [fourier |] ; apply Rgt_not_eq ;
 apply Rplus_le_lt_0_compat ; [apply Rabs_pos | apply Rlt_0_1].
Qed.

(** A kind of reciprocal for the Abel's lemma*)
Lemma Rpser_bound_criteria : forall (An : nat -> R) (x l : R),
    Pser An x l -> Cv_radius_weak An x.
Proof.
intros An x l Hxl.
 destruct Hxl with 1 as (N, HN) ; [fourier |].
 assert (H1 : forall n :  nat, (n >= S N)%nat -> gt_abs_Pser An (Rabs x) n <= Rmax 2 (Rabs (An 0%nat) + 1)).
  intros n Hn ; case_eq n ; unfold gt_abs_Pser.
  intro H ; simpl ; rewrite Rmult_1_r ; apply Rle_trans with (Rabs (An 0%nat) +1) ;
   [intuition | apply RmaxLess2].
   intros m Hrew ; replace (Rabs (An (S m) * Rabs x ^ S m)) with (Rabs ((sum_f_R0 (fun n0 : nat => An n0 * x ^ n0) (S m) - l) +
         (l - sum_f_R0 (fun n0 : nat => An n0 * x ^ n0) m))).
   apply Rle_trans with (Rabs (sum_f_R0 (fun n0 : nat => An n0 * x ^ n0) (S m) - l)
         + Rabs (l - sum_f_R0 (fun n0 : nat => An n0 * x ^ n0) m)).
   apply Rabs_triang.
   apply Rle_trans with 2 ; [|apply RmaxLess1] ; apply Rlt_le ; apply Rplus_lt_compat ;
   [| rewrite Rabs_minus_sym] ; apply HN ; intuition.
   simpl sum_f_R0 ; rewrite Rabs_mult ; rewrite RPow_abs ; rewrite Rabs_Rabsolu ;
   rewrite <- Rabs_mult ; apply Rabs_eq_compat.
   unfold Rminus ; repeat (rewrite Rplus_assoc).
   replace (- l + (l + - sum_f_R0 (fun n0 : nat => An n0 * x ^ n0) m)) with
          (- sum_f_R0 (fun n0 : nat => An n0 * x ^ n0) m) by field.
   rewrite <- Rplus_comm ; rewrite Rplus_assoc ; rewrite Rplus_opp_l.
   intuition.
   destruct (Rseq_partial_bound (gt_Pser An x) (S N)) as (B,HB).
   exists (Rmax B (Rmax 2 (Rabs (An 0%nat) + 1))).
   intros y Hy ; destruct Hy as (i,Hi) ; rewrite Hi.
   case (le_lt_dec i (S N)) ; intro Hi_b.
   apply Rle_trans with B ; [apply HB | apply RmaxLess1] ; intuition.
   replace (gt_abs_Pser An x i) with (gt_abs_Pser An (Rabs x) i).
   apply Rle_trans with (Rmax 2 (Rabs (An 0%nat) + 1)) ; [apply H1 | apply RmaxLess2] ; intuition.
   unfold gt_abs_Pser ; rewrite RPow_abs ; rewrite Rabs_mult ; rewrite Rabs_Rabsolu ;
   rewrite <- Rabs_mult ; reflexivity.
Qed.