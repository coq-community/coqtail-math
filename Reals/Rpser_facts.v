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
Require Export Rpser_def.
Require Import Fourier.
Require Import Max.
Require Import Min.
Require Import RIneq.
Require Import Rsequence.
Require Import Rsequence_facts.
Require Import Ranalysis_def.
Require Import RFsequence.
Require Import RFsequence_facts.

Open Scope R_scope.

(** * Tools *)

Definition q_pow_i := fun q n => q ^ n.

Lemma sum_q_pow_i : forall (q : R) (m k : nat),
  q <> 1 ->
  sum_f_R0 (fun i : nat => q_pow_i q (m + i)) k = q^m * (1 - q ^ S k) / (1 - q).
Proof.
intros q m k q_neq_1.
 induction m.
  assert (H := tech3 q k q_neq_1) ; rewrite Rmult_1_l ; rewrite <- H ; unfold q_pow_i ; simpl ;
  apply sum_eq ; intros i i_ub ; intuition.
 replace (sum_f_R0 (fun i : nat => q_pow_i q (S m + i)) k) with (q * (sum_f_R0 (fun i : nat => q_pow_i q (m + i)) k)).
 rewrite IHm ; simpl ; unfold Rdiv ; repeat (rewrite Rmult_assoc) ; repeat (apply Rmult_eq_compat_l) ;
 reflexivity.
 clear ; induction k.
 simpl ; intuition.
 simpl ; rewrite Rmult_plus_distr_l ; rewrite IHk ; apply Rplus_eq_compat_l ; apply Rmult_eq_compat_l.
 unfold q_pow_i ; replace (k + S m)%nat with (S (k + m))%nat by intuition ; simpl ; reflexivity.
Qed.

(** * Abel's lemma : convergence of the power serie inside the cv-disc *)

Lemma Cauchy_crit_partial_sum : forall (An : nat -> R) (r : R), 
     Cv_radius_weak An r -> forall x, Rabs x < r -> Cauchy_crit (sum_f_R0 (gt_Pser An x)).
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
        <= M * sum_f_R0 (fun i : nat => q_pow_i (Rabs x / r) (S (min m n) + i)) ((max m n) - S (min m n))).
  elim Rho ; intros M HM ; exists M ; intros m n m_neq_n.
  rewrite Hrew ; [| assumption].
  assert (H : forall n, Rabs (An n * r^n) <= M).
   intro u ; apply HM ; exists u ; unfold gt_abs_Pser ; reflexivity.
  assert (Temp : forall k n, Rabs (sum_f_R0 (fun i : nat => gt_Pser An x (k + i)) n) <=
       M * sum_f_R0 (fun i : nat => q_pow_i (Rabs x / r) (k + i)) n).
   clear -H Hrew_abs r_0 ; intros k n ; induction n.
   simpl ; replace (k+0)%nat with k%nat by intuition ; unfold gt_Pser, q_pow_i.
   replace (An k * x ^ k) with ((An k * r ^ k) * (x / r) ^ k).
   rewrite Rabs_mult ; rewrite <- Hrew_abs ; rewrite RPow_abs ; apply Rmult_le_compat_r ;
   [apply Rabs_pos | apply H].
   repeat (rewrite Rmult_assoc) ; apply Rmult_eq_compat_l.
   unfold Rdiv ; rewrite Rpow_mult_distr ; rewrite Rmult_comm ; rewrite Rmult_assoc ;
   rewrite <- Rmult_1_r ; apply Rmult_eq_compat_l.
   rewrite <- Rpow_mult_distr ; rewrite Rinv_l ; [apply pow1 | assumption].
   simpl ; apply Rle_trans with (M * sum_f_R0 (fun i : nat => q_pow_i (Rabs x / r) (k + i)) n
          + Rabs (gt_Pser An x (k + S n))).
   apply Rle_trans with (Rabs (sum_f_R0 (fun i : nat => gt_Pser An x (k + i)) n)
          + Rabs (gt_Pser An x (k + S n))) ; [apply Rabs_triang | apply Rplus_le_compat_r ;
   assumption].
   rewrite Rmult_plus_distr_l ; apply Rplus_le_compat_l. 
   unfold gt_Pser, q_pow_i ; replace (An (k + S n)%nat * x ^ (k + S n)) with
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
   rewrite sum_q_pow_i in HM'. apply HM'.
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

(** * Definition of the sum of a power serie (0 outside the convergence disc) *)

Definition weaksum_r (An : nat -> R) (r : R) (Pr : Cv_radius_weak An r) : R -> R.
Proof.
intros An r Rho x.
 case (Rlt_le_dec (Rabs x) r) ; intro x_bd.
 elim (Rpser_abel _ _ Rho _ x_bd) ; intros y Hy ; exact y.
 exact 0.
Defined.

Definition sum_r (An : nat -> R) (r : R) (Pr : finite_cv_radius An r) : R -> R.
Proof.
intros An r Pr x.
 case (Rlt_le_dec (Rabs x) r) ; intro x_bd.
  assert (rho : Cv_radius_weak An (middle (Rabs x) r)).
  apply Pr; split.
  apply Rle_trans with (Rabs x).
   apply Rabs_pos.
   left ; apply (proj1 (middle_is_in_the_middle _ _ x_bd)).
   apply (proj2 (middle_is_in_the_middle _ _ x_bd)).
 apply (weaksum_r An (middle (Rabs x) r) rho x).
 exact 0.
Defined.

Definition sum (An : nat -> R) (Pr : infinite_cv_radius An) : R -> R.
Proof.
intros An Pr r.
 apply (weaksum_r An (Rabs r +1) (Pr (Rabs r + 1)) r).
Defined.

(** Proof that it is really the sum *)

Lemma weaksum_r_sums : forall (An : nat -> R) (r : R) (Pr : Cv_radius_weak An r) (x : R),
      Rabs x < r -> Pser An x (weaksum_r An r Pr x).
Proof.
intros An r Pr x x_bd.
 unfold weaksum_r ; case (Rlt_le_dec (Rabs x) r) ; intro s.
 destruct (Rpser_abel An r Pr x s) as (l,Hl) ; simpl ; assumption.
 apply False_ind ; fourier.
Qed.

Lemma sum_r_sums : forall  (An : nat -> R) (r : R) (Pr : finite_cv_radius An r),
      forall x, Rabs x < r -> Pser An x (sum_r An r Pr x).
Proof.
intros An r Pr x x_ub.
 unfold sum_r ; destruct (Rlt_le_dec (Rabs x) r) as [x_bd | x_nbd].
 apply weaksum_r_sums.
 apply (proj1 (middle_is_in_the_middle _ _ x_bd)).
  apply False_ind ; fourier.
Qed.

Lemma sum_sums : forall  (An : nat -> R) (Pr : infinite_cv_radius An),
      forall x, Pser An x (sum An Pr x).
Proof.
intros An Pr x.
 apply weaksum_r_sums ; intuition.
Qed.


(** Proof that the sum is unique *)

Lemma weaksum_r_unique : forall (An : nat -> R) (r : R) (Pr1 Pr2 : Cv_radius_weak An r) (x : R),
     Rabs x < r -> weaksum_r An r Pr1 x = weaksum_r An r Pr2 x.
Proof.
intros An r Pr1 Pr2 x x_bd ;
 assert (T1 := weaksum_r_sums _ _ Pr1 _ x_bd) ;
 assert (T2 := weaksum_r_sums _ _ Pr2 _ x_bd) ;
 eapply Pser_unique ; eassumption.
Qed.

Lemma weaksum_r_unique_strong : forall (An : nat -> R) (r1 r2 : R) (Pr1 : Cv_radius_weak An r1)
     (Pr2 : Cv_radius_weak An r2) (x : R), Rabs x < r1 -> Rabs x < r2 ->
     weaksum_r An r1 Pr1 x = weaksum_r An r2 Pr2 x.
Proof.
intros An r1 r2 Pr1 Pr2 x x_bd1 x_bd2.
  assert (T1 := weaksum_r_sums _ _ Pr1 _ x_bd1) ;
  assert (T2 := weaksum_r_sums _ _ Pr2 _ x_bd2) ;
 eapply Pser_unique ; eassumption.
Qed.

Lemma sum_r_unique : forall (An : nat -> R) (r : R) (Pr1 Pr2 : finite_cv_radius An r) (x : R),
     Rabs x < r -> sum_r An r Pr1 x = sum_r An r Pr2 x.
Proof.
intros An r Pr1 Pr2 x x_bd ;
 assert (T1 := sum_r_sums _ _ Pr1 _ x_bd) ;
 assert (T2 := sum_r_sums _ _ Pr2 _ x_bd) ;
 eapply Pser_unique ; eassumption.
Qed.

Lemma sum_r_unique_strong : forall (An : nat -> R) (r1 r2 : R) (Pr1 : finite_cv_radius An r1)
     (Pr2 : finite_cv_radius An r2) (x : R), Rabs x < r1 -> Rabs x < r2 ->
     sum_r An r1 Pr1 x = sum_r An r2 Pr2 x.
Proof.
intros An r1 r2 Pr1 Pr2 x x_bd1 x_bd2 ;
 assert (T1 := sum_r_sums _ _ Pr1 _ x_bd1) ;
 assert (T2 := sum_r_sums _ _ Pr2 _ x_bd2) ;
 eapply Pser_unique ; eassumption.
Qed.

Lemma sum_unique : forall (An : nat -> R) (Pr1 Pr2 : infinite_cv_radius An) (x : R),
      sum An Pr1 x = sum An Pr2 x.
Proof.
intros An Pr1 Pr2 x ;
 assert (T1 := sum_sums  _ Pr1 x) ;
 assert (T2 := sum_sums  _ Pr2 x) ;
 eapply Pser_unique ; eassumption.
Qed.

(** Abel's lemma : Normal convergence of the power serie *)

Lemma Rpser_abel2_prelim : forall (An : nat -> R) (r : R), 
     Cv_radius_weak An r -> forall x, Rabs x < r -> { l | Pser (fun n => Rabs (An n)) x l}.
Proof.
intros An r Rho x x_bd ;
 assert (Rho' := Cv_radius_weak_Rabs_compat An r Rho) ;
 pose (l := weaksum_r (fun n => Rabs (An n)) r Rho' x) ;
 exists l ; apply weaksum_r_sums ; assumption.
Qed.

Lemma Rpser_abel2 : forall (An : nat -> R) (r : R), 
     Cv_radius_weak An r -> forall r0 : posreal, r0 < r ->
     CVN_r (fun n x => gt_Pser An x n) r0.
Proof.
intros An r Pr r0 r0_ub.
 destruct r0 as (a,a_pos).
 assert (a_bd : Rabs a < r).
  rewrite Rabs_right ; [| apply Rgt_ge ; apply Rlt_gt] ; assumption.
 assert (r_pos : 0 < r). 
  apply Rlt_trans with a ; assumption.
 assert (r'_bd : Rabs ((a + r) / 2) < r).
  rewrite Rabs_right.
  assert (Hrew : r = ((r+r)/2)) by field ; rewrite Hrew at 2; unfold Rdiv ;
  apply Rmult_lt_compat_r ; [apply Rinv_0_lt_compat ; intuition |] ;
  apply Rplus_lt_compat_r ; rewrite Rabs_right in a_bd ; intuition.
  apply Rle_ge ; unfold Rdiv ; replace 0 with (0 * /2) by field ; apply Rmult_le_compat_r ;
  fourier.
 assert (r'_bd2 : Rabs (Rabs ((a + r) / 2)) < r).
  rewrite Rabs_right ; [assumption | apply Rle_ge ; apply Rabs_pos].
 assert (Pr' := Cv_radius_weak_Rabs_compat _ _ Pr).
 exists (gt_abs_Pser An ((a+r)/2)) ; exists (weaksum_r (fun n => Rabs (An n)) r Pr' (Rabs ((a+r)/2))) ; split.
 assert (H := weaksum_r_sums (fun n => Rabs (An n)) r Pr' (Rabs ((a + r) / 2)) r'_bd2).
 assert (Main := Pser_Rseqcv_link _ _ _ H). 
 intros eps eps_pos ; destruct (Main eps eps_pos) as (N, HN) ; exists N.
  assert (Hrew : forall k, Rabs (gt_abs_Pser An ((a + r) / 2) k) = gt_Pser (fun n0 : nat => Rabs (An n0)) (Rabs ((a + r) / 2)) k).
   intro k ; unfold gt_abs_Pser, gt_Pser ; rewrite Rabs_Rabsolu ; rewrite Rabs_mult ; rewrite RPow_abs ; reflexivity.
  assert (Temp : forall n, sum_f_R0 (fun k : nat => Rabs (gt_abs_Pser An ((a + r) / 2) k)) n
            = sum_f_R0 (gt_Pser (fun n0 : nat => Rabs (An n0)) (Rabs ((a + r) / 2))) n).
   intros n ; clear -Hrew ; induction n ; simpl ; rewrite Hrew ; [| rewrite IHn] ; reflexivity.
  intros n n_lb ; rewrite Temp ; apply HN ; assumption.
 intros n y Hyp ; unfold gt_Pser, gt_abs_Pser ; repeat (rewrite Rabs_mult) ;
 apply Rmult_le_compat_l ; [apply Rabs_pos |] ; repeat (rewrite <- RPow_abs) ;
 apply pow_le_compat ; [apply Rabs_pos |] ; unfold Boule in Hyp ; apply Rle_trans with a ;
 apply Rlt_le ; replace (y-0) with y in Hyp by intuition ; intuition ; rewrite Rabs_right.
 assert (Hrew : a = ((a+a)/2)) by field ; rewrite Hrew at 1; unfold Rdiv ;
  apply Rmult_lt_compat_r ; [apply Rinv_0_lt_compat ; intuition |] ;
  apply Rplus_lt_compat_l ; intuition.
  apply Rle_ge ; unfold Rdiv ; replace 0 with (0 * /2) by field ; apply Rmult_le_compat_r ;
  fourier.
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
Lemma Rpser_bound_criteria (An : nat -> R) (x l : R) :
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

(** A sufficient condition for the radius of convergence*)
Lemma Rpser_finite_cv_radius_caracterization (An : nat -> R) (x0 l : R) :
   Pser An x0 l -> (forall l : R, ~ Pser_abs An x0 l)  -> finite_cv_radius An (Rabs x0).
Proof.
intros An x0 l Hcv Hncv.
split; intros x Hx.

 apply Cv_radius_weak_le_compat with x0.
  rewrite Rabs_pos_eq with x; intuition.
  apply (Rpser_bound_criteria _ _ l Hcv).
  
 intro Hf.
 destruct (Rpser_abel2_prelim An x Hf (Rabs x0)) as [l' Hl'].
 rewrite Rabs_Rabsolu; trivial.
 apply Hncv with l'.
trivial.
Qed.

Lemma Rpser_infinite_cv_radius_caracterization An : (forall x, {l | Pser An x l}) ->
     infinite_cv_radius An.
Proof.
intros An weaksum r ; destruct (weaksum r) as (l, Hl) ; apply Rpser_bound_criteria with l ;
 assumption.
Qed.

(*
  The following lemma uses classical propositions
Require Import Classical.

Lemma cv_radius_decidability : forall An,
     (exists r, finite_cv_radius An r) \/ (infinite_cv_radius An).
Proof.
intro An.
 case (classic (forall r, Cv_radius_weak An r)) ; intro Hyp.
 right ; apply infinite_cv_radius_caracterization ; intro x ; apply Abel with (2* (Rabs x) + 1).
 apply Hyp.
 case (Req_or_neq (Rabs x)) ; intro H.
  rewrite H ; intuition.
  apply Rlt_trans with (2 * Rabs x).
  replace (2 * Rabs x) with (Rabs x + Rabs x) by field.
  apply Rle_lt_trans with (Rabs x + 0).
  intuition.
  apply Rplus_lt_compat_l ; apply Rabs_pos_lt.
  intro Hf ; apply H ; rewrite Hf ; apply Rabs_R0.
  intuition.
  assert (H : ~ (forall r:R, ~~Cv_radius_weak An r)).
   intros Hf ; apply Hyp ; intros r.
  apply (NNPP (Cv_radius_weak An r) (Hf r)).
  assert (Main := not_all_not_ex _ _ H).
  left.
*)

(** * Definition of the formal derivative *)

(* begin hide *)

Lemma Rpser_cv_speed_pow_id : forall x : R, Rabs x < 1 ->
     Un_cv (fun n : nat => INR (S n) *  x ^ S n) 0.
Proof.
intros x x_bd eps eps_pos.
 case (Req_or_neq x) ; intro Hx.
  exists 0%nat ; intros ; unfold R_dist ; rewrite Rminus_0_r ;
  rewrite Hx ; rewrite pow_i ; [| intuition] ; rewrite Rmult_0_r ; rewrite Rabs_R0 ;
  assumption.
 assert (H : Un_cv (fun n => /INR (S n)) 0).
  apply cv_infty_cv_R0.
  intros n Hf ; replace 0 with (INR 0) in Hf by intuition.
  discriminate (INR_eq _ _ Hf).
  intro B ; assert (0 <= IZR (up (Rabs B))).
  apply Rle_trans with (Rabs B) ; [apply Rabs_pos |] ;
  apply Rge_le ; left ; apply (proj1 (archimed (Rabs B))).
  assert (H1 : (0 <= up (Rabs B))%Z).
  apply le_IZR ; assumption.
  destruct (IZN (up (Rabs B)) H1) as (N, HN) ; exists N ;
  intros n n_lb ; apply Rlt_le_trans with (INR (S N)).
  apply Rlt_trans with (IZR (up (Rabs B))).
  apply Rle_lt_trans with (Rabs B) ; [apply RRle_abs |] ;
  apply (proj1 (archimed (Rabs B))).
  rewrite HN.
  rewrite <- INR_IZR_INZ.
  intuition.
  intuition.
  assert (Rinv_r_pos : 0 < (1 + 1 / Rabs x) / 2 - 1).
   apply Rlt_Rminus ; apply Rle_lt_trans with ((1 + 1)/2).
   right ; field.
   unfold Rdiv ; apply Rmult_lt_compat_r.
   apply Rinv_0_lt_compat ; intuition.
   apply Rplus_lt_compat_l ; rewrite Rmult_1_l ; rewrite <- Rinv_1 ;
   apply Rinv_lt_contravar.
   rewrite Rmult_1_r ; apply Rabs_pos_lt ; assumption. 
   assumption.
   pose (k := (1 + Rabs x) / 2).
   assert (k_pos : 0 <= k).
    unfold k ; replace 0 with (0/2) by field ; unfold Rdiv ; apply Rmult_le_compat_r.
    left ; apply Rinv_0_lt_compat ; intuition.
    apply Rle_zero_pos_plus1 ; apply Rabs_pos.
 assert (k_lt_1 : ((1 + Rabs x) / 2) < 1).
  apply Rlt_le_trans with ((1 + 1) /2).
  unfold Rdiv ; apply Rmult_lt_compat_r.
  apply Rinv_0_lt_compat ; intuition.
  apply Rplus_lt_compat_l ; assumption.
  right ; field.
  assert (Main : forall M eps, 0 < eps -> 0 < M -> exists N, forall n, (n >= N)%nat ->
             M * ((1 + Rabs x) / 2) ^ n < eps).
   clear -k_lt_1 k_pos ; intros M eps eps_pos M_pos ;
   assert (r_bd : 0 <= (1 + Rabs x) / 2 < 1) by intuition ;
   destruct (Rseq_pow_lt_1_cv ((1 + Rabs x) / 2) r_bd (eps / M)) as (N, HN).
   unfold Rdiv ; apply Rmult_lt_0_compat ; [| apply Rinv_0_lt_compat] ; assumption.
   exists N ; intros n n_lb.
   apply Rlt_le_trans with (M * (eps / M)).
   apply Rmult_lt_compat_l.
   assumption.
   replace (((1 + Rabs x) / 2) ^ n) with (Rabs (((1 + Rabs x) / 2) ^ n - 0)).
   apply HN ; assumption.
   rewrite Rminus_0_r ; apply Rabs_right.
   apply Rle_ge ; apply pow_le ; assumption.
   right ; field ; apply Rgt_not_eq ; assumption.
   destruct (H ((1 + 1 / Rabs x) / 2 - 1) Rinv_r_pos) as (N, HN).
assert (Temp : forall M i : nat, (M >= S N)%nat -> Rabs (INR (i + S M) * x ^ (i + S M)) <
        (1 + Rabs x) / 2 * Rabs (INR (i + M) * x ^ (i + M))).
 intros M i M_lb.
 apply Rle_lt_trans with (Rabs ((INR (i + S M) / (INR (i + M))) * ((INR (i + M)) * x ^ (i + S M)))).
 right ; apply Rabs_eq_compat ; field ; apply Rgt_not_eq ; intuition.
 replace (i + S M)%nat with (S (i + M))%nat by intuition ;
 rewrite <- tech_pow_Rmult.
 repeat (rewrite Rabs_mult ; rewrite <- Rmult_assoc).
 apply Rmult_lt_compat_r.
 apply Rabs_pos_lt ; apply pow_nonzero ; assumption.
 rewrite Rmult_comm, <- Rmult_assoc.
 apply Rmult_lt_compat_r.
 apply Rabs_pos_lt ; apply Rgt_not_eq ; intuition.
 replace (INR (S (i + M)) / INR (i + M)) with (1 + / INR (i + M)).
 apply Rlt_le_trans with (Rabs x * (1 + 1 / Rabs x) / 2).
 unfold Rdiv ; rewrite Rmult_assoc ; apply Rmult_lt_compat_l.
 apply Rabs_pos_lt ; assumption.
 rewrite Rabs_right.
 assert (Temp : forall a b c, b < c - a -> a + b < c).
  clear ; intros ; fourier.
 apply Temp.
 replace (/INR (i + M)) with (R_dist (/INR (S (i + pred M))) 0).
 apply HN ; intuition.
 unfold R_dist ; rewrite Rminus_0_r ; replace (S (i + pred M))%nat with (i + M)%nat.
 apply Rabs_right ; left ; apply Rinv_0_lt_compat ; intuition.
 intuition.
 apply Rle_ge ; apply Rle_zero_pos_plus1.
 left ; apply Rinv_0_lt_compat ; intuition.
 right ; field.
 apply Rgt_not_eq ; apply Rabs_pos_lt ; assumption.
 replace (INR (S (i + M))) with (1 + INR (i + M)).
 field ; apply Rgt_not_eq ; intuition.
 replace (S (i + M)) with (1 + (i + M))%nat by intuition ; rewrite S_O_plus_INR.
 intuition.
 pose (An_0 := Rabs (INR (S N))).
 assert (An_0_pos : 0 < An_0 * Rabs x ^ (S N)). 
  apply Rmult_lt_0_compat.
  unfold An_0 ; apply Rabs_pos_lt ; apply Rgt_not_eq ; intuition.
  apply pow_lt ; apply Rabs_pos_lt ; assumption.
 destruct (Main (An_0 * Rabs x ^ (S N)) eps eps_pos An_0_pos) as (N2, HN2).
 exists (N2 + S N)%nat ; intros n n_lb.
 fold k in Temp.
 assert (Temp2 : forall i : nat,
      (fun i0 : nat => Rabs (INR (i0 + S N) * x ^ (i0 + S N))) (S i) <
      k * (fun i0 : nat => Rabs (INR (i0 + S N) * x ^ (i0 + S N))) i).
 intro i.
 replace (S i + S N)%nat with (i + S (S N))%nat by ring.
 apply Temp ; intuition.
 clear Temp.
 unfold R_dist, Rminus ; rewrite Ropp_0 ; rewrite Rplus_0_r.
 assert (Temp : forall m n, (m >= n)%nat -> {p | (m = n + p)%nat}).
   clear ; intros m n ; induction n ; intro H.
   exists m ; intuition.
   case (le_lt_eq_dec _ _ H) ; clear H ; intro H.
   assert (H' : (m >= n)%nat) by intuition.
   destruct (IHn H') as (p, Hp) ; destruct p.
   exists 0%nat ; apply False_ind ; intuition.
   exists p ; intuition.
   exists 0%nat ; intuition.
  destruct (Temp n (N2 + S N)%nat n_lb) as (p,Hp).
  rewrite Hp. replace (S (N2 + S N + p))%nat with ((S N2 + p) + S N)%nat by intuition.
 assert (H' := tech4 (fun i : nat => Rabs (INR (i + S N) * x ^ (i + S N))) k
             (S N2 + p) k_pos Temp2).
 apply Rle_lt_trans with (Rabs (INR (0 + S N) * x ^ (0 + S N)) * k ^ (S N2 + p)).
 apply H'.
 simpl (0 + S N)%nat ; rewrite Rabs_mult ; fold An_0 ; unfold k ; rewrite <- RPow_abs ;
 apply HN2.
 intuition.
Qed. 

(* end hide *)

(** Caracterization of the cv radius of the formal derivative *)

Lemma Cv_radius_weak_derivable_compat : forall An r,
         Cv_radius_weak An r -> forall r', Rabs r' < Rabs r ->
         Cv_radius_weak (An_deriv An) r'.
Proof.
intros An r rho r' r'_bd.
 assert (Rabsr_pos : 0 < Rabs r).
  apply Rle_lt_trans with (Rabs r') ; [apply Rabs_pos | assumption].
 assert (x_lt_1 : Rabs (r'/ r) < 1).
  unfold Rdiv ; rewrite Rabs_mult ; rewrite Rabs_Rinv.
  replace 1 with (Rabs r *  / Rabs r).
  apply Rmult_lt_compat_r ; [apply Rinv_0_lt_compat |] ; assumption.
  apply Rinv_r ; apply Rgt_not_eq ; assumption.
  intro Hf ; rewrite Hf, Rabs_R0 in Rabsr_pos ; apply (Rlt_irrefl _ Rabsr_pos).
  destruct rho as (B,HB).
  case (Req_or_neq r') ; intro r'_lb.
  exists (Rabs (An 1%nat)) ; intros x Hx ; destruct Hx as (i, Hi) ;
 rewrite Hi ; unfold gt_abs_Pser, An_deriv.
 destruct i.
 simpl ; rewrite Rmult_1_l ; rewrite Rmult_1_r ; apply Rle_refl.
 rewrite r'_lb ; rewrite pow_i ; [| intuition] ; repeat (rewrite Rmult_0_r) ;
 rewrite Rabs_R0 ; apply Rabs_pos.
 assert (Rabsr'_pos : 0 < Rabs r') by (apply Rabs_pos_lt ; assumption). 
 destruct (Rpser_cv_speed_pow_id (r' / r) x_lt_1 (Rabs r') Rabsr'_pos) as (N, HN).
 destruct (Rseq_partial_bound (gt_abs_Pser (An_deriv An) r') N) as (B2, HB2).
 exists (Rmax B B2) ; intros x Hx ; destruct Hx as (i, Hi) ;
 rewrite Hi ; unfold gt_abs_Pser in * ; case (le_lt_dec i N) ; intro H.
 rewrite <- Rabs_Rabsolu ; apply Rle_trans with B2 ; [apply HB2 | apply RmaxLess2] ;
 assumption.
 apply Rle_trans with (Rabs (/r' * (INR (S i) * (r' / r) ^ S i) * An (S i) * r ^ S i)).
 right ; apply Rabs_eq_compat ; unfold An_deriv ; field_simplify.
 unfold Rdiv ; repeat (rewrite Rmult_assoc) ; repeat (apply Rmult_eq_compat_l).
 rewrite Rpow_mult_distr.
 rewrite Rinv_1 ; rewrite Rmult_1_r.
 rewrite Rmult_assoc.
 replace ((/ r) ^ S i * (r ^ S i * / r')) with (/ r').
 simpl ; field ; assumption.
 field_simplify.
 unfold Rdiv ; repeat (rewrite <- Rmult_assoc) ; apply Rmult_eq_compat_r.
 rewrite <- Rinv_pow.
 field.
 apply pow_nonzero.
 intro Hf ; rewrite Hf, Rabs_R0 in r'_bd.
 assert (H0 : 0 < 0).
 apply Rlt_trans with (Rabs r') ; assumption.
 apply (Rlt_irrefl _ H0).
 intro Hf ; rewrite Hf, Rabs_R0 in r'_bd.
 assert (H0 : 0 < 0).
 apply Rlt_trans with (Rabs r') ; assumption.
 apply (Rlt_irrefl _ H0).
 assumption.
 assumption.
 assumption.
 rewrite Rmult_assoc ; rewrite Rabs_mult.
 apply Rle_trans with (Rabs (/ r' * (INR (S i) * (r' / r) ^ S i)) * B).
 apply Rmult_le_compat_l ; [apply Rabs_pos |] ; apply HB ; exists (S i) ; reflexivity.
 apply Rle_trans with (1*B) ; [| rewrite Rmult_1_l ; apply RmaxLess1].
 apply Rmult_le_compat_r.
 apply Rle_trans with (Rabs (An 0%nat * r ^ 0)) ; [apply Rabs_pos |] ;
 apply HB ; exists 0%nat ; reflexivity.
 rewrite Rabs_mult ; apply Rle_trans with (Rabs (/r') * Rabs r').
 apply Rmult_le_compat_l.
 apply Rabs_pos.
 apply Rle_trans with (R_dist (INR (S i) * (r' / r) ^ S i) 0) ;
 [right ; unfold R_dist ; rewrite Rminus_0_r ; reflexivity |] ; left ; apply HN ;
 intuition.
 rewrite <- Rabs_mult ; rewrite Rinv_l ; [| assumption] ; rewrite Rabs_R1 ; right ; trivial.
Qed.

(** Derivability of partial sums *)

Definition Rpser_partial_sum_derive An n x := match n with
     | 0%nat => 0
     | S _      => sum_f_R0 (gt_Pser (An_deriv An) x) (pred n)
end.

Lemma Rpser_derive_finite_sum : forall An n x,
       derivable_pt_lim (fun x => sum_f_R0 (gt_Pser An x) n) x (Rpser_partial_sum_derive An n x).
Proof.
intros An n x ;
 unfold Rpser_partial_sum_derive, gt_Pser, An_deriv ;
 apply (derivable_pt_lim_finite_sum An x n).
Qed.

(* begin hide *)

Lemma Rpser_derivability_prelim : forall x r, Rabs x < Rabs r ->
      Rabs x < (Rabs x + Rabs r)/2 < Rabs r.
Proof.
intros x r x_bd ; split.
 apply Rle_lt_trans with ((Rabs x + Rabs x)/2).
 apply Rle_trans with (Rabs ((x+x) /2)).
 right ; apply Rabs_eq_compat ; field.
 unfold Rdiv ; rewrite Rabs_mult.
 replace (Rabs (/2)) with (/2).
 apply Rmult_le_compat_r ; intuition.
 apply Rabs_triang.
 rewrite Rabs_right ; intuition ; fourier.
 unfold Rdiv ; apply Rmult_lt_compat_r ; fourier.
 apply Rlt_le_trans with ((Rabs r + Rabs r) / 2).
 unfold Rdiv ; apply Rmult_lt_compat_r ; fourier.
 right ; field.
Qed.

Lemma Rpser_derivability_prelim2 : forall x r, Rabs x < Rabs r ->
      Rabs x < Rabs ((Rabs x + Rabs r)/2) < Rabs r.
Proof.
intros x r x_bd ; replace (Rabs ((Rabs x + Rabs r)/2)) with ((Rabs x + Rabs r)/2).
 apply Rpser_derivability_prelim ; assumption.
 unfold Rdiv ; rewrite Rabs_mult ; replace (Rabs (/2)) with (/2).
 apply Rmult_eq_compat_r.
 symmetry ; rewrite Rabs_right ; [reflexivity |].
 apply Rle_ge ; apply Rplus_le_le_0_compat ; apply Rabs_pos.
 rewrite Rabs_right ; intuition ; fourier.
Qed.

(* end hide *)

(** Sum of the formal derivative *)

Definition weaksum_r_derive (An : nat -> R) (r : R) (Rho : Cv_radius_weak An r) (x : R) : R.
Proof.
intros An r Rho x ; case (Rlt_le_dec (Rabs x) r) ; intro x_bd.
 pose (r' := (Rabs x + Rabs r)/2).
 rewrite <- Rabs_right in x_bd by (apply Rle_ge ; apply Rle_trans with (Rabs x) ;
 [apply Rabs_pos | left ; assumption]).
 assert (H := Rpser_derivability_prelim2 _ _ x_bd).
 assert (r'_bd : Rabs r' < Rabs r).
  destruct H ; intuition.
 apply (weaksum_r (An_deriv An) ((Rabs x + Rabs r) / 2)
      (Cv_radius_weak_derivable_compat An r Rho r'
      r'_bd) x).
 apply 0.
Defined.

Definition sum_r_derive (An : nat -> R) (r : R) (Rho : finite_cv_radius An r) (x : R) : R.
Proof.
intros An r Rho z.
 destruct (Rlt_le_dec (Rabs z) r) as [z_bd | z_gt].
 assert (H : 0 <= middle (Rabs z) r < r).
  split.
  left ; apply middle_le_lt_pos ; [| apply Rle_lt_trans with (Rabs z) ; [| assumption]] ;
  apply Rabs_pos.
  apply (middle_is_in_the_middle _ _ z_bd).
 apply (weaksum_r_derive _ _ (proj1 Rho (middle (Rabs z) r) H) z).
 apply 0.
Defined.

Definition sum_derive (An : nat -> R) (Rho : infinite_cv_radius An) (z : R) : R.
Proof.
 intros An Rho z ; apply (weaksum_r_derive _ _ (Rho (Rabs z + 1)%R) z).
Defined.

(** Proof that it is really the sum *)

Lemma weaksum_r_derive_sums : forall (An : nat -> R) (r : R) (Pr : Cv_radius_weak An r) (x : R),
      Rabs x < r -> Pser (An_deriv An) x (weaksum_r_derive An r Pr x).
Proof.
intros An r Pr x x_bd.
 unfold weaksum_r_derive ; case (Rlt_le_dec (Rabs x) r) ; intro s.
 rewrite <- Rabs_right in x_bd.
 apply weaksum_r_sums.
 apply (proj1 (Rpser_derivability_prelim _ _ x_bd)).
 apply Rle_ge ; apply Rle_trans with (Rabs x) ;
 [apply Rabs_pos | left ; assumption].
 assert (H : Rabs x < Rabs x) by (apply Rlt_le_trans with r ; assumption) ;
 elim (Rlt_irrefl _ H).
Qed.

Lemma sum_r_derive_sums : forall (An : nat -> R) (r : R) (Pr : finite_cv_radius An r) (z : R),
      Rabs z < r -> Pser (An_deriv An) z (sum_r_derive An r Pr z).
Proof.
intros An r Pr z z_bd ; unfold sum_r_derive ;
 destruct (Rlt_le_dec (Rabs z) r) as [z_bd2 | Hf].
 apply weaksum_r_derive_sums ; apply (middle_is_in_the_middle _ _ z_bd).
 assert (F : r < r) by (apply Rle_lt_trans with (Rabs z) ; assumption) ;
 destruct (Rlt_irrefl _ F).
Qed.

Lemma sum_derive_sums : forall (An : nat -> R) (Pr : infinite_cv_radius An) (z : R),
      Pser (An_deriv An) z (sum_derive An Pr z).
Proof.
intros An Pr z ; unfold sum_derive ; apply weaksum_r_derive_sums ; intuition.
Qed.

(** Proof that this derivative is unique *)

Lemma weaksum_r_derive_unique : forall (An : nat -> R) (r : R) (Pr1 Pr2 : Cv_radius_weak An r) (z : R),
      Rabs z < r -> weaksum_r_derive An r Pr1 z = weaksum_r_derive An r Pr2 z .
Proof.
intros An r Pr1 Pr2 z z_bd ;
 assert (T1 := weaksum_r_derive_sums _ _ Pr1 _ z_bd) ;
 assert (T2 := weaksum_r_derive_sums _ _ Pr2 _ z_bd).
 eapply Pser_unique ; eassumption.
Qed.

Lemma sum_r_derive_unique : forall (An : nat -> R) (r : R) (Pr1 Pr2 : finite_cv_radius An r) (z : R),
      Rabs z < r -> sum_r_derive An r Pr1 z = sum_r_derive An r Pr2 z .
Proof.
intros An r Pr1 Pr2 z z_bd ;
 assert (T1 := sum_r_derive_sums _ _ Pr1 _ z_bd) ;
 assert (T2 := sum_r_derive_sums _ _ Pr2 _ z_bd).
 eapply Pser_unique ; eassumption.
Qed.

Lemma sum_derive_unique : forall (An : nat -> R) (Pr1 Pr2 : infinite_cv_radius An) (z : R),
      sum_derive An Pr1 z = sum_derive An Pr2 z .
Proof.
intros An Pr1 Pr2 z ;
 assert (T1 := sum_derive_sums _ Pr1 z) ;
 assert (T2 := sum_derive_sums _ Pr2 z).
 eapply Pser_unique ; eassumption.
Qed.

(** Proof that the formal derivative is the actual derivative within the cv-disk *)

Lemma derivable_pt_lim_weaksum_r (An:nat->R) (r:R) (Pr : Cv_radius_weak An r) : forall x,
      Rabs x < r -> derivable_pt_lim (weaksum_r An r Pr) x (weaksum_r_derive An r Pr x).
Proof.
intros An r rho x x_bd.
 assert (x_bd' : Rabs x < Rabs r).
  apply Rlt_le_trans with r ; [assumption | right ; symmetry ; apply Rabs_right].
  apply Rle_ge ; apply Rle_trans with (Rabs x) ; [apply Rabs_pos | left ; assumption].
assert (lb_lt_x : - (Rabs x + Rabs r) / 2 < x).
  apply Rlt_le_trans with (- (Rabs x + Rabs x)/2).
  unfold Rdiv ; apply Rmult_lt_compat_r ; [fourier |] ;
  apply Ropp_gt_lt_contravar ; apply Rplus_lt_compat_l ; assumption.
  unfold Rabs ; case (Rcase_abs x) ; intro H.
  right ; field.
  apply Rle_trans with 0.
  unfold Rdiv ; rewrite Ropp_mult_distr_l_reverse ;
  apply Rge_le ; apply Ropp_0_le_ge_contravar.
  apply Rle_mult_inv_pos ; fourier.
  intuition.
 assert (x_lt_ub : x < (Rabs x + Rabs r) / 2).
  apply Rle_lt_trans with ((Rabs x + Rabs x)/2).
  unfold Rabs ; case (Rcase_abs x) ; intro H.
  apply Rle_trans with 0.
  left ; assumption.
  rewrite <- Ropp_plus_distr.
  unfold Rdiv ; apply Rle_mult_inv_pos.
  fourier.
  fourier.
  right ; field.
  unfold Rdiv ; apply Rmult_lt_compat_r ; [fourier |] ; apply Rplus_lt_compat_l ;
  assumption.
    pose (r' := ((Rabs x + Rabs r)/2 + Rabs r)/2).
    assert (r'_bd1 := proj2 (Rpser_derivability_prelim _ _ x_bd')).
    replace ((Rabs x + Rabs r) / 2) with (Rabs ((Rabs x + Rabs r) / 2)) in r'_bd1 ; [| apply Rabs_right ;
    unfold r' ; apply Rle_ge ; unfold Rdiv ; apply Rle_mult_inv_pos ; [| fourier] ;
    apply Rplus_le_le_0_compat ; apply Rabs_pos].
    assert (r'_bd := proj2 (Rpser_derivability_prelim _ _ r'_bd1)).
    assert (Temp : (Rabs ((Rabs x + Rabs r) / 2) + Rabs r) / 2 = r').
     unfold r' ; unfold Rdiv ; apply Rmult_eq_compat_r ; apply Rplus_eq_compat_r ;
     apply Rabs_right ; apply Rle_ge ; apply Rle_mult_inv_pos ; [| fourier] ;
     apply Rplus_le_le_0_compat ; apply Rabs_pos.
     rewrite Temp in r'_bd ; clear Temp ;
    fold r' in r'_bd ; replace r' with (Rabs r') in r'_bd ; [| apply Rabs_right ;
    unfold r' ; apply Rle_ge ; unfold Rdiv ; apply Rle_mult_inv_pos ; [| fourier] ;
    apply Rplus_le_le_0_compat ; [| apply Rabs_pos] ; unfold Rdiv ;
    apply Rle_mult_inv_pos ; [| fourier] ; apply Rplus_le_le_0_compat ; apply Rabs_pos].
    pose (r'' := ((Rabs x + Rabs r) / 2)).
    assert (r''_pos : 0 < r'').
    unfold r''. apply Rlt_mult_inv_pos ; [| fourier] ;
     apply Rplus_le_lt_0_compat ; [| apply Rle_lt_trans with (Rabs x) ; [| assumption]] ;
     apply Rabs_pos.
    assert (r''_bd : r'' < r').
     unfold r'', r'.
     unfold Rdiv ; apply Rmult_lt_compat_r ; [fourier |] ; apply Rplus_lt_compat_r.
     apply Rabs_def1 ; [| rewrite <- Ropp_mult_distr_l_reverse] ; assumption.
    pose (myR := mkposreal r'' r''_pos).
    assert (myR_ub : myR < r') by intuition.
    assert (Abel2' := Rpser_abel2 (An_deriv An) r'
         (Cv_radius_weak_derivable_compat An r rho r' r'_bd) myR myR_ub).
   assert (cv_interv : forall y : R, Boule 0 (mkposreal_lb_ub x (- (Rabs x + Rabs r) / 2)
         ((Rabs x + Rabs r) / 2) lb_lt_x x_lt_ub) y ->
         {l : R | Un_cv (fun N : nat => SP
         (fun (n : nat) (x : R) => gt_Pser (An_deriv An) x n) N y) l}).
    intros y y_bd.
    exists (weaksum_r_derive An r rho y).
    assert (y_bd2 : Rabs y < r).
     unfold Boule, mkposreal_lb_ub in y_bd ; rewrite Rminus_0_r in y_bd.
     apply Rlt_trans with (((Rabs x + Rabs r) / 2 - - (Rabs x + Rabs r) / 2) / 2).
     assumption.
     apply Rle_lt_trans with ((Rabs x + Rabs r) / 2).
     right ; field.
     destruct (middle_is_in_the_middle _ _ x_bd) as (_, Temp) ; unfold middle in Temp.
     rewrite Rabs_right with r ; [assumption | apply Rle_ge ;
     apply Rle_trans with (Rabs x) ; [apply Rabs_pos | intuition]].
     intros alpha alpha_pos ; destruct (weaksum_r_derive_sums An r rho y y_bd2
           alpha alpha_pos) as (N, HN) ; exists N ; intros n n_lb ; apply HN ;
           assumption.
   assert (CVN : CVN_r (fun (n : nat) (x : R) => gt_Pser (An_deriv An) x n)
         (mkposreal_lb_ub x (- (Rabs x + Rabs r) / 2) ((Rabs x + Rabs r) / 2)
         lb_lt_x x_lt_ub)).
    apply Rpser_abel2 with r'.
    apply Cv_radius_weak_derivable_compat with r ; assumption.
    unfold mkposreal_lb_ub.
    apply Rle_lt_trans with r'' ; [| assumption].
    right ; unfold r'' ; intuition.
     assert (Temp : ((Rabs x + Rabs r) / 2 - - (Rabs x + Rabs r) / 2) / 2
           = (Rabs x + Rabs r) / 2).
       field.
     intuition.
   assert (Main := CVN_CVU_interv (fun n x => gt_Pser (An_deriv An) x n)
          (mkposreal_lb_ub x (- (Rabs x + Rabs r) / 2) ((Rabs x + Rabs r) / 2)
          lb_lt_x x_lt_ub) cv_interv CVN).
   assert (Main2 : RFseq_cvu (Rpser_partial_sum_derive An) (weaksum_r_derive An r rho)
          ((- (Rabs x + Rabs r) / 2 + (Rabs x + Rabs r) / 2) / 2)
          (mkposreal_lb_ub x (- (Rabs x + Rabs r) / 2) ((Rabs x + Rabs r) / 2)
          lb_lt_x x_lt_ub)).
    clear -Main x_bd; intros eps eps_pos ; destruct (Main eps eps_pos) as (N, HN) ;
    exists (S N) ; intros n y n_lb y_bd.
    assert (y_bd2 : Boule 0
         (mkposreal_lb_ub x (- (Rabs x + Rabs r) / 2) ((Rabs x + Rabs r) / 2)
         lb_lt_x x_lt_ub) y).
     unfold Boule in y_bd ; unfold Boule ; replace ((- (Rabs x + Rabs r) / 2
          + (Rabs x + Rabs r) / 2)/2) with 0 in y_bd by field ; assumption.
    assert(n_lb2 : (N <= pred n)%nat) by intuition.
    assert (Temp := HN (pred n) y n_lb2 y_bd2).
    assert (T1 := SFL_interv_right (fun (n : nat) (x : R) => gt_Pser (An_deriv An) x n)
            (mkposreal_lb_ub x (- (Rabs x + Rabs r) / 2)
            ((Rabs x + Rabs r) / 2) lb_lt_x x_lt_ub) cv_interv y y_bd2).
    assert (y_bd3 : Rabs y < r).
     unfold Boule, mkposreal_lb_ub in y_bd2 ; rewrite Rminus_0_r in y_bd2.
     apply Rlt_trans with (((Rabs x + Rabs r) / 2 - - (Rabs x + Rabs r) / 2) / 2).
     assumption.
     apply Rle_lt_trans with ((Rabs x + Rabs r) / 2).
     right ; field.
     destruct (middle_is_in_the_middle _ _ x_bd) as (_, Temp') ; unfold middle in Temp'.
     rewrite Rabs_right with r ; [assumption | apply Rle_ge ;
     apply Rle_trans with (Rabs x) ; [apply Rabs_pos | intuition]].
    assert (T2_temp := weaksum_r_derive_sums An r rho y y_bd3).
    assert (T2 := Pser_Rseqcv_link _ _ _ T2_temp) ; clear T2_temp.
    assert (Hrew : (fun N : nat => sum_f_R0 (gt_Pser (An_deriv An) y) N)
    = (fun N : nat => SP (fun (n : nat) (x : R) => gt_Pser (An_deriv An) x n) N y)).
     unfold SP ; reflexivity.
    rewrite Hrew in T2 ; clear Hrew.
    assert (Lim_eq := UL_sequence _ _ _ T1 T2).
    rewrite <- Lim_eq.
    unfold SP in Temp ; unfold Rpser_partial_sum_derive.
    assert (Hrew : n = S (pred n)).
     apply S_pred with N ; intuition.
    rewrite Hrew.
    unfold R_dist ; rewrite Rabs_minus_sym ; apply Temp.
  assert (Dfn_eq_fn' : forall (x0 : R) (n : nat), - (Rabs x + Rabs r) / 2 < x0 ->
          x0 < (Rabs x + Rabs r) / 2 -> derivable_pt_lim
          ((fun (n0 : nat) (x : R) => sum_f_R0 (gt_Pser An x) n0) n) x0
          (Rpser_partial_sum_derive An n x0)).
   intros y n y_lb y_ub.
   apply derivable_pt_lim_finite_sum.
  assert (fn_cv_f : RFseq_cv_interv (fun (n : nat) (x : R) => sum_f_R0 (gt_Pser An x) n)
          (weaksum_r An r rho) (- (Rabs x + Rabs r) / 2) ((Rabs x + Rabs r) / 2)).
   intros y lb_lt_y y_lt_ub eps eps_pos.
    assert(y_bd1 : - Rabs r < y).
     apply Rlt_trans with (- (Rabs x + Rabs r) / 2) ; [| assumption].
     apply Rle_lt_trans with (- (Rabs r + Rabs r) / 2).
     right ; field.
     unfold Rdiv ; apply Rmult_lt_compat_r ; [fourier |] ; apply Ropp_lt_contravar ;
     apply Rplus_lt_compat_r ; assumption.
    assert(y_bd2 : y < Rabs r).
     apply Rlt_trans with ((Rabs x + Rabs r) / 2) ; [assumption |] ;
     apply Rlt_le_trans with ((Rabs r + Rabs r) / 2) ; [| right ; field].
     unfold Rdiv ; apply Rmult_lt_compat_r ; [fourier |] ; apply Rplus_lt_compat_r ;
     assumption.
   assert (y_bd : Rabs y < Rabs r).
    apply Rabs_def1 ; assumption.
    replace (Rabs r) with r in y_bd ; [| symmetry ; apply Rabs_right ; apply Rle_ge ;
    apply Rle_trans with (Rabs x) ; [apply Rabs_pos | left ; assumption]].
   destruct (weaksum_r_sums An r rho y y_bd eps eps_pos) as (N, HN) ; exists N ;
   intros n n_lb ; apply HN ; assumption.
    apply (RFseq_cvu_derivable (fun n x => sum_f_R0 (gt_Pser An x) n)
         (Rpser_partial_sum_derive An)
         (weaksum_r An r rho) (weaksum_r_derive An r rho) x
         (- (Rabs x + Rabs r)/2) ((Rabs x + Rabs r)/2)
         lb_lt_x x_lt_ub Dfn_eq_fn' fn_cv_f Main2).
   intros y y_lb y_ub.
   apply CVU_continuity with (fn:=Rpser_partial_sum_derive An) (x:=0) (r:=(mkposreal_lb_ub x (- (Rabs x + Rabs r) / 2)
             ((Rabs x + Rabs r) / 2) lb_lt_x x_lt_ub)).
             intros eps eps_pos ; destruct (Main2 eps eps_pos) as (N, HN) ; exists N ; 
             intros n z n_lb z_bd.
             rewrite Rabs_minus_sym ; apply HN.
   assumption.
   replace ((- (Rabs x + Rabs r) / 2 + (Rabs x + Rabs r) / 2) / 2) with 0 by field.
   assumption.
   intros.
   destruct n.
   unfold Rpser_partial_sum_derive.
   apply continuity_const ; unfold constant ; intuition.
   unfold Rpser_partial_sum_derive ; apply continuity_finite_sum.
   unfold Boule ; rewrite Rminus_0_r.
   unfold mkposreal_lb_ub.
   replace (((Rabs x + Rabs r) / 2 - - (Rabs x + Rabs r) / 2) / 2) with
   ((Rabs x + Rabs r) / 2) by field.
   apply Rabs_def1 ; intuition.
   clear -y_lb ; apply Rle_lt_trans with (- (Rabs x + Rabs r) / 2).
   right ; field.
   assumption.
Qed.

Lemma derivable_pt_lim_sum_r (An:nat->R) (r:R) (Pr : finite_cv_radius An r) : forall z,
      Rabs z < r -> derivable_pt_lim (sum_r An r Pr) z (sum_r_derive An r Pr z).
Proof.
intros An r Pr z z_bd eps eps_pos. 
 assert (H : 0 <= middle (Rabs z) r < r).
  split.
  left ; apply middle_le_lt_pos ; [| apply Rle_lt_trans with (Rabs z) ; [| assumption]] ;
  apply Rabs_pos.
  apply (middle_is_in_the_middle _ _ z_bd).
 destruct (derivable_pt_lim_weaksum_r _ _ (proj1 Pr (middle (Rabs z) r) H) _
 (proj1 (middle_is_in_the_middle _ _ z_bd)) _ eps_pos) as [delta Hdelta].
 pose (delta' := Rmin delta (((middle (Rabs z) r) - Rabs z) / 2)%R) ;
 assert (delta'_pos : 0 < delta').
  apply Rmin_pos.
   apply delta.
   apply ub_lt_2_pos with (middle (Rabs z) (middle (Rabs z) r)) ;
   apply (middle_is_in_the_middle _ _ (proj1 (middle_is_in_the_middle _ _ z_bd))).
  exists (mkposreal delta' delta'_pos) ; intros h h_neq h_bd.

 replace (sum_r An r Pr (z + h)) with (weaksum_r An (middle (Rabs z) r)
               (proj1 Pr (middle (Rabs z) r) H) (z + h)).
 replace (sum_r An r Pr z) with (weaksum_r An (middle (Rabs z) r)
               (proj1 Pr (middle (Rabs z) r) H) z).
 replace (sum_r_derive An r Pr z) with (weaksum_r_derive An (middle (Rabs z) r)
              (proj1 Pr (middle (Rabs z) r) H) z).
 apply Hdelta ; [assumption | apply Rlt_le_trans with delta'] ;
 [assumption | apply Rmin_l].

 unfold sum_r_derive ; destruct (Rlt_le_dec (Rabs z) r) as [z_bd2 | Hf].
 apply weaksum_r_derive_unique ; apply (middle_is_in_the_middle _ _ z_bd).
 assert (F : r < r) by (apply Rle_lt_trans with (Rabs z) ; assumption) ;
 destruct (Rlt_irrefl _ F).

 unfold sum_r ; destruct (Rlt_le_dec (Rabs z) r) as [z_bd2 | Hf].
 apply weaksum_r_unique ; apply (middle_is_in_the_middle _ _ z_bd).
 assert (F : r < r) by (apply Rle_lt_trans with (Rabs z) ; assumption) ;
 destruct (Rlt_irrefl _ F).

 unfold sum_r ; destruct (Rlt_le_dec (Rabs (z + h)) r) as [z_bd2 | Hf].
 apply weaksum_r_unique_strong.
 apply Rle_lt_trans with (Rabs z + Rabs h)%R.
 apply Rabs_triang.
 apply Rlt_le_trans with (Rabs z + ((middle (Rabs z) r - Rabs z) / 2))%R.
 apply Rplus_lt_compat_l ; apply Rlt_le_trans with delta' ; [assumption | apply Rmin_r].
 unfold Rminus ; field_simplify ; unfold Rdiv ; rewrite Rinv_1, Rmult_1_r.
 left ; do 2 eapply middle_is_in_the_middle ; assumption.
 eapply middle_is_in_the_middle ; assumption.
 assert (F : r < r).
  apply Rlt_trans with (middle (Rabs z) r).
  apply Rle_lt_trans with (Rabs (z + h)).
  assumption.
  apply Rle_lt_trans with (Rabs z + Rabs h)%R.
  apply Rabs_triang.
  apply Rlt_trans with (Rabs z + ((middle (Rabs z) r - Rabs z) / 2))%R.
  apply Rplus_lt_compat_l ; apply Rlt_le_trans with delta' ; [intuition | apply Rmin_r].
  unfold middle ; field_simplify.
  apply Rlt_le_trans with ((2 * Rabs z + r + r) / 4)%R.
  unfold Rdiv ; apply Rmult_lt_compat_r ; [fourier |].
  apply Rplus_lt_compat_r.
  apply Rle_lt_trans with (2 * Rabs z + Rabs z)%R.
  right ; ring.
  apply Rplus_lt_compat_l ; assumption.
  right ; field.
  eapply middle_is_in_the_middle ; assumption.
  destruct (Rlt_irrefl _ F).
Qed.

Lemma derivable_pt_lim_sum (An:nat->R) (Pr : infinite_cv_radius An) : forall z,
      derivable_pt_lim (sum An Pr) z (sum_derive An Pr z).
Proof.
intros An Pr z eps eps_pos. 
 assert (H : 0 <= Rabs z < Rabs z + 1).
  split ; [apply Rabs_pos |] ; intuition.
 destruct (derivable_pt_lim_weaksum_r _ _ (Pr (Rabs z + 1)%R) z (proj2 H) _ eps_pos) as [delta Hdelta].

 pose (delta' := Rmin delta 1) ; assert (delta'_pos : 0 < delta').
  apply Rmin_pos ; [apply delta | apply Rlt_0_1].
 exists (mkposreal _ delta'_pos) ; intros h h_neq h_bd.

 replace (sum An Pr (z + h)) with (weaksum_r An (Rabs z + 1) (Pr (Rabs z + 1)%R) (z + h)).
 apply Hdelta.
 assumption.
 apply Rlt_le_trans with delta' ; [assumption | apply Rmin_l].

 unfold sum.
 apply weaksum_r_unique_strong.
 apply Rle_lt_trans with (Rabs z + Rabs h)%R.
 apply Rabs_triang.
 apply Rplus_lt_compat_l ; apply Rlt_le_trans with delta' ;
 [intuition | apply Rmin_r].
 intuition.
Qed.


(** * Derivabilty / Continuity of the sum within the cv disk *)

Lemma derivable_pt_weaksum_r (An:nat->R) (r:R) (Pr : Cv_radius_weak An r) : forall x,
      Rabs x < r -> derivable_pt (weaksum_r An r Pr) x.
Proof.
intros An r rho x x_bd.
 exists (weaksum_r_derive An r rho x) ; apply derivable_pt_lim_weaksum_r ; assumption.
Qed.

Lemma continuity_pt_weaksum_r (An:nat->R) (r:R) (Pr : Cv_radius_weak An r) : forall x,
      Rabs x < r -> continuity_pt (weaksum_r An r Pr) x.
Proof.
intros An r rho x x_bd ; apply derivable_continuous_pt ; apply derivable_pt_weaksum_r ;
 assumption.
Qed.

(** * Comparison of Taylor development *)

Section Taylor.

Variable Un : nat -> R.
Variable En : nat -> R.
Variable r : R.

(* begin hide *)
Lemma partial_sum_null : forall N x,
sum_f_R0 (fun n0 : nat => 
(if le_lt_dec n0 N then 0 else Un n0) * x ^ n0) N = 0.
Proof.
intros N x.
assert (Hrec : forall n, (n<= N)%nat ->
sum_f_R0 (fun n0 : nat => (if le_lt_dec n0 N then 0 else Un n0) * x ^ n0) n =0).
intros n Hn.
induction n.
simpl; ring.
rewrite tech5; rewrite IHn.
destruct (le_lt_dec (S n) N).
  ring.
  apply False_ind; omega.
omega.
apply Hrec; intuition.
Qed.

Lemma partial_sum : forall N x
(Vn := fun n : nat => if le_lt_dec n N then 0 else Un n) n 
(Hle : (N<= n)%nat), 
sum_f_R0 (fun n0 : nat => Un n0 * x ^ n0) n =
sum_f_R0 (fun n0 : nat => Un n0 * x ^ n0) N +
sum_f_R0 (fun n0 : nat => Vn n0 * x ^ n0) n.
Proof.
intros N x Vn n Hle.
induction Hle.
unfold Vn.
rewrite partial_sum_null; ring.
simpl; rewrite IHHle; unfold Vn at 3.
destruct (le_lt_dec (S m ) N).
  apply False_ind; intuition.
  intuition.
Qed.
(* end hide *)

Lemma Rpser_big_O_partial_sum :
  forall N (H : 0 < r) (Hcv : Rseq_cv En 0) (pr : Cv_radius_weak Un r),
    (fun p => weaksum_r Un r pr (En p) - sum_f_R0 (fun n => Un n * (En p) ^ n) N) = O((fun p => (En p) ^ (S N))).
Proof.
intros N H Hcv pr.
pose (Vn := fun n => if le_lt_dec n N then 0 else Un n).
pose (Wn := fun n => Un (n + S N)%nat).
assert (prv : Cv_radius_weak Vn r).
  destruct pr as [M HM].
  exists M; intros m Hm.
  destruct Hm as [i Hi]; rewrite Hi.
  unfold gt_abs_Pser.
  unfold Vn; destruct le_lt_dec.
  rewrite Rmult_0_l; rewrite Rabs_R0.
  eapply Rle_trans.
    apply Rabs_pos.
    apply HM.
    exists i; reflexivity.
  apply HM.
  unfold EUn, gt_abs_Pser.
  exists i; reflexivity.
assert (prw : Cv_radius_weak Wn r).
  destruct pr as [M HM].
  exists (M / r ^ (S N)); intros m Hm.
  destruct Hm as [i Hi]; rewrite Hi.
  unfold gt_abs_Pser, Wn.
  apply (Rmult_le_reg_l (r ^ (S N))).
  apply pow_lt; assumption.
  replace (r ^ (S N) * (M / r ^ (S N)))
    with M by (field; apply Rgt_not_eq; apply pow_lt; assumption).
  rewrite <- (Rabs_right (r ^ (S N))); [|apply Rle_ge; apply pow_le; fourier].
  rewrite <- Rabs_mult.
  rewrite Rmult_comm.
  rewrite Rmult_assoc.
  rewrite <- pow_add.
  apply HM.
  unfold EUn, gt_abs_Pser.
  exists (i + (S N))%nat; reflexivity.
pose (St := fun x => weaksum_r Un r pr x).
pose (Sr := fun x => weaksum_r Vn r prv x).
pose (Sp := fun x => sum_f_R0 (fun n => Un n * x ^ n) N).
pose (Ss := fun x => weaksum_r Wn r prw x).
assert (Hsum : forall x, Rabs x < r -> St x = Sp x + Sr x).
  intros x Hx.
  eapply Rseq_cv_unique.
    apply weaksum_r_sums; assumption.
    assert (Hcvv := weaksum_r_sums Vn r prv x Hx).
    intros eps Heps; destruct (Hcvv eps Heps) as [n0 Hn0].
    exists (Max.max N n0); intros n Hn.
    cutrewrite (sum_f_R0 (fun n => Un n * x ^ n) n = sum_f_R0 (fun n => Un n * x ^ n) N + sum_f_R0 (fun n => Vn n * x ^ n) n).
    assert (Hrw : exists p, n = (N + p)%nat).
      exists (n - N)%nat.
      assert (n >= N)%nat.
        eapply le_trans; [apply Max.le_max_l|eexact Hn].
      omega.
    destruct Hrw as [p Hp]; subst n.
    unfold R_dist.
    rewrite Rplus_comm.
    unfold Rminus.
    rewrite Rplus_assoc.
    rewrite Ropp_plus_distr.
    rewrite <- Rplus_assoc with (r2 := - Sp x).
    rewrite Rplus_opp_r.
    rewrite Rplus_0_l.
    apply Hn0; eapply le_trans; [apply Max.le_max_r|eexact Hn].
    assert (Hle : (N <= n)%nat).
      eapply le_trans; [apply Max.le_max_l|eexact Hn].
    clear - Un Hle.
    apply partial_sum; apply Hle.
assert (Hmul : forall x, Rabs x < r -> Sr x = x ^ (S N) * Ss x).
  intros x Hx.
  eapply Rseq_cv_unique.
    apply weaksum_r_sums; assumption.
    assert (Hcvw := weaksum_r_sums Wn r prw x Hx).
    destruct (Req_dec x 0) as [Hz|Hnz].
      rewrite Hz.
      intros eps Heps.
      exists 0%nat; intros n _.
      cutrewrite (sum_f_R0 (fun n => Vn n * 0 ^ n) n = 0).
      rewrite pow_ne_zero; [|omega].
      rewrite Rmult_0_l.
      rewrite R_dist_eq.
      assumption.
      induction n; simpl.
        unfold Vn.
        destruct le_lt_dec; [field|apply False_ind; omega].
        rewrite Rmult_0_l.
        rewrite Rmult_0_r.
        rewrite Rplus_0_r.
        assumption.
      intros eps Heps.
      destruct (Hcvw (eps / Rabs (x ^ (S N)))) as [n0 Hn0].
        unfold Rdiv; apply Rmult_gt_0_compat.
          assumption.
          apply Rinv_0_lt_compat.
          apply Rabs_pos_lt; apply pow_nonzero; assumption.
      exists (n0 + S N)%nat; intros n Hn.
      cutrewrite (sum_f_R0 (fun n => Vn n * x ^ n) n =
        x ^ S N * sum_f_R0 (fun n => Wn n * x ^ n) (n - (S N))).
      unfold R_dist; rewrite <- Rmult_minus_distr_l.
      rewrite Rabs_mult.
      apply (Rmult_lt_reg_l (/ Rabs (x ^ S N))).
      apply Rinv_0_lt_compat.
      apply Rabs_pos_lt; apply pow_nonzero; assumption.
      rewrite <- Rmult_assoc.
      rewrite Rinv_l.
      rewrite Rmult_1_l.
      rewrite Rmult_comm.
      apply Hn0; omega.
      apply Rgt_not_eq.
      apply Rabs_pos_lt; apply pow_nonzero; assumption.
    assert (Hrw : exists p, (n = N + S p)%nat).
      exists (n - (S N))%nat; omega.
    destruct Hrw as [p Hp]; subst n.
    clear - p.
      induction p; simpl.
        replace (N + 1)%nat with (S N) by omega.
        replace (S N - S N)%nat with 0%nat by omega.
        simpl; unfold Vn, Wn.
        rewrite partial_sum_null.
        destruct le_lt_dec as [H|_]; [apply False_ind; omega|].
        rewrite plus_0_l.
        field.
        rewrite <- plus_n_Sm.
        replace (S (N + S p) - S N)%nat with (S (N + S p - S N))%nat by omega.
        simpl; rewrite IHp.
        rewrite <- tech_pow_Rmult.
        unfold Vn, Wn.
        destruct le_lt_dec as [H|_]; [apply False_ind; omega|].
        replace (S (N + S p - S N) + S N)%nat with (S (N + S p))%nat by omega.
        rewrite Rmult_plus_distr_l.
        apply Rplus_eq_compat_l.
        rewrite pow_add.        
        field_simplify_eq; repeat rewrite Rmult_assoc.
        apply Rmult_eq_compat_l.
        replace (N + S p - S N)%nat with p by omega.
        rewrite <- tech_pow_Rmult.
        field.
assert (Hct : continuity_pt Ss 0).
  apply continuity_pt_weaksum_r.
  rewrite Rabs_R0; assumption.
destruct (Hct 1) as [alp [Halp Hd]]; [fourier|].
assert (Hradius : exists P, forall p, (p >= P)%nat -> Rabs (En p) < r /\ Rabs (En p) < alp).
  destruct (Hcv r H) as [P1 HP1].
  destruct (Hcv alp Halp) as [P2 HP2].
  exists (Max.max P1 P2); intros p Hp.
  rewrite <- (Rminus_0_r (En p)); split.
  apply HP1; eapply le_trans; [apply Max.le_max_l|apply Hp].
  apply HP2; eapply le_trans; [apply Max.le_max_r|apply Hp].
destruct Hradius as [P HP].
exists (Rabs (Ss 0) + 1); split.
  apply Rle_ge; apply Rplus_le_le_0_compat.
    apply Rabs_pos.
    fourier.
  exists P; intros p Hp.
  assert (Hp1 : Rabs (En p) < r).
    apply (HP p); assumption.
  assert (Hp2 : Rabs (En p) < alp).
    apply (HP p); assumption.
  rewrite Hsum; [|assumption].
  rewrite Rplus_comm.
  unfold Rminus; rewrite Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  rewrite Hmul; [|assumption].
  rewrite Rabs_mult.
  rewrite Rmult_comm.
  apply Rmult_le_compat_r; [apply Rabs_pos|].
  rewrite <- (Rplus_0_l (Rabs (Ss (En p)))).
  pattern 0 at 1; erewrite <- Rplus_opp_r.
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  rewrite Rplus_comm.
  eapply Rle_trans.
    apply Rabs_triang_inv.
    destruct (Req_dec (En p) 0) as [He|He].
      rewrite He; unfold Rminus; rewrite Rplus_opp_r.
      rewrite Rabs_R0; fourier.
    apply Rlt_le; apply (Hd (En p)); split.
      compute; auto.
      simpl; unfold R_dist; rewrite Rminus_0_r.
      apply Hp2.
Qed.

Lemma Rpser_little_O_partial_sum :
  forall N (H : 0 < r) (Hcv : Rseq_cv En 0) (pr : Cv_radius_weak Un r),
    (fun p => weaksum_r Un r pr (En p) - sum_f_R0 (fun n => Un n * (En p) ^ n) N) = o((fun p => (En p) ^ N)).
Proof.
intros N H Hcv pr.
eapply Rseq_big_O_little_O_trans; [apply Rpser_big_O_partial_sum; assumption|].
intros eps Heps.
destruct (Hcv eps Heps) as [M HM].
exists M; intros n Hn.
simpl pow; rewrite Rabs_mult.
apply Rmult_le_compat_r; [apply Rabs_pos|].
apply Rlt_le; replace (En n) with (En n - 0) by field.
apply HM; assumption.
Qed.

End Taylor.
