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
Require Import Rsequence_facts.
Require Import Rsequence_cv_facts.
Require Import Rsequence_usual_facts.
Require Import Rtactic.
Require Import MyRIneq.

Require Import Cprop_base.
Require Import Csequence.
Require Import Csequence_facts.
Require Import Cpser_def Cpser_base_facts Cpser_facts.
Require Import Cseries.
Require Import Cseries_facts.
Require Import Cdefinitions.
Require Import Canalysis_def.


Open Scope C_scope.

(** * Definition and manipulation of the general term of the power serie of the exponential *)

Definition exp_seq (n : nat) := / INC (fact n).

Lemma exp_seq_neq : forall n : nat, exp_seq n <> 0.
Proof.
intro n ; unfold exp_seq ; apply Cinv_neq_0_compat ;
 apply not_0_INC ; apply fact_neq_0.
Qed.

Lemma Cdiv_exp_seq_simpl : forall n, (exp_seq (S n)) / (exp_seq n) = / INC (S n).
Proof.
intros n ; unfold exp_seq.
 replace (fact (S n))%nat with ((S n) * fact n)%nat by reflexivity ;
 unfold Cdiv ; rewrite mult_INC, Cinv_involutive ;
 [rewrite Cinv_mult_distr ;
  [rewrite Cmult_assoc, Cinv_l, Cmult_1_r ;
   [reflexivity |] | |] |] ;
   apply not_0_INC ; auto ;  apply fact_neq_0.
Qed.

Lemma Deriv_exp_seq_simpl : forall n, An_deriv exp_seq n = exp_seq n.
Proof.
intro n ; unfold exp_seq, An_deriv, Cseq_shift, Cseq_mult.
 replace (fact (S n))%nat with ((S n) * fact n)%nat by reflexivity.
 rewrite mult_INC, Cinv_mult_distr, <- Cmult_assoc, Cinv_r, Cmult_1_l ;
 [reflexivity | | |] ; replace C0 with (INC O) by reflexivity ; apply not_INC ;
 try apply fact_neq_0 ; intuition.
Qed.

(** * This power serie has a radius of convergence that is infinite *)

Lemma exp_infinite_cv_radius : infinite_cv_radius exp_seq.
Proof.
intros r.
 pose (M := (/ (Rabs r + 1))%R) ; assert (M_pos : 0 < M).
  unfold M ; apply Rinv_0_lt_compat ;
  apply Rplus_le_lt_0_compat ; [apply Rabs_pos | apply Rlt_0_1].
 apply (Cpser_alembert_prelim2 exp_seq M M_pos exp_seq_neq).

assert (t : (1 > 0)%nat) by constructor ;
 assert (H := Rseq_poly_cv 1 t) ;
 assert (H2 := Rseq_cv_pos_infty_shift_compat_reciprocal _ H) ;
 assert (H3 := Rseq_cv_pos_infty_inv_compat _ H2) ;
 clear t H H2 ; destruct (H3 _ M_pos) as [N HN] ; exists N ;
 intros n.
 rewrite Cdiv_exp_seq_simpl, <- IRC_INR_INC, <- Cinv_IRC_Rinv.
 rewrite Cnorm_IRC_Rabs.
 apply Rle_trans with (R_dist ((/ Rseq_shift (Rseq_poly 1))%Rseq (N + n)%nat) 0).
 right ; unfold R_dist, Rseq_shift, Rseq_poly, pow ; apply Rabs_eq_compat ;
 rewrite Rminus_0_r, <- (Rmult_1_r (INR (S (N + n)))) ; reflexivity.
 left ; apply HN ; intuition.
 apply not_0_INR ; intuition.

unfold M ; rewrite Rinv_involutive ; [| apply Rgt_not_eq ; apply Rplus_le_lt_0_compat ;
 [apply Rabs_pos | apply Rlt_0_1]] ; intuition.
Qed.

Definition Cexp (z : C) := sum  _ exp_infinite_cv_radius z.

Definition Deriv_Cexp (z : C) := sum_derive _ exp_infinite_cv_radius z.


(** * The exponential is its own derivative *)

Lemma Cexp_eq_Deriv_Cexp : forall z, Cexp z = Deriv_Cexp z.
Proof.
intro z.
 assert (T1 := sum_sums _ exp_infinite_cv_radius z) ;
 assert (T2 := sum_derive_sums _ exp_infinite_cv_radius z).
 symmetry ; eapply Cpser_unique_extentionality.
 apply Deriv_exp_seq_simpl.
 apply T2.
 apply T1.
Qed.

Lemma derivable_pt_lim_Cexp : forall z, derivable_pt_lim Cexp z (Cexp z).
Proof.
intro z ; rewrite Cexp_eq_Deriv_Cexp ;
 apply derivable_pt_lim_sum.
Qed.

(** ** Euler's Formula*)

Lemma Cexp_exp_compat : forall a : R, Cexp a =  exp a.
Proof.
intros a ; unfold exp, Cexp ; destruct (exist_exp a) as (l, H).
 pose (l1 := sum exp_seq exp_infinite_cv_radius (a +i  0)) ;
 assert (H1 := sum_sums _ exp_infinite_cv_radius (a +i 0)) ;
 replace (sum exp_seq exp_infinite_cv_radius (a +i  0)) with l1 in * by reflexivity.
rewrite <- Ceq ; simpl.

split.
apply (Rseq_cv_unique (sum_f_R0 (fun j : nat => (/ INR (fact j) * a ^ j)%R))).
  apply Rseq_cv_eq_compat with (fun n => Cre (sum_f_C0 (fun j : nat => / INC (fact j) * (a +i  0) ^ j) n)).
   intro n ; induction n.
  simpl ; field.
  rewrite sum_f_C0_simpl, tech5, <- Cre_add_compat, IHn ;
  apply Rplus_eq_compat_l.
  rewrite Cre_mul, Cpow_Cim_0, Cpow_Cre_0, Rmult_0_r, Rminus_0_r.
  rewrite INC_inv_Cre_INR ; [reflexivity | apply fact_neq_0].
 apply (Cseq_Rseq_Rseq_equiv _ _) ; apply Pser_Cseqcv_link ; unfold exp_seq in H1 ; apply H1.
 apply H.

 apply (Rseq_cv_unique (fun n => Cim (sum_f_C0 (fun j : nat => / INC (fact j) * (a +i  0) ^ j) n))).
  apply (Cseq_Rseq_Rseq_equiv _ _) ; apply Pser_Cseqcv_link ; unfold exp_seq in H1 ; apply H1.
  apply (Rseq_cv_eq_compat R0) ; [| apply Rseq_constant_cv].
  intro n ; induction n ; unfold Rseq_constant in *.
  simpl ; field.
  rewrite sum_f_C0_simpl, <- Cim_add_compat, <- IHn, Cim_mul, Cpow_Cim_0,
  Cpow_Cre_0, INC_inv_Cim_INR ; [ring | apply fact_neq_0].
Qed.

Lemma Cre_Cpow_2 : forall (a : R) (n : nat), Cre ((0 +i a) ^ (2 * n)) = ((-1) ^ n * a ^ (2*n))%R.
Proof.
intros a n ; induction n.
 simpl ; ring.
 replace (2 * S n)%nat with (S (S (2 * n))) by intuition.
 do 2 rewrite Cpow_S, Cre_mul ; rewrite IHn.
 rewrite Cim_mul.
 replace (Cre (0 +i a)) with R0 by reflexivity.
 repeat rewrite IHn ; simpl ; ring.
Qed.

Lemma Cim_Cpow_2 : forall (a : R) (n : nat), Cim ((0 +i a) ^ (2 * n)) = R0.
Proof.
intros a n ; induction n.
 simpl ; ring.
 replace (2 * S n)%nat with (S (S (2 * n))) by intuition.
 do 2 rewrite Cpow_S, Cim_mul ; rewrite IHn.
 rewrite Cre_mul.
 replace (Cre (0 +i a)) with R0 by reflexivity.
 repeat rewrite IHn ; ring.
Qed.

Lemma Cre_Cpow_S2 : forall (a : R) (p : nat), Cre ((0 +i  a) ^ S (2 * p)) = R0.
Proof.
intros a n ; induction n.
 simpl ; ring.
 replace (2 * S n)%nat with (S (S (2 * n))) by intuition.
 do 2 rewrite Cpow_S, Cre_mul ; rewrite IHn.
 rewrite Cim_mul.
 replace (Cre (0 +i a)) with R0 by reflexivity.
 repeat rewrite IHn ; ring.
Qed.

Lemma Cim_Cpow_S2 : forall (a : R) (n : nat), Cim ((0 +i a) ^ (S (2 * n))) = ((-1) ^ n * a ^ S (2*n))%R.
Proof.
intros a n ; induction n.
 simpl ; ring.
 replace (2 * S n)%nat with (S (S (2 * n))) by intuition.
 do 2 rewrite Cpow_S, Cim_mul ; rewrite IHn.
 rewrite Cre_mul.
 replace (Cre (0 +i a)) with R0 by reflexivity.
 repeat rewrite IHn ; simpl ; ring.
Qed.

Lemma Cexp_trigo_compat : forall a, Cexp (0 +i a) = cos a +i sin a.
Proof.
intros a ; rewrite <- Ceq ; split ; simpl ;
 pose (l := sum _ exp_infinite_cv_radius (0 +i  a)) ;
 replace (Cexp (0 +i  a)) with l by reflexivity.
 unfold cos ; destruct (exist_cos (Rsqr a)) as (l', Hl') ; unfold cos_in, cos_n in Hl'.
 apply Rseq_cv_unique with (fun N => Cre (sum_f_C0 (gt_pser exp_seq (0 +i a)) N)).
 apply (Cseq_Rseq_Rseq_equiv _ _) ; apply Pser_Cseqcv_link ; apply sum_sums.
 intros eps eps_pos ; destruct (Hl' _ eps_pos) as [N HN] ; exists (2 * N)%nat ;
 intros n n_lb ; unfold R_dist.

 destruct (n_modulo_2 n) as [H|H] ; destruct H as [p Hp] ; rewrite Hp.
 replace (Cre (sum_f_C0 (gt_pser exp_seq (0 +i  a)) (2 * p))) with
  (sum_f_R0 (fun i : nat => ((-1) ^ i / INR (fact (2 * i)) * a² ^ i)%R) p).
 apply HN ; lia.

clear ; induction p.
 simpl ; field.
 replace (2 * S p)%nat with (S (S (2 * p)))%nat by intuition.
 do 2 rewrite sum_f_C0_simpl ; rewrite tech5 ; do 2 rewrite<- Cre_add_compat ;
 rewrite <- IHp, Rplus_assoc ; apply Rplus_eq_compat_l.
 replace ((-1) ^ S p / INR (fact (2 * S p)) * a² ^ S p)%R
 with (Cre (gt_pser exp_seq (0 +i  a) (S (S (2 * p))))).
 replace (Cre (gt_pser exp_seq (0 +i  a) (S (2 * p))))%R with R0.
 symmetry ; apply Rplus_0_l.
 unfold_gt ; unfold exp_seq ; rewrite Cre_mul.
 replace (S (S (2 * p))) with (2 * S p)%nat by intuition.
 rewrite Cim_inv_INC, Rmult_0_l, Cre_Cpow_S2 ; ring.
 unfold_gt ; unfold exp_seq ; rewrite Cre_mul.
 replace (S (S (2 * p))) with (2 * S p)%nat by intuition.
 rewrite Cre_Cpow_2, Cim_Cpow_2, INC_inv_Cre_INR.
 unfold Rsqr ; rewrite pow_mult, Rmult_0_r, Rminus_0_r.
 rewrite Rmult_comm ; unfold Rdiv ; do 2 rewrite Rmult_assoc ;
 apply Rmult_eq_compat_l.
 rewrite Rmult_comm ; simpl (pow a (S (S O))) ;
 rewrite Rmult_1_r ; reflexivity.
 apply fact_neq_0.

 replace (Cre (sum_f_C0 (gt_pser exp_seq (0 +i  a)) (S (2 * p)))) with
  (sum_f_R0 (fun i : nat => ((-1) ^ i / INR (fact (2 * i)) * a² ^ i)%R) p).
 apply HN ; lia.

clear ; induction p.
 simpl ; field.
 replace (2 * S p)%nat with (S (S (2 * p)))%nat by intuition.
 do 2 rewrite sum_f_C0_simpl ; rewrite tech5 ; do 2 rewrite<- Cre_add_compat ;
 rewrite <- IHp, Rplus_assoc ; apply Rplus_eq_compat_l.
 replace ((-1) ^ S p / INR (fact (2 * S p)) * a² ^ S p)%R
 with (Cre (gt_pser exp_seq (0 +i  a) (S (S (2 * p))))).
 replace (Cre (gt_pser exp_seq (0 +i  a) (S (S (S (2 * p))))))%R with R0.
 symmetry ; apply Rplus_0_r.
 unfold_gt ; unfold exp_seq ; rewrite Cre_mul.
 replace (S (S (2 * p))) with (2 * S p)%nat by intuition.
 rewrite Cim_inv_INC, Rmult_0_l, Cre_Cpow_S2 ; ring.
 unfold_gt ; unfold exp_seq ; rewrite Cre_mul.
 replace (S (S (2 * p))) with (2 * S p)%nat by intuition.
 rewrite Cre_Cpow_2, Cim_Cpow_2, INC_inv_Cre_INR.
 unfold Rsqr ; rewrite pow_mult, Rmult_0_r, Rminus_0_r.
 rewrite Rmult_comm ; unfold Rdiv ; do 2 rewrite Rmult_assoc ;
 apply Rmult_eq_compat_l.
 rewrite Rmult_comm ; simpl (pow a (S (S O))) ;
 rewrite Rmult_1_r ; reflexivity.
 apply fact_neq_0.

 unfold sin ; destruct (exist_sin (Rsqr a)) as (l', Hl') ; unfold sin_in, sin_n in Hl'.
 apply Rseq_cv_unique with (fun N => Cim (sum_f_C0 (gt_pser exp_seq (0 +i a)) N)).
 apply (Cseq_Rseq_Rseq_equiv _ _) ; apply Pser_Cseqcv_link ; apply sum_sums.
 intros eps eps_pos ; destruct (Req_dec a 0) as [a_eq | a_neq].
 exists O ; intros n n_lb ; unfold R_dist, gt_pser ; rewrite a_eq, Rmult_0_l.
 apply Rle_lt_trans with (Rabs (0 - 0)) ;
  [| rewrite Rminus_0_r, Rabs_R0 ; assumption].
 right ; apply Rabs_eq_compat ; apply Rminus_eq_compat ; [| reflexivity].
 induction n.
 simpl ; field.
 rewrite sum_f_C0_simpl, <- Cim_add_compat, IHn, Rplus_0_l ;
 unfold gt_pser ; replace (0 +i 0) with C0 by reflexivity.
 unfold Cseq_mult ; rewrite C0_pow, Cmult_0_r ; simpl ; intuition.
 intuition.

pose (eps' := (eps / Rabs a)%R) ; assert (eps'_pos : 0 < eps').
 unfold eps', Rdiv ; apply Rlt_mult_inv_pos ; [| apply Rabs_pos_lt] ; assumption.
destruct (Hl' _ eps'_pos) as [N HN] ; exists (S (2 * N))%nat ;
 intros n n_lb ; unfold R_dist.

 destruct (n_modulo_2 n) as [H|H] ; destruct H as [p Hp] ; rewrite Hp.
 destruct p.
 apply False_ind ; clear -n_lb Hp ; lia.
 replace (Cim (sum_f_C0 (gt_pser exp_seq (0 +i  a)) (2 * S p))) with
  (a * sum_f_R0 (fun i : nat => ((-1) ^ i / INR (fact (2 * i + 1)) * a² ^ i)%R) p)%R.
  rewrite <- Rmult_minus_distr_l, Rabs_mult ; apply Rlt_le_trans with (Rabs a * eps')%R.
  apply Rmult_lt_compat_l ; [apply Rabs_pos_lt ; assumption|] ; apply HN ; lia. 
  unfold eps' ; right ; field ; apply Rabs_no_R0 ; assumption.
  rewrite scal_sum.
  clear ; induction p.
  simpl ; field.

 replace (2 * S (S p))%nat with (S (S (2 * S p))) by intuition.
 rewrite tech5 ; do 2 rewrite sum_f_C0_simpl, <- Cim_add_compat.
 rewrite IHp, Rplus_assoc ; apply Rplus_eq_compat_l.
 replace (Cim (gt_pser exp_seq (0 +i  a) (S (S (2 * S p)))))%R with R0.
 unfold_gt ; unfold exp_seq.
 rewrite Cim_mul, Cre_Cpow_S2, Cim_Cpow_S2, Rmult_0_l, Rplus_0_r,
 Rplus_0_r.
 unfold Rsqr.
 rewrite INC_inv_Cre_INR.
 replace (a ^ S (2 * S p))%R with (a * (a ^ 2) ^ (S p))%R.
 replace (2 * S p + 1)%nat with (S (2 * S p)) by intuition.
 rewrite (Rmult_comm (/ INR (fact (S (2 * S p)))) _) ; unfold Rdiv ;
 repeat rewrite Rmult_assoc ; apply Rmult_eq_compat_l.
 rewrite Rmult_comm, <- Rmult_assoc ; apply Rmult_eq_compat_r.
 rewrite Rmult_comm ; apply Rmult_eq_compat_l.
 simpl ; repeat rewrite Rmult_1_r ; reflexivity.
 rewrite <- pow_mult ; simpl ; reflexivity.
 apply fact_neq_0.
unfold_gt ; unfold exp_seq ; rewrite Cim_mul ;
replace ( S (S (2 * S p))) with (2 * (S (S p)))%nat by intuition ;
rewrite Cim_Cpow_2, INC_inv_Cim_INR.
do 2 rewrite Rmult_0_r ; ring.
apply fact_neq_0.

 replace (Cim (sum_f_C0 (gt_pser exp_seq (0 +i  a)) (S (2 * p)))) with
  (a * sum_f_R0 (fun i : nat => ((-1) ^ i / INR (fact (2 * i + 1)) * a² ^ i)%R) p)%R.
  rewrite <- Rmult_minus_distr_l, Rabs_mult ; apply Rlt_le_trans with (Rabs a * eps')%R.
  apply Rmult_lt_compat_l ; [apply Rabs_pos_lt ; assumption|] ; apply HN ; lia. 
  unfold eps' ; right ; field ; apply Rabs_no_R0 ; assumption.
  rewrite scal_sum.
  clear ; induction p.
  simpl ; field.

 replace (2 * (S p))%nat with (S (S (2 * p))) by intuition.
 rewrite tech5 ; do 2 rewrite sum_f_C0_simpl, <- Cim_add_compat.
 rewrite IHp, Rplus_assoc ; apply Rplus_eq_compat_l.
 replace (Cim (gt_pser exp_seq (0 +i  a) (S (S (2 * p)))))%R with R0.
 unfold_gt ; unfold exp_seq.
 replace (S (S (S (2 * p)))) with (S (2 * (S p))) by intuition.
 rewrite Cim_mul, Cre_Cpow_S2, Cim_Cpow_S2, Rmult_0_l,
 Rplus_0_l, Rplus_0_r.
 unfold Rsqr.
 rewrite INC_inv_Cre_INR.
 replace (a ^ S (2 * S p))%R with (a * (a ^ 2) ^ (S p))%R.
 replace (2 * S p + 1)%nat with (S (2 * S p)) by intuition.
 rewrite (Rmult_comm (/ INR (fact (S (2 * S p)))) _) ; unfold Rdiv ;
 repeat rewrite Rmult_assoc ; apply Rmult_eq_compat_l.
 rewrite Rmult_comm, <- Rmult_assoc ; apply Rmult_eq_compat_r.
 rewrite Rmult_comm ; apply Rmult_eq_compat_l.
 simpl ; repeat rewrite Rmult_1_r ; reflexivity.
 rewrite <- pow_mult ; simpl ; reflexivity.
 apply fact_neq_0.
unfold_gt ; unfold exp_seq ; rewrite Cim_mul ;
replace (S (S (2 * p))) with (2 * (S p))%nat by intuition ;
rewrite Cim_Cpow_2, INC_inv_Cim_INR.
do 2 rewrite Rmult_0_r ; ring.
apply fact_neq_0.
Qed.

Lemma Cexp_abs_cv : forall z, {l | Cser_abs_cv (gt_pser exp_seq z) l}.
Proof.
intro z ; assert (z_bd : Cnorm z < Cnorm z + 1) by intuition ;
 destruct (Cpser_abel2_prelim _ _ (exp_infinite_cv_radius (Cnorm z + 1)%R) _ z_bd) as [l Hl].
 unfold Cpser_norm in Hl.
 exists (Cre l) ; unfold Cser_abs_cv.
apply Rseq_cv_eq_compat with 
      (fun n => Cre (sum_f_C0 (fun n : nat => Cnorm (gt_pser exp_seq z n)) n)).
intro n ; rewrite <- sum_f_C0_Cre_compat ; simpl ; reflexivity.
apply Cseq_cv_re_compat.
auto.
Qed.

Lemma binomial_diag : forall n, Binomial.C n n = 1%R.
Proof.
intros n.
unfold Binomial.C.
rewrite minus_diag.
simpl.
field.
INR_solve; apply fact_neq_0.
Qed.

Lemma binomial_zero : forall n, Binomial.C n 0 = 1%R.
Proof.
intros n.
unfold Binomial.C.
simpl.
rewrite <- minus_n_O.
field.
INR_solve; apply fact_neq_0.
Qed.

Open Scope C_scope.

Lemma binomial_sum : forall (x y:C) n,
  (x + y) ^ n = sum_f_C0 (fun p => IRC (Binomial.C n p) * x ^ p * y ^ (n - p)) n.
Proof.
intros x y n.
induction n.
 unfold Binomial.C; simpl.
 rewrite <- Ceq; simpl; split; field.
 
 destruct n.
  unfold Binomial.C; simpl.
  rewrite <- Ceq; simpl; split; field.
  
  rewrite sum_f_C0_simpl.
  rewrite <- sum_f_C0_reindex.
  
  rewrite Csum_eq_compat with _ (fun k => 
    Binomial.C (S n)    k  * x ^ S k * y ^ (S (S n) - S k) +
    Binomial.C (S n) (S k) * x ^ S k * y ^ (S (S n) - S k)) _.
   rewrite sum_f_C0_add_compat.
   rewrite Cpow_S.
   rewrite IHn.
   rewrite Cmult_add_distr_l.
   do 2 (rewrite Cmult_comm; rewrite sum_f_C0_mult).
   assert (AP:forall a b c d e f, a = d + f -> b = c + e -> a + b = c + (d + e) + f)
     by (intros; subst; ring); apply AP; clear AP.
    rewrite sum_f_C0_simpl.
    repeat rewrite binomial_diag.
    repeat rewrite minus_diag.
    apply Cadd_eq_compat.
     apply Csum_eq_compat_weak; intro; simpl; ring.
     simpl; ring.
    
    rewrite <- sum_f_C0_reindex.
    apply Cadd_eq_compat.
     simpl; repeat rewrite binomial_zero; ring.
     apply Csum_eq_compat; intros j Hj.
     rewrite <- minus_Sn_m with (S n) _; [|lia].
     simpl; ring.
   
   intros j Hj.
   repeat rewrite <- Cmult_add_distr_r.
   rewrite <- Binomial.pascal; [|lia].
   rewrite Cadd_IRC_Rplus; trivial.
Qed.

Lemma Cexp_add : forall a b, Cexp (a + b) = (Cexp a * Cexp b)%C.
Proof.
intros a b.
unfold Cexp.
pose (gt_pser exp_seq) as tg.
apply Cser_cv_unique with (tg (a + b)).
apply sum_sums.
destruct (Cexp_abs_cv a) as [lna Hlna].
 eapply Cser_cv_eq_compat.
  2:eapply (Ccauchy_product (tg a) (tg b)) ; try apply sum_sums.
  
  intro n; simpl.
  unfold tg, exp_seq ; unfold_gt.
  rewrite binomial_sum.
  rewrite sum_f_C0_mult.
  apply Csum_eq_compat_weak; intros p.
  unfold Binomial.C.
  rewrite Cdiv_IRC_Rdiv.
   repeat rewrite Cmult_IRC_Rmult.
   repeat rewrite IRC_INR_INC.
   field; repeat split; replace C0 with (INC O)%C by trivial;
     apply not_INC; apply fact_neq_0.
  apply Rmult_integral_contrapositive.
   INR_solve; apply fact_neq_0.
apply Hlna.
Qed.

Lemma Cexp_0 : Cexp C0 = C1.
Proof.
replace C0 with (IRC (IZR 0)) by auto.
rewrite Cexp_exp_compat ; rewrite exp_0 ; auto.
Qed.

Lemma Cexp_mult : forall a n, Cexp (INC n * a) = (Cexp a) ^ n.
Proof.
intros a n ; induction n.
simpl ; rewrite Cmult_0_l ; apply Cexp_0.
rewrite S_INC, Cpow_S, Cmult_add_distr_r,
 Cmult_1_l, Cexp_add, IHn ; ring. 
Qed.
