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

Require Import Rinterval Ranalysis_def.
Require Import Rpser_def Rpser_base_facts Rpser_cv_facts Rpser_sums.
Require Import Rpow_facts.
Require Import Rsequence_def Rsequence_facts.
Require Import Rseries_def Rseries_facts.
Require Import RFsequence_facts.

Require Import Cpow Cpser_def Cpser_base_facts.
Require Import CFsequence CFsequence_facts.
Require Import Csequence Csequence_def Csequence_facts.
Require Import Cmet Cnorm Ctacfield.
Require Import Cprop_base.

Require Import Canalysis_def.
Require Import Canalysis_cont.
Require Import Canalysis_deriv.
Require Import Canalysis_basic_facts.

Local Open Scope C_scope.

Lemma Rseq_norm_abs_Cre : 
forall (An : nat -> C), {l | Rseq_cv (fun n => sum_f_R0 (fun n =>(Cnorm (An n))) n) l} -> 
{l | Rseq_cv (fun n => sum_f_R0 (fun n =>(Rabs (Cre (An n))))n) l}.
Proof.
intros An H.
apply Rseries_CV_comp with (fun n0 : nat => Cnorm (An n0)) .
intros n. split.
apply Rabs_pos. 
apply Cre_le_Cnorm.
exact H.
Qed.

Lemma Rseq_norm_abs_Cim : 
forall (An : nat -> C), {l | Rseq_cv (fun n => sum_f_R0 (fun n =>(Cnorm (An n)))n) l} -> 
{l | Rseq_cv (fun n => sum_f_R0 (fun n =>(Rabs (Cim (An n))))n) l}.
Proof.
intros An H.
apply Rseries_CV_comp with (fun n0 : nat => Cnorm (An n0)) .
intros n. split.
apply Rabs_pos. 
apply Cim_le_Cnorm.
exact H.
Qed.

Lemma Cseq_norm_Rseq :
forall (An : nat -> C), {l | Rseq_cv (fun n => sum_f_R0 (fun n =>(Cnorm (An n)))n) l} -> 
{l | Cseq_cv (fun n => sum_f_C0 (fun n =>((An n)))n) l}.
Proof.
intros An H.
generalize (Rseq_norm_abs_Cim An H).
generalize (Rseq_norm_abs_Cre An H).
intros Hre Him.
assert ( H1 : {l : R |
      Rseq_cv
        (fun n : nat => sum_f_R0 (fun n0 : nat => Cim (An n0)) n) l}).
apply (Rser_abs_cv_cv  (fun n0 : nat => Cim (An n0))).
unfold Rser_abs_cv.
unfold Rseq_abs.
apply Him.
assert ( H2 : {l : R |
      Rseq_cv
        (fun n : nat => sum_f_R0 (fun n0 : nat => Cre (An n0)) n) l}).
apply (Rser_abs_cv_cv  (fun n0 : nat => Cre (An n0))).
unfold Rser_abs_cv.
unfold Rseq_abs.
apply Hre.
destruct H1 as (lim, H1).
destruct H2 as (lre, H2).
exists (lre +i lim).
apply <- Cseq_Rseq_Rseq_equiv.
split. simpl.
assert ((fun n : nat => Cre (sum_f_C0 (fun n0 : nat => An n0) n)) ==
(fun n : nat => sum_f_R0 (fun n0 : nat => Cre (An n0)) n)).
unfold "==".
intros n. rewrite <- sum_f_C0_Cre_compat. reflexivity.
apply (Rseq_cv_eq_compat (fun n : nat => sum_f_R0 (fun n0 : nat => Cre (An n0)) n)
(fun n : nat => Cre (sum_f_C0 (fun n0 : nat => An n0) n))).
apply Rseq_eq_sym. assumption.
assumption.
assert ((fun n : nat => Cim (sum_f_C0 (fun n0 : nat => An n0) n)) ==
(fun n : nat => sum_f_R0 (fun n0 : nat => Cim (An n0)) n)).
unfold "==".
intros n. rewrite <- sum_f_C0_Cim_compat. reflexivity.
apply (Rseq_cv_eq_compat (fun n : nat => sum_f_R0 (fun n0 : nat => Cim (An n0)) n)
(fun n : nat => Cim (sum_f_C0 (fun n0 : nat => An n0) n))).
apply Rseq_eq_sym. assumption.
assumption.
Qed.
 

Lemma Cpser_abel : forall (An : nat -> C) (r : R), 
     Cv_radius_weak An r -> forall x, Cnorm x < r -> {l | Cpser An x l}.
Proof.
intros An r Rho x x_ub.
 case (Req_or_neq r) ; intro r_0.
 exists 0 ; apply False_ind ; rewrite r_0 in x_ub ; assert (0 <= Cnorm x). apply Cnorm_pos. lra.
assert (Hrew_abs : (Cnorm (x / r) = Cnorm x / r)%R).
 unfold Cdiv, Rdiv ; rewrite Cnorm_Cmult ; apply Rmult_eq_compat_l ;
 replace (/r) with (IRC (/r)). rewrite Cnorm_IRC_Rabs.
 apply Rabs_right.
 left ; apply Rinv_0_lt_compat ; apply Rle_lt_trans with (Cnorm x) ;
 [apply Cnorm_pos | assumption].
 CusingR_f ; assumption.
assert (Rabsx_r_lt_1 : Cnorm x / r < 1).
 apply Rle_lt_trans with (Cnorm x / r * (r / r))%R.
 right ; field ; assumption.
 replace 1%R with (r / r)%R by (field ; assumption).
 unfold Rdiv ; rewrite <- Rmult_assoc.
 apply Rmult_lt_compat_r.
 apply Rinv_0_lt_compat ; apply Rle_lt_trans with (Cnorm x) ;
 [apply Cnorm_pos | assumption].
 rewrite Rmult_assoc ; rewrite Rinv_l ; [| assumption] ; rewrite Rmult_1_r ; assumption.

 assert (Rho' : Rpser_def.Cv_radius_weak (fun n : nat => Cnorm (An n)) r).
 destruct Rho as [M HM] ; exists M.
 intros u [n Hn] ; rewrite Hn ; unfold gt_abs_pser, Rpser_def.gt_pser,
 Rseq_abs, Rseq_mult. unfold gt_norm_pser, gt_pser, Cseq_norm, Cseq_mult in HM.
 replace (Rabs (Cnorm (An n) * r ^ n))%R with (Cnorm (An n * r ^ n))%R.
 apply HM ; exists n ; reflexivity.
 rewrite Rabs_mult ; replace (Rabs (r ^ n))%R with (Rabs (Cnorm r ^ n))%R.
 rewrite <- Rabs_mult, <- Cnorm_pow, <- Cnorm_Cmult, Rabs_Cnorm ; reflexivity.
 rewrite <- Cnorm_pow, IRC_pow_compat, Cnorm_IRC_Rabs, Rabs_Rabsolu ;
 reflexivity.
 rewrite <- Rabs_Cnorm in x_ub.
 assert (Cnorm_cauchy := Cauchy_crit_Rseq_pps
    (fun n => Cnorm (An n)) r Rho' (Cnorm x) x_ub).

assert (T : Rseries.Cauchy_crit (sum_f_R0 (fun n : nat => Cnorm (An n * x ^ n)))).
 intros eps eps_pos ; destruct (Cnorm_cauchy eps eps_pos) as [N HN] ;
 exists N ; intros m n m_lb n_lb.
 
assert (Hrew : forall An x n, sum_f_R0 (fun n0 : nat => Cnorm (An n0 * x ^ n0)) n
      = sum_f_R0 (Rpser_def.gt_pser (fun n0 : nat => Cnorm (An n0)) (Cnorm x)) n).
 clear ; intros An x n ; induction n.
 unfold Rpser_def.gt_pser ; simpl ; rewrite Cnorm_Cmult, Cnorm_C1 ;
 reflexivity.
 simpl sum_f_R0 ; rewrite IHn ; apply Rplus_eq_compat_l ;
 unfold Rpser_def.gt_pser ; simpl ; repeat rewrite Cnorm_Cmult ;
 rewrite Cnorm_pow ; reflexivity.
repeat rewrite Hrew ; rewrite R_dist_sym ; apply HN ; assumption.

 destruct (Cseq_norm_Rseq (fun n => An n * x ^ n) (R_complete _ T)) as [l Hl] ;
 exists l ; apply Hl.
Qed.

(** Definition of the sum of a power serie (0 outside the cv-disc) *)

Definition weaksum_r : forall (An : nat -> C) (r : R) (Pr : Cv_radius_weak An r), C -> C.
Proof.
intros An r Rho x.
 case (Rlt_le_dec (Cnorm x) r) ; intro x_bd.
 elim (Cpser_abel _ _ Rho _ x_bd) ; intros y Hy ; exact y.
 exact 0.
Defined.

Definition sum_r : forall (An : nat -> C) (r : R) (Pr : finite_cv_radius An r), C -> C.
Proof.
intros An r Pr x.
 case (Rlt_le_dec (Cnorm x) r) ; intro x_bd.
  assert (rho : Cv_radius_weak An (middle (Cnorm x) r)).
  apply Pr; split.
  apply Rle_trans with (Cnorm x).
   apply Cnorm_pos.
   left ; apply (proj1 (middle_is_in_the_middle _ _ x_bd)).
   apply (proj2 (middle_is_in_the_middle _ _ x_bd)).
 apply (weaksum_r An (middle (Cnorm x) r) rho x).
 exact 0.
Defined.

Definition sum : forall (An : nat -> C) (Pr : infinite_cv_radius An), C -> C.
Proof.
intros An Pr r.
 apply (weaksum_r An (Cnorm r +1) (Pr (Cnorm r + 1)%R) r).
Defined.

(** Establishing the link between these functions and the sum *)

Lemma weaksum_r_sums : forall (An : nat -> C) (r : R) (Pr : Cv_radius_weak An r) (x : C),
      Cnorm x < r -> Cpser An x (weaksum_r An r Pr x).
Proof.
intros An r Pr x x_bd.
 unfold weaksum_r ; case (Rlt_le_dec (Cnorm x) r) ; intro s.
 destruct (Cpser_abel An r Pr x s) as (l,Hl) ; simpl ; assumption.
 apply False_ind ; lra.
Qed.

Lemma sum_r_sums : forall (An : nat -> C) (r : R) (Pr : finite_cv_radius An r),
      forall x, Cnorm x < r -> Cpser An x (sum_r An r Pr x).
Proof.
intros An r Pr x x_ub.
 unfold sum_r ; destruct (Rlt_le_dec (Cnorm x) r) as [x_bd | x_nbd].
 apply weaksum_r_sums.
 apply (proj1 (middle_is_in_the_middle _ _ x_bd)).
  apply False_ind ; lra.
Qed.

Lemma sum_sums : forall (An : nat -> C) (Pr : infinite_cv_radius An),
      forall x, Cpser An x (sum An Pr x).
Proof.
intros An Pr x.
 apply weaksum_r_sums ; intuition.
Qed.

(** Proof that the sum is unique *)

Lemma weaksum_r_unique : forall (An : nat -> C) (r : R) (Pr1 Pr2 : Cv_radius_weak An r) (x : C),
     Cnorm x < r -> weaksum_r An r Pr1 x = weaksum_r An r Pr2 x.
Proof.
intros An r Pr1 Pr2 x x_bd ;
 assert (T1 := weaksum_r_sums _ _ Pr1 _ x_bd) ;
 assert (T2 := weaksum_r_sums _ _ Pr2 _ x_bd) ;
 eapply Pser_unique ; eassumption.
Qed.

Lemma weaksum_r_unique_strong : forall (An : nat -> C) (r1 r2 : R) (Pr1 : Cv_radius_weak An r1)
     (Pr2 : Cv_radius_weak An r2) (x : C), Cnorm x < r1 -> Cnorm x < r2 ->
     weaksum_r An r1 Pr1 x = weaksum_r An r2 Pr2 x.
Proof.
intros An r1 r2 Pr1 Pr2 x x_bd1 x_bd2.
  assert (T1 := weaksum_r_sums _ _ Pr1 _ x_bd1) ;
  assert (T2 := weaksum_r_sums _ _ Pr2 _ x_bd2) ;
 eapply Pser_unique ; eassumption.
Qed.

Lemma sum_r_unique : forall (An : nat -> C) (r : R) (Pr1 Pr2 : finite_cv_radius An r) (x : C),
     Cnorm x < r -> sum_r An r Pr1 x = sum_r An r Pr2 x.
Proof.
intros An r Pr1 Pr2 x x_bd ;
 assert (T1 := sum_r_sums _ _ Pr1 _ x_bd) ;
 assert (T2 := sum_r_sums _ _ Pr2 _ x_bd) ;
 eapply Pser_unique ; eassumption.
Qed.

Lemma sum_r_unique_strong : forall (An : nat -> C) (r1 r2 : R) (Pr1 : finite_cv_radius An r1)
     (Pr2 : finite_cv_radius An r2) (x : C), Cnorm x < r1 -> Cnorm x < r2 ->
     sum_r An r1 Pr1 x = sum_r An r2 Pr2 x.
Proof.
intros An r1 r2 Pr1 Pr2 x x_bd1 x_bd2 ;
 assert (T1 := sum_r_sums _ _ Pr1 _ x_bd1) ;
 assert (T2 := sum_r_sums _ _ Pr2 _ x_bd2) ;
 eapply Pser_unique ; eassumption.
Qed.

Lemma sum_unique : forall (An : nat -> C) (Pr1 Pr2 : infinite_cv_radius An) (x : C),
      sum An Pr1 x = sum An Pr2 x.
Proof.
intros An Pr1 Pr2 x ;
 assert (T1 := sum_sums  _ Pr1 x) ;
 assert (T2 := sum_sums  _ Pr2 x) ;
 eapply Pser_unique ; eassumption.
Qed.
   
(** Abel's lemma : Normal convergence of the power serie *)

Lemma Cpser_abel2_prelim : forall (An : nat -> C) (r : R), 
     Cv_radius_weak An r -> forall x, Cnorm x < r ->
     { l | Cpser_norm An x l}.
Proof.
intros An r Rho x x_bd.
 assert (Rho' : Rpser_def.Cv_radius_weak (fun n => Cnorm (An n)) r).
  destruct Rho as [B HB] ; exists B ; intros u [n Hn] ; rewrite Hn ; apply HB ;
  exists n ; unfold_gt ; unfold gt_abs_pser, Rpser_def.gt_pser, Rseq_mult, Rseq_abs.
  rewrite Rabs_mult, Cnorm_Cmult, Rabs_Cnorm ; apply Rmult_eq_compat_l ;
  rewrite IRC_pow_compat, Cnorm_IRC_Rabs ; reflexivity.
 rewrite <- Rabs_Cnorm in x_bd ; pose (l := Rpser_sums.weaksum_r _ _ Rho' (Cnorm x)) ;
 exists l ; unfold Cpser_norm, Pser, infinite_sum.
 assert (Hl := Rpser_sums.weaksum_r_sums _ _ Rho' (Cnorm x) x_bd) ;
 unfold Rseries.Pser, Rfunctions.infinite_sum in Hl.

 assert (Hrew : forall n, IRC (sum_f_R0 (fun n0 : nat => (Cnorm (An n0) * Cnorm x ^ n0)%R) n) =
                  sum_f_C0 (fun n0 : nat => Cnorm (An n0 * x ^ n0)) n).
 clear ; intro n ; induction n.
  simpl ; rewrite Cmult_1_r, Rmult_1_r ; reflexivity.
  simpl ; rewrite <- IHn.
  rewrite Cadd_IRC_Rplus ; apply Cadd_eq_compat_l.
  repeat rewrite Cnorm_Cmult ; repeat rewrite Cmult_IRC_Rmult ;
  apply Cmult_eq_compat_l ; rewrite Cnorm_pow ; reflexivity.
  intros eps eps_pos ; destruct (Hl _ eps_pos) as [N HN] ;
  exists N ; intros n n_lb ; simpl ; unfold C_dist.
  unfold_gt.
 rewrite <- Hrew, <- Cminus_IRC_Rminus, Cnorm_IRC_Rabs ;
  apply HN ; assumption.
Qed.  


Lemma Cpser_abel2 : forall (An : nat -> C) (r : R), 
     Cv_radius_weak An r -> forall r0 : posreal, r0 < r ->
     CVN_r (fun n x => gt_pser An x n) r0.
Proof.
intros An r Pr r0 r0_ub.
 destruct r0 as (a,a_pos).
 assert (a_bd : Rabs a < r).
  rewrite Rabs_right ; [| apply Rgt_ge ; apply Rlt_gt] ; assumption.
 assert (r_pos : 0 < r). 
  apply Rlt_trans with a ; assumption.
 assert (r'_bd : Rabs ((a + r) / 2) < r).
  rewrite Rabs_right.
  assert (Hrew : r = ((r+r)/2)%R) by field ; rewrite Hrew at 2; unfold Rdiv ;
  apply Rmult_lt_compat_r ; [apply Rinv_0_lt_compat ; intuition |] ;
  apply Rplus_lt_compat_r ; rewrite Rabs_right in a_bd ; intuition.
  apply Rle_ge ; unfold Rdiv ; replace 0%R with (0 * /2)%R by field ;
  apply Rmult_le_compat_r ; lra.
 assert (r'_bd2 : Cnorm (Rabs ((a + r) / 2)) < r).
 rewrite Cnorm_IRC_Rabs, Rabs_Rabsolu ; assumption.
 assert (Pr' := Cv_radius_weak_Cnorm_compat2 _ _ Pr).
 exists (gt_abs_pser (fun n => Cnorm (An n)) ((a+r)/2)).
 exists (Rpser_sums.weaksum_r (fun n => Cnorm (An n)) r Pr' (Rabs ((a+r)/2))) ; split.
 rewrite Cnorm_IRC_Rabs in r'_bd2 ;
 assert (H := Rpser_sums.weaksum_r_sums (fun n => Cnorm (An n)) r Pr' (Rabs ((a + r) / 2)) r'_bd2).
 unfold Rpser in H.
 intros eps eps_pos ; destruct (H eps eps_pos) as (N, HN) ; exists N.
  assert (Hrew : forall k, Cnorm (gt_abs_pser (fun n => Cnorm (An n)) ((a + r) / 2) k)
  = Rpser_def.gt_pser (fun n0 : nat => Cnorm (An n0)) (Rabs ((a + r) / 2)) k).
   intro k ; unfold gt_abs_pser, Rpser_def.gt_pser, Rseq_mult, Rseq_abs.
   rewrite Cnorm_IRC_Rabs, Rabs_Rabsolu, Rabs_mult, <- RPow_abs, Rabs_Cnorm ;
   reflexivity.
 assert (Temp : forall n, sum_f_R0 (fun k : nat =>
             Cnorm (gt_abs_pser (fun n0 : nat => Cnorm (An n0)) ((a + r) / 2) k)) n
            = sum_f_R0 (Rpser_def.gt_pser (fun n0 : nat => Cnorm (An n0)) (Rabs ((a + r) / 2))) n).
   intros n ; clear -Hrew ; induction n ; simpl ; rewrite Hrew ; [| rewrite IHn] ; reflexivity.
  intros n n_lb ; rewrite Temp ; apply HN ; assumption.
 intros n y Hyp ; unfold_gt ; unfold gt_abs_pser, Rpser_def.gt_pser, Rseq_abs, Rseq_mult.
 rewrite Rabs_mult, Rabs_Cnorm ; repeat rewrite Cnorm_Cmult, Cnorm_IRC_Rabs,
 Rabs_mult, Rabs_right.
 apply Rmult_le_compat_l.
 apply Cnorm_pos.
 rewrite Rabs_Rabsolu.
 rewrite <- Cnorm_IRC_Rabs ; rewrite <- IRC_pow_compat ;
 repeat rewrite Cnorm_pow ; apply pow_incr ; split ; [apply Cnorm_pos |].
 unfold Boule in Hyp ; simpl in Hyp ; unfold C_dist in Hyp ;
 rewrite Cnorm_minus_sym, Cminus_0_r in Hyp.
 apply Rle_trans with a ; [left ; assumption |].
 rewrite Cnorm_IRC_Rabs, Rabs_right.
 apply Rle_trans with ((a + a) / 2)%R ; [right ; field | unfold Rdiv ;
 apply Rmult_le_compat_r ; [lra | apply Rplus_le_compat_l ; left ; assumption]].
 unfold Rdiv ; apply Rle_ge ; apply Rle_mult_inv_pos ; lra.
 apply Rle_ge ; apply Cnorm_pos.
Qed.

Lemma Rminus_Rlt : forall a b, 0 < a - b -> b < a.
Proof.
intros a b H.
 replace b with (b + 0)%R by ring.
 replace a with (b + (a - b))%R by ring.
 apply Rplus_lt_compat_l ; assumption.
Qed.

Lemma Cpser_alembert_prelim : forall (An : nat -> C) (M : R),
       0 < M -> (forall n : nat, An n <> C0) ->
       Cseq_bound (fun n => (An (S n) / An n)) M -> forall r,
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
 exists (Cnorm (An 0%nat)) ; intros x Hyp ;
  elim Hyp ; intros n Hn ; rewrite Hn ;
  unfold_gt ; rewrite Cnorm_Cmult.
  clear Hn ; induction n.
  simpl ; rewrite Cnorm_C1 ; rewrite Rmult_1_r ; right ; reflexivity.
  apply Rle_trans with (Cnorm (An (S n) / (An n)) * Cnorm (An n) * Cnorm (r ^ S n))%R.
  right ; repeat rewrite <- Cnorm_Cmult ; apply Cnorm_eq_compat ;
  field ; apply An_neq.
  apply Rle_trans with (M * Cnorm (An n) * Cnorm (r ^ S n))%R.
  repeat apply Rmult_le_compat_r ; [| | apply An_frac_ub] ; apply Cnorm_pos.
  simpl ; rewrite Cnorm_Cmult.
  apply Rle_trans with (M * Cnorm (An n) * (/M * Cnorm (r ^ n)))%R.
  repeat rewrite <- Rmult_assoc ; apply Rmult_le_compat_r ; [apply Cnorm_pos |
  repeat rewrite Rmult_assoc ; repeat apply Rmult_le_compat_l].
  left ; assumption.
  apply Cnorm_pos.
  rewrite Cnorm_IRC_Rabs ; left ; assumption.
  apply Rle_trans with (Cnorm (An n) * Cnorm (r ^ n))%R ; [right ; field ;
  apply Rgt_not_eq |] ; assumption.
 exists (Cnorm (An 0%nat)).
  intros x Hx ; destruct Hx as (n,Hn) ; rewrite Hn ;
   unfold_gt ; destruct n.
  right ; apply Cnorm_eq_compat ; ring.
  destruct (Req_dec r 0) as [Hr | Hf].
  rewrite Hr ; unfold gt_norm_pser ; rewrite Cnorm_Cmult, Cnorm_pow,
  Cnorm_IRC_Rabs, RPow_abs, pow_i, Rabs_R0, Rmult_0_r ;
  [apply Cnorm_pos | intuition].
  apply False_ind ; assert (T := Rabs_no_R0 _ Hf) ;
  apply T ; symmetry ; assumption.
Qed.

Lemma Cpser_alembert_prelim2 : forall (An : nat -> C) (M : R),
       0 < M -> (forall n : nat, An n <> C0) ->
       Cseq_eventually (fun Un => Cseq_bound Un M) (fun n => (An (S n) / An n)) ->
       forall r, Rabs r < / M -> Cv_radius_weak An r.
Proof.
intros An M M_pos An_neq An_frac_event r r_bd.
destruct An_frac_event as [N HN].
 assert (Rho : Cv_radius_weak (fun n => (An (N + n)%nat)) r).
  apply Cpser_alembert_prelim with M.
  assumption.
  intro n ; apply An_neq.
  intro n ; replace (N + S n)%nat with (S (N + n)) by intuition ; apply HN.
  assumption.
 apply Cv_radius_weak_padding_neg_compat with N ;
 destruct Rho as [T HT] ; exists T ; intros u Hu ; destruct Hu as [n Hn] ;
 rewrite Hn ; unfold_gt ; rewrite plus_comm ; apply HT ;
 exists n ; reflexivity.
Qed.

Lemma Cpser_alembert_prelim3 : forall (An : nat -> C) (lambda : C),
       0 < Cnorm (lambda) -> (forall n : nat, An n <> C0) ->
       Rseq_cv (fun n : nat => Cnorm (An (S n) / An n)) (Cnorm lambda) -> forall r,
       Rabs r < / (Cnorm lambda) -> Cv_radius_weak An r.
Proof.
intros An lam lam_pos An_neq An_frac_cv r r_bd.
 assert (middle_lb := proj1 (middle_is_in_the_middle _ _ r_bd)).
 assert (middle_ub := proj2 (middle_is_in_the_middle _ _ r_bd)).
 assert (middle_pos : 0 < middle (Rabs r) (/Cnorm lam)).
  apply Rle_lt_trans with (Rabs r) ; [apply Rabs_pos | assumption].
 pose (eps := (/ (middle (Rabs r) (/ Cnorm lam)) - Cnorm lam)%R).
 assert (eps_pos : 0 < eps).
  apply Rgt_minus ; rewrite <- Rinv_involutive.
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat ; [| apply Rinv_0_lt_compat] ; assumption.
  assumption.
  apply Rgt_not_eq ; assumption.
 apply Cpser_alembert_prelim2 with (Cnorm lam + eps)%R.
 lra.
 apply An_neq.
 destruct (An_frac_cv (/ (middle (Rabs r) (/ Cnorm lam)) - Cnorm lam))%R as [N HN].
 assumption.
 exists N ; intro n.
 apply Rle_trans with (Cnorm lam + (Cnorm (An (S (N + n)) / An (N + n)%nat)
      - Cnorm lam))%R.
 right ; ring.
 apply Rplus_le_compat_l ; apply Rle_trans with
   (R_dist (Cnorm (An (S (N + n)) / An (N + n)%nat)) (Cnorm lam))%R.
 apply RRle_abs.
 left ; apply HN ; intuition.
 replace (Cnorm lam + eps)%R with (/ (middle (Rabs r) (/ Cnorm lam)))%R.
 rewrite Rinv_involutive ; [| apply Rgt_not_eq] ; assumption.
 unfold eps ; ring.
Qed.

Lemma Cpser_alembert_prelim4 : forall (An : nat -> C),
       (forall n : nat, An n <> C0) ->
       Rseq_cv (fun n : nat => Cnorm (An (S n) / An n)) R0 ->
       infinite_cv_radius An.
Proof.
intros An An_neq An_frac_0 r.
 assert (eps_pos : 0 < /(Rabs r + 1)).
  apply Rinv_0_lt_compat ; apply Rplus_le_lt_0_compat ; [apply Rabs_pos |
  apply Rlt_0_1].
 apply Cpser_alembert_prelim2 with (/(Rabs r + 1))%R.
 assumption.
 apply An_neq.
 destruct (An_frac_0 (/ (Rabs r + 1))%R eps_pos) as [N HN] ; exists N ; intro n.
 apply Rle_trans with (R_dist (Cnorm (An (S (N + n)) / An (N + n)%nat)) 0) ; [right |].
 unfold R_dist in |-* ; rewrite Rminus_0_r, Rabs_right ; [reflexivity | apply Rle_ge ;
 apply Cnorm_pos].
 left ; apply HN ; intuition.
 rewrite Rinv_involutive ; [lra |] ; apply Rgt_not_eq ;
 apply Rplus_le_lt_0_compat ; [apply Rabs_pos | apply Rlt_0_1].
Qed.

Lemma Cpser_bound_criteria : forall (An : nat -> C) (z l : C),
    Cpser An z l -> Cv_radius_weak An (Cnorm z).
Proof.
intros An z l Hzl.
 destruct Hzl with R1 as (N, HN) ; [lra |].
 assert (H1 : forall n :  nat, (n >= S N)%nat -> gt_norm_pser An z n
    <= Rmax 2 (Cnorm (An 0%nat) + 1)).
  intros n Hn ; case_eq n ; unfold_gt.
  intro H ; simpl ; rewrite Cmult_1_r ; apply Rle_trans with (Cnorm (An 0%nat) +1)%R ;
   [intuition | apply RmaxLess2].
   intros m Hrew ; replace (Cnorm (An (S m) * z ^ S m)) with
         (Cnorm ((sum_f_C0 (fun n0 : nat => An n0 * z ^ n0) (S m) - l) +
         (l - sum_f_C0 (fun n0 : nat => An n0 * z ^ n0) m))).
    apply Rle_trans with (Rplus (Cnorm (sum_f_C0 (fun n0 : nat => An n0 * z ^ n0)%C (S m) - l))
          (Cnorm (l - sum_f_C0 (fun n0 : nat => An n0 * z ^ n0) m))).
  apply Cnorm_triang.
   apply Rle_trans with 2 ; [|apply RmaxLess1] ; apply Rlt_le ; apply Rplus_lt_compat ;
   [| rewrite Cnorm_minus_sym].
   apply Rle_lt_trans with (dist C_met (sum_f_C0 (fun n0 : nat => An n0 * z ^ n0)
         (S m)) l).
  right ; simpl ; unfold C_dist ; reflexivity.
  simpl (dist C_met) ;unfold C_dist ; unfold Cseq_sum, gt_pser, Cseq_mult in HN ;
  apply HN ; intuition.
  apply Rle_lt_trans with (dist C_met (sum_f_C0 (fun n0 : nat => An n0 * z ^ n0) m) l).
  right ; simpl ; unfold C_dist ; reflexivity.
  simpl (dist C_met) ;unfold C_dist ; unfold Cseq_sum, gt_pser, Cseq_mult in HN ;
  apply HN ; intuition.
   simpl sum_f_C0 ; apply Cnorm_eq_compat.
   simpl ; ring.
   destruct (Cseq_partial_bound (gt_pser An z) (S N)) as (B,HB).
   exists (Rmax B (Rmax 2 (Cnorm (An 0%nat) + 1))).
   intros y Hy ; destruct Hy as [u Hu] ; rewrite Hu.
   case (le_lt_dec u (S N)) ; intro Hu_b.
   apply Rle_trans with B.
   unfold_gt ; rewrite Cnorm_Cmult, Cnorm_pow, Cnorm_invol.
   rewrite <- Cnorm_pow. rewrite <- Cnorm_Cmult.
   apply HB ; assumption.
   apply RmaxLess1.
   unfold_gt ; rewrite Cnorm_Cmult.
   rewrite Cnorm_pow, Cnorm_invol, <- Cnorm_pow, <- Cnorm_Cmult.
   apply Rle_trans with (Rmax 2 (Cnorm (An 0%nat) + 1)) ; [apply H1 | apply RmaxLess2] ; intuition.
Qed.

(** A sufficient condition for the radius of convergence*)
Lemma Cpser_finite_cv_radius_caracterization : forall (An : nat -> C) (z l : C),
   Cpser An z l -> (forall l' : R, ~ Cpser_norm An z l')  -> finite_cv_radius An (Cnorm z).
Proof.
intros An z l Hcv Hncv.
split; intros x Hx.

 apply Cv_radius_weak_le_compat with (Cnorm z).
 rewrite Rabs_Cnorm ; rewrite Rabs_right ; intuition.

  apply (Cpser_bound_criteria _ _ l Hcv).
  
 intro Hf.
 destruct (Cpser_abel2_prelim An x Hf z) as [l' Hl'].
 assumption.
 apply (Hncv (Cnorm l')).
Abort.

Lemma Cpser_infinite_cv_radius_caracterization :
  forall An, (forall x, {l | Cpser An x l}) ->
  infinite_cv_radius An.
Proof.
intros An weaksum r ; destruct (weaksum r) as (l, Hl).
 assert (H := Cpser_bound_criteria An r l Hl).
 rewrite Cnorm_IRC_Rabs in H.
 apply Cv_radius_weak_le_compat with (Rabs r).
 rewrite Rabs_Rabsolu ; right ; reflexivity.
 assumption.
Qed.


Lemma Cv_radius_weak_derivable_compat : forall An r,
         Cv_radius_weak An r -> forall r', Rabs r' < Rabs r ->
         Cv_radius_weak (An_deriv An) r'.
Proof.
intros An r rho r' r'_bd.
 assert (Rabsr_pos : 0 < Rabs r).
  apply Rle_lt_trans with (Rabs r') ; [apply Rabs_pos | assumption].
 assert (x_lt_1 : Rabs (r'/ r) < 1).
  unfold Rdiv ; rewrite Rabs_mult ; rewrite Rabs_Rinv.
  replace 1%R with (Rabs r *  / Rabs r)%R.
  apply Rmult_lt_compat_r ; [apply Rinv_0_lt_compat |] ; assumption.
  apply Rinv_r ; apply Rgt_not_eq ; assumption.
  intro Hf ; rewrite Hf, Rabs_R0 in Rabsr_pos ; apply (Rlt_irrefl _ Rabsr_pos).
  destruct rho as (B,HB).
  case (Req_or_neq r') ; intro r'_lb.
  exists (Cnorm (An 1%nat)) ; intros x Hx ; destruct Hx as (i, Hi) ;
 rewrite Hi ; unfold An_deriv, Cseq_shift ; unfold_gt.
 destruct i.
 simpl ; rewrite Cmult_1_l, Cmult_1_r ; apply Rle_refl.
 rewrite r'_lb ; rewrite IRC_pow_compat, pow_i ; [| intuition] ;
 repeat rewrite Cmult_0_r, Cnorm_C0 ; apply Cnorm_pos.
 assert (Rabsr'_pos : 0 < Rabs r') by (apply Rabs_pos_lt ; assumption). 
 destruct (Rpser_cv_speed_pow_id (r' / r) x_lt_1 (Rabs r') Rabsr'_pos) as (N, HN).
 destruct (Rseq_partial_bound (gt_norm_pser (An_deriv An) r') N) as (B2, HB2).
 exists (Rmax B B2) ; intros x Hx ; destruct Hx as (i, Hi) ;
 rewrite Hi ; unfold gt_norm_pser, gt_pser, Cseq_norm, Cseq_mult in * ;
  case (le_lt_dec i N) ; intro H.
 apply Rle_trans with B2 ; [rewrite <- Rabs_Cnorm ; apply HB2 | apply RmaxLess2] ;
 assumption.
 apply Rle_trans with (Cnorm (/r' * (INC (S i) * (r' / r) ^ S i) * An (S i) * r ^ S i)).
 right ; apply Cnorm_eq_compat ; unfold An_deriv, Cseq_shift, Cseq_mult ; field_simplify.
 unfold Cdiv ; repeat (rewrite Cmult_assoc) ; repeat (apply Cmult_eq_compat_l).
  rewrite Cpow_mul_distr_l.
 try (rewrite Cinv_1 ; rewrite Cmult_1_r).
 rewrite Cmult_assoc.
 replace ((/ r) ^ S i * (r ^ S i * / r')) with (/ r').
 simpl ; field ; auto with complex.
 assert (r_neq : r <> 0%R).
  intro Hf ; rewrite Hf, Rabs_R0 in Rabsr_pos ; elim (Rlt_irrefl _ Rabsr_pos).
 rewrite <- Cpow_inv.
 rewrite <- Cmult_assoc.
 field ; split.
 auto with complex.
 apply Cpow_neq_compat ; auto with complex.
  auto with complex.
 auto with complex.
 apply Rle_trans with (Cnorm (/ r' * (INC (S i) * (r' / r) ^ S i)) * B)%R.
 rewrite Cmult_assoc, Cnorm_Cmult ; apply Rmult_le_compat_l ;
 [apply Cnorm_pos |] ; apply HB ; exists (S i) ; reflexivity.
 apply Rle_trans with (1*B)%R ; [| rewrite Rmult_1_l ; apply RmaxLess1].
 apply Rmult_le_compat_r.
 apply Rle_trans with (Cnorm (An 0%nat * r ^ 0)) ; [apply Cnorm_pos |] ;
 apply HB ; exists 0%nat ; reflexivity.
 rewrite Cnorm_Cmult ; apply Rle_trans with (Cnorm (/r') * Cnorm r')%R.
 apply Rmult_le_compat_l.
 apply Cnorm_pos.
 apply Rle_trans with (Cnorm ((INC (S i) * (r' / r) ^ S i) - 0)).
 right ; rewrite Cminus_0_r ; reflexivity.
 apply Rle_trans with (R_dist (INR (S i) * (r' / r) ^ S i) 0)%R.
 right ; unfold R_dist ; rewrite <- Cnorm_IRC_Rabs ; apply Cnorm_eq_compat.
 rewrite Cminus_IRC_Rminus ; unfold Rminus ; apply Cadd_eq_compat_r.
 rewrite Cmult_IRC_Rmult, IRC_INR_INC ; apply Cmult_eq_compat_l.
 rewrite <- IRC_pow_compat, Cdiv_IRC_Rdiv.
 reflexivity.
  intro Hf ; rewrite Hf, Rabs_R0 in Rabsr_pos ; elim (Rlt_irrefl _ Rabsr_pos).
  rewrite Cnorm_IRC_Rabs ; left ; apply HN ; intuition.
 rewrite <- Cnorm_Cmult ; rewrite Cinv_l ; [| auto with complex] ; rewrite Cnorm_C1 ; right ; trivial.
Qed.


(** Derivability of partial sums *)

Definition Cpser_partial_sum_derive An n x := match n with
     | 0%nat => C0
     | S _      => sum_f_C0 (gt_pser (An_deriv An) x) (pred n)
end.

Lemma Cpser_derive_finite_sum : forall An n x,
       derivable_pt_lim (fun x => sum_f_C0 (gt_pser An x) n) x (Cpser_partial_sum_derive An n x).
Proof.
intros An n x ;
 unfold Cpser_partial_sum_derive, gt_pser, An_deriv ;
 apply (derivable_pt_lim_partial_sum An x n).
Qed.

(** * Sum of the formal derivative *)

Definition weaksum_r_derive : forall (An : nat -> C) (r : R) (Rho : Cv_radius_weak An r) (z : C), C.
Proof.
intros An r Rho z ; case (Rlt_le_dec (Cnorm z) r) ; intro z_bd.
 pose (r' := middle (Cnorm z)  (Rabs r)).
 assert (r_pos : Rabs r = r).
  apply Rabs_right ; left ; apply Rle_lt_trans with (Cnorm z) ;
  [apply Cnorm_pos | assumption].
 assert (r'_bd : Rabs r' < Rabs r).
  assert (H := proj2 (middle_is_in_the_middle _ _ z_bd)).
  rewrite <- r_pos in H.
  apply Rle_lt_trans with r'.
  right ; apply Rabs_right ; apply Rle_ge ; apply Rle_trans with (Cnorm z) ;
  rewrite <- r_pos in z_bd ;  [apply Cnorm_pos | left ;
  apply (proj1 (middle_is_in_the_middle _ _ z_bd))].
  apply H.
 apply (weaksum_r (An_deriv An) r'
      (Cv_radius_weak_derivable_compat An r Rho r' r'_bd) z).
apply C0.
Defined.

Definition sum_r_derive : forall (An : nat -> C) (r : R) (Rho : finite_cv_radius An r) (z : C), C.
Proof.
intros An r Rho z.
 destruct (Rlt_le_dec (Cnorm z) r) as [z_bd | z_gt].
 assert (H : 0 <= middle (Cnorm z) r < r).
  split.
  left ; apply middle_le_lt_pos_lt ; [| apply Rle_lt_trans with (Cnorm z) ; [| assumption]] ;
  apply Cnorm_pos.
  apply (middle_is_in_the_middle _ _ z_bd).
 apply (weaksum_r_derive _ _ (proj1 Rho (middle (Cnorm z) r) H) z).
 apply C0.
Defined.

Definition sum_derive : forall (An : nat -> C) (Rho : infinite_cv_radius An) (z : C), C.
Proof.
 intros An Rho z ; apply (weaksum_r_derive _ _ (Rho (Cnorm z + 1)%R) z).
Defined.

(** Proof that it is really the sum *)

Lemma weaksum_r_derive_sums : forall (An : nat -> C) (r : R) (Pr : Cv_radius_weak An r) (z : C),
      Cnorm z < r -> Cpser (An_deriv An) z (weaksum_r_derive An r Pr z).
Proof.
intros An r Pr z z_bd.
 unfold weaksum_r_derive ; case (Rlt_le_dec (Cnorm z) r) ; intro s.
 rewrite <- Rabs_right in z_bd.
 apply weaksum_r_sums ; apply (proj1 (middle_is_in_the_middle _ _ z_bd)).
 apply Rle_ge ; apply Rle_trans with (Cnorm z) ; [apply Cnorm_pos | left ; assumption].
 assert (H : Cnorm z < Cnorm z) by (apply Rlt_le_trans with r ; assumption) ;
 elim (Rlt_irrefl _ H).
Qed.

Lemma sum_r_derive_sums : forall (An : nat -> C) (r : R) (Pr : finite_cv_radius An r) (z : C),
      Cnorm z < r -> Cpser (An_deriv An) z (sum_r_derive An r Pr z).
Proof.
intros An r Pr z z_bd ; unfold sum_r_derive ;
 destruct (Rlt_le_dec (Cnorm z) r) as [z_bd2 | Hf].
 apply weaksum_r_derive_sums ; apply (middle_is_in_the_middle _ _ z_bd).
 assert (F : r < r) by (apply Rle_lt_trans with (Cnorm z) ; assumption) ;
 destruct (Rlt_irrefl _ F).
Qed.

Lemma sum_derive_sums : forall (An : nat -> C) (Pr : infinite_cv_radius An) (z : C),
      Cpser (An_deriv An) z (sum_derive An Pr z).
Proof.
intros An Pr z ; unfold sum_derive ; apply weaksum_r_derive_sums ; intuition.
Qed.

(** Proof that the sum is unique *)

Lemma weaksum_r_derive_unique : forall (An : nat -> C) (r : R) (Pr1 Pr2 : Cv_radius_weak An r) (z : C),
      Cnorm z < r -> weaksum_r_derive An r Pr1 z = weaksum_r_derive An r Pr2 z .
Proof.
intros An r Pr1 Pr2 z z_bd ;
 assert (T1 := weaksum_r_derive_sums _ _ Pr1 _ z_bd) ;
 assert (T2 := weaksum_r_derive_sums _ _ Pr2 _ z_bd).
 eapply Pser_unique ; eassumption.
Qed.

Lemma sum_r_derive_unique : forall (An : nat -> C) (r : R) (Pr1 Pr2 : finite_cv_radius An r) (z : C),
      Cnorm z < r -> sum_r_derive An r Pr1 z = sum_r_derive An r Pr2 z .
Proof.
intros An r Pr1 Pr2 z z_bd ;
 assert (T1 := sum_r_derive_sums _ _ Pr1 _ z_bd) ;
 assert (T2 := sum_r_derive_sums _ _ Pr2 _ z_bd).
 eapply Pser_unique ; eassumption.
Qed.

Lemma sum_derive_unique : forall (An : nat -> C) (Pr1 Pr2 : infinite_cv_radius An) (z : C),
      sum_derive An Pr1 z = sum_derive An Pr2 z .
Proof.
intros An Pr1 Pr2 z ;
 assert (T1 := sum_derive_sums _ Pr1 z) ;
 assert (T2 := sum_derive_sums _ Pr2 z).
 eapply Pser_unique ; eassumption.
Qed.

(** * Derivability of a power serie within its disc of convergence *)

Lemma derivable_pt_lim_weaksum_r : forall (An:nat->C) (r:R) (Pr : Cv_radius_weak An r) z,
      Cnorm z < r -> derivable_pt_lim (weaksum_r An r Pr) z (weaksum_r_derive An r Pr z).
Proof.
intros An r rho z z_bd.
 assert (r_pos : 0 < r) by (apply Rle_lt_trans with (Cnorm z) ; [apply Cnorm_pos | assumption]).
 pose (midd := middle (Cnorm z) r) ; assert (midd_pos : 0 < midd).
  unfold midd ; apply middle_le_lt_pos_lt ; [apply Cnorm_pos | assumption].
 pose (r' := mkposreal midd midd_pos).
 assert (z_bd' : Cnorm z < midd).
  apply (middle_is_in_the_middle _ _ z_bd).
 assert (r'_ub : r' < r).
  apply (proj2 (middle_is_in_the_middle _ _ z_bd)).

 pose (fn := fun N z => sum_f_C0 (gt_pser An z) N) ;
 pose (fn' := fun N z => Cpser_partial_sum_derive An N z) ;
 pose (f := weaksum_r An r rho) ;
 pose (g := weaksum_r_derive An r rho).

 assert (z_in : Boule 0 r' z).
  unfold Boule ; simpl ; unfold C_dist ; rewrite Cnorm_minus_sym,
   Cminus_0_r ; assumption.

 assert (fn_deriv : forall (x : C) (n : nat), Boule 0 r' x -> derivable_pt_lim (fn n) x (fn' n x)).
  intros ; apply Cpser_derive_finite_sum.

 assert (fn_cv : CFseq_cv_boule fn f 0 r').
  intros a a_in.
   assert (a_bd : Cnorm a < r).
    unfold Boule in a_in ; simpl in a_in ; unfold C_dist in a_in ;
    rewrite Cnorm_minus_sym, Cminus_0_r in a_in.
    apply Rlt_trans with midd ; assumption.
  assert (H := weaksum_r_sums An r rho a a_bd).
  intros eps eps_pos ; destruct (H eps eps_pos) as [N HN] ; exists N ;
  intros n n_lb ; unfold fn, f ; simpl in HN ; unfold C_dist in HN.
  apply HN ; assumption.

assert (cv : forall z : C, Boule 0 r' z ->  {l : C |  Cseq_cv (fun N : nat =>
                    CFpartial_sum (fun n : nat => (fun (n0 : nat) (z0 : C) =>
                        gt_pser (An_deriv An) z0 n0) n z) N) l}).
  intros a a_in.
   exists (weaksum_r_derive An r rho a).
   apply Pser_Cseqcv_link ; apply weaksum_r_derive_sums.
   apply Rlt_trans with r' ; [unfold Boule in a_in ; simpl in a_in ; unfold C_dist in a_in ;
   rewrite Cminus_0_l, Cnorm_opp in a_in ; apply a_in | assumption].

  assert (r''_comp : Rabs (middle r' r) < Rabs r).
  rewrite Rabs_right ; [rewrite Rabs_right |].
  apply (proj2 (middle_is_in_the_middle _ _ r'_ub)).
  left ; assumption.
  left ; apply middle_le_lt_pos_lt.
  left ; unfold r' ; apply middle_le_lt_pos_lt ; [apply Cnorm_pos | assumption].
  assumption.

  assert (rho_An' := Cv_radius_weak_derivable_compat An r rho (middle r' r) r''_comp).
  assert (cvn_r : CVN_r (fun (n : nat) (z : C) => gt_pser (An_deriv An) z n) r').
   apply Cpser_abel2 with (middle r' r).
   assumption.
   apply (proj1 (middle_is_in_the_middle _ _  r'_ub)).
 assert (fn'_cvu := CVN_CVU_boule (fun n z => gt_pser (An_deriv An) z n) r' cv cvn_r).
 assert (fn'_cvu2 : CFseq_cvu fn' g 0 r').
 unfold fn', g.
 intros eps eps_pos ; destruct (fn'_cvu _ eps_pos) as [N HN] ; exists (S N) ;
 clear fn'_cvu fn_deriv rho_An' ; intros n y n_lb y_bd.
 assert (H : n = S (pred n)) by intuition ; rewrite H ; clear H ; simpl.
 unfold CFseq_cvu, SFL_interv, CFpartial_sum in HN.
 assert (predn_lb : (N <= pred n)%nat) by intuition.
 assert (Temp := HN (pred n) y predn_lb y_bd).
 destruct (Rlt_le_dec (Cnorm (0 - y)) r') as [H | Hf].
 destruct (cv y H) as [l Hl].
 assert (Hrew : l = weaksum_r_derive An r rho y).
  eapply Cseq_cv_unique ; [apply Hl |] ;
  apply Pser_Cseqcv_link ; apply weaksum_r_derive_sums.
  apply Rlt_trans with r' ; [rewrite Cminus_0_l, Cnorm_opp in H |] ;
  assumption.
  rewrite <- Hrew ; assumption.
  clear - y_bd Hf ; assert (Hf2 : Cnorm (0 - y) < Cnorm (0 - y)) by
  (apply Rlt_le_trans with r' ; assumption) ; elim (Rlt_irrefl _ Hf2).

 assert (g_cont : (forall x : C, Boule 0 r' x -> continuity_pt g x)).
  intros a a_in ; apply CVU_continuity_boule with fn' C0 r'.
  apply fn'_cvu2.
  intros N y y_in ; unfold fn'.
  unfold Cpser_partial_sum_derive ; induction N.
  apply continuity_pt_const ; unfold constant ; intros ; trivial.
  destruct N ; simpl ; [unfold gt_pser, An_deriv |].
  intros eps eps_pos ; exists R1 ; split ; [apply Rlt_0_1 |] ; intros x [_ Hx] ;
  simpl ; unfold C_dist ; repeat rewrite Cpow_0.
  unfold Cminus ; rewrite Cadd_opp_r, Cnorm_C0 ; assumption.
  apply continuity_pt_add ; [assumption |].
  unfold gt_pser.
  apply continuity_pt_mult.
  apply continuity_pt_const.
  intros r1 r2 ; unfold An_deriv ; reflexivity.
  apply derivable_continuous ; apply derivable_Cpow.
  assumption.

 exact (CFseq_cvu_derivable fn fn' f g z 0 r' z_in fn_deriv fn_cv fn'_cvu2 g_cont).
Qed.

Lemma derivable_pt_lim_sum_r : forall (An:nat->C) (r:R) (Pr : finite_cv_radius An r) z,
      Cnorm z < r -> derivable_pt_lim (sum_r An r Pr) z (sum_r_derive An r Pr z).
Proof.
intros An r Pr z z_bd eps eps_pos. 
 assert (H : 0 <= middle (Cnorm z) r < r).
  split.
  left ; apply middle_le_lt_pos_lt ; [| apply Rle_lt_trans with (Cnorm z) ; [| assumption]] ;
  apply Cnorm_pos.
  apply (middle_is_in_the_middle _ _ z_bd).
 destruct (derivable_pt_lim_weaksum_r _ _ (proj1 Pr (middle (Cnorm z) r) H) _
 (proj1 (middle_is_in_the_middle _ _ z_bd)) _ eps_pos) as [delta Hdelta].
 pose (delta' := Rmin delta (((middle (Cnorm z) r) - Cnorm z) / 2)%R) ;
 assert (delta'_pos : 0 < delta').
  apply Rmin_pos.
   apply delta.
   apply ub_lt_2_pos with (middle (Cnorm z) (middle (Cnorm z) r)) ;
   apply (middle_is_in_the_middle _ _ (proj1 (middle_is_in_the_middle _ _ z_bd))).
  exists (mkposreal delta' delta'_pos) ; intros h h_neq h_bd.

 replace (sum_r An r Pr (z + h)) with (weaksum_r An (middle (Cnorm z) r)
               (proj1 Pr (middle (Cnorm z) r) H) (z + h)).
 replace (sum_r An r Pr z) with (weaksum_r An (middle (Cnorm z) r)
               (proj1 Pr (middle (Cnorm z) r) H) z).
 replace (sum_r_derive An r Pr z) with (weaksum_r_derive An (middle (Cnorm z) r)
              (proj1 Pr (middle (Cnorm z) r) H) z).
 apply Hdelta ; [assumption | apply Rlt_le_trans with delta'] ;
 [assumption | apply Rmin_l].

 unfold sum_r_derive ; destruct (Rlt_le_dec (Cnorm z) r) as [z_bd2 | Hf].
 apply weaksum_r_derive_unique ; apply (middle_is_in_the_middle _ _ z_bd).
 assert (F : r < r) by (apply Rle_lt_trans with (Cnorm z) ; assumption) ;
 destruct (Rlt_irrefl _ F).

 unfold sum_r ; destruct (Rlt_le_dec (Cnorm z) r) as [z_bd2 | Hf].
 apply weaksum_r_unique ; apply (middle_is_in_the_middle _ _ z_bd).
 assert (F : r < r) by (apply Rle_lt_trans with (Cnorm z) ; assumption) ;
 destruct (Rlt_irrefl _ F).

 unfold sum_r ; destruct (Rlt_le_dec (Cnorm (z + h)) r) as [z_bd2 | Hf].
 apply weaksum_r_unique_strong.
 apply Rle_lt_trans with (Cnorm z + Cnorm h)%R.
 apply Cnorm_triang.
 apply Rlt_le_trans with (Cnorm z + ((middle (Cnorm z) r - Cnorm z) / 2))%R.
 apply Rplus_lt_compat_l ; apply Rlt_le_trans with delta' ; [assumption | apply Rmin_r].
 unfold Rminus ; field_simplify ; unfold Rdiv ; try (rewrite Rinv_1, Rmult_1_r).
 left ; do 2 eapply middle_is_in_the_middle ; assumption.
 eapply middle_is_in_the_middle ; assumption.
 assert (F : r < r).
  apply Rlt_trans with (middle (Cnorm z) r).
  apply Rle_lt_trans with (Cnorm (z + h)).
  assumption.
  apply Rle_lt_trans with (Cnorm z + Cnorm h)%R.
  apply Cnorm_triang.
  apply Rlt_trans with (Cnorm z + ((middle (Cnorm z) r - Cnorm z) / 2))%R.
  apply Rplus_lt_compat_l ; apply Rlt_le_trans with delta' ; [intuition | apply Rmin_r].
  unfold middle ; field_simplify.
  apply Rlt_le_trans with ((2 * Cnorm z + r + r) / 4)%R.
  unfold Rdiv ; apply Rmult_lt_compat_r ; [lra |].
  apply Rplus_lt_compat_r.
  apply Rle_lt_trans with (2 * Cnorm z + Cnorm z)%R.
  right ; ring.
  apply Rplus_lt_compat_l ; assumption.
  right ; field.
  eapply middle_is_in_the_middle ; assumption.
  destruct (Rlt_irrefl _ F).
Qed.

Lemma derivable_pt_lim_sum : forall (An:nat->C) (Pr : infinite_cv_radius An) z,
      derivable_pt_lim (sum An Pr) z (sum_derive An Pr z).
Proof.
intros An Pr z eps eps_pos. 
 assert (H : 0 <= Cnorm z < Cnorm z + 1).
  split ; [apply Cnorm_pos |] ; intuition.
 destruct (derivable_pt_lim_weaksum_r _ _ (Pr (Cnorm z + 1)%R) z (proj2 H) _ eps_pos) as [delta Hdelta].

 pose (delta' := Rmin delta 1) ; assert (delta'_pos : 0 < delta').
  apply Rmin_pos ; [apply delta | apply Rlt_0_1].
 exists (mkposreal _ delta'_pos) ; intros h h_neq h_bd.

 replace (sum An Pr (z + h)) with (weaksum_r An (Cnorm z + 1) (Pr (Cnorm z + 1)%R) (z + h)).
 apply Hdelta.
 assumption.
 apply Rlt_le_trans with delta' ; [assumption | apply Rmin_l].

 unfold sum.
 apply weaksum_r_unique_strong.
 apply Rle_lt_trans with (Cnorm z + Cnorm h)%R.
 apply Cnorm_triang.
 apply Rplus_lt_compat_l ; apply Rlt_le_trans with delta' ;
 [intuition | apply Rmin_r].
 intuition.
Qed.
