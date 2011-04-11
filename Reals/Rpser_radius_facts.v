Require Import Reals.
Require Import Fourier.
Require Import Rpow_facts.

Require Import Rpser_def Rpser_base_facts.
Require Import Rpser_cv_facts Rpser_sums.

Open Local Scope R_scope.

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

(** A sufficient condition for the radius of convergence*)
Lemma Rpser_finite_cv_radius_caracterization : forall (An : nat -> R) (x0 l : R),
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

Lemma Rpser_infinite_cv_radius_caracterization : forall An, (forall x, {l | Pser An x l}) ->
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