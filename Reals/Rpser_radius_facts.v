Require Import Reals.
Require Import Fourier.
Require Import Rpow_facts.

Require Import Ranalysis_def.
Require Import Rsequence_facts RFsequence RFsequence_facts.
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

Lemma Cv_radius_weak_derivable_compat_rev : forall An r,
         Cv_radius_weak (An_deriv An) r ->
         Cv_radius_weak An r.
Proof.
intros An r [B HB] ; exists (Rmax (B * Rabs r) (Rabs (An O))) ;
 intros x [i Hi] ; subst.
 destruct i.
  unfold gt_abs_Pser ; simpl ; rewrite Rmult_1_r ; apply Rmax_r.

 apply Rle_trans with (Rabs (An (S i) * r ^ i) * Rabs r).
  right ; rewrite <- Rabs_mult ; apply Rabs_eq_compat ;
   simpl ; ring.
 apply Rle_trans with (gt_abs_Pser (An_deriv An) r i * / INR (S i) * Rabs r).
  unfold gt_abs_Pser, An_deriv ; rewrite <- (Rabs_pos_eq (/ INR (S i))),
  <- (Rabs_mult _ (/ INR (S i))).
  apply Rmult_le_compat_r ; [apply Rabs_pos |] ; right ; apply Rabs_eq_compat ;
  field ; apply not_0_INR ; omega.
  rewrite S_INR ; left ; apply RinvN_pos.
 apply Rle_trans with (gt_abs_Pser (An_deriv An) r i * / 1 * Rabs r).
  apply Rmult_le_compat_r ; [apply Rabs_pos |] ;
  apply Rmult_le_compat_l ; [apply Rabs_pos |] ;
  apply Rle_Rinv ; [fourier
  | replace 0 with (INR O) by reflexivity ; apply lt_INR
  | replace 1 with (INR 1) by reflexivity ; apply le_INR] ; omega.
 rewrite Rinv_1, Rmult_1_r ; apply Rle_trans with (B * Rabs r).
  apply Rmult_le_compat_r ; [apply Rabs_pos |] ;
  apply HB ; exists i ; reflexivity.
 apply Rmax_l.
Qed.

Lemma finite_cv_radius_derivable_compat : forall An r,
         finite_cv_radius An r ->
         finite_cv_radius (An_deriv An) r.
Proof.
intros An r Rho ; split.
 intros r' (r'_lb, r'_ub) ; apply Cv_radius_weak_derivable_compat with
 (r := middle (Rabs r) (Rabs r')).
 apply (proj1 Rho) ; split.
 left ; apply middle_lt_le_pos_lt.
 apply Rabs_pos_lt ; apply Rgt_not_eq ; apply Rlt_gt ;
 apply Rle_lt_trans with r' ; assumption.
 apply Rabs_pos.
 rewrite middle_comm ; apply Rlt_le_trans with (Rabs r).
 eapply middle_is_in_the_middle.
 apply Rle_lt_trans with r' ; [right ; apply Rabs_right ; intuition |].
 apply Rlt_le_trans with r ; [assumption | right ; symmetry ; apply Rabs_right ;
 left ; apply Rle_lt_trans with r' ; assumption].
 right ; apply Rabs_right ; left ; apply Rle_lt_trans with r' ; assumption.
 apply Rle_lt_trans with r'.
 right ; apply Rabs_right ; intuition.
 rewrite Rabs_right.
 apply Rle_lt_trans with (Rabs r') ; [right ; symmetry ;apply Rabs_right ;
 intuition | rewrite middle_comm].
 eapply middle_is_in_the_middle.
 apply Rle_lt_trans with r' ; [right ; apply Rabs_right ; intuition |].
 apply Rlt_le_trans with r ; [assumption | right ; symmetry ; apply Rabs_right ;
 left ; apply Rle_lt_trans with r' ; assumption].
 left ; apply middle_lt_le_pos_lt ;  [apply Rabs_pos_lt ; apply Rgt_not_eq ;
 apply Rlt_gt ; apply Rle_lt_trans with r' ; assumption | apply Rabs_pos].

 intros r' rltr' Hf ; destruct Rho as [H_bd H_ub].
  apply (H_ub _ rltr') ; apply Cv_radius_weak_derivable_compat_rev ;
   assumption.
Qed.


Lemma infinite_cv_radius_derivable_compat : forall An,
         infinite_cv_radius An ->
         infinite_cv_radius (An_deriv An).
Proof.
intros An Rho r ; apply Cv_radius_weak_derivable_compat with (r := (Rabs r) + 1).
 apply Rho.
 replace (Rabs (Rabs r + 1)) with (Rabs r + 1).
 fourier.
 symmetry ; apply Rabs_right.
 apply Rle_ge ; apply Rle_trans with (Rabs r) ; [apply Rabs_pos | fourier].
Qed.