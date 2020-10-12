Require Import Reals.
Require Import Fourier Lra.
Require Import Rpow_facts.

Require Import Rinterval Rextensionality.
Require Import Rsequence_facts Rsequence_sums_facts Rsequence_rewrite_facts.
Require Import RFsequence RFsequence_facts.
Require Import Rpser_def Rpser_def_simpl Rpser_base_facts.
Require Import Rpser_cv_facts Rpser_sums.
Require Import MyINR.

Local Open Scope R_scope.

(** Abel's lemma : Normal convergence of the power serie *)

Lemma Rpser_abs_cv_radius_weak : forall (An : Rseq) (r : R), 
  Cv_radius_weak An r -> forall x, Rabs x < r ->
  { l | Rpser_abs An x l}.
Proof.
intros An r Rho x x_bd ;
 assert (Rho' := proj1 (Cv_radius_weak_abs An r) Rho) ;
 pose (l := weaksum_r (| An |) r Rho' (Rabs x)) ;
 exists l ; rewrite Rpser_abs_unfold ; apply weaksum_r_sums ;
 rewrite Rabs_Rabsolu ; assumption.
Qed.

Lemma Rpser_abs_infinite_cv_radius: forall An,
  infinite_cv_radius An -> forall x, {l | Rpser_abs An x l}.
Proof.
intros An rAn x ; apply (Rpser_abs_cv_radius_weak _ _
 (rAn (Rabs x + 1)) x (Rlt_n_Sn _)).
Qed.

Lemma Rpser_abel2 : forall An r, Cv_radius_weak An r ->
  forall r' : posreal, r' < r -> CVN_r (fun n x => gt_pser An x n) r'.
Proof.
intros An r Pr [a a_pos] r'_ub.
 assert (a_bd : Rabs a < r) by (rewrite Rabs_pos_eq ; [| left] ; assumption).
 assert (r_pos : 0 < r) by (apply Rlt_trans with a ; assumption).
 assert (r'_bd : Rabs (middle a r) < r).
  rewrite Rabs_pos_eq ; [apply middle_is_in_the_middle |
   left ; apply middle_lt_lt_pos_lt] ; assumption.
 rewrite Cv_radius_weak_abs in Pr.
 exists (gt_abs_pser An (middle a r)) ;
 exists (weaksum_r (| An |) r Pr (Rabs (middle a r))) ; split.
 rewrite <- Rseq_cv_Un_cv_equiv ;
 apply Rseq_cv_eq_compat with (Rseq_sum (gt_abs_pser An (middle a r))).
 intro n ; fold (Rseq_abs (gt_abs_pser An (middle a r))) ;
 apply Rseq_sum_ext with (Vn := gt_abs_pser An (middle a r)) ;
 apply Rseq_abs_idempotent.
 assert (tmp := Rseq_sum_ext _ _ (gt_abs_pser_unfold An (middle a r))) ;
 symmetry in tmp ; apply (Rseq_cv_eq_compat  _ _ _ tmp) ; clear tmp.
 apply weaksum_r_sums ; rewrite Rabs_Rabsolu ; assumption.
 intros n y B ; apply gt_abs_pser_le_compat ; unfold Boule in B ;
 apply Rle_trans with a ; [left |].
 unfold Rminus in B ; rewrite Ropp_0, Rplus_0_r in B ; apply B.
 rewrite Rabs_pos_eq ; [left ; apply middle_is_in_the_middle |
 left ; apply middle_lt_lt_pos_lt] ; assumption.
Qed.

(** A sufficient condition for the radius of convergence*)
Lemma Rpser_finite_cv_radius_caracterization : forall An x l,
  Rpser An x l -> (forall l : R, ~ Rpser_abs An x l) ->
  finite_cv_radius An (Rabs x).
Proof.
intros An x l Hcv Hncv ; split; intros r Hr.
 apply Cv_radius_weak_le_compat with x.
  rewrite Rabs_pos_eq ; [left |] ; apply Hr.
  apply (Rpser_bound_criteria _ _ l Hcv).
 intro Hf ;
 destruct (Rpser_abs_cv_radius_weak An r Hf x Hr) as [l' Hl'] ;
 apply Hncv with l' ; assumption.
Qed.

Lemma Rpser_infinite_cv_radius_caracterization :
  forall An, (forall x, {l | Rpser An x l}) -> infinite_cv_radius An.
Proof.
intros An weaksum r ; destruct (weaksum r) as (l, Hl) ;
 apply Rpser_bound_criteria with l ; assumption.
Qed.

(** * Caracterization of the cv radius of the formal derivative *)

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
 rewrite Hi ; unfold gt_abs_pser, gt_pser, An_deriv, Rseq_shift, Rseq_mult, Rseq_abs.
 destruct i.
 simpl ; rewrite Rmult_1_l ; rewrite Rmult_1_r ; apply Rle_refl.
 rewrite r'_lb ; rewrite pow_i ; [| intuition] ; repeat (rewrite Rmult_0_r) ;
 rewrite Rabs_R0 ; apply Rabs_pos.
 assert (Rabsr'_pos : 0 < Rabs r') by (apply Rabs_pos_lt ; assumption). 
 destruct (Rpser_cv_speed_pow_id (r' / r) x_lt_1 (Rabs r') Rabsr'_pos) as (N, HN).
 destruct (Rseq_partial_bound (gt_abs_pser (An_deriv An) r') N) as (B2, HB2).
 exists (Rmax B B2) ; intros x Hx ; destruct Hx as (i, Hi) ;
 rewrite Hi ; unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult in * ;
 case (le_lt_dec i N) ; intro H.
 rewrite <- Rabs_Rabsolu ; apply Rle_trans with B2 ; [apply HB2 | apply RmaxLess2] ;
 assumption.
 apply Rle_trans with (Rabs (/r' * (INR (S i) * (r' / r) ^ S i) * An (S i) * r ^ S i)).
 right ; apply Rabs_eq_compat ; unfold An_deriv, Rseq_shift, Rseq_mult ; field_simplify.
 unfold Rdiv ; repeat (rewrite Rmult_assoc) ; repeat (apply Rmult_eq_compat_l).
 rewrite Rpow_mult_distr.
 try (rewrite Rinv_1 ; rewrite Rmult_1_r).
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
  Cv_radius_weak (An_deriv An) r -> Cv_radius_weak An r.
Proof.
intros An r [B HB] ; exists (Rmax (B * Rabs r) (Rabs (An O))) ;
 intros x [i Hi] ; subst.
 destruct i.
  apply Rle_trans with (Rabs (An O)) ; [apply gt_abs_pser_0_ub | apply Rmax_r].
  rewrite gt_abs_pser_S ; apply Rle_trans with (B * Rabs r) ; [| apply Rmax_l].
  apply Rmult_le_compat_r ; [apply Rabs_pos |].
  apply Rle_trans with (gt_abs_pser (An_deriv An) r i) ; [| apply HB ; exists i ;
  reflexivity].
  rewrite <- (Rmult_1_l (gt_abs_pser (Rseq_shift An) r i)).
  unfold gt_abs_pser, gt_pser, An_deriv, Rseq_shift, Rseq_abs, Rseq_mult.
  rewrite Rmult_assoc, (Rabs_mult (INR (S i))) ; apply Rmult_le_compat_r ;
  [apply Rabs_pos |] ; rewrite <- INR_1, Rabs_INR ; apply le_INR ; lia.
Qed.

Lemma finite_cv_radius_derivable_compat : forall An r,
  finite_cv_radius An r <->
  finite_cv_radius (An_deriv An) r.
Proof.
intros An r ; split.

intros [H_ub H_lub] ; split.
 intros r' (r'_lb, r'_ub) ; apply Cv_radius_weak_derivable_compat with
 (r := middle (Rabs r) (Rabs r')).
 apply H_ub ; split.
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

 intros r' rltr' Hf ; apply (H_lub _ rltr') ;
  apply Cv_radius_weak_derivable_compat_rev ; assumption.

intros [H_ub H_lub] ; split.
 intros r' r'_bd ; apply Cv_radius_weak_derivable_compat_rev ;
  apply H_ub ; assumption.

 intros r' rltr' Hf.
  assert (r0_bd : r < middle r r') by
   (apply middle_is_in_the_middle ; assumption).
  apply (H_lub _ r0_bd) ; eapply Cv_radius_weak_derivable_compat.
  eassumption.
  assert (r_pos : 0 <= r).
   eapply finite_cv_radius_pos ; split ; [apply H_ub | apply H_lub].
  assert (r'_pos : 0 <= r') by (left ; apply Rle_lt_trans with r ; assumption).
  assert (middle_pos : 0 <= middle r r') by
   (apply middle_le_le_pos ; assumption).
  do 2 (rewrite Rabs_pos_eq ; [| assumption]) ; apply middle_is_in_the_middle ;
  assumption.
Qed.

Lemma infinite_cv_radius_derivable_compat : forall An,
         infinite_cv_radius An <->
         infinite_cv_radius (An_deriv An).
Proof.
intro An ; split.
intros Rho r ; apply Cv_radius_weak_derivable_compat with (r := (Rabs r) + 1).
 apply Rho.
 replace (Rabs (Rabs r + 1)) with (Rabs r + 1).
 lra.
 symmetry ; apply Rabs_right.
 apply Rle_ge ; apply Rle_trans with (Rabs r) ; [apply Rabs_pos | lra].

intros Rho r ; apply Cv_radius_weak_derivable_compat_rev ; apply Rho.
Qed.

(** Using the results on the derivative, we can now talk about Rseq_prod. *)

Lemma Cv_radius_weak_prod_compat:
  forall (An Bn : Rseq) (r1 r2 : R),
  Cv_radius_weak An r1 ->
  Cv_radius_weak Bn r2 ->
  forall r, Rabs r < Rmin (Rabs r1) (Rabs r2) ->
  Cv_radius_weak (An # Bn) r.
Proof.
intros An Bn r1 r2 rAn rBn r Hr.
 apply Cv_radius_weak_ext with (An_deriv (fun n => if eq_nat_dec n 0 then 0
else (Rseq_div (An # Bn) (Rseq_shift INR)) (pred n))).

unfold An_deriv, Rseq_shift, Rseq_mult, Rseq_div, Rdiv ; intro n ; simpl.
rewrite <- Rmult_assoc, Rmult_comm, <- Rmult_assoc, Rinv_l, Rmult_1_l.
 reflexivity.
 apply Rgt_not_eq ; unfold Rgt ; replace (match n with | 0%nat => 1 | S _ => INR n + 1 end)
 with (INR (S n)) by auto ; apply lt_0_INR ; lia.
apply Cv_radius_weak_derivable_compat with (Rmin (Rabs r1) (Rabs r2)).

destruct (Cv_radius_weak_prod_prelim An Bn r1 r2 rAn rBn) as [B HB] ;
 exists (B * Rabs (Rmin (Rabs r1) (Rabs r2))) ;
 intros x [i Hi] ; subst ; unfold gt_abs_pser, Rseq_abs, gt_pser,
 Rseq_mult ; destruct i as [| j].
  simpl ; rewrite Rmult_1_r, Rabs_R0 ; apply Rle_trans with
  ((gt_abs_pser ((An # Bn) / Rseq_shift INR)) (Rmin (Rabs r1) (Rabs r2)) O *
  Rabs (Rmin (Rabs r1) (Rabs r2))).
  apply Rmult_le_pos ; [unfold gt_abs_pser, Rseq_abs|] ; apply Rabs_pos.
  apply Rmult_le_compat_r ; [apply Rabs_pos | apply HB ; exists O ; reflexivity].
 simpl.
 rewrite (Rmult_comm (Rmin (Rabs r1) (Rabs r2))), <- Rmult_assoc, Rabs_mult,
  (Rabs_pos_eq (Rmin (Rabs r1) (Rabs r2))).
  apply Rmult_le_compat_r.
  apply MyRIneq.Rmin_pos ; apply Rabs_pos.
  apply HB ; exists j ; reflexivity.
  apply MyRIneq.Rmin_pos ; apply Rabs_pos.
  rewrite (Rabs_pos_eq (Rmin (Rabs r1) (Rabs r2))) ;
  [assumption | apply MyRIneq.Rmin_pos ; apply Rabs_pos].
Qed.

Lemma infinite_cv_radius_prod_compat: forall (An Bn : Rseq),
  infinite_cv_radius An -> infinite_cv_radius Bn ->
  infinite_cv_radius (An # Bn).
Proof.
intros An Bn rAn rBn r ; apply Cv_radius_weak_prod_compat with (Rabs r + 1) (Rabs r + 1).
 apply rAn.
 apply rBn.
 apply Rlt_le_trans with (Rabs r + 1) ; [lra |].
 right ; rewrite Rmin_diag ; symmetry ; apply Rabs_pos_eq ;
 rewrite Rplus_comm ; apply Rle_zero_pos_plus1, Rabs_pos.
Qed.

(** Same thing but for the nth derivative. *)

Lemma Cv_radius_weak_nth_derivable_compat (k : nat) : forall An r,
         Cv_radius_weak An r -> forall r', Rabs r' < Rabs r ->
         Cv_radius_weak (An_nth_deriv An k) r'.
Proof.
induction k ; intros An r rAn r' r'_bd.

 erewrite Cv_radius_weak_ext ; [| apply An_nth_deriv_0].
  eapply Cv_radius_weak_le_compat ; [left |] ; eassumption.

 assert (Hrew : Rabs (middle (Rabs r') (Rabs r)) = middle (Rabs r') (Rabs r)).
  apply Rabs_pos_eq ; apply middle_le_le_pos ; apply Rabs_pos.
 erewrite Cv_radius_weak_ext ; [| apply An_nth_deriv_S] ;
  apply Cv_radius_weak_derivable_compat with (middle (Rabs r') (Rabs r)).
 apply IHk with r ; [| rewrite Hrew ; apply middle_is_in_the_middle] ;
  assumption.
 rewrite Hrew ; apply middle_is_in_the_middle ; assumption.
Qed.

Lemma Cv_radius_weak_nth_derivable_compat_rev (k : nat) : forall An r,
         Cv_radius_weak (An_nth_deriv An k) r ->
         Cv_radius_weak An r.
Proof.
induction k ; intros An r rAn.

 erewrite Cv_radius_weak_ext.
  eassumption.
  symmetry ; apply An_nth_deriv_0.

 apply IHk ; apply Cv_radius_weak_derivable_compat_rev ;
  erewrite Cv_radius_weak_ext.
  eassumption.
  symmetry ; apply An_nth_deriv_S.
Qed.

Lemma finite_cv_radius_nth_derivable_compat (k : nat) : forall An r,
         finite_cv_radius An r <->
         finite_cv_radius (An_nth_deriv An k) r.
Proof.
induction k ; intros An r.
rewrite <- finite_cv_radius_ext ;
 [reflexivity | apply An_nth_deriv_0].

split ; intro Rho.
 rewrite finite_cv_radius_ext ; [| eapply An_nth_deriv_S].
  rewrite <- finite_cv_radius_derivable_compat, <- IHk ; assumption.
 rewrite IHk, finite_cv_radius_derivable_compat ;
  rewrite <- finite_cv_radius_ext ;
  [| eapply An_nth_deriv_S] ; assumption.
Qed.

Lemma infinite_cv_radius_nth_derivable_compat (k : nat) : forall An,
         infinite_cv_radius An <->
         infinite_cv_radius (An_nth_deriv An k).
Proof.
induction k ; intro An.
rewrite <- infinite_cv_radius_ext ;
 [| eapply An_nth_deriv_0] ; reflexivity.

split ; intro Rho.
 rewrite infinite_cv_radius_ext ; [| eapply An_nth_deriv_S].
  rewrite <- infinite_cv_radius_derivable_compat, <- IHk ; assumption.
 rewrite IHk, infinite_cv_radius_derivable_compat,
  <- infinite_cv_radius_ext ; [| eapply An_nth_deriv_S] ; assumption.
Qed.
