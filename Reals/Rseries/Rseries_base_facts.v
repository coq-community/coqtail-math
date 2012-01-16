Require Import Rsequence.
Require Import Rseries_def.

(** Basic facts *)

Lemma Rser_cv_unique: forall An l1 l2,
  Rser_cv An l1 -> Rser_cv An l2 -> l1 = l2.
Proof.
intros ; eapply Rseq_cv_unique ; eassumption.
Qed.

Lemma Rser_cv_ext: forall An Bn l, An == Bn ->
  (Rser_cv An l <-> Rser_cv Bn l).
Proof.
intros ; apply Rseq_cv_eq_compat, Rseq_sum_ext ; assumption.
Qed.

(** Compatibility with common operations *)

Lemma Rser_cv_scal_compat_l: forall An la (l : R),
  Rser_cv An la -> Rser_cv (l * An) (l * la).
Proof.
intros ; eapply Rseq_cv_eq_compat.
 apply Rseq_sum_scal_compat_l.
 apply Rseq_cv_mult_compat ; intuition.
Qed.

Lemma Rser_cv_scal_compat_r: forall An la (l : R),
  Rser_cv An la -> Rser_cv (An * l) (la * l).
Proof.
intros ; eapply Rseq_cv_eq_compat.
 apply Rseq_sum_scal_compat_r.
 apply Rseq_cv_mult_compat ; intuition.
Qed.

Lemma Rser_cv_opp_compat: forall An l,
  Rser_cv An l -> Rser_cv (- An) (- l).
Proof.
intros ; eapply Rseq_cv_eq_compat.
 apply Rseq_sum_opp_compat.
 apply Rseq_cv_opp_compat ; assumption.
Qed.

Lemma Rser_cv_plus_compat: forall An Bn la lb,
  Rser_cv An la -> Rser_cv Bn lb -> Rser_cv (An + Bn) (la + lb).
Proof.
intros ; eapply Rseq_cv_eq_compat.
 apply Rseq_sum_plus_compat.
 apply Rseq_cv_plus_compat ; assumption.
Qed.

Lemma Rser_cv_minus_compat: forall An Bn la lb,
  Rser_cv An la -> Rser_cv Bn lb -> Rser_cv (An - Bn) (la - lb).
Proof.
intros ; eapply Rseq_cv_eq_compat.
 apply Rseq_sum_minus_compat.
 apply Rseq_cv_minus_compat ; assumption.
Qed.

(** Series convergence shifting compatibility *)

Lemma Rser_cv_shift : forall An l, Rser_cv An l ->
  Rser_cv (Rseq_shift An) (l - (An O)).
Proof.
intros An l Hl ; eapply Rseq_cv_eq_compat.
 intro n ; apply Rseq_sum_shift_compat.
 apply Rseq_cv_minus_compat.
  apply Rseq_cv_shift_compat_reciprocal ; assumption.
  apply Rseq_constant_cv.
Qed.

Lemma Rser_cv_shift_rev : forall An l,
  Rser_cv (Rseq_shift An) l ->  Rser_cv An (l + An 0%nat).
Proof.
intros An l Hl ; apply Rseq_cv_shift_compat ; apply Rseq_cv_eq_compat with
 (Rseq_plus (Rseq_sum (Rseq_shift An)) (An O)).
 intro n ; unfold Rseq_plus, Rseq_constant ;
  rewrite (Rseq_sum_shift_compat An n) ; ring.
 apply Rseq_cv_plus_compat ; [assumption | apply Rseq_constant_cv].
Qed.

Lemma Rser_cv_shift_rev2: forall Un l,
  Rser_cv (Rseq_shift Un) (l - (Un O)) -> Rser_cv Un l.
Proof.
intros ; replace l with (l - Un O + Un O) by ring ;
 apply Rser_cv_shift_rev ; assumption.
Qed.

Lemma Rser_cv_shifts : forall k An l, Rser_cv An l ->
  Rser_cv (Rseq_shifts An (S k)) (l - Rseq_sum An k).
Proof.
intros k An l Hl ; eapply Rseq_cv_eq_compat.
 intro n ; apply Rseq_sum_shifts_compat.
 apply Rseq_cv_minus_compat.
  apply Rseq_cv_shifts_compat_reciprocal ; assumption.
  apply Rseq_constant_cv.
Qed.

Lemma Rser_cv_shifts_rev : forall k An l,
  Rser_cv (Rseq_shifts An (S k)) l ->  Rser_cv An (l + Rseq_sum An k).
Proof.
intros k An l Hl ; apply Rseq_cv_shifts_compat with (S k) ; apply Rseq_cv_eq_compat with
 (Rseq_plus (Rseq_sum (Rseq_shifts An (S k))) (Rseq_sum An k)).
 intro n ; unfold Rseq_plus, Rseq_constant ;
  rewrite (Rseq_sum_shifts_compat An k n) ; ring.
 apply Rseq_cv_plus_compat ; [assumption | apply Rseq_constant_cv].
Qed.

Lemma Rser_cv_sig_shift_rev: forall An,
  {l | Rser_cv (Rseq_shift An) l} -> {l | Rser_cv An l}.
Proof.
intros An [l Hl] ; exists (l + An O) ; apply Rser_cv_shift_rev ; assumption.
Qed.

Lemma Rser_cv_sig_shifts_rev: forall k An,
  {l | Rser_cv (Rseq_shifts An k) l} -> {l | Rser_cv An l}.
Proof.
intros [| k] An [l Hl].
 exists l ; eapply Rser_cv_ext ; [symmetry ; apply Rseq_shifts_0 | assumption].
 exists (l + Rseq_sum An k) ; apply Rser_cv_shifts_rev ; assumption.
Qed.

(** If a series converges absolutely, then it converges *)

Lemma Rser_abs_cv_cv : forall An, {l | Rser_abs_cv An l} -> {l | Rser_cv An l}.
Proof.
intros An Habs ; apply (cv_cauchy_2 An),
 cauchy_abs, cv_cauchy_1, Habs.
Qed.

(** If a series converges, its coefficients' sequence converges to zero *)

Lemma Rser_cv_zero : forall An l, Rser_cv An l -> Rseq_cv An 0.
Proof.
intros An l Hl ; apply Rseq_cv_shift_compat ;
 apply Rseq_cv_eq_compat with (Rseq_shift (Rseq_sum An) - Rseq_sum An)%Rseq.
 clear ; intro p ; unfold Rseq_shift, Rseq_minus ; rewrite Rseq_sum_simpl ; ring.
 replace 0 with (l - l) by ring ; apply Rseq_cv_minus_compat ;
 [apply Rseq_cv_shift_compat_reciprocal |] ; assumption.
Qed.
