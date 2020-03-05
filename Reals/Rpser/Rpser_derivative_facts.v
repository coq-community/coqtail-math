Require Import Reals Rpow_facts.
Require Import Lra MyRIneq.

Require Import Ranalysis_def Rfunction_def Rextensionality.

Require Import Rsequence_facts RFsequence RFsequence_facts.
Require Import Rpser_def Rpser_def_simpl Rpser_base_facts.
Require Import Rpser_radius_facts Rpser_sums Rpser_derivative.

Require Import Rinterval.
Require Import Rfunction_classes Nth_derivative_def Nth_derivative_facts.

Local Open Scope R_scope.

(** * An_nth_deriv is the general term of the nth derivative of sum An. *)

Lemma nth_derive_Rball_sum_explicit (k : nat):
  forall An r x (rAn: finite_cv_radius An r)
  (rAnk: finite_cv_radius (An_nth_deriv An k) r)
  (rdAnk: D_Rball 0 r k (sum_r An r rAn)),
  Rball 0 r x ->
  nth_derive_Rball 0 r (sum_r An r rAn) rdAnk x
  = sum_r (An_nth_deriv An k) r rAnk x.
Proof.
induction k ; intros An r x rAn rAnk rdAnk x_in.
 apply sum_r_ext ; symmetry ; apply An_nth_deriv_0.

 simpl ; assert (rdAn: finite_cv_radius (An_deriv An) r).
  rewrite <- finite_cv_radius_derivable_compat ; assumption.
 rewrite nth_derive_Rball_ext with (g := sum_r (An_deriv An) r rdAn)
 (pr2 := D_Rball_infty_Rpser _ _ rdAn k).
 assert (rdAnk': finite_cv_radius (An_nth_deriv (An_deriv An) k) r).
  rewrite <- finite_cv_radius_nth_derivable_compat ; assumption.
 rewrite sum_r_ext with (rBn := rdAnk').
 erewrite (IHk _ _ _ rdAn rdAnk') ; [reflexivity | assumption].
 apply An_nth_deriv_S'.
 intros y y_in ; rewrite derive_Rball_sum_r.
  apply sum_r_ext ; reflexivity.
  assumption.
 assumption.
Qed.

Lemma nth_derive_sum_explicit (k : nat) :
  forall (An : Rseq) (rAn : infinite_cv_radius An)
  (rAnk : infinite_cv_radius (An_nth_deriv An k))
  (rdAnk : D k (sum _ rAn)),
  nth_derive (sum _ rAn) rdAnk == sum _ rAnk.
Proof.
induction k ; intros An rAn rAnk rdAn x.
 apply sum_ext ; symmetry ; apply An_nth_deriv_0.

 simpl.
 assert (rdAn' : infinite_cv_radius (An_deriv An)) by
  (rewrite <- infinite_cv_radius_derivable_compat ; assumption).
 rewrite (nth_derive_ext _ _ (sum (An_deriv An) rdAn') _ (D_infty_Rpser _ rdAn' k)).

 assert (rAnk' : infinite_cv_radius (An_nth_deriv (An_deriv An) k)) by
  (rewrite <- infinite_cv_radius_nth_derivable_compat ; assumption).
 rewrite (IHk _ _ rAnk').
 erewrite <- sum_ext ; [| eapply An_nth_deriv_S'] ; reflexivity.

 intro ; unfold derive ; apply derive_pt_sum.
Qed.