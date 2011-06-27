Require Import Reals Rpow_facts.
Require Import Fourier MyRIneq.

Require Import Ranalysis_def Rfunction_def Rextensionality.

Require Import Rsequence_facts RFsequence RFsequence_facts.
Require Import Rpser_def Rpser_def_simpl Rpser_base_facts.
Require Import Rpser_radius_facts Rpser_sums Rpser_derivative.

Require Import Rfunction_classes Nth_derivative_def Nth_derivative_facts.

Open Local Scope R_scope.

(** * An_nth_deriv is the general term of the nth derivative of sum An. *)

Lemma nth_derive_sum_explicit (k : nat) :
  forall (An : Rseq) (rAn : infinite_cv_radius An)
  (rAnk : infinite_cv_radius (An_nth_deriv An k))
  (rdAnk : D k (sum _ rAn)),
  nth_derive (sum _ rAn) rdAnk == sum _ rAnk.
Proof.
induction k ; intros An rAn rAnk rdAn x.
 rewrite (sum_ext _ _ (An_nth_deriv_0 An) _ rAn) ; simpl ; reflexivity.

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