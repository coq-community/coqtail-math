Require Import Rsequence_def Rsequence_base_facts.
Require Import Reals Rfunction_def Rfunction_facts Rextensionality.

Require Import Nth_derivative_def Nth_derivative_facts.
Require Import Rpser.
Require Import Rfunction_classes.

Require Import Dequa_def Dequa_facts Dequa_quote.
Require Import List.

(* Require Import LegacyField_Theory. *)

Local Open Scope R_scope.

Lemma constant_is_cst : forall (c : R) (rc: infinite_cv_radius (constant_seq c)),
  forall x, sum _ rc x = c.
Proof.
intros c rc ; solve_diff_equa ; reflexivity.
Qed.

Lemma identity_is_id : forall (ri : infinite_cv_radius identity_seq)
 (di : derivable (sum _ ri)), forall x, derive (sum _ ri) di x = 1.
Proof.
intros ri di ; solve_diff_equa ; unfold An_deriv, identity_seq,
 constant_seq, Rseq_shift, Rseq_mult ; intros [ | n] ; simpl ; ring.
Qed.

Lemma diff_equa_cos : forall (rc : infinite_cv_radius cos_seq),
  forall x, nth_derive (sum _ rc) (D_infty_Rpser _ rc 2%nat) x
  = - nth_derive (sum _ rc) (D_infty_Rpser _ rc O) x.
Proof.
intro rc ; solve_diff_equa ; intro n ; rewrite An_nth_deriv_S',
 An_nth_deriv_1, (An_deriv_ext _ (- sin_seq)).
 rewrite An_deriv_opp_compat ; unfold Rseq_opp ;
  apply Ropp_eq_compat ; apply Deriv_sin_seq_simpl.
 apply Deriv_cos_seq_simpl.
Qed.

Lemma diff_equa_sin : forall (rc : infinite_cv_radius sin_seq),
  forall x, nth_derive (sum _ rc) (D_infty_Rpser _ rc 2%nat) x
  = - nth_derive (sum _ rc) (D_infty_Rpser _ rc O) x.
Proof.
intro rc ; solve_diff_equa ; intro n ; rewrite An_nth_deriv_S',
 An_nth_deriv_1, (An_deriv_ext _ cos_seq) ;
 [apply Deriv_cos_seq_simpl | apply Deriv_sin_seq_simpl].
Qed.

Lemma diff_equa_exp : forall n (re : infinite_cv_radius exp_seq) x,
  nth_derive (sum _ re) (D_infty_Rpser _ re (S n)) x
  = nth_derive (sum _ re) (D_infty_Rpser _ re n) x.
Proof.
intros n re ; solve_diff_equa ; rewrite An_nth_deriv_S',
 (An_nth_deriv_ext _ exp_seq) ; [reflexivity | apply Deriv_exp_seq_simpl].
Qed.

Require Import Commutative_ring_binomial.



Lemma Rexp_mult_simpl : forall a b x,
  Rexp (a * x) * Rexp (b * x) = Rexp ((a + b) * x).
Proof.
intros a b ; unfold Rexp ; solve_diff_equa.
Abort.
