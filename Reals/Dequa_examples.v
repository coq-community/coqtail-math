Require Import Reals Rfunction_def Rfunction_facts Rextensionality.
Require Import Rsequence_def Rsequence_base_facts.

Require Import Nth_derivative_def Nth_derivative_facts.
Require Import Rpser.
Require Import C_n_def C_n_facts C_n_usual.

Require Import Dequa_def Dequa_facts.
Require Import List.

Require Import LegacyField_Theory.

Open Local Scope de_scope.

Lemma constant_is_cst : forall r, 
 [| y 0 0 :=: `c r |]R ((existT _ _ (constant_infinite_cv_radius r)) :: nil).
Proof.
intros r ; apply interp_equa_in_N_R ; simpl ; apply An_nth_deriv_0.
Qed.

Lemma identity_is_id :
 [| y 0 1 :=: cst 1 |]R ((existT _ _ identity_infinite_cv_radius) :: nil).
Proof.
apply interp_equa_in_N_R ; simpl ; rewrite An_nth_deriv_1.
intro n ; unfold An_deriv, Rseq_shift, Rseq_mult, constant_seq, identity_seq.
 destruct (eq_nat_dec n 0) ; destruct (eq_nat_dec (S n) 1).
   subst ; rewrite Rmult_1_r ; reflexivity.
   subst ; destruct (f (eq_refl 1%nat)).
  inversion e as [H] ; destruct (f H).
  rewrite Rmult_0_r ; reflexivity.
Qed.

Lemma diff_equa_cos :
 [| y 0 2 :=: - y 0 0 |]R ((existT _ _ cos_infinite_cv_radius) :: nil).
Proof.
apply interp_equa_in_N_R ; simpl.
 do 2 (rewrite An_nth_deriv_S', An_nth_deriv_0).
 intro n ; rewrite (An_deriv_ext _ (- sin_seq)%Rseq) ;
  [ | apply Deriv_cos_seq_simpl] ; rewrite An_deriv_opp_compat ;
  unfold Rseq_opp ; apply Ropp_eq_compat ;
  apply Deriv_sin_seq_simpl.
Qed.

Lemma diff_equa_sin :
 [| y 0 2 :=: - y 0 0 |]R ((existT _ _ sin_infinite_cv_radius) :: nil).
Proof.
apply interp_equa_in_N_R ; simpl.
 do 2 (rewrite An_nth_deriv_S', An_nth_deriv_0).
 intro n ; rewrite (An_deriv_ext _ (cos_seq)%Rseq) ;
  [apply Deriv_cos_seq_simpl | apply Deriv_sin_seq_simpl].
Qed.

Lemma diff_equa_exp : forall n,
 [| y 0 (S n) :=: y 0 n |]R ((existT _ _ exp_infinite_cv_radius) :: nil).
Proof.
intro n ; apply interp_equa_in_N_R ; simpl ;
 rewrite An_nth_deriv_S', (An_nth_deriv_ext _ exp_seq) ;
 [reflexivity | apply Deriv_exp_seq_simpl].
Qed.