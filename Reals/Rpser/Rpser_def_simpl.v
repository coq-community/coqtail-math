Require Import Lia.
Require Import MyRIneq Rpow_facts.
Require Import Rsequence_def Rsequence_rewrite_facts.
Require Import Rpser_def.

Local Open Scope Rseq_scope.
Local Open Scope R_scope.

(** ** Simplification lemmas about the new concepts. *)
(** * gt_pser, gt_abs_pser *)

Lemma gt_pser_0 : forall An r, gt_pser An r O = An O.
Proof.
intros ; unfold gt_pser, Rseq_mult ;
rewrite pow_O ; apply Rmult_1_r.
Qed.

Lemma gt_abs_pser_0 : forall An r,
  gt_abs_pser An r O = Rabs (An O).
Proof.
intros ; unfold gt_abs_pser, Rseq_abs ;
rewrite gt_pser_0 ; reflexivity.
Qed.

Lemma gt_pser_1 : forall An n, gt_pser An 1 n = An n.
Proof.
intros An n ; unfold gt_pser, Rseq_mult ; rewrite pow1 ; ring.
Qed.

Lemma gt_abs_pser_1 : forall An n, gt_abs_pser An 1 n = Rabs (An n).
Proof.
intros An n ; unfold gt_abs_pser, Rseq_abs ; f_equal ; apply gt_pser_1.
Qed.

Lemma gt_abs_pser_S : forall An r n,
  gt_abs_pser An r (S n) = gt_abs_pser (Rseq_shift An) r n * Rabs r.
Proof.
intros An r n ; unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult, Rseq_shift ;
 simpl ; rewrite (Rmult_comm r), <- Rmult_assoc; apply Rabs_mult.
Qed.

Lemma gt_abs_pser_0_ub : forall An n,
  gt_abs_pser An 0 n <= Rabs (An O).
Proof.
intros An [ |i] ; unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult.
rewrite pow_O, Rmult_1_r ; reflexivity.
rewrite pow_i ; [rewrite Rmult_0_r, Rabs_R0 ; apply Rabs_pos | lia].
Qed.

Lemma gt_abs_pser_le_compat : forall An r r' n,
  Rabs r <= Rabs r' -> 
  gt_abs_pser An r n <= gt_abs_pser An r' n.
Proof.
intros An r r' n Hrr' ; unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult ;
do 2 rewrite Rabs_mult, <- RPow_abs ; apply Rmult_le_compat_l ; [apply Rabs_pos |] ;
apply pow_le_compat ; [apply Rabs_pos | assumption].
Qed.

Lemma gt_abs_pser_unfold : forall An r,
  gt_abs_pser An r == gt_pser (| An |) (Rabs r).
Proof.
intros An r n ; unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult ;
 rewrite RPow_abs ; apply Rabs_mult.
Qed.

Lemma gt_pser_zip_compat : forall An Bn r,
  gt_pser (Rseq_zip An Bn) r == Rseq_zip (gt_pser An (r ^ 2)) (r * gt_pser Bn (r ^ 2)).
Proof.
intros An Bn r n ; unfold gt_pser, Rseq_zip, Rseq_mult, Rseq_constant ;
 case (n_modulo_2 n) ; intros [p Hp].
 rewrite <- pow_mult, <- Hp ; reflexivity.
 rewrite <- pow_mult, Hp, <- tech_pow_Rmult ; ring.
Qed.

(** Extenstionality of the concepts *)

Lemma gt_pser_ext : forall An Bn x, An == Bn ->
  gt_pser An x == gt_pser Bn x.
Proof.
intros An Bn x Heq n ; unfold gt_pser, Rseq_mult ;
rewrite Heq ; reflexivity.
Qed.

Lemma gt_abs_pser_ext : forall An Bn x, An == Bn ->
  gt_abs_pser An x == gt_abs_pser Bn x.
Proof.
intros ; intro n ; unfold gt_abs_pser, Rseq_abs ;
erewrite gt_pser_ext ; eauto.
Qed.

(** gt_abs_pser is compatible with Rabs & Rseq_abs. *)

Lemma gt_abs_pser_Rabs_compat : forall An r,
  gt_abs_pser An (Rabs r) == gt_abs_pser An r.
Proof.
intros An r n ; unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult ;
 rewrite Rabs_mult, RPow_abs, Rabs_Rabsolu, <- Rabs_mult ;
 reflexivity.
Qed.

Lemma gt_abs_pser_Rseq_abs_compat : forall An r,
  gt_abs_pser (| An |) r == gt_abs_pser An r.
Proof.
intros An r n ; unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult ;
 rewrite Rabs_mult, Rabs_Rabsolu, <- Rabs_mult ; reflexivity.
Qed.

(** * An_deriv, An_nth_deriv *)
(** Relation between An_nth_deriv & An_deriv. *)

Lemma An_nth_deriv_0 : forall An, An_nth_deriv An 0 == An.
Proof.
 intros An n ; unfold An_nth_deriv, Rseq_shifts, Rseq_div, Rseq_mult, Rdiv ;
 rewrite plus_0_l ; field ; apply not_0_INR ; apply fact_neq_0.
Qed.

Lemma An_nth_deriv_S : forall An k,
 An_nth_deriv An (S k) == An_deriv (An_nth_deriv An k).
Proof.
assert (Hrew : forall n, / Rseq_fact n = INR (S n) * / Rseq_fact (S n)).
 intro n ; unfold Rseq_fact ; rewrite fact_simpl, mult_INR, Rinv_mult_distr,
 <- Rmult_assoc.
 symmetry ; apply Rinv_r_simpl_r ; apply not_0_INR ; lia.
 apply not_0_INR ; lia.
 apply INR_fact_neq_0.
intros An k n ; unfold An_nth_deriv, An_deriv, Rseq_shift, Rseq_shifts,
 Rseq_div, Rseq_mult, Rdiv ; rewrite Hrew, <- plus_n_Sm.
 simpl ; ring.
Qed.

Lemma An_nth_deriv_S' : forall An k,
 An_nth_deriv An (S k) == An_nth_deriv (An_deriv An) k.
Proof.
intros An k n ; unfold An_nth_deriv, An_deriv, Rseq_shift, Rseq_shifts,
 Rseq_mult, Rseq_div, Rdiv ; simpl (S k + n)%nat ; rewrite Rseq_fact_simpl ;
 ring.
Qed.

Lemma An_nth_deriv_1 : forall An, An_nth_deriv An 1 == An_deriv An.
Proof.
intros An n ; rewrite An_nth_deriv_S ; unfold An_deriv, Rseq_mult, Rseq_shift ;
 rewrite An_nth_deriv_0 ; reflexivity.
Qed.

Lemma An_expand_1 : forall An, An_expand An 1 == An.
Proof.
intros An n ; unfold An_expand, Rseq_pow, Rseq_mult ;
rewrite pow1, Rmult_1_l ; reflexivity.
Qed.
