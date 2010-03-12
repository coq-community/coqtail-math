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

Require Import Reals.
Require Import Rintegral.
Require Import Rintegral_usual.
Require Import Rintegral_tactic.
Require Import Fourier.
Require Import Rsequence_facts.
Require Import Rsequence_subsequence.

Open Local Scope R_scope.

Coercion INR : nat >-> R.

Definition sin_n n := fun x => pow (sin x) n.

Lemma integrable_sin_n n : Riemann_integrable (comp (fun x => pow x n) sin) 0 (PI/2).
Proof.
intro n.
apply RiemannInt_P6.
pose proof PI_RGT_0; fourier.
intros x Hx; apply continuity_pt_comp.
  apply continuity_sin.
  apply derivable_continuous; apply derivable_pow.
Qed.

Definition W_even n := ((PI/2)*(fact (2 * n))/(2 ^ (2 * n) * (fact n) ² )).
Definition W_odd n := ((2^(2*n) * (fact n) ²)/(fact (S (2 * n)))).

Lemma Wallis_0 : Rint (sin_n 0)  0 (PI/2) (PI/2).
Proof.
apply Rint_eq_compat with (fct_cte 1).
  trivial.
assert(Hrew : (PI/2) = (1*(PI/2 -0))) by ring; rewrite Hrew at 2; clear Hrew.
auto with Rint.
Qed.

Lemma Wallis_1 : Rint (sin_n 1)  0 (PI/2) 1.
Proof.
unfold sin_n.
apply Rint_eq_compat with sin.
  auto with *.
assert(Heq : 1 = (cos 0 - cos (PI/2))).
  rewrite cos_PI2, cos_0; ring.
rewrite Heq at 3.
auto with Rint.
Qed.

(** Recurrence formula *)
Lemma Wallis_formula Wn n: 
  Rint (sin_n n) 0 (PI/2) Wn-> 
    Rint (sin_n (S (S n))) 0 (PI/2) (Wn * (S n)/(S (S n))).
Proof.
intros Wn n H.
pose (RiemannInt (integrable_sin_n (S (S n)))) as W2n.
pose proof (Rint_RiemannInt_link _ _ _ (integrable_sin_n (S (S n)))) as HW2.
assert (W2n = (S n) * (Wn - W2n)) as Heq.
replace (S n * (Wn - W2n)) with 
  (comp (fun x => x ^ (S n)) sin (PI/2) *((- cos)%F (PI/2)) - comp (fun x => x ^ (S n)) sin 0 *((- cos)%F 0) - (-(S n) * (Wn - W2n))).
eapply Rint_parts with (f' := fun x => ((S n) * sin x ^ n)* cos x) (g' := sin).
  left; apply PI2_RGT_0.

  intros.
  apply derivable_pt_lim_comp.
    auto with Rcont.
    apply derivable_pt_lim_pow.

  intros.
  replace (sin x) with (- - sin x) by ring.
  auto with Rcont.
  
  intros.
  apply continuity_pt_mult.
    apply continuity_pt_mult; auto with Rcont.
      apply continuity_pt_const; intros u v; reflexivity.
      reg.
    auto with Rcont.
    auto with Rcont.

  apply Rint_eq_compat with (comp (fun x : R => x ^ S (S n)) sin).
  intros; unfold comp, mult_fct; simpl; ring.
  apply Rint_RiemannInt_link.
  
  apply Rint_eq_compat with (fun x => (- S n) * (sin x ^ n - sin x ^ (S (S n)))).
  intros.
  unfold mult_fct, opp_fct.
  rewrite Rmult_assoc.
  replace (cos x * - cos x) with (-(1 - (sin x)²)).
  unfold Rsqr; simpl; ring.
  rewrite <- (cos2 x); unfold Rsqr; ring.
  apply Rint_scalar_mult_compat_l.
  apply Rint_minus; trivial.

  unfold opp_fct, comp;
  rewrite cos_0, cos_PI2, sin_PI2, sin_0;
  simpl; ring.

replace (Wn * S n / S (S n)) with (W2n).
  trivial.
rewrite Rmult_comm.
replace W2n with (/(S (S n)) * (S (S n))* W2n).
replace Wn with ((Wn - W2n) + W2n) by ring.
rewrite Rmult_plus_distr_l.
rewrite <- Heq.
unfold Rdiv.
rewrite Rmult_comm with (r1 := (W2n + S n * W2n)).
rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
simpl; ring.
field.
auto with *.
Qed.

Lemma Wallis_even n : Rint (sin_n (2 * n)) 0 (PI/2) (W_even n).
Proof.
unfold W_even.
induction n.
  simpl; unfold Rsqr; field_simplify; apply Wallis_0.

apply Rint_eq_compat with (sin_n (S (S (2 *  n)))).
  intros; simpl;
  replace (S (n + S (n + 0))) with (S (S (n + (n + 0)))) by auto;
  reflexivity.

replace (PI / 2 * fact (2 * S n) / (2 ^ (2 * S n) * (fact (S n)) ²)) with
  ((PI / 2 * fact (2 * n) / (2 ^ (2 * n) * (fact n)²)) * S (2 * n) / (S (S (2 * n)))).
apply Wallis_formula; apply IHn.

replace (2 * S n)%nat with (S (S (2 * n))) by auto with *.
repeat rewrite fact_simpl.
repeat rewrite <- tech_pow_Rmult.
unfold Rsqr.
replace (S (S (2*n))) with (2 * (S n))%nat by auto with *.
repeat rewrite mult_INR.
replace (INR 2) with 2 by trivial; field.

repeat split.
apply not_0_INR; apply fact_neq_0.
auto with *.
apply pow_nonzero; pose proof Rlt_R0_R2; intro; fourier.
Qed.



Lemma Wallis_odd n : Rint (sin_n (S (2 * n))) 0 (PI/2) ((2^(2*n) * (fact n) ²)/(fact (S (2 * n)))).
Proof.
unfold W_odd.
induction n.
  simpl; unfold Rsqr; replace (1 * (1 * 1) / 1) with 1 by field; apply Wallis_1.
apply Rint_eq_compat with (sin_n (S (S (S (2 * n))))).
  intros; simpl.
replace (n + S (n + 0))%nat with (S (n + (n + 0))) by auto;
reflexivity.
replace (2 ^ (2 * S n) * (fact (S n))² / fact (S (2 * S n))) with
  ((2 ^ (2 * n) * (fact n)² / fact (S (2 * n))) * (S (S (2 * n)))/(S (S (S (2 * n))))).
apply Wallis_formula; apply IHn.

replace (2 * S n)%nat with (S (S (2 * n))) by auto with *.
repeat rewrite fact_simpl.
repeat rewrite <- tech_pow_Rmult.
unfold Rsqr.
replace (S (S (2*n))) with (2 * (S n))%nat by auto with *.
repeat rewrite mult_INR.
replace (INR 2) with 2 by trivial; field.

repeat split;apply not_0_INR; try (auto with *).
apply fact_neq_0.
Qed.

Lemma Wallis_odd_le_even n : W_odd n <= W_even n.
Proof.
intro n.
apply (Rint_le_compat (sin_n (S (2 * n))) (sin_n (2 * n)) 0 (PI/2)).
  left; apply PI2_RGT_0.
  
  intros; unfold sin_n.
  replace (sin u ^ (2 * n)) with (1 * sin u ^ (2 * n)) by ring.
  rewrite <- tech_pow_Rmult.
  apply Rmult_le_compat_r.
    apply pow_le.
    apply sin_ge_0; intuition; fourier.
    pose proof (SIN_bound u); intuition.

apply Wallis_odd.
apply Wallis_even.
Qed.


Lemma Wallis_even_le_odd n : W_even (S n) <= W_odd n.
Proof.
intro n.
apply (Rint_le_compat (sin_n (2 * (S n))) (sin_n (S (2 * n))) 0 (PI/2)).
  left; apply PI2_RGT_0.
  
  intros; unfold sin_n.
  replace (2 * (S n))%nat with (S (S (2 * n))) by auto with *.
  replace (sin u ^ (S (2 * n))) with (1 * sin u ^ (S (2 * n))) by ring.
  rewrite <- tech_pow_Rmult.
  apply Rmult_le_compat_r.
    apply pow_le.
    apply sin_ge_0; intuition; fourier.
    pose proof (SIN_bound u); intuition.

apply Wallis_even.
apply Wallis_odd.
Qed.


Lemma Wallis_maj (n : nat) : (2*n/ (S (2 * n))) * (W_even n) <= W_odd n.
Proof.
intro n.
destruct n.

  unfold W_even, W_odd, Rsqr.
  simpl; field_simplify; fourier.

   replace 2 with (INR 2) by trivial; rewrite <- mult_INR.
  replace (2 * S n)%nat with (S (S (2 * n))) by auto with *.

  replace (W_odd (S n)) with (INR (S (S (2 * n))) / INR (S (S (S (2 * n)))) * W_odd n).

  apply Rmult_le_compat_l.
  unfold Rdiv.
  repeat apply Rmult_le_pos; auto with *.

  apply Wallis_even_le_odd.
  
  rewrite Rmult_comm.
  unfold Rdiv.
  rewrite <- Rmult_assoc.
  eapply (Rint_uniqueness _ 0 (PI/2)).
  apply Wallis_formula.
  apply Wallis_odd.
  replace (S (S (2 * n))) with (2 * (S n))%nat by auto with *.
  apply Wallis_odd.
Qed.

Lemma W_even_pos : forall n, 0 < W_even n.
Proof.
intro n.
 unfold W_even, Rsqr, Rdiv.
 repeat apply Rmult_lt_0_compat.
 fourier.
 fourier.
 apply Rmult_lt_reg_l with 4.
 fourier.
 rewrite Rmult_0_r ; apply PI_RGT_0.
 fourier.
 apply INR_fact_lt_0.
 repeat rewrite Rinv_mult_distr ; repeat apply Rmult_lt_0_compat.
 rewrite Rinv_pow.
 apply pow_lt ; fourier.
 apply Rgt_not_eq ; fourier.
 apply Rinv_0_lt_compat ; apply INR_fact_lt_0.
 apply Rinv_0_lt_compat ; apply INR_fact_lt_0.
 apply Rgt_not_eq ; apply INR_fact_lt_0.
 apply Rgt_not_eq ; apply INR_fact_lt_0.
 apply Rgt_not_eq ; apply pow_lt ; fourier.
 apply Rmult_integral_contrapositive_currified ; apply Rgt_not_eq ; apply INR_fact_lt_0.
Qed.

Lemma Wallis_bound : forall (n : nat),  2*n / (S(2 * n)) <= W_odd n / W_even n <= 1.
Proof.
intro n ; split.
 apply Rle_trans with (2 * n / S (2 * n) * (W_even n / W_even n)).
 right ; field ; split.
 apply Rgt_not_eq ; apply W_even_pos.
 apply not_0_INR ; discriminate.
 unfold Rdiv ; rewrite <- Rmult_assoc ; apply Rmult_le_compat_r.
 left ; apply Rinv_0_lt_compat ; apply W_even_pos.
 apply Wallis_maj.
 rewrite <- Rinv_r with (W_even n).
 unfold Rdiv ; apply Rmult_le_compat_r.
 left ; apply Rinv_0_lt_compat ; apply W_even_pos.
 apply Wallis_odd_le_even.
 apply Rgt_not_eq ; apply W_even_pos.
Qed.

Lemma Wallis_quotient_lim1 : Rseq_cv (fun n => W_odd n / W_even n) 1.
Proof.
apply Rseq_sandwich_theorem
  with (Un := fun (n : nat) => 2 * n / (S (2 * n))) (Wn := fun n => 1).
  apply Rseq_cv_eq_compat with (Un := fun n => 2 * n / (2 * n + 1)).
    intros n.
    rewrite S_INR; rewrite mult_INR; reflexivity.
  apply Rseq_equiv_cv_div.
    apply Rseq_equiv_sym.
    apply Rseq_equiv_plus_little_O_compat_l.
    apply Rseq_equiv_refl.
    apply Rseq_little_O_Rmult_compat_r; [|intro H; fourier].
    eapply Rseq_little_O_eq_compat
      with (Un := Rseq_poly 0) (Vn := Rseq_poly 1).
      intros n; unfold Rseq_poly; apply pow_O.
      intros n; unfold Rseq_poly; apply pow_1.
      apply Rseq_poly_little_O; constructor.
    intros n; assert (H := pos_INR n); intros Hc; fourier.
  apply Rseq_constant_cv.
  apply Wallis_bound.
Qed.

Lemma Wallis_quotient :
  forall n, W_odd n / W_even n = (2*2 ^ (4*n) * (fact n) ^ 4)/(PI*fact (2 * n) * fact (S (2 * n))).
Proof.
intro n; unfold W_odd, W_even, Rsqr, Rdiv.
replace (2 ^ (4 * n)) with ((2 ^ (2 * n)) * (2 ^ (2 * n))).
field; repeat split.
  apply not_0_INR; apply fact_neq_0.
  apply not_0_INR; apply fact_neq_0.
  apply PI_neq0.
  apply not_0_INR; apply fact_neq_0.
  apply pow_nonzero; intros H; fourier.
  replace (4 * n)%nat with (2 * n + 2 * n)%nat by omega.
  rewrite pow_add.
  reflexivity.
Qed.

Lemma Stirling_subproof_tech_admitted : 
  exists l : R, l <> 0 /\ (fun n => fact n) ~ (fun n => (n /(exp 1)) ^ n * sqrt n * l).
Admitted.

Lemma Wallis_quotient_lim2 l : 
l <> 0 ->
  (fun n => fact n) ~ (fun n => (n /(exp 1)) ^ n * sqrt n * l) ->
    Rseq_cv (fun n => W_odd n / W_even n) (l²/(2*PI)).
Proof.
intros l Hneq Hl.
apply Rseq_cv_eq_compat with (fun n => (2*2 ^ (4*n) * (fact n) ^ 4)/(PI*fact (2 * n) * fact (S (2 * n)))).
  intro; rewrite Wallis_quotient; reflexivity.
assert (H2n : (fun n : nat => fact (2*n)) ~ (fun n : nat => (2*n / exp 1) ^ (2*n) * sqrt (2*n) * l)).
  pose (mult 2) as db.
  apply Rseq_equiv_eq_compat with (fun n => fact (db n)) (fun k => (fun n : nat => (n / exp 1) ^ n * sqrt n * l) (db k)).
  intro n; unfold db; reflexivity.
  intro n; unfold db; rewrite mult_INR; reflexivity.
  apply Rseq_equiv_subseq_compat with (Un := fact) (Vn := fun k : nat => (k / exp 1) ^ k * sqrt k * l)(phi := db).
  assumption.
  apply extractor_mult_2.

assert (H2n1 : (fun n : nat => fact (S(2*n))) ~ (fun n : nat => (S(2*n) / exp 1) ^ (S(2*n)) * sqrt (S(2*n)) * l)).
  pose (fun n => S (mult 2 n)) as db.
  apply Rseq_equiv_eq_compat with (fun n => fact (db n)) (fun k => (fun n : nat => (n / exp 1) ^ n * sqrt n * l) (db k)).
  intro n; unfold db; reflexivity.
  intro n; unfold db; reflexivity.
  apply Rseq_equiv_subseq_compat with (Un := fact) (Vn := fun k : nat => (k / exp 1) ^ k * sqrt k * l)(phi := db).
  assumption.
  unfold db; apply extractor_comp.
  apply extractor_S.
  apply extractor_mult_2.
  
apply Rseq_equiv_cv_constant.
Open Local Scope Rseq_scope.
apply Rseq_equiv_eq_compat with 
  (Un := 2 * (fun n => 2 ^ (4 * n)) * fact * fact * fact * fact *
  / (PI * (fun n => fact (2 * n)) * (fun n => fact (S (2 * n))))) (Vn := (l² / (2 * PI))%R).
intro n; unfold Rseq_mult, Rseq_inv, Rdiv, Rseq_constant; ring.
intro; reflexivity.
apply Rseq_equiv_trans with 
(2 * (fun n => 2 ^ (4 * n)) * ((fun n : nat => ((n / exp 1) ^ n * sqrt n * l)%R))*((fun n : nat => ((n / exp 1) ^ n * sqrt n * l)%R))*((fun n : nat => ((n / exp 1) ^ n * sqrt n * l)%R))*((fun n : nat => ((n / exp 1) ^ n * sqrt n * l)%R))*
  / (PI * (fun n : nat => ((2 * n / exp 1) ^ (2 * n) * sqrt (2 * n) * l)%R) *  (fun n => (S (2 * n) / exp 1) ^ S (2 * n) * sqrt (S (2 * n)) * l)%R)).

repeat apply Rseq_equiv_mult_compat;
  try apply Rseq_equiv_refl; try assumption.
apply Rseq_equiv_inv_compat. (*TODO : 2eme subgoal sqrt 2* n <> 0 etait faux. Generalisation du lemme*)
exists O. intros n Hn.
unfold Rseq_mult, Rseq_constant.
apply Rmult_integral_contrapositive ; split ; 
[ apply Rmult_integral_contrapositive ; split ; 
[ apply PI_neq0 | apply INR_fact_neq_0] | apply INR_fact_neq_0 ].

exists (S O). intros n Hn; unfold Rseq_mult, Rseq_constant.
(* crade *)
assert(H : {m | n = S m}). exists (pred n). intuition.
destruct H as (m, Subst).
rewrite Subst.
(* fin crade *)
apply Rmult_integral_contrapositive ; split ; 
[ apply Rmult_integral_contrapositive ; split ; 
[ apply PI_neq0 | apply Rmult_integral_contrapositive ; split ; 
[ apply Rmult_integral_contrapositive ; split ; 
[ (apply pow_nonzero ; unfold Rdiv ; apply Rmult_integral_contrapositive ; split ;
[ apply Rmult_integral_contrapositive ; split ; 
[ (intro ; fourier) | (apply not_0_INR ; intuition) ] | (apply Rinv_neq_0_compat ; generalize (exp_pos 1) ; intros ; intro ; fourier)])
| (intro H ; apply sqrt_eq_0 in H ; [ (apply Rmult_integral in H ; destruct H as [H|H] ; [ fourier | (generalize H ; apply not_0_INR ; intuition) ])
| apply Rmult_le_pos ; intuition ]) ]
| apply Hneq ] ] | apply Rmult_integral_contrapositive ; split ; 
[ apply Rmult_integral_contrapositive ; split ;
[ (apply pow_nonzero ; unfold Rdiv ; apply Rmult_integral_contrapositive ; split ;
[ apply not_0_INR ; intuition | (apply Rinv_neq_0_compat ; generalize (exp_pos 1) ; intros ; intro ; fourier) ])
| (intro H ; apply sqrt_eq_0 in H ; [ (apply not_0_INR in H ; intuition )
| apply pos_INR ])
] | apply Hneq ] ].

apply Rseq_equiv_mult_compat.
apply Rseq_equiv_mult_compat.
apply Rseq_equiv_refl.
assumption.
assumption.
clear Hl H2n H2n1.
apply Rseq_cv_equiv_constant.
admit.
Admitted.
    

(* Lemma Stirling : (fun n => fact n) ... with 
 Rseq_cv_unique [Wallis_quotient_lim1 | Wallis_quotient_lim2 *)

