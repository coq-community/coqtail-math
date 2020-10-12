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

Require Import Max.
Require Import Reals.
Require Import Rintegral.
Require Import Rintegral_usual.
Require Import Rintegral_tactic.
Require Import Lia Lra.
Require Import Rsequence_facts.
Require Import Rsequence_subsequence.
Require Import Rpser.
Require Import RTaylor.
Require Import MyRfunctions.
Require Import Rsequence_tactics.

Local Open Scope R_scope.

Section Wallis.
(** printing ~	~ *)
Local Coercion INR : nat >-> R.

Definition sin_n n := fun x => pow (sin x) n.

Lemma integrable_sin_n : forall n, Riemann_integrable (comp (fun x => pow x n) sin) 0 (PI/2).
Proof.
intro n.
apply RiemannInt_P6.
pose proof PI_RGT_0; lra.
intros x Hx; apply continuity_pt_comp.
  apply continuity_sin.
  apply derivable_continuous; apply derivable_pow.
Qed.

Definition W_even n := ((PI/2)*(fact (2 * n))/(2 ^ (2 * n) * (fact n) ^2 )).
Definition W_odd n := ((2^(2*n) * (fact n) ^2)/(fact (S (2 * n)))).

Lemma Wallis_0 : Rint (sin_n 0)  0 (PI/2) (PI/2).
Proof.
apply Rint_eq_compat with (fct_cte 1).
  trivial.
assert(Hrew : (PI/2) = (1*(PI/2 -0))) by ring.
apply Rint_eq with (1 * (PI / 2 - 0)).
 auto with Rint.
 ring.
Qed.

Lemma Wallis_1 : Rint (sin_n 1)  0 (PI/2) 1.
Proof.
unfold sin_n.
apply Rint_eq_compat with sin.
  auto with *.
assert(Heq : 1 = (cos 0 - cos (PI/2))).
  rewrite cos_PI2, cos_0; ring.
apply Rint_eq with (cos 0 - cos (PI / 2)) ; auto with Rint.
Qed.


(** Recurrence formula *)
Lemma Wallis_formula : forall Wn n,
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
  replace (cos x * - cos x) with (-(1 - (sin x)^2)).
  unfold Rsqr; simpl; ring.
  replace ((sin x) ^ 2) with ((sin x)²) by (unfold Rsqr; ring).
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

Lemma Wallis_even : forall n, Rint (sin_n (2 * n)) 0 (PI/2) (W_even n).
Proof.
unfold W_even.
induction n.
  simpl; unfold Rsqr; field_simplify; apply Wallis_0.

apply Rint_eq_compat with (sin_n (S (S (2 *  n)))).
  intros; simpl;
  replace (S (n + S (n + 0))) with (S (S (n + (n + 0)))) by auto;
  reflexivity.

replace (PI / 2 * fact (2 * S n) / (2 ^ (2 * S n) * (fact (S n)) ^2)) with
  ((PI / 2 * fact (2 * n) / (2 ^ (2 * n) * (fact n)^2)) * S (2 * n) / (S (S (2 * n)))).
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
apply pow_nonzero; pose proof Rlt_R0_R2; intro; lra.
Qed.



Lemma Wallis_odd : forall n, Rint (sin_n (S (2 * n))) 0 (PI/2) ((2^(2*n) * (fact n) ^2)/(fact (S (2 * n)))).
Proof.
unfold W_odd.
induction n.
  simpl; replace (1 * (1 * (1*1)) / 1) with 1 by field; apply Wallis_1.
apply Rint_eq_compat with (sin_n (S (S (S (2 * n))))).
  intros; simpl.
replace (n + S (n + 0))%nat with (S (n + (n + 0))) by auto;
reflexivity.
replace (2 ^ (2 * S n) * (fact (S n))^2 / fact (S (2 * S n))) with
  ((2 ^ (2 * n) * (fact n)^2 / fact (S (2 * n))) * (S (S (2 * n)))/(S (S (S (2 * n))))).
apply Wallis_formula; apply IHn.

replace (2 * S n)%nat with (S (S (2 * n))) by auto with *.
repeat rewrite fact_simpl.
repeat rewrite <- tech_pow_Rmult.
unfold Rsqr.
replace (S (S (2*n))) with (2 * (S n))%nat by auto with *.
repeat rewrite mult_INR.
replace (INR 2) with 2 by trivial; field.

repeat split;apply not_0_INR; try (auto with * ).
apply fact_neq_0.
Qed.

Lemma Wallis_odd_le_even : forall n, W_odd n <= W_even n.
Proof.
intro n.
apply (Rint_le_compat (sin_n (S (2 * n))) (sin_n (2 * n)) 0 (PI/2)).
  left; apply PI2_RGT_0.
  
  intros; unfold sin_n.
  replace (sin u ^ (2 * n)) with (1 * sin u ^ (2 * n)) by ring.
  rewrite <- tech_pow_Rmult.
  apply Rmult_le_compat_r.
    apply pow_le.
    apply sin_ge_0; intuition; lra.
    pose proof (SIN_bound u); intuition.

apply Wallis_odd.
apply Wallis_even.
Qed.


Lemma Wallis_even_le_odd : forall n, W_even (S n) <= W_odd n.
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
    apply sin_ge_0; intuition; lra.
    pose proof (SIN_bound u); intuition.

apply Wallis_even.
apply Wallis_odd.
Qed.


Lemma Wallis_maj : forall n : nat, (2*n/ (S (2 * n))) * (W_even n) <= W_odd n.
Proof.
intro n.
destruct n.

  unfold W_even, W_odd, Rsqr.
  simpl; field_simplify; lra.

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
 repeat apply Rmult_lt_0_compat; try lra.
  now apply Rlt_le_trans with (7 / 8); lra || apply pi2_int.
  now apply INR_fact_lt_0.
  repeat rewrite Rinv_mult_distr ; repeat apply Rmult_lt_0_compat.
   rewrite Rinv_pow.
    apply pow_lt ; lra.
    apply Rgt_not_eq ; lra.
   apply Rinv_0_lt_compat, pow_lt, INR_fact_lt_0.
   apply Rgt_not_eq, pow_lt ; lra.
   apply Rgt_not_eq, pow_lt, INR_fact_lt_0.
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
    apply Rseq_little_O_Rmult_compat_r; [|intro H; lra].
    eapply Rseq_little_O_eq_compat
      with (Un := Rseq_poly 0) (Vn := Rseq_poly 1).
      intros n; unfold Rseq_poly; apply pow_O.
      intros n; unfold Rseq_poly; apply pow_1.
      apply Rseq_poly_little_O; constructor.
    intros n; assert (H := pos_INR n); intros Hc; lra.
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
  apply pow_nonzero; intros H; lra.
  replace (4 * n)%nat with (2 * n + 2 * n)%nat by lia.
  rewrite pow_add.
  reflexivity.
Qed.

Lemma Rseq_cv_eq_compat1 : forall Un Vn l,
  {m | forall n, (n >= m)%nat -> Un n = Vn n} ->
    Rseq_cv Un l -> Rseq_cv Vn l.
Proof.
intros Un Vn l Heq Hseq.
intros eps Heps.
destruct Heq as (m, Heq).
destruct (Hseq eps Heps) as (N, Hseq2).
exists (max N m).
intros n Hn. 
assert (Hm : (n >= m)%nat). apply le_trans with (max N m) ; intuition.
unfold R_dist in *.
rewrite <- (Heq n) ; intuition;
try (apply Hseq2; intuition; apply le_trans with (max N m) ; intuition).
Qed.

Lemma sqrt_id : forall n : nat, (INR n <> 0)%R -> sqrt (2 * n) / (2 * n) = /sqrt (2 * n).
Proof.
intros n H1.
rewrite <- (sqrt_sqrt (2 * n)) at 2.
field.
intro H. apply H1. apply Rmult_eq_reg_l with 2. rewrite Rmult_0_r. apply sqrt_eq_0 ; intuition.
apply Rmult_le_pos ; intuition. intro ; lra.
apply Rmult_le_pos ; intuition.
Qed.

Lemma Rseq_equiv_eq : forall Un Vn, 
  {m | forall n, (n >= m)%nat -> Un n = Vn n} -> Un ~ Vn.
Proof.
intros Un Vn Heq eps Heps.
destruct Heq as (N, Heq).
exists N. intros n HN.
unfold Rseq_constant, Rseq_minus, Rseq_plus.
rewrite (Heq n).
ring_simplify (Vn n - Vn n).
rewrite Rabs_R0. apply Rmult_le_pos.
intuition.
apply Rabs_pos.
assumption.
Qed.

Lemma DL_sqrt_1 : forall Un, Rseq_cv Un 0 -> (fun n => sqrt (1 + Un n) - 1) = o(1).
Proof.
intros Un Un0.
intros eps Heps.
destruct (Un0 eps Heps) as (N, HUn).
assert (H01 : 0 < 1) by lra.
destruct (Un0 1 H01) as (N1, HUn1).
exists (max N N1).
intros n HNmax.
unfold Rseq_constant. rewrite Rabs_R1. rewrite Rmult_1_r.
apply Rle_trans with (Rabs (Un n)).
apply sqrt_var_maj.
unfold R_dist in *. left.
assert (HN : (n >= N1)%nat). apply le_trans with (max N N1) ; intuition.
generalize (HUn1 n HN) ; intros HU1.
rewrite Rminus_0_r in HU1. assumption.
left. 
assert (HN : (n >= N)%nat). apply le_trans with (max N N1) ; intuition.
generalize (HUn n HN) ; intros HU1.
unfold R_dist in HU1.
rewrite Rminus_0_r in HU1. assumption.
Qed.

Lemma Rseq_cv_inv_INR : Rseq_cv (fun n => /INR (n + 1)) 0.
Proof.
generalize RinvN_cv. intros useful.
intros eps Heps.
destruct (useful eps Heps) as (N, H).
exists N.
intros n Hn.
generalize (H n Hn). intros H1.
unfold pos in  H1. simpl in H1.
rewrite plus_INR. apply H1.
Qed.

Lemma Rinv_plus : forall a b c : R, c <> 0 -> (a + b) / c = a / c + (b / c).
Proof.
intros a b c d.
field ; apply d.
Qed.

Lemma Rinv_eq_1 : forall a, a <> 0 -> a / a = 1.
Proof.
intros.
field ; assumption.
Qed.

Lemma pow_exp_ln : forall x n, 0 < x -> x ^ n = exp (n * ln x).
Proof.
intros x n H.
induction n. 
 simpl. rewrite Rmult_0_l. rewrite exp_0. reflexivity.
 
 rewrite S_INR. rewrite Rmult_plus_distr_r.
 rewrite <- tech_pow_Rmult. rewrite exp_plus.
 rewrite Rmult_1_l. rewrite exp_ln ; [ | apply H].
 rewrite IHn. ring.
Qed.

Lemma Rseq_equiv_ln : forall Un, Rseq_cv Un 0 -> (fun n => ln (1 + Un n)) ~ Un.
Proof.
intros Un Hu.
destruct (Hu 1) as [M HM]; [lra|].
apply Rseq_equiv_sym.
intros eps Heps.
assert (H1 : 0 < 1) by lra.
destruct (Rpser_little_O_partial_sum _ Un 1 1 H1 Hu ln_plus_cv_radius eps Heps) as [N HN].
exists (Max.max M N); intros n Hn.
unfold Rseq_minus; simpl.
pattern Un at 2; replace (Un n) with (Un n ^ 1) by field.
eapply Rle_trans; [right|apply HN].
  simpl; rewrite ln_plus_taylor_sum.
  rewrite Rabs_minus_sym.
  apply f_equal; field.
  replace (Un n) with (Un n - 0) by field; apply HM.
  eapply le_trans; [apply Max.le_max_l|eassumption].
eapply le_trans; [apply Max.le_max_r|eassumption].
Qed.

Lemma Rseq_cv_inv_INR_0_1 : Rseq_cv (fun n => - / (2 * INR n + 1))%R 0%R.
Proof.
replace 0 with (-0)%R by intuition. apply Rseq_cv_opp_compat.
generalize RinvN_cv. intros useful.
intros eps Heps;
destruct (Rseq_cv_inv_INR eps Heps) as (N, Hun).
exists N. intros n Hn.
generalize (Hun n Hn) ; intros Hun1.
apply Rle_lt_trans with (/INR (n + 1))%R.
 unfold R_dist. rewrite Rminus_0_r. rewrite Rabs_pos_eq.
  apply Rle_Rinv.
   generalize (pos_INR n) ; intros ; rewrite plus_INR ; intuition.
   generalize (pos_INR n) ; intros ; lra.
   rewrite plus_INR. simpl. apply Rplus_le_compat_r. replace (INR n)%R with ((INR n ) * 1)%R by ring. rewrite Rmult_comm. apply Rmult_le_compat.
    intuition.
    apply pos_INR.
    intuition.
    intuition.
 left. apply Rinv_0_lt_compat. generalize (pos_INR n) ; intros ; lra.
unfold R_dist in Hun1. rewrite Rminus_0_r in Hun1. rewrite Rabs_right in Hun1. apply Hun1.
left. apply Rgt_lt. apply Rinv_0_lt_compat. intuition.
Qed.

Lemma Rseq_equiv_continuity : forall Un Vn l f, continuity_pt f l -> 
  f l <> 0 -> Rseq_cv Un l -> Rseq_cv Vn l ->
    (fun n : nat => f (Un n)) ~ (fun n : nat => f (Vn n)).
Proof.
intros Un Vn l f Hcont H0 Hun Hvn.
apply Rseq_equiv_trans with (f l).
 apply Rseq_cv_equiv_constant.
  assumption.
  apply Rseq_cv_continuity_compat ; [assumption | reg].

 apply Rseq_equiv_sym. 
 apply Rseq_cv_equiv_constant.
  assumption.
  apply Rseq_cv_continuity_compat ; [assumption | reg].
Qed.

Lemma Wallis_quotient_lim2 : forall l, 
l <> 0 ->
  (fun n => fact n) ~ (fun n => (n /(exp 1)) ^ n * sqrt n * l) ->
    Rseq_cv (fun n => W_odd n / W_even n) (l^2/(2*PI)).
Proof.
intros l Hneq Hl.
apply Rseq_cv_eq_compat with (fun n => (2*2 ^ (4*n) * (fact n) ^ 4)/(PI*fact (2 * n) * fact (S (2 * n)))).
  intro; rewrite Wallis_quotient; reflexivity.
assert (H2n : (fun n => fact (2 * n)) ~ (fun n => (2 * n / exp 1) ^ (2 * n) * sqrt (2 * n) * l)).
  assert (Hex : is_extractor (mult 2)).
    intros n; lia.
  pose (exist _ _ Hex) as db.
  assert (Hrw1 : extracted db fact == (fun n => fact (2 * n))).
    intros n; reflexivity.
  assert (Hrw2 : extracted db (fun n => (n / exp 1) ^ n * sqrt n * l) == (fun n => (2 * n / exp 1) ^ (2 * n) * sqrt (2 * n) * l)).
    intros n; unfold extracted. simpl.
    repeat rewrite plus_INR; simpl.
    replace (n + (n + 0)) with (2 * n) by field.
    reflexivity.
  eapply Rseq_equiv_eq_compat; [eassumption|eassumption|].
  apply Rseq_equiv_subseq_compat with (Un := fact) (Vn := fun k : nat => (k / exp 1) ^ k * sqrt k * l) (phi := db).
  assumption.
assert (H2n1 : (fun n : nat => fact (S(2*n))) ~ (fun n : nat => (S(2*n) / exp 1) ^ (S(2*n)) * sqrt (S(2*n)) * l)).
  assert (Hex : is_extractor (fun n => S (mult 2 n))).
    intros n; lia.
  pose (exist _ _ Hex) as db.
  apply Rseq_equiv_eq_compat with (extracted db fact) (extracted db (fun n : nat => (n / exp 1) ^ n * sqrt n * l)).
    intro n; unfold db; reflexivity.
    intro n; unfold db; reflexivity.
  apply Rseq_equiv_subseq_compat with (Un := fact) (Vn := fun k : nat => (k / exp 1) ^ k * sqrt k * l)(phi := db).
  assumption.
  
apply Rseq_equiv_cv_constant.
Local Open Scope Rseq_scope.
apply Rseq_equiv_eq_compat with 
  (Un := 2 * (fun n => 2 ^ (4 * n)) * fact * fact * fact * fact *
  / (PI * (fun n => fact (2 * n)) * (fun n => fact (S (2 * n))))) (Vn := (l^2 / (2 * PI))%R).
intro n; unfold Rseq_mult, Rseq_inv, Rdiv, Rseq_constant; ring.
intro; reflexivity.
apply Rseq_equiv_trans with 
(2 * (fun n => 2 ^ (4 * n)) * ((fun n : nat => ((n / exp 1) ^ n * sqrt n * l)%R))*((fun n : nat => ((n / exp 1) ^ n * sqrt n * l)%R))*((fun n : nat => ((n / exp 1) ^ n * sqrt n * l)%R))*((fun n : nat => ((n / exp 1) ^ n * sqrt n * l)%R))*
  / (PI * (fun n : nat => ((2 * n / exp 1) ^ (2 * n) * sqrt (2 * n) * l)%R) *  (fun n => (S (2 * n) / exp 1) ^ S (2 * n) * sqrt (S (2 * n)) * l)%R)).

repeat apply Rseq_equiv_mult_compat;
  try apply Rseq_equiv_refl; try assumption.
apply Rseq_equiv_inv_compat.
exists O. intros n Hn.
unfold Rseq_mult, Rseq_constant.
apply Rmult_integral_contrapositive ; split ; 
[ apply Rmult_integral_contrapositive ; split ; 
[ apply PI_neq0 | apply INR_fact_neq_0] | apply INR_fact_neq_0 ].

exists (S O). intros n Hn; unfold Rseq_mult, Rseq_constant.

assert(H : {m | n = S m}). exists (pred n). intuition.
destruct H as (m, Subst).
rewrite Subst.

apply Rmult_integral_contrapositive ; split ; 
[ apply Rmult_integral_contrapositive ; split ; 
[ apply PI_neq0 | apply Rmult_integral_contrapositive ; split ; 
[ apply Rmult_integral_contrapositive ; split ; 
[ (apply pow_nonzero ; unfold Rdiv ; apply Rmult_integral_contrapositive ; split ;
[ apply Rmult_integral_contrapositive ; split ; 
[ (intro ; lra) | (apply not_0_INR ; intuition) ] | (apply Rinv_neq_0_compat ; generalize (exp_pos 1) ; intros ; intro ; lra)])
| (intro H ; apply sqrt_eq_0 in H ; [ (apply Rmult_integral in H ; destruct H as [H|H] ; [ lra | (generalize H ; apply not_0_INR ; intuition) ])
| apply Rmult_le_pos ; intuition ]) ]
| apply Hneq ] ] | apply Rmult_integral_contrapositive ; split ; 
[ apply Rmult_integral_contrapositive ; split ;
[ (apply pow_nonzero ; unfold Rdiv ; apply Rmult_integral_contrapositive ; split ;
[ apply not_0_INR ; intuition | (apply Rinv_neq_0_compat ; generalize (exp_pos 1) ; intros ; intro ; lra) ])
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
unfold Rdiv. 
apply Rmult_integral_contrapositive ; split .
 apply pow_nonzero; assumption.
 apply Rinv_neq_0_compat.
 apply Rmult_integral_contrapositive; split.
  intro ; lra.
  apply PI_neq0.
unfold Rseq_constant, Rseq_mult, Rseq_div, Rseq_plus, Rseq_minus, Rseq_inv.
(* Simplification of the expression ! *)
apply Rseq_cv_eq_compat1 with 
(fun n:nat => (sqrt (2 * n) / sqrt (S (2 * n))) * (Rsqr l / PI * exp 1) * ((2 * n) / S (2 * n)) ^ (S (2 * n)) * /2)%R.
exists (S O). intros n Hn.
(* need to have n <> 0 *)
assert(H : {m | n = S m}). exists (pred n). intuition.
destruct H as (m, Subst).
(* Solving the simplification equation *)
unfold Rseq_constant.
unfold Rdiv.
ring_simplify.
replace (sqrt n ^ 4) with (n ^ 2) by (rewrite <- (sqrt_sqrt n) at 1 ; [ring | intuition]).
repeat rewrite Rpow_mult_distr.
repeat rewrite <- pow_mult.
repeat rewrite Rinv_mult_distr.
replace (2 ^ (4 * n))%R with (2 ^ (2 * n) * 2 ^ (2 * n))%R by (repeat rewrite pow_mult ; 
rewrite <- Rpow_mult_distr ; replace (2 ^ 2 * 2 ^ 2)%R with (2 ^ 4)%R by (unfold pow ; ring) ; ring).
rewrite (mult_comm n 4).
replace (n ^ (4 * n))%R with (n ^ (2 * n) * n ^ (2 * n))%R by 
(rewrite <- pow_add ; ring_simplify (2 * n + 2 * n)%nat ; ring).
replace ((/exp 1) ^ (4 * n))%R with ((/exp 1) ^ (2 * n) * (/exp 1) ^ (2 * n))%R by 
(rewrite <- pow_add ; ring_simplify (2 * n + 2 * n)%nat ; ring).
repeat rewrite Rinv_pow. rewrite Rinv_involutive.
rewrite <- tech_pow_Rmult with (exp 1) (2 * n)%nat.
rewrite <- (Rinv_pow (exp 1) _).
do 2 rewrite <- tech_pow_Rmult.
replace (/sqrt (2 * n))%R with (sqrt (2 * n) / (2 * n))%R by (apply sqrt_id ; inversion Hn ; [intuition | apply not_0_INR ; intuition]).
unfold Rsqr. unfold Rdiv.
repeat rewrite <- Rinv_pow. field.

(* Solving the "<> 0" equations *)

split. assumption.
split. intro H. apply sqrt_eq_0 in H. apply not_0_INR in H. assumption.
intuition.
intuition.
split. apply pow_nonzero. apply not_0_INR. intuition.
split. apply not_0_INR. intuition.
split. apply pow_nonzero. apply not_0_INR. intuition.
split. apply pow_nonzero. intro. lra.
split. apply PI_neq0.
apply pow_nonzero. intro. generalize (exp_pos 1) ; intros ; lra.
apply not_0_INR. intuition.
intro ; lra. 
apply not_0_INR. intuition. 
intro. generalize (exp_pos 1) ; intros ; lra.
intro. generalize (exp_pos 1) ; intros ; lra.
apply Rinv_neq_0_compat. intro. generalize (exp_pos 1) ; intros ; lra.
apply not_0_INR ; intuition.
apply Rinv_neq_0_compat. intro. generalize (exp_pos 1) ; intros ; lra.
apply not_0_INR ; intuition.
intro ; lra.
apply pow_nonzero. apply not_0_INR ; intuition.
apply pow_nonzero. apply Rinv_neq_0_compat. intro. generalize (exp_pos 1) ; intros ; lra.
apply Rmult_integral_contrapositive ; split.
apply pow_nonzero. apply not_0_INR ; intuition.
apply pow_nonzero. apply Rinv_neq_0_compat. intro. generalize (exp_pos 1) ; intros ; lra.
intro H. apply sqrt_eq_0 in H. generalize H. apply not_0_INR ; intuition.
apply pos_INR.
apply Rmult_integral_contrapositive ; split.
apply Rmult_integral_contrapositive ; split.
apply pow_nonzero. apply not_0_INR ; intuition.
apply pow_nonzero. apply Rinv_neq_0_compat. intro. generalize (exp_pos 1) ; intros ; lra.
intro H. apply sqrt_eq_0 in H. generalize H. apply not_0_INR ; intuition.
apply pos_INR.
apply Hneq.
apply pow_nonzero. intro ; lra.
apply pow_nonzero. apply not_0_INR ; intuition.
apply Rmult_integral_contrapositive ; split.
apply pow_nonzero. intro ; lra.
apply pow_nonzero. apply not_0_INR ; intuition.
apply pow_nonzero. apply Rinv_neq_0_compat. intro. generalize (exp_pos 1) ; intros ; lra.
apply Rmult_integral_contrapositive ; split.
apply Rmult_integral_contrapositive ; split.
apply pow_nonzero. intro ; lra.
apply pow_nonzero. apply not_0_INR ; intuition.
apply pow_nonzero. apply Rinv_neq_0_compat. intro. generalize (exp_pos 1) ; intros ; lra.
intro H. apply sqrt_eq_0 in H. generalize H. apply Rmult_integral_contrapositive ; split.
intro ; lra.
apply not_0_INR. intuition.
apply Rmult_le_pos. intuition.
intuition.
apply Rmult_integral_contrapositive ; split.
apply Rmult_integral_contrapositive ; split.
apply Rmult_integral_contrapositive ; split.
apply pow_nonzero. intro ; lra.
apply pow_nonzero. apply not_0_INR ; intuition.
apply pow_nonzero. apply Rinv_neq_0_compat. intro. generalize (exp_pos 1) ; intros ; lra.
intro H. apply sqrt_eq_0 in H. generalize H. apply Rmult_integral_contrapositive ; split.
intro ; lra.
apply not_0_INR. intuition.
apply Rmult_le_pos. intuition. intuition.
assumption.
apply PI_neq0.
apply Rmult_integral_contrapositive ; split.
apply Rmult_integral_contrapositive ; split.
apply Rmult_integral_contrapositive ; split.
apply Rmult_integral_contrapositive ; split.
apply pow_nonzero. intro ; lra.
apply pow_nonzero. apply not_0_INR ; intuition.
apply pow_nonzero. apply Rinv_neq_0_compat. intro. generalize (exp_pos 1) ; intros ; lra.
intro H. apply sqrt_eq_0 in H. generalize H. apply Rmult_integral_contrapositive ; split.
intro ; lra.
apply not_0_INR. intuition.
apply Rmult_le_pos. intuition. intuition.
assumption.
apply Rmult_integral_contrapositive ; split.
apply PI_neq0.
apply Rmult_integral_contrapositive ; split.
apply Rmult_integral_contrapositive ; split.
apply Rmult_integral_contrapositive ; split.
apply Rmult_integral_contrapositive ; split.
apply pow_nonzero. intro ; lra.
apply pow_nonzero. apply not_0_INR ; intuition.
apply pow_nonzero. apply Rinv_neq_0_compat. intro. generalize (exp_pos 1) ; intros ; lra.
intro H. apply sqrt_eq_0 in H. generalize H. apply Rmult_integral_contrapositive ; split.
intro ; lra.
apply not_0_INR. intuition.
apply Rmult_le_pos. intuition. intuition.
assumption.
apply Rmult_integral_contrapositive ; split.
apply Rmult_integral_contrapositive ; split.
apply Rmult_integral_contrapositive ; split.
apply pow_nonzero. apply not_0_INR ; intuition.
apply pow_nonzero. apply Rinv_neq_0_compat. intro. generalize (exp_pos 1) ; intros ; lra.
intro H. apply sqrt_eq_0 in H. generalize H. apply not_0_INR. intuition.
apply pos_INR. assumption.
(* End of "<> 0" *)

(* end of simplification *)

eapply Rseq_equiv_cv_compat.
  2: reflexivity.
 symmetry; instantiate (1 := (1 * (Rsqr l / PI * exp 1) * /exp 1 * /2)).
 apply Rseq_equiv_mult_compat ; [ | apply Rseq_equiv_eq ; exists O ; intro ; intuition ].
 apply Rseq_equiv_mult_compat.
  apply Rseq_equiv_mult_compat ; [ | apply Rseq_equiv_eq ; exists O ; intro ; intuition ].
  pose (Un := (fun n => - / (2 * INR n + 1))%R).
  assert (Hcv0 : Rseq_cv Un 0). unfold Un.
   apply Rseq_cv_inv_INR_0_1.
  intros eps Heps.
  destruct (DL_sqrt_1 Un Hcv0 eps Heps) as (N, DL).
  exists N.
  intros n HN. generalize (DL n HN). intros DL1.
  unfold Rseq_constant, Rseq_plus, Rseq_minus, Rseq_mult, Rseq_inv, Un in *.
  rewrite <-sqrt_div ; [ | (apply Rmult_le_pos ; intuition) | intuition ].
  rewrite S_INR. rewrite mult_INR. do 2 rewrite S_INR.
  replace (2 * n)%R with ((2 * n + 1) - 1)%R by ring. rewrite Rplus_0_l.
  unfold Rminus. rewrite Rinv_plus.
   rewrite Rinv_eq_1. unfold Rdiv in *. rewrite Ropp_mult_distr_l_reverse. rewrite Rmult_1_l. rewrite Rabs_minus_sym in DL1. apply DL1.
    generalize (pos_INR n) ; intuition ; lra.
    generalize (pos_INR n) ; intuition ; lra.
 apply Rseq_equiv_trans with (fun n : nat => exp ((2 * n + 1) * ln (1 - /(2 * INR n + 1)))).
 pose (Un := (fun n:nat => - /(2 * (INR n) + 1))%R).
 assert (Hcv0 : Rseq_cv Un 0).
  apply Rseq_cv_inv_INR_0_1.
 apply Rseq_equiv_trans with (fun n : nat => exp ((2 * n + 1) * (- / (2 * n + 1)))).
  apply Rseq_equiv_eq. exists O. intros n Hn.
  field_simplify ((2 * n + 1) * - / (2 * n + 1))%R. unfold Rseq_constant, Rseq_inv.
   rewrite <- exp_Ropp. unfold Rdiv. try rewrite Rinv_1. try rewrite Rmult_1_r. reflexivity.
   generalize (pos_INR n) ; intuition ; lra.
  apply Rseq_equiv_continuity with ((-1)).
   reg.
   generalize (exp_pos (-1)) ; intros l1 H1 ; lra.
   apply Rseq_cv_eq_compat with (-R1).
   intros n. unfold Rseq_constant, Rseq_minus, Rseq_plus, Rseq_opp.
   field. intros H1 ; generalize (pos_INR n) ; intros ; lra.
   change (-1)%R with (-(1%R))%R. intuition.
   eapply Rseq_equiv_cv_compat.
     2: reflexivity.
    symmetry; instantiate (1 := (fun n => (2 * INR n + 1) * - / (2 * INR n + 1))%R).
    apply Rseq_equiv_mult_compat.
     apply Rseq_equiv_refl.
     apply Rseq_equiv_sym. apply Rseq_equiv_ln.
     apply Hcv0.
    apply Rseq_cv_eq_compat with (-R1).
    unfold Rseq_opp, Rseq_constant, Rseq_minus.
    intros n. field. generalize (pos_INR n) ; intuition ; lra.
    change (-1)%R with (-(1%R))%R. intuition.
 apply Rseq_equiv_eq.
 exists 1%nat.
 intros n Hn.
 rewrite pow_exp_ln.
  replace (2 * n)%R with ((2 * n + 1) - 1)%R by ring.
  rewrite S_INR. rewrite mult_INR. repeat rewrite S_INR.
  rewrite Rplus_0_l.
  unfold Rminus. rewrite Rinv_plus. rewrite Rinv_eq_1.
   ring_simplify (2 * n + 1 + -(1) + 1)%R. unfold Rdiv. ring_simplify (1 + -(1) * / ((1 + 1) * n + 1))%R.
   rewrite (Rplus_comm (- / (2 * n + 1)) _). reflexivity.
   generalize (pos_INR n) ; intuition ; lra.
   generalize (pos_INR n) ; intuition ; lra.
   unfold Rdiv. apply Rmult_lt_0_compat. apply Rmult_lt_0_compat ; intuition.
   apply Rinv_0_lt_compat.
   rewrite S_INR. generalize (pos_INR n) ; intuition ; lra.
apply Rseq_cv_eq_compat with (Rsqr l / (2 * PI)).
intro. unfold Rseq_mult, Rseq_plus, Rseq_constant, Rseq_div, Rseq_inv.
field. split. 
apply PI_neq0.
intro. generalize (exp_pos 1) ; intros ; lra.
intros eps Heps. exists O. intros n Hn.
unfold R_dist. unfold Rseq_constant, Rseq_div, Rseq_inv, Rseq_mult.
unfold Rdiv, Rsqr. rewrite Rminus_diag_eq.
rewrite Rabs_R0. apply Heps.
ring.
Qed.

End Wallis.
