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


(** Proof of Stirling equivalence of factorial. *)

Require Import Reals.
Require Import Rsequence_facts.
Require Import Rseries_def.
Require Import Rseries_facts.
Require Import Rseries_usual.
Require Import Rpser.
Require Import Rintegral.
Require Import RTaylor.
Require Import Lia.
Require Import Lra.
Require Import Wallis.
Open Scope R_scope.

(** printing ~	~ *)
(** Partial result : De Moivre approximation. *)

Section De_Moivre.
(* begin hide *)

Let Un n := (INR n) ^ n * exp (- (INR n)) * sqrt (INR n) / Rseq_fact n.

Let Vn n :=
match n with
| 0 => 0
| _ => ln (Un (S n) / Un n)
end.

Hint Resolve lt_0_INR : stirling.
Hint Resolve sqrt_lt_R0 : stirling.
Hint Resolve exp_pos : stirling.
Hint Resolve lt_O_fact : stirling.
Hint Resolve pow_lt : stirling.
Hint Resolve Rmult_lt_0_compat : stirling.
Hint Resolve Rinv_0_lt_compat : stirling.
Hint Resolve Rgt_not_eq : stirling.

Lemma Vn_O : Vn 0 = 0.
Proof.
unfold Vn; simpl; auto.
Qed.

Lemma Vn_S : forall n, (0 < n)%nat -> Vn n = ln (Un (S n) / Un n).
Proof.
intros n Hn.
unfold Vn.
destruct n; [apply False_ind; lia|].
reflexivity.
Qed.

Lemma ln_pow : forall r n, 0 < r -> ln (r ^ n) = INR n * ln r.
Proof.
intros r n Hr; induction n.
simpl; rewrite ln_1; rewrite Rmult_0_l; auto.
replace (r ^ S n) with (r * r ^ n) by reflexivity.
rewrite ln_mult.
rewrite S_INR; rewrite IHn; field.
assumption.
apply pow_lt; assumption.
Qed.

Lemma ln_sqrt : forall r, 0 < r -> ln (sqrt r) = ln r / 2.
Proof.
intros r Hr.
assert (H : 2 <> 0).
  intros Hc; lra.
unfold Rdiv; rewrite Rmult_comm.
apply (Rmult_eq_reg_l 2); [|assumption].
rewrite <- Rmult_assoc.
rewrite Rinv_r; [|assumption].
rewrite Rmult_1_l.
replace 2 with (INR 2) by reflexivity.
rewrite <- ln_pow.
replace (sqrt r ^ 2) with (sqrt r * sqrt r) by field.
rewrite sqrt_def; [reflexivity|lra].
apply sqrt_lt_R0; assumption.
Qed.

Lemma Un_pos : forall n, (0 < n)%nat -> 0 < Un n.
Proof.
intros n Hn; unfold Un.
unfold Rseq_fact.
repeat apply Rmult_lt_0_compat; auto with stirling.
Qed.

Lemma Vn_simpl :
  forall n, (0 < n)%nat -> Vn n = (INR n + / 2) * ln (1 + / INR n) - 1.
Proof.
intros n Hn.
rewrite Vn_S; [|assumption]; unfold Un, Rseq_fact, Rdiv.
assert (Hnpos : 0 < INR n).
  apply lt_0_INR; assumption.
assert (HSnpos : 0 < INR (S n)).
  apply lt_0_INR; constructor; assumption.
replace (1 + / INR n) with ((INR n + 1) * / INR n) by (field; auto with stirling).
rewrite fact_simpl.
repeat rewrite mult_INR.
repeat (rewrite ln_mult || rewrite ln_Rinv); auto 6 with stirling.
repeat rewrite ln_exp; auto with stirling.
repeat rewrite ln_pow; auto with stirling.
repeat rewrite ln_sqrt; auto with stirling.
repeat rewrite S_INR.
field.
lra.
Qed.

Let Tn n :=
match n with
| 0 => 0 
| _ => (- 1) ^ (S n) / (INR n)
end.

Let Rn n := (/ INR n + - / 2 * (/ INR n) ^ 2 + / 3 * (/ INR n) ^ 3).

Let Sn n := ln (1 + / INR n) - Rn n.

Let Qn d n := Rseq_inv_poly d n.

Lemma Qn_S : forall d n, (0 < n)%nat -> Qn d n = (/ INR n) ^ d.
Proof.
intros d n H; unfold Qn.
destruct n; [apply False_ind; lia|reflexivity].
Qed.
Lemma ln_taylor_3 : Sn = O(Qn 4).
Proof.
unfold Sn, Rn in *.
eapply Rseq_big_O_asymptotic.
  intros; eassumption.
exists 2%nat.
eapply Rseq_big_O_eq_compat.
  3: eapply Rpser_big_O_partial_sum with
    (Un := Tn) (pr := ln_plus_cv_radius)
    (En := fun n => / INR (2 + n)) (N := 3%nat).
  intros n ; unfold Rseq_shifts.
  rewrite <- ln_plus_taylor_sum.
  unfold Tn; apply Rplus_eq_compat_l.
  unfold Rseq_pps. unfold Rseq_sum. unfold gt_pser. unfold Rseq_mult.
  simpl; destruct n; simpl; field.
  destruct n; intros Hc.
    lra.
    assert (H := pos_INR (S n)); lra.
    rewrite Rabs_Rinv.
    rewrite <- Rinv_1.
    apply Rinv_1_lt_contravar; [apply Rle_refl|].
    rewrite Rabs_right; [|apply Rle_ge; apply pos_INR].
    replace (2 + n)%nat with (S (S n)) by lia.
    repeat rewrite S_INR.
    assert (H := pos_INR n); lra.
    replace (2 + n)%nat with (S (S n)) by lia.
    repeat rewrite S_INR.
    intros Hc; assert (H := pos_INR n); lra.
  apply Rseq_eq_refl.
  lra.
  apply Rseq_cv_pos_infty_inv_compat.
  apply Rseq_cv_pos_infty_eq_compat with (Un := fun n => 2 + Rseq_poly 1 n).
    intros n; replace (2 + n)%nat with (S (S n)) by lia.
    do 2 rewrite S_INR; unfold Rseq_poly; ring.
  eapply Rseq_cv_finite_plus_pos_infty_r.
    apply Rseq_constant_cv.
    apply Rseq_poly_cv; auto.
Qed.

Lemma Vn_maj : Vn = O(Qn 2).
Proof.
eapply Rseq_big_O_asymptotic.
  intros; eassumption.
exists 1%nat.
eapply Rseq_big_O_eq_compat
  with (Un := fun n => (INR (1 + n) + / 2) * Sn (1 + n) + / 12 * Qn 2 (1 + n) + / 6 * Qn 3 (1 + n)).
intros n ; unfold Rseq_shifts.
set (p := (1 + n)%nat).
assert (Hp : INR p <> 0).
  unfold p.
  replace (1 + n)%nat with (S n) by auto.
  auto with real.
rewrite Vn_simpl; [|unfold p; lia].
replace (ln (1 + / INR p)) with (Sn p + Rn p).
repeat (rewrite Qn_S; [|unfold p; lia]).
unfold Rn.
field; assumption.
unfold Sn, Rn; field; assumption.
apply Rseq_eq_refl.
repeat apply Rseq_big_O_plus_compat_l.
  eapply Rseq_big_O_eq_compat with (Vn := fun n => INR (1 + n) * Qn 3 (1 + n)) (Un := fun n => (INR (1 + n) + / 2) * Sn (1 + n)).
    reflexivity.
    intros n; unfold Rseq_shifts ; repeat (rewrite Qn_S; [|lia]).
    rewrite <- tech_pow_Rmult.
    field; replace (1 + n)%nat with (S n) by auto; auto with real.
  apply Rseq_big_O_mult_compat.
  exists 2; split; [lra|].
  exists 0%nat; intros n Hn.
  assert (Hle : 1 <= INR (1 + n)).
    replace (1 + n)%nat with (S n) by auto.
    rewrite S_INR.
    assert (H := pos_INR n); lra.
  rewrite Rabs_right; [|lra].
  rewrite Rabs_right; [|lra].
  lra.
  destruct ln_taylor_3 as [K [HK [N HN]]].
  exists K; split; [assumption|].
  exists (S N); intros n Hn.
  eapply Rle_trans.
  apply HN; lia.
  apply Rmult_le_compat_l; [lra|].
  assert (Hle : 1 <= INR (1 + n)).
    replace (1 + n)%nat with (S n) by auto.
    rewrite S_INR.
    assert (H := pos_INR n); lra.
  assert (Qn 4 (1 + n) = Qn 1 (1 + n) * Qn 3 (1 + n)) as ->; swap 1 2.
  rewrite Rabs_mult.
  rewrite <- Rmult_1_l.
  apply Rmult_le_compat_r; [apply Rabs_pos|].
  rewrite Qn_S; [|lia]; rewrite pow_1.
  rewrite Rabs_right; [|left; apply Rinv_0_lt_compat; lra].
  apply (Rmult_le_reg_l (INR (1 + n))); [lra|].
  rewrite Rinv_r; [|intros Hc; lra].
  rewrite Rmult_1_r; assumption.
  repeat (rewrite Qn_S; [|lia]).
  repeat rewrite <- tech_pow_Rmult.
  field; intros Hc; lra.
  apply Rseq_big_O_Rmult_compat_l; apply Rseq_big_O_refl.
  apply Rseq_big_O_Rmult_compat_l.
  exists 1; split; [lra|].
  exists 0%nat; intros n _ ; unfold Rseq_shifts.
  rewrite Rmult_1_l.
  assert (HINR : 0 < INR (1 + n)).
    replace (1 + n)%nat with (S n) by lia.
    rewrite S_INR; assert (H := pos_INR n); lra.
  repeat (rewrite Qn_S; [|lia]).
  rewrite Rabs_right; [|apply Rle_ge; apply pow_le; auto with real].
  rewrite Rabs_right; [|apply Rle_ge; apply pow_le; auto with real].
  repeat rewrite <- tech_pow_Rmult; rewrite pow_O.
  repeat apply Rmult_le_compat_l; auto with real.
  rewrite Rmult_1_r.
  apply (Rmult_le_reg_l (INR (1 + n))); auto.
  rewrite Rinv_r; [|auto with stirling].
  rewrite Rmult_1_r.
  replace (1 + n)%nat with (S n) by auto.
  rewrite S_INR.
  assert (H := pos_INR n); lra.
Qed.

Lemma Rser_cv_Riemann : {l | Rser_abs_cv (Qn 2) l}.
Proof.
apply Rser_cv_inv_poly; lia.
Qed.

Lemma Rser_cv_Vn : {l | Rser_cv Vn l}.
Proof.
apply Rser_abs_cv_cv.
eapply Rser_big_O_cv; [apply Vn_maj|].
apply Rser_cv_Riemann.
Qed.


Lemma Vn_ser_eq : forall n, sum_f_R0 Vn n = ln (Un (S n)) - ln (Un 1).
Proof.
intros n.
induction n.
  unfold Vn; simpl; ring.
  simpl sum_f_R0; rewrite IHn.
  unfold Rdiv; rewrite ln_mult.
  rewrite ln_Rinv; [ring|].
  apply Un_pos; lia.
  apply Un_pos; lia.
  apply Rinv_0_lt_compat; apply Un_pos; lia.
Qed.

Lemma Un_cv : {l | Rseq_cv Un l & 0 < l}.
Proof.
assert (Hcv : {l | Rseq_cv (fun n => ln (Un n)) l}).
  destruct Rser_cv_Vn as [l Hl].
  exists (l + ln (Un 1)).
  eapply Rseq_cv_asymptotic.
    intros Xn HX; pattern Xn; apply HX.
  exists 1%nat; intros eps Heps.
  destruct (Hl eps Heps) as [N HN].
  exists N; intros n Hn.
  unfold R_dist, Rseq_shifts.
  replace (1 + n)%nat with (S n) by lia.
  replace (ln (Un (S n)) - (l + (ln (Un 1))))
    with (ln (Un (S n)) - ln (Un 1) - l) by ring.
  rewrite <- Vn_ser_eq.
  apply HN; assumption.
destruct Hcv as [l Hl].
exists (exp l).
eapply Rseq_cv_asymptotic.
  intros Xn HX; pattern Xn; apply HX.
exists 1%nat.
eapply Rseq_cv_eq_compat with (fun n => exp (ln (Un (S n)))).
  intros n; rewrite exp_ln.
  replace (S n) with (1 + n)%nat by lia; reflexivity.
  apply Un_pos; lia.
apply Rseq_cv_continuity_compat.
intros eps Heps.
destruct (Hl eps Heps) as [N HN].
exists N; intros n Hn.
apply HN; lia.
apply derivable_continuous_pt.
apply derivable_exp.
apply exp_pos.
Qed.

(* end hide *)

Lemma De_Moivre_equiv : {C | Rseq_fact ~ (fun n => C * (INR n) ^ n * exp (- (INR n)) * sqrt (INR n)) & 0 < C}.
Proof.
destruct Un_cv as [l Hl Hp].
exists (/ l).
apply Rseq_equiv_sym.
apply Rseq_equiv_1.
intros n; apply not_0_INR.
apply fact_neq_0.
apply Rseq_equiv_sym.
intros eps Heps.
destruct (Hl (eps * / 2 * l)) as [N HN].
  apply Rmult_lt_0_compat; [lra|assumption].
exists N; intros n Hn.
unfold Rseq_constant, Rseq_minus, Rseq_div.
rewrite (Rabs_right 1); [|lra].
rewrite Rmult_1_r.
rewrite Rabs_minus_sym.
apply Rle_trans with (eps / 2); [left|lra].
apply (Rmult_lt_reg_l l); [assumption|].
pattern l at 1; rewrite <- Rabs_right; [|lra].
rewrite <- Rabs_mult.
rewrite (Rmult_comm l (eps / 2)).
replace (l * (/ l * INR n ^ n * exp (- INR n) * sqrt (INR n) / Rseq_fact n - 1))
  with (INR n ^ n * exp (- INR n) * sqrt (INR n) / Rseq_fact n - l).
apply HN; assumption.
field; split.
  intro; lra.
  apply not_0_INR; apply fact_neq_0.
apply Rinv_0_lt_compat; assumption.
Qed.

End De_Moivre.
(* begin hide *)

Lemma exp_pow x n : (exp x) ^ n = exp (x* (INR n)).
Proof.
induction n.
 ring_simplify.
 rewrite Rmult_0_r, exp_0; reflexivity.

 simpl pow.
 replace (S n)%R with (n+1)%nat by lia.
 rewrite plus_INR.
 replace (INR 1) with R1 by trivial.
 ring_simplify (x * (INR n + R1)).
 rewrite exp_plus, IHn.
 auto with *.
Qed.
(* end hide *)

(** Final result : Stirling approximation. *)

Section Stirling.

Local Coercion INR : nat >-> R.

Lemma Stirling_equiv : Rseq_fact ~ (fun n => sqrt (2 * PI) * (INR n) ^ n * exp (- (INR n)) * sqrt (INR n)).
Proof.
destruct De_Moivre_equiv as [l Hl].
assert(l^2/(2*PI) = 1) as Heq.
 eapply Rseq_cv_unique.
 apply Wallis_quotient_lim2.
  auto with *.
  assert (Hrw : (fun n => l * n ^ n * exp (-n) * sqrt n) == (fun n => ((n / exp R1) ^ n * sqrt n * l))).
   intro n.
   rewrite exp_Ropp.
   replace (exp n) with (exp (R1*n)) by auto with *.
   rewrite <- (exp_pow R1 n).
   unfold Rdiv; rewrite Rpow_mult_distr, Rinv_pow.
    field.
    assert (H := exp_pos 1); auto with *.
  eapply Rseq_equiv_eq_compat.
   apply Rseq_eq_refl.
   apply Hrw.

   trivial.

 apply Wallis_quotient_lim1.

replace l with (sqrt(2*PI)) in Hl.
apply Hl.

assert(HPI := PI_RGT_0).
apply sqrt_lem_1.
lra.
auto with *.
replace (l*l) with ((l^2 / (2*PI))* (2*PI)).
rewrite Heq; ring.
unfold Rdiv, Rsqr; field; auto with *.
Qed.

End Stirling.
