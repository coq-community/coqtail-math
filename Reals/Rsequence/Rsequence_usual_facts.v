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

Require Import Lia.
Require Import Reals.
Require Import Rsequence_def.
Require Import Rsequence_base_facts.
Require Import Rsequence_cv_facts.
Require Import Rsequence_rel_facts.
Require Import Rsequence_rewrite_facts.
Require Import MyRIneq MyReals Lra.
(** printing ~	~ *)
(** * Convergence of usual sequences. *)

(* Convergence of INR *)

Lemma Rseq_cv_pos_infty_INR : Rseq_cv_pos_infty INR.
Proof.
intros M ; pose (n := up (Rabs M)) ; assert (n_pos : (0 <= n)%Z).
 apply le_0_IZR ; transitivity (Rabs M).
  apply Rabs_pos.
  left ; destruct (archimed (Rabs M)) ; assumption.
 destruct (IZN _ n_pos) as [N HN] ; exists N.
 intros m m_lb ; apply Rlt_le_trans with (INR N).
 apply Rle_lt_trans with (Rabs M) ; [apply Rle_abs |].
 rewrite INR_IZR_INZ, <- HN ; destruct (archimed (Rabs M)) ; assumption.
 apply le_INR ; assumption.
Qed.

Lemma Rseq_poly_shifts_equiv : forall d k, (Rseq_poly d) ~ (Rseq_shifts (Rseq_poly d) k).
Proof.
intros d k eps eps_pos.
 assert (lemma : Rseq_cv (fun n => 1 - (1 + INR k / INR n) ^ d)%R 0).
  rewrite <- (Rplus_opp_r 1) ; apply Rseq_cv_minus_compat.
   apply Rseq_constant_cv.
   rewrite <- (pow1 d) ; apply Rseq_cv_pow_compat ; rewrite pow1.
   rewrite <- (Rplus_0_r 1) ; apply Rseq_cv_plus_compat.
    rewrite Rplus_0_r ; apply Rseq_constant_cv.
   rewrite <- (Rmult_0_r (INR k)) ; apply Rseq_cv_mult_compat.
    apply Rseq_constant_cv.
   apply Rseq_cv_pos_infty_inv_compat, Rseq_cv_pos_infty_INR.
 destruct (lemma _ eps_pos) as [N HN] ; exists (S N) ; intros n n_lb.
  transitivity (Rabs (1 - (1 + INR k / INR n) ^ d) * Rabs (Rseq_poly d n)).
   right ; rewrite <- Rabs_mult ; apply Rabs_eq_compat ;
   unfold Rseq_poly, Rseq_minus, Rseq_shift ; ring_simplify.
   rewrite Rplus_comm, Ropp_mult_distr_l_reverse, <- Rpow_mult_distr.
   apply Rplus_eq_compat_l, Ropp_eq_compat, Rpow_eq_compat.
   rewrite plus_INR ; field ; apply not_0_INR ; lia.
  apply Rmult_le_compat_r ; [apply Rabs_pos |].
  rewrite <- (Rminus_0_r (1 - _)) ; left ; apply HN ; lia.
Qed.

Lemma Rseq_poly_shift_equiv : forall d,
  (Rseq_poly d) ~ (Rseq_shift (Rseq_poly d)).
Proof.
intros d ; eapply Rseq_equiv_eq_compat, Rseq_poly_shifts_equiv.
 reflexivity.
 eapply Rseq_eq_trans.
  apply Rseq_shifts_shift.
  apply Rseq_shifts_0.
Qed.

(** Convergence of polynomials. *)

(**********)
Lemma Rseq_poly_cv : forall d, (d > 0)%nat -> Rseq_cv_pos_infty (Rseq_poly d).
Proof.
intros d H M.
assert (Hm : forall n, Rseq_poly d n >= INR n).
unfold Rseq_poly; induction H; intros n.
simpl; lra.
eapply Rge_trans with (INR n * INR n)%R.
rewrite <- tech_pow_Rmult.
apply Rmult_ge_compat_l; [apply Rle_ge; apply pos_INR|apply IHle].
destruct n; auto with real.
destruct n; auto with real.
left; rewrite <- Rmult_1_r.
apply Rmult_gt_compat_l.
apply lt_0_INR; lia.
apply lt_1_INR; lia.
destruct (IZN (up (Rmax 0 (M + 1)))) as [N Hz].
apply le_0_IZR.
destruct (archimed (Rmax 0 (M + 1))) as [Hp _].
left; eapply Rle_lt_trans; [apply RmaxLess1|eexact Hp].
exists N; intros n Hn.
eapply Rlt_le_trans with (INR n); [|apply Rge_le; apply Hm].
eapply Rlt_le_trans with (INR N); [|apply le_INR; assumption].
rewrite INR_IZR_INZ; rewrite <- Hz.
destruct (archimed (Rmax 0 (M + 1))) as [Hp _].
eapply Rlt_trans; [|eexact Hp].
eapply Rlt_le_trans with (M + 1)%R; [lra|apply RmaxLess2].
Qed.

(** Convergence of power sequences. *)

(**********)
Lemma Rseq_pow_eq_1_cv : Rseq_cv (Rseq_pow 1) 1.
Proof.
intros eps Heps.
exists 1%nat; intros n Hn.
assert (He : Rseq_pow 1 n = 1).
clear Hn; induction n; simpl; try rewrite IHn; field.
rewrite He; rewrite R_dist_eq; assumption.
Qed.

(**********)
Lemma Rseq_pow_lt_1_cv : forall r, 0 <= r < 1 -> Rseq_cv (Rseq_pow r) 0.
intros r [Hl Hr] eps Heps.
unfold R_dist; unfold Rseq_pow.
assert (exists N, forall n, (n >= N)%nat -> Rabs (r ^ n) < eps).
apply pow_lt_1_zero; [rewrite Rabs_right|]; try apply Rle_ge; assumption.
destruct H as [N H].
exists N; intros n Hn.
rewrite Rminus_0_r.
apply H; assumption.
Qed.

Lemma Rseq_pow_abs_compat : forall r, Rseq_pow (Rabs r) == Rseq_abs (Rseq_pow r).
Proof.
intros r n ; unfold Rseq_pow, Rseq_abs ; apply RPow_abs.
Qed.

Lemma Rseq_pow_lt_1_cv_strong : forall r, Rabs r < 1 -> Rseq_cv (Rseq_pow r) 0.
intros r H eps eps_pos ;
 assert (Hx : 0 <= Rabs r < 1) by (split ; [apply Rabs_pos | assumption]) ;
 destruct (Rseq_pow_lt_1_cv _ Hx _ eps_pos) as [N HN] ; exists N ; intros n n_lb.
 eapply Rle_lt_trans ; [| eapply HN ; eassumption].
  right ; unfold R_dist, Rseq_pow ; do 2 rewrite Rminus_0_r, <- RPow_abs ;
  rewrite Rabs_Rabsolu ; reflexivity.
Qed.

(**********)
Lemma Rseq_pow_gt_1_cv : forall r, r > 1 -> Rseq_cv_pos_infty (Rseq_pow r).
Proof.
intros r Hr M.
unfold Rseq_pow.
destruct (Pow_x_infinity r) with (b := (M + 1)%R) as [N HN].
rewrite Rabs_right; lra.
exists N; intros n Hn.
rewrite <- Rabs_right.
eapply Rlt_le_trans with (M + 1)%R; [lra|].
apply Rge_le; apply HN; assumption.
left; apply pow_lt; lra.
Qed.

(** Convergence of factorial. *)

(**********)
Lemma Rseq_fact_cv : Rseq_cv_pos_infty Rseq_fact.
Proof.
intros M.
assert (forall n, (INR n) <= Rseq_fact n).
unfold Rseq_fact.
intros n; apply le_INR.
destruct n.
simpl; repeat constructor.
rewrite fact_simpl.
pattern (S n) at 1; rewrite <- mult_1_r.
apply mult_le_compat_l.
induction n.
simpl; constructor.
rewrite fact_simpl; pattern 1%nat; rewrite <- mult_1_r.
apply mult_le_compat; lia.
destruct (IZN (up (Rmax 0 (M + 1)))) as [N Hz].
apply le_0_IZR.
destruct (archimed (Rmax 0 (M + 1))) as [Hp _].
left; eapply Rle_lt_trans; [apply RmaxLess1|eexact Hp].
exists N; intros n Hn.
eapply Rlt_le_trans with (INR n); [|apply H].
eapply Rlt_le_trans with (INR N); [|apply le_INR; assumption].
rewrite INR_IZR_INZ; rewrite <- Hz.
destruct (archimed (Rmax 0 (M + 1))) as [Hp _].
eapply Rlt_trans; [|eexact Hp].
eapply Rlt_le_trans with (M + 1)%R; [lra|apply RmaxLess2].
Qed.

(** * Growth comparison. *)

(**********)
Lemma Rseq_poly_little_O : forall d1 d2, (d1 < d2)%nat -> (Rseq_poly d1) = o(Rseq_poly d2).
Proof.
intros d1 d2 Hd.
intros eps Heps.
unfold Rseq_poly.
pose (k := (d2 - d1)%nat).
assert (Hk : (k > 0)%nat); [unfold k; lia|].
assert (HM : exists N, forall n, (n >= N)%nat -> /eps < Rseq_poly k n).
apply Rseq_poly_cv; assumption.
destruct HM as [N HN].
exists N; intros n Hn.
replace d2 with (d1 + k)%nat by (unfold k; lia).
rewrite pow_add; rewrite Rabs_mult.
rewrite Rmult_comm.
rewrite Rmult_assoc.
pattern (Rabs (INR n ^ d1)) at 1; rewrite <- Rmult_1_r.
apply Rmult_le_compat_l; [apply Rabs_pos|].
rewrite <- (Rinv_l eps); [|apply Rgt_not_eq; assumption].
apply Rmult_le_compat_r; [lra|].
rewrite Rabs_right; [|apply Rle_ge; apply pow_le; apply pos_INR].
left; apply HN; assumption.
Qed.

(**********)
Lemma Rseq_inv_poly_little_O : forall d1 d2, (d1 < d2)%nat -> (Rseq_inv_poly d2) = o(Rseq_inv_poly d1).
Proof.
intros d1 d2 Hd.
eapply Rseq_little_O_asymptotic.
  intros Wn Xn H; eexact H.
exists 1%nat.
eapply Rseq_little_O_eq_compat
  with (Un := fun n => / (INR (S n) ^ d2)) (Vn := fun n => (/ INR (S n) ^ d1)).
intros n; unfold Rseq_inv_poly.
replace (1 + n)%nat with (S n) by lia.
rewrite Rinv_pow; [reflexivity|auto with real].
intros n; unfold Rseq_inv_poly.
replace (1 + n)%nat with (S n) by lia.
rewrite Rinv_pow; [reflexivity|auto with real].
apply Rseq_little_O_inv_contravar.
intros eps Heps.
destruct (Rseq_poly_little_O d1 d2 Hd eps Heps) as [N HN].
exists N; intros n Hn; apply HN; lia.
intros n; apply pow_nonzero; auto with real.
intros n; apply pow_nonzero; auto with real.
Qed.

(**********)
Lemma Rseq_pow_little_O : forall r1 r2, (0 <= r1 < r2) -> (Rseq_pow r1) = o(Rseq_pow r2).
Proof.
intros r1 r2 [Hp Hr] eps Heps.
pose (k := (r1 / r2)%R).
assert (Hkl : 0 <= k).
unfold k; unfold Rdiv; replace 0 with (0 * 0)%R by field.
apply Rmult_le_compat; try apply Rle_refl; try lra.
left; apply Rinv_0_lt_compat; eapply Rle_lt_trans; eassumption.
assert (Hkr : k < 1).
unfold k; unfold Rdiv.
rewrite <- (Rinv_r r2).
apply Rmult_lt_compat_r; [|assumption].
apply Rinv_0_lt_compat; eapply Rle_lt_trans; [eexact Hp|eexact Hr].
apply Rgt_not_eq; eapply Rle_lt_trans; [eexact Hp|eexact Hr].
unfold Rseq_pow.
assert (Hk : exists N, forall n, (n >= N)%nat -> Rabs (k ^ n) < eps).
apply pow_lt_1_zero; [rewrite Rabs_right|]; try apply Rle_ge; assumption.
destruct Hk as [N HN].
exists N; intros n Hn.
replace r1 with (k * r2)%R.
assert ((k * r2) ^ n = k ^ n * r2 ^ n)%R as ->; swap 1 2.
rewrite Rabs_mult.
apply Rmult_le_compat_r; [apply Rabs_pos|].
left; apply HN; apply Hn.
clear Hn HN; induction n; simpl; try rewrite IHn; field.
unfold k; field; apply Rgt_not_eq; eapply Rle_lt_trans; [eexact Hp|eexact Hr].
Qed.

(**********)
Lemma Rseq_poly_pow_gt_1_little_O : forall d r, r > 1 -> (Rseq_poly d) = o(Rseq_pow r).
Proof.
intros d r Hr.
pose (npow := (fix F m d := match d with O => 1 | S d => m * F m d end)%nat).
(* Lack of a lemma in stdlib *)
assert (Hpow : (forall x y n, pow (x * y) n = pow x n * pow y n)%R).
intros x y n; induction n.
simpl; rewrite Rmult_1_l; reflexivity.
repeat rewrite <- tech_pow_Rmult; rewrite IHn; field.
(* end of lemma *)
assert (Ho : forall k, Rseq_poly (npow 2%nat k) = o(Rseq_pow r)).
induction k; simpl.
(* Case k = 0 *)
set (x := (r - 1)%R).
assert (Hx : x > 0); [unfold x; lra|].
assert (Hdev : forall n, (2 <= n)%nat -> (1 + x) ^ n >= 1 + INR n * x + (INR n * (INR n - 1)) * /2 * x * x).
intros n H; induction H.
simpl; right; field.
rewrite <- tech_pow_Rmult.
eapply Rge_trans.
apply Rmult_ge_compat_l; [lra|apply IHle].
repeat rewrite S_INR.
field_simplify.
unfold Rdiv; apply Rmult_ge_compat_r; [lra|].
assert (HINR : 1 < INR m); [apply lt_1_INR; lia|].
rewrite <- Rplus_0_l.
unfold Rminus; repeat rewrite Rplus_assoc.
rewrite <- Rplus_assoc.
apply Rplus_ge_compat_r.
rewrite <- Ropp_mult_distr_r_reverse.
rewrite <- Rmult_plus_distr_l.
rewrite <- (Rmult_0_l 0).
apply Rmult_ge_compat; try lra.
apply Rle_ge; apply pow_le; lra.
simpl.
pattern (INR m) at 3; rewrite <- Rmult_1_r.
rewrite <- Ropp_mult_distr_r_reverse.
rewrite <- Rmult_plus_distr_l.
rewrite <- (Rmult_0_l 0).
apply Rmult_ge_compat; try lra.
assert (Hmin : forall n, (2 <= n)%nat -> r ^ n > (INR n * (INR n - 1) * / 2 * x * x)).
intros n Hd.
replace r with (1 + x)%R by (unfold x; field).
rewrite <- Rplus_0_l.
eapply Rlt_le_trans; [|apply Rge_le; apply Hdev; assumption].
apply Rplus_lt_compat_r.
assert (HINR: 0 <= INR n); [apply pos_INR; lia|].
pattern 0; rewrite <- Rplus_0_l.
apply Rplus_lt_le_compat; [lra|].
apply Rmult_le_pos; lra.
assert (HO : (Rseq_poly 2) = O(fun n => INR n * (INR n - 1) * / 2 * x * x)%R).
unfold Rseq_poly.
exists (INR 4 * / x * / x)%R; split.
  apply Rle_ge; rewrite <- (Rmult_0_r 0).
  rewrite Rmult_assoc.
  apply Rmult_le_compat; try apply Rle_refl.
  apply pos_INR.
  left; apply Rmult_lt_0_compat; apply Rinv_0_lt_compat; assumption.
  exists 2%nat; intros n Hn.
  repeat rewrite Rabs_mult.
  repeat rewrite Rabs_right; try lra.
  simpl; field_simplify; [|apply Rgt_not_eq; assumption].
  replace ((4 * INR n ^ 2 - 4 * INR n) / 2)%R
    with (INR n * (2 * (INR n - 1)))%R by field.
  replace (INR n ^ 2 / 1)%R with (INR n * INR n)%R by field.
  apply Rmult_le_compat_l; [apply pos_INR|].
  replace 1%R with (INR 1) by reflexivity.
  rewrite <- minus_INR; [|lia].
  change 2 with (INR 2).
  rewrite <- 2mult_INR.
  apply le_INR; lia.
  replace 1%R with (INR 1) by reflexivity.
  rewrite <- minus_INR; [apply Rle_ge; apply pos_INR|lia].
  apply Rle_ge; apply pos_INR.
  apply Rle_ge; apply pow_le; apply pos_INR.
assert (HO2 : (fun n => INR n * (INR n - 1) * / 2 * x * x)%R = O(Rseq_pow r)).
  exists 1; split; [lra|].
  exists 2%nat; intros n Hn.
  rewrite Rabs_right; [rewrite Rabs_right|].
  left; rewrite Rmult_1_l; apply Hmin; assumption.
  apply Rle_ge; apply pow_le; lra.
  apply Rle_ge; left; repeat apply Rmult_lt_0_compat; try lra.
  apply lt_0_INR; lia.
  replace 1 with (INR 1) by reflexivity; rewrite <- minus_INR; [|lia].
  apply lt_0_INR; lia.
eapply Rseq_little_O_big_O_trans.
  apply (Rseq_poly_little_O 1 2); lia.
  eapply Rseq_big_O_trans.
    apply HO.
    apply HO2.
(* Case k > 0 *)
set (kk := npow 2%nat k).
rewrite plus_0_r.
replace (kk + kk)%nat
  with (2 * kk)%nat by ring.
intros eps Heps.
destruct (IHk (/ Rabs (2 ^ kk) * sqrt eps * / sqrt r))%R as [N HN].
repeat apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat; apply Rabs_pos_lt;
apply pow_nonzero; apply Rgt_not_eq; lra.
apply sqrt_lt_R0; lra.
apply Rinv_0_lt_compat; apply sqrt_lt_R0; lra.
exists (2 * N)%nat; intros n Hn.
unfold Rseq_poly; unfold Rseq_pow.
pose (m :=
  match Even.even_odd_dec n with
  | left evn => proj1_sig (Div2.even_2n n evn)
  | right odd => S (proj1_sig (Div2.odd_S2n n odd))
  end
).
assert (Hm : (n <= 2 * m /\ 2 * m <= S n)%nat).
destruct (Even.even_odd_dec n) as [Hm|Hm];
[destruct (Div2.even_2n n Hm) as [p Hp]|destruct (Div2.odd_S2n n Hm) as [p Hp]];
simpl in m; unfold Div2.double in Hp; unfold m; lia.
destruct Hm as [Hml Hmr].
apply Rle_trans with (Rabs (INR (2 * m) ^ (2 * kk))).
repeat rewrite Rabs_right.
apply pow_incr; split; [apply pos_INR|apply le_INR; assumption].
apply Rle_ge; apply pow_le; apply pos_INR.
apply Rle_ge; apply pow_le; apply pos_INR.
rewrite pow_Rsqr; rewrite mult_INR.
unfold Rsqr; repeat rewrite Hpow; repeat rewrite Rabs_mult; simpl.
eapply Rle_trans.
apply Rmult_le_compat.
replace 0 with (0 * 0)%R by field;
apply Rmult_le_compat; (apply Rle_refl || apply Rabs_pos).
replace 0 with (0 * 0)%R by field;
apply Rmult_le_compat; (apply Rle_refl || apply Rabs_pos).
change (1 + 1) with 2.
apply Rmult_le_compat_l; [apply Rabs_pos|]; apply HN; lia.
apply Rmult_le_compat_l; [apply Rabs_pos|]; apply HN; lia.
unfold Rseq_pow.
change (1 + 1) with 2.
field_simplify.
simpl; unfold Rdiv; repeat rewrite Rinv_1;
repeat rewrite Rmult_1_r.
rewrite sqrt_sqrt; [|lra].
rewrite sqrt_sqrt; [|lra].
rewrite Rmult_assoc.
apply Rmult_le_compat_l; [lra|].
pattern (/ r)%R at 1; rewrite <- Rabs_right; [|left; apply Rinv_0_lt_compat; lra].
repeat rewrite <- Rabs_mult.
rewrite <- pow_add.
repeat rewrite Rabs_right.
apply (Rmult_le_reg_l r); [lra|].
field_simplify.
unfold Rdiv; repeat rewrite Rinv_1; repeat rewrite Rmult_1_r.
rewrite tech_pow_Rmult.
apply Rle_pow; [lra|].
replace (m + m)%nat with (2 * m)%nat by ring; assumption.
apply Rgt_not_eq; lra.
apply Rle_ge; apply pow_le; lra.
replace 0 with (0 * 0)%R by field.
apply Rmult_ge_compat; try lra.
left; apply pow_lt; lra.
left; apply Rinv_0_lt_compat; lra.
split; apply Rgt_not_eq.
apply sqrt_lt_R0; lra.
apply Rabs_pos_lt; apply pow_nonzero; apply Rgt_not_eq; lra.
assert (Hp : (forall n, exists p, n < npow 2 p)%nat).
intros n.
destruct (zerop n) as [H|H].
exists 0%nat; simpl; lia.
induction H.
exists 1%nat; simpl; lia.
destruct IHle as [p Hp].
exists (S p); simpl; lia.
destruct (Hp d) as [dm Hdm].
apply Rseq_little_O_trans with (Rseq_poly (npow 2 dm)%nat).
apply Rseq_poly_little_O; assumption.
apply Ho.
Qed.

(**********)
Lemma Rseq_inv_poly_pow_lt_1_little_O : forall d r, 0 < r < 1 -> (Rseq_pow r) = o(Rseq_inv_poly d).
Proof.
intros d r [Hr1 Hr2].
eapply Rseq_little_O_asymptotic.
  intros Wn Xn H; eexact H.
exists 1%nat.
apply Rseq_little_O_eq_compat
  with (Un := fun n => / ((/ r) ^ (S n))) (Vn := fun n => (/ INR (S n) ^ d)).
intros n; unfold Rseq_pow.
replace (1 + n)%nat with (S n) by lia.
rewrite Rinv_pow; [|auto with real].
rewrite Rinv_involutive; [|auto with real].
reflexivity.
intros n; unfold Rseq_inv_poly.
replace (1 + n)%nat with (S n) by lia.
rewrite Rinv_pow; [|auto with real].
reflexivity.
apply Rseq_little_O_inv_contravar.
intros eps Heps.
destruct (Rseq_poly_pow_gt_1_little_O d (/ r)) with (eps := eps) as [N HN].
  rewrite <- Rinv_1.
  apply Rinv_lt_contravar.
  rewrite Rmult_1_r; assumption.
  assumption.
  assumption.
exists N; intros n Hn.
apply HN; lia.
intros n; apply pow_nonzero; auto with real.
intros n; apply pow_nonzero; auto with real.
Qed.

(**********)
Lemma Rseq_pow_fact_little_O : forall r, 0 <= r -> (Rseq_pow r) = o(Rseq_fact).
Proof.
assert (HO : forall n, Rseq_pow (INR n) = O(Rseq_fact)).
  intros n.
  assert (Hp: 0 <= INR n ^ n).
    apply pow_le; apply pos_INR.
  assert (Hf: / INR (fact n) > 0).
    apply Rinv_0_lt_compat.
    replace 0 with (INR 0) by reflexivity.
    apply lt_INR; apply lt_O_fact.
  exists (INR n ^ n / INR (fact n)); split.
    replace 0 with (0 * 0)%R by field.
    apply Rmult_ge_compat; try lra;
      try left; apply Hf.
  exists n; intros m Hm.
  induction Hm.
    rewrite Rabs_right; [|apply Rle_ge; apply Hp].
    rewrite Rabs_right; [|apply Rle_ge; apply pos_INR].
    right.
      unfold Rseq_pow; unfold Rseq_fact; field.
      apply Rgt_not_eq.
      replace 0 with (INR 0) by reflexivity.
      apply lt_INR; apply lt_O_fact.
    simpl; unfold Rseq_fact; rewrite fact_simpl.
    rewrite mult_INR.
    repeat rewrite Rabs_mult.
    set (K := INR n ^ n / INR (fact n)).
    replace (K * (Rabs (INR (S m)) * Rabs (INR (fact m))))
      with (Rabs (INR (S m)) * (K * (Rabs (INR (fact m)))))
      by field.
    apply Rmult_le_compat; try apply Rabs_pos.
    repeat rewrite Rabs_right; try (apply Rle_ge; apply pos_INR).
    apply le_INR; lia.
    apply IHHm.
intros r Hr.
destruct (IZN (up r)) as [d Hd].
  destruct (archimed r) as [H _].
  apply le_IZR.
  eapply Rle_trans.
    simpl; eexact Hr.
    left; eexact H.
apply Rseq_little_O_big_O_trans with (Rseq_pow (INR d)).
apply Rseq_pow_little_O; split.
  assumption.
  destruct (archimed r) as [H _].
  rewrite Hd in H.
  rewrite <- INR_IZR_INZ in H.
  exact H.
apply HO.
Qed.

(**********)
Lemma Rseq_poly_fact_little_O : forall d, Rseq_poly d = o(Rseq_fact).
Proof.
intros d.
eapply Rseq_little_O_trans.
apply Rseq_poly_pow_gt_1_little_O.
instantiate (1 := 2); lra.
apply Rseq_pow_fact_little_O; lra.
Qed.

(** * Things that don't have anything to do there... *)

(**********)
Lemma Rseq_ln_cv : Rseq_cv_pos_infty (fun n => ln (INR n)).
Proof.
intro m.
destruct (Rseq_poly_cv 1) with (M := Rabs m) as [N HN]; [lia|].
destruct (IZN(up (exp (INR N)))) as [N1 HN1].
  apply le_IZR; simpl.
  apply Rle_trans with (exp (INR N)).
    left; apply exp_pos.
  left; eapply (proj1 (archimed _)).
exists N1.
intros n Hn.
apply Rle_lt_trans with (Rabs m).
  apply RRle_abs.
apply Rlt_le_trans with (INR N).
  replace (INR N) with (INR N ^ 1) by field.
  apply (HN _ (le_refl _)).
rewrite <- ln_exp with (INR N).
left; apply ln_increasing.
  apply exp_pos.
apply Rlt_le_trans with (IZR (Z_of_nat N1)).
  rewrite <- HN1.
  apply (proj1(archimed _)).
rewrite <- INR_IZR_INZ; apply le_INR; apply Hn.
Qed.
