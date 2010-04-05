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

Require Import Rbase.
Require Import Rsequence.
Require Import Ranalysis.
Require Import Rfunctions.
Require Import Rseries_def.
Require Import Fourier.
Require Import RiemannInt.
Require Import SeqProp.
Require Import Ranalysis_def.
Require Import MyRIneq.

Local Open Scope R_scope.

(** * Intermediate Value Theorem on an Interval and its corollary *)
(** This proof was mainly taken from Reals.Rsqrt_def *)

Lemma IVT_interv_prelim0 : forall (x y:R) (P:R->bool) (N:nat),
       x < y ->
       interval x y (Dichotomy_ub x y P N) /\ interval x y (Dichotomy_lb x y P N).
Proof.
intros x y P N x_lt_y.
induction N.
 simpl ; intuition.
  split ; [left ; assumption | right ; reflexivity].
  split ; [right ; reflexivity | left ; assumption].
 simpl.
 replace ((Dichotomy_lb x y P N + Dichotomy_ub x y P N) / 2) with
  (middle (Dichotomy_lb x y P N) (Dichotomy_ub x y P N)).
 case (P (middle (Dichotomy_lb x y P N) (Dichotomy_ub x y P N))).
 split.
 apply middle_interval ; intuition.
 intuition.
 split ; [| apply middle_interval] ; intuition.
 unfold middle ; reflexivity.
Qed.

Lemma IVT_interv_prelim1 : forall (x y b:R) (D : R -> bool),
       x < y ->
       Rseq_cv (dicho_up x y D) b ->
       interval x y b.
Proof.
intros x y x0 D x_lt_y bnd.
 assert (Main : forall n, interval x y (dicho_up x y D n)).
  intro n. unfold dicho_up.
  apply (proj1 (IVT_interv_prelim0 x y D n x_lt_y)).
 split.
  apply Rle_cv_lim with (Vn:=dicho_up x y D) (Un:=fun n => x).
  intro n ; exact (proj1 (Main n)).
  unfold Un_cv ; intros ; exists 0%nat ; intros ; unfold R_dist ; replace (x -x) with 0 by field ; rewrite Rabs_R0 ; assumption.
  assumption.
  apply Rle_cv_lim with (Un:=dicho_up x y D) (Vn:=fun n => y).
  intro n ; exact (proj2 (Main n)).
  assumption.
  unfold Un_cv ; intros ; exists 0%nat ; intros ; unfold R_dist ; replace (y -y) with 0 by field ; rewrite Rabs_R0 ; assumption.
Qed.

Lemma IVT_interv : forall (f : R -> R) (x y : R),
       continuity_interval f x y ->
       x < y ->
       interval (f x) (f y) 0 ->
       {z : R | interval x y z /\ f z = 0}.
Proof.
intros f x y H H0 [H1 H2].
 case (Rle_lt_or_eq_dec _ _ H1) ; clear H1 ; intro H1.
 case (Rle_lt_or_eq_dec _ _ H2) ; clear H2 ; intro H2.
  cut (x <= y).
  intro.
  generalize (dicho_lb_cv x y (fun z:R => cond_positivity (f z)) H3).
  generalize (dicho_up_cv x y (fun z:R => cond_positivity (f z)) H3).
  intros X X0.
  elim X; intros.
  elim X0; intros.
  assert (H4 := cv_dicho _ _ _ _ _ H3 p0 p).
  rewrite H4 in p0.
  exists x0.
  split.
  split.
  apply Rle_trans with (dicho_lb x y (fun z:R => cond_positivity (f z)) 0).
  simpl in |- *.
  right; reflexivity.
  apply growing_ineq.
  apply dicho_lb_growing; assumption.
  assumption.
  apply Rle_trans with (dicho_up x y (fun z:R => cond_positivity (f z)) 0).
  apply decreasing_ineq.
  apply dicho_up_decreasing; assumption.
  assumption.
  right; reflexivity.
  2: left; assumption.
  set (Vn := fun n:nat => dicho_lb x y (fun z:R => cond_positivity (f z)) n).
  set (Wn := fun n:nat => dicho_up x y (fun z:R => cond_positivity (f z)) n).
  cut ((forall n:nat, f (Vn n) <= 0) -> f x0 <= 0).
  cut ((forall n:nat, 0 <= f (Wn n)) -> 0 <= f x0).
  intros.
  cut (forall n:nat, f (Vn n) <= 0).
  cut (forall n:nat, 0 <= f (Wn n)).
  intros.
  assert (H9 := H6 H8).
  assert (H10 := H5 H7).
  apply Rle_antisym; assumption.
  intro.
  unfold Wn in |- *.
  cut (forall z:R, cond_positivity z = true <-> 0 <= z).
  intro.
  assert (H8 := dicho_up_car x y (fun z:R => cond_positivity (f z)) n).
  elim (H7 (f (dicho_up x y (fun z:R => cond_positivity (f z)) n))); intros.
  apply H9.
  apply H8.
  elim (H7 (f y)); intros.
  apply H12.
  left ; assumption.
  intro.
  unfold cond_positivity in |- *.
  case (Rle_dec 0 z); intro.
  split.
  intro; assumption.
  intro; reflexivity.
  split.
  intro feqt;discriminate feqt.
  intro.
  elim n0; assumption.
  unfold Vn in |- *.
  cut (forall z:R, cond_positivity z = false <-> z < 0).
  intros.
  assert (H8 := dicho_lb_car x y (fun z:R => cond_positivity (f z)) n).
  elim (H7 (f (dicho_lb x y (fun z:R => cond_positivity (f z)) n))); intros.
  left ; apply H9.
  apply H8.
  elim (H7 (f x)); intros.
  apply H12.
  assumption.
  intro.
  unfold cond_positivity in |- *.
  case (Rle_dec 0 z); intro.
  split.
  intro feqt; discriminate feqt.
  intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ r H7)).
  split.
  intro; auto with real.
  intro; reflexivity.
  cut (Un_cv Wn x0).
  intros.
  assert (Temp : x <= x0 <= y).
   apply IVT_interv_prelim1 with (D:=(fun z : R => cond_positivity (f z))) ; assumption.
  assert (H7 := continuity_seq f Wn x0 (H x0 Temp) H5).
  case (total_order_T 0 (f x0)); intro.
  elim s; intro.
  left; assumption.
  rewrite <- b; right; reflexivity.
  unfold Un_cv in H7; unfold R_dist in H7.
  cut (0 < - f x0).
  intro.
  elim (H7 (- f x0) H8); intros.
  cut (x2 >= x2)%nat; [ intro | unfold ge in |- *; apply le_n ].
  assert (H11 := H9 x2 H10).
  rewrite Rabs_right in H11.
  pattern (- f x0) at 1 in H11; rewrite <- Rplus_0_r in H11.
  unfold Rminus in H11; rewrite (Rplus_comm (f (Wn x2))) in H11.
  assert (H12 := Rplus_lt_reg_r _ _ _ H11).
  assert (H13 := H6 x2).
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H13 H12)).
  apply Rle_ge; left; unfold Rminus in |- *; apply Rplus_le_lt_0_compat.
  apply H6.
  exact H8.
  apply Ropp_0_gt_lt_contravar; assumption.
  unfold Wn in |- *; assumption.
  cut (Un_cv Vn x0).
  intros.
  assert (Temp : x <= x0 <= y).
   apply IVT_interv_prelim1 with (D:=(fun z : R => cond_positivity (f z))) ; assumption.
  assert (H7 := continuity_seq f Vn x0 (H x0 Temp) H5).
  case (total_order_T 0 (f x0)); intro.
  elim s; intro.
  unfold Un_cv in H7; unfold R_dist in H7.
  elim (H7 (f x0) a); intros.
  cut (x2 >= x2)%nat; [ intro | unfold ge in |- *; apply le_n ].
  assert (H10 := H8 x2 H9).
  rewrite Rabs_left in H10.
  pattern (f x0) at 2 in H10; rewrite <- Rplus_0_r in H10.
  rewrite Ropp_minus_distr' in H10.
  unfold Rminus in H10.
  assert (H11 := Rplus_lt_reg_r _ _ _ H10).
  assert (H12 := H6 x2).
  cut (0 < f (Vn x2)).
  intro.
  elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ H13 H12)).
  rewrite <- (Ropp_involutive (f (Vn x2))).
  apply Ropp_0_gt_lt_contravar; assumption.
  apply Rplus_lt_reg_r with (f x0 - f (Vn x2)).
  rewrite Rplus_0_r; replace (f x0 - f (Vn x2) + (f (Vn x2) - f x0)) with 0;
    [ unfold Rminus in |- *; apply Rplus_lt_le_0_compat | ring ].
  assumption.
  apply Ropp_0_ge_le_contravar; apply Rle_ge; apply H6.
  right; rewrite <- b; reflexivity.
  left; assumption.
  unfold Vn in |- *; assumption.
  exists y ; repeat split ; intuition.
  exists x ; repeat split ; intuition.
Qed.
