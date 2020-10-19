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
Require Export Rsequence.
Require Import Ranalysis.
Require Import Rfunctions.
Require Import Rseries_def.
Require Import Lra.
Require Import RiemannInt.
Require Import SeqProp.
Require Import MyRIneq.
Require Import Rinterval Ranalysis_def Ranalysis_def_simpl.
Require Import Ranalysis_continuity.

Local Open Scope R_scope.

(** * Intermediate Value Theorem on an Interval and its corollary *)
(** This proof was mainly taken from Reals.Rsqrt_def *)

Lemma dicho_steps_interval_compat : forall x y P N, x <= y ->
  interval x y (dicho_up x y P N)
  /\ interval x y (dicho_lb x y P N).
Proof.
intros x y P N x_le_y ; induction N.
 simpl ; split ; [apply interval_r | apply interval_l] ; assumption.
 simpl ; split ; fold (middle (Dichotomy_lb x y P N) (Dichotomy_ub x y P N)) ;
 destruct (P (middle (Dichotomy_lb x y P N) (Dichotomy_ub x y P N))) ;
 try apply interval_middle_compat ; apply IHN.
Qed.

Lemma dicho_interval_compat : forall x y l P, x <= y ->
  Rseq_cv (dicho_up x y P) l -> interval x y l.
Proof.
intros x y l P x_le_y Hl ; eapply Rseq_interval_compat ;
 [| eassumption] ; intro ; apply dicho_steps_interval_compat ;
 assumption.
Qed.

Lemma cond_positivity_car: forall x,
  cond_positivity x = true <-> 0 <= x.
Proof.
intro ; unfold cond_positivity ; destruct (Rle_dec 0 x) ;
 intuition ; discriminate.
Qed.

Lemma cond_positivity_car': forall x,
  cond_positivity x = false <-> x < 0.
Proof.
intro ; unfold cond_positivity ; destruct (Rle_dec 0 x) ; intuition.
 discriminate.
 destruct (Rlt_irrefl 0) ; eapply Rle_lt_trans ; eassumption.
Qed.

Lemma Rseq_cv_0_abs_compat : forall Un,
  Rseq_cv (| Un |) 0 -> Rseq_cv Un 0.
Proof.
intros Un HUn eps eps_pos ; destruct (HUn _ eps_pos) as [N HN] ;
 exists N ; intros n n_lb ; apply Rle_lt_trans with (R_dist (|Un| n)%R 0).
  right ; unfold R_dist, Rseq_abs ; do 2 rewrite Rminus_0_r ;
  rewrite Rabs_Rabsolu ; reflexivity.
  apply HN ; assumption.
Qed.

Lemma dicho_diff_cv : forall x y P, x <= y ->
  Rseq_cv (dicho_up x y P - dicho_lb x y P) 0.
Proof.
intros x y P xley ; eapply Rseq_cv_eq_compat.
 intro n ; apply dicho_lb_dicho_up ; assumption.
 eapply Rseq_cv_pos_infty_div_compat, Rseq_constant_cv.
 apply Rseq_pow_gt_1_cv ; lra.
Qed.

Lemma interval_open_interval : forall x y z,
  interval x y z -> x <> z -> y <> z ->
  open_interval x y z.
Proof.
intros x y z [xz zy] x_neq y_neq ; split ;
 apply Rle_neq_lt ; auto.
Qed.

Lemma IVT_open_interval_prelim : forall (f : R -> R) (x y : R),
  continuity_interval x y f -> x < y -> open_interval (f x) (f y) 0 ->
  {z : R | open_interval x y z /\ f z = 0}.
Proof.
intros f x y Hf xlty O_in ; assert (xley := Rlt_le _ _ xlty) ;
 pose (P := fun z => cond_positivity (f z)) ; pose (Zn := dicho_up x y P) ;
 pose (Zn' := dicho_lb x y P) ; assert (Hcv := dicho_diff_cv _ _ P xley) ;
 destruct (dicho_up_cv x y P xley) as [z Hz] ; exists z.
 assert (Hz' : Rseq_cv Zn' z).
  destruct (dicho_lb_cv x y P xley) as [z' Hz'] ;
  rewrite <- (cv_dicho _ _ _ _ _ xley Hz' Hz) ; assumption.
 assert (fz_eq : f z = 0).
  apply Rle_antisym.

  apply Rseq_negative_limit with (fun n => f (Zn' n)).
  intro n ; left ; rewrite <- cond_positivity_car' ; fold (P (Zn' n)) ;
  apply dicho_lb_car ; unfold P ; rewrite cond_positivity_car' ; apply O_in.

  eapply Rseq_cv_continuity_interval_compat ; [eapply dicho_interval_compat |
  intro ; apply dicho_steps_interval_compat | |] ; eassumption.

  apply Rseq_positive_limit with (fun n => f (Zn n)).
  intro n ; rewrite <- cond_positivity_car ; fold (P (Zn n)) ;
  apply dicho_up_car ; unfold P ; rewrite cond_positivity_car ;
  left ;  apply O_in.
  eapply Rseq_cv_continuity_interval_compat ; [eapply dicho_interval_compat |
  intro ; apply dicho_steps_interval_compat | |] ; eassumption.

  split ; [apply interval_open_interval | assumption].
   eapply dicho_interval_compat ; eassumption.
   intro Hfalse ; rewrite Hfalse in O_in ; apply (Rlt_irrefl 0) ;
   apply Rle_lt_trans with (f z) ; [right ; symmetry ; apply fz_eq | apply O_in].
   intro Hfalse ; rewrite Hfalse in O_in ; apply (Rlt_irrefl 0) ;
   apply Rlt_le_trans with (f z) ; [apply O_in | right ; apply fz_eq].
Qed.

Lemma IVT_open_interval : forall (f : R -> R) (x y : R) l,
  continuity_interval x y f -> x < y -> open_interval (f x) (f y) l ->
  { z : R | open_interval x y z /\ f z = l }.
Proof.
intros f x y l Hf Hxy Hl ;
 destruct IVT_open_interval_prelim with (f - (fun _ => l))%F x y as [z [z_in Hz]].
  apply continuity_in_minus, continuity_in_const ; assumption.
  assumption.
  clear - Hl; destruct Hl ; split ; unfold minus_fct ; lra.
 exists z ; split ; [assumption |].
  clear - Hz ; unfold minus_fct in * ; intuition.
Qed. 

Lemma IVT_interval : forall (f : R -> R) (x y : R) l,
  continuity_interval x y f -> x <= y -> interval (f x) (f y) l ->
  {z : R | interval x y z /\ f z = l}.
Proof.
intros f x y l Hf xley [fxlel llefy] ;
 destruct (Rle_lt_or_eq_dec _ _ xley) as [xlty | xeqy].
 destruct (Rle_lt_or_eq_dec _ _ fxlel) as [fxltl | fxeql].
 destruct (Rle_lt_or_eq_dec _ _ llefy) as [lltfy | leqfy].
 destruct (IVT_open_interval _ _ _ l Hf xlty) as [z [z_in Hz]].
  split ; assumption.
  exists z ; split ; [apply open_interval_interval |] ; assumption.
  exists y ; split ; [apply interval_r |] ; auto.
  exists x ; split ; [apply interval_l |] ; auto.
  exists y ; subst ; split ; [apply interval_r | apply Rle_antisym] ; auto.
Qed.
