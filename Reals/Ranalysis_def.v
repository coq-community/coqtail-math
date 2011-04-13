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

(* This work has been mainly taken from Guillaume Allais's internship (MARELLE team - INRIA Sophia Antipolis)*)

Require Import Rbase.
Require Import Ranalysis1.
Require Import Fourier.
Require Import Rfunctions.
Require Import MyRIneq.
Require Import Ranalysis2.
Require Import Rtopology.

Local Open Scope R_scope.

(** * Basic notions *)

Definition open_interval (lb ub x:R) := lb < x < ub.
Definition interval (lb ub x:R) := lb <= x <= ub.
Definition middle (x:R) (y:R) : R := (x+y)/2.

Definition continuity_open_interval (f : R -> R) (lb ub:R) := forall x:R,
      open_interval lb ub x -> continuity_pt f x.
Definition continuity_interval (f : R -> R) (lb ub:R) := forall x:R,
      interval lb ub x -> continuity_pt f x.

Definition derivable_open_interval (f : R -> R) (lb ub:R) := forall x:R,
      open_interval lb ub x -> derivable_pt f x.
Definition derivable_interval (f : R -> R) (lb ub:R) := forall x:R,
      interval lb ub x -> derivable_pt f x.

Definition injective_interval (f : R -> R) (lb ub:R) := forall (x y:R),
      interval lb ub x -> interval lb ub y -> f x = f y -> x = y.
Definition surjective_interval (f : R -> R) (lb ub:R) := forall y:R,
      interval lb ub y -> exists x:R, y = f x.

Definition injective (f : R -> R) := forall (x y:R), f x = f y -> x = y.
Definition surjective (f : R -> R) := forall y:R, exists x:R, y = f x.
Definition bijective (f : R -> R) := injective f /\ surjective f.

Definition strictly_increasing_interval (f : R -> R) (lb ub:R) := forall x y,
       interval lb ub x -> interval lb ub y -> x < y -> f x < f y.
Definition strictly_decreasing_interval (f : R -> R) (lb ub:R) := forall x y,
       interval lb ub x -> interval lb ub y -> x < y -> f y < f x.
Definition strictly_monotonous_interval (f : R -> R) (lb ub : R) :=
     {strictly_increasing_interval f lb ub} + {strictly_decreasing_interval f lb ub}.

Definition increasing_interval (f : R -> R) (lb ub:R) := forall x y,
       interval lb ub x -> interval lb ub y -> x <= y -> f x <= f y.
Definition decreasing_interval (f : R -> R) (lb ub:R) := forall x y,
       interval lb ub x -> interval lb ub y -> x <= y -> f y <= f x.
Definition monotonous_interval (f : R -> R) (lb ub : R) :=
     {increasing_interval f lb ub} + {decreasing_interval f lb ub}.

Definition strictly_increasing (f : R -> R) := forall x y, x < y -> f x < f y.
Definition strictly_decreasing (f : R -> R) := forall x y, x < y -> f y < f x.
Definition strictly_monotonous (f : R -> R) :=
     {strictly_increasing f} + {strictly_decreasing f}.


Definition reciprocal_interval (f g:R -> R) (lb ub:R) := forall x,
       interval lb ub x -> (comp f g) x = id x.
Definition reciprocal_open_interval (f g:R -> R) (lb ub:R) := forall x,
       open_interval lb ub x -> (comp f g) x = id x.

Definition reciprocal (f g:R -> R) := forall x, (comp f g) x = id x.

(** Manipulation *)

Lemma middle_identity : forall x, middle x x = x.
Proof.
intros ; unfold middle ; field.
Qed.

Lemma middle_comm : forall x y, middle x y = middle y x.
Proof.
intros ; unfold middle ; field.
Qed.

Lemma middle_unfold : forall x y, middle x y = (x + y) / 2.
Proof.
intros ; reflexivity.
Qed.

Lemma middle_R0 : forall x, middle (- x) x = 0.
Proof.
intros ; unfold middle ; field.
Qed.

Lemma middle_is_in_the_middle : forall x y, x < y -> x < middle x y < y.
Proof.
intros x y x_lt_y ; split.
 apply Rle_lt_trans with (middle x x).
 right ; symmetry ; apply middle_identity.
 unfold middle, Rdiv ; apply Rmult_lt_compat_r ; [fourier |] ;
 apply Rplus_lt_compat_l ; assumption.
 apply Rlt_le_trans with (middle y y).
 unfold middle, Rdiv ; apply Rmult_lt_compat_r ; [fourier |] ;
 apply Rplus_lt_compat_r ; assumption.
 right ; apply middle_identity.
Qed.

Lemma Rabs_middle_is_in_the_middle : forall x y, 0 <= x -> x < y ->
  x < Rabs (middle x y) < y.
Proof.
intros x y x_pos x_lt_y.
 assert (mxy_pos : 0 < middle x y).
  apply Rle_lt_trans with x ;
  [| apply middle_is_in_the_middle] ;
  assumption.
 rewrite Rabs_pos_eq ;
 [ apply middle_is_in_the_middle |] ;
 intuition.
Qed.

Lemma middle_interval : forall lb ub x y, interval lb ub x -> interval lb ub y ->
       interval lb ub (middle x y).
Proof.
intros lb ub x y x_in_I y_in_I.
 split ; unfold middle, interval in *.
 replace lb with ((lb + lb) * /2) by field.
 unfold Rdiv ; apply Rmult_le_compat_r ; intuition.
 replace ub with ((ub + ub) * /2) by field.
 unfold Rdiv ; apply Rmult_le_compat_r ; intuition.
Qed.

Lemma middle_lt_lt_pos : forall x y, 0 < x -> 0 < y -> 0 < middle x y.
Proof.
intros x y x_pos y_pos ; unfold middle, Rdiv ;
 apply Rlt_mult_inv_pos ; fourier.
Qed.

Lemma middle_le_lt_pos : forall x y, 0 <= x -> 0 < y -> 0 < middle x y.
Proof.
intros x y x_pos y_pos ; unfold middle, Rdiv ;
 apply Rlt_mult_inv_pos ; fourier.
Qed.

Lemma middle_lt_le_pos : forall x y, 0 < x -> 0 <= y -> 0 < middle x y.
Proof.
intros x y x_pos y_pos ; rewrite middle_comm ;
 apply middle_le_lt_pos ; assumption.
Qed.

Lemma middle_lt_lt_neg : forall x y, x < 0 -> y < 0 -> middle x y < 0.
Proof.
intros x y x_neg y_neg ; unfold middle, Rdiv ;
 replace 0 with ((x + y) * 0) by ring ;
 apply Rmult_lt_gt_compat_neg_l ; fourier.
Qed.

Lemma middle_le_lt_neg : forall x y, x <= 0 -> y < 0 -> middle x y < 0.
Proof.
intros x y x_pos y_pos ; unfold middle, Rdiv ;
  replace 0 with ((x + y) * 0) by ring ;
 apply Rmult_lt_gt_compat_neg_l ; fourier.
Qed.

Lemma middle_lt_le_neg : forall x y, x < 0 -> y <= 0 -> middle x y < 0.
Proof.
intros x y x_neg y_neg ; rewrite middle_comm ;
 apply middle_le_lt_neg ; assumption.
Qed.

Lemma interval_l : forall lb ub, lb <= ub -> interval lb ub lb.
Proof.
intros ; split ; [right |] ; trivial.
Qed.

Lemma interval_r : forall lb ub, lb <= ub -> interval lb ub ub.
Proof.
intros ; split ; [| right] ; trivial.
Qed.

Lemma open_interval_interval : forall lb ub x,
     open_interval lb ub x -> interval lb ub x.
Proof.
 intros ; split ; unfold open_interval in * ; intuition.
Qed.

Lemma interval_opp_compat : forall lb ub x,
     interval lb ub x ->
     interval (-ub) (-lb) (-x).
Proof.
intros ; unfold interval in * ; split ; intuition ; fourier.
Qed.

Lemma open_interval_opp_compat : forall lb ub x,
     open_interval lb ub x ->
     open_interval (-ub) (-lb) (-x).
Proof.
intros ; unfold open_interval in * ; split ; intuition ; fourier.
Qed.

Lemma strictly_increasing_strictly_monotonous_interval : forall f lb ub,
      strictly_increasing_interval f lb ub -> strictly_monotonous_interval f lb ub.
Proof.
intros ; left ; assumption.
Qed.

Lemma strictly_decreasing_strictly_monotonous_interval : forall f lb ub,
      strictly_decreasing_interval f lb ub -> strictly_monotonous_interval f lb ub.
Proof.
intros ; right ; assumption.
Qed.

Lemma strictly_increasing_increasing_interval : forall f lb ub,
     strictly_increasing_interval f lb ub -> increasing_interval f lb ub.
Proof.
intros f lb ub f_incr x y x_in_I y_in_I x_le_y.
 destruct x_le_y as [x_lt_y | x_eq_y].
 left ; apply f_incr ; assumption.
 right ; subst ; reflexivity.
Qed.

Lemma strictly_decreasing_decreasing_interval : forall f lb ub,
     strictly_decreasing_interval f lb ub -> decreasing_interval f lb ub.
Proof.
intros f lb ub f_incr x y x_in_I y_in_I x_le_y.
 destruct x_le_y as [x_lt_y | x_eq_y].
 left ; apply f_incr ; assumption.
 right ; subst ; reflexivity.
Qed.

Lemma strictly_monotonous_monotonous_interval : forall f lb ub,
     strictly_monotonous_interval f lb ub ->
     monotonous_interval f lb ub.
Proof.
intros f lb ub [H | H] ; [left ; apply strictly_increasing_increasing_interval
 | right ; apply strictly_decreasing_decreasing_interval] ; apply H.
Qed.

Lemma strictly_monotonous_injective_interval : forall f lb ub,
      strictly_monotonous_interval f lb ub -> injective_interval f lb ub.
Proof.
intros f c r Hf ; destruct Hf as [f_incr | f_decr] ;
 intros x y x_in_B y_in_B fx_eq_fy ;
 destruct (Rlt_le_dec x y) as [x_lt_y | x_ge_y].
  assert (H := f_incr _ _ x_in_B y_in_B x_lt_y) ; rewrite fx_eq_fy in H ;
  elim (Rlt_irrefl _ H).
  destruct x_ge_y as [y_lt_x | x_eq_y].
   assert (H := f_incr _ _ y_in_B x_in_B y_lt_x) ; rewrite fx_eq_fy in H ;
   elim (Rlt_irrefl _ H).
   symmetry ; assumption.
  assert (H := f_decr _ _ x_in_B y_in_B x_lt_y) ; rewrite fx_eq_fy in H ;
  elim (Rlt_irrefl _ H).
  destruct x_ge_y as [y_lt_x | x_eq_y].
   assert (H := f_decr _ _ y_in_B x_in_B y_lt_x) ; rewrite fx_eq_fy in H ;
   elim (Rlt_irrefl _ H).
   symmetry ; assumption.
Qed.

Lemma strictly_increasing_Rmin_simpl : forall f lb ub,
     lb < ub -> strictly_increasing_interval f lb ub ->
     Rmin (f lb) (f ub) = f lb.
Proof.
intros f lb ub lb_lt_ub f_incr ; assert (flb_lt_fub : f lb < f ub).
 apply f_incr ; [apply interval_l | apply interval_r |] ; intuition.
 unfold Rmin ; destruct (Rle_dec (f lb) (f ub)) ; intuition.
Qed.

Lemma strictly_increasing_Rmax_simpl : forall f lb ub,
     lb < ub -> strictly_increasing_interval f lb ub ->
     Rmax (f lb) (f ub) = f ub.
Proof.
intros f lb ub lb_lt_ub f_incr ; assert (flb_lt_fub : f lb < f ub).
 apply f_incr ; [apply interval_l | apply interval_r |] ; intuition.
 unfold Rmax ; destruct (Rle_dec (f lb) (f ub)) ; intuition.
Qed.

Lemma strictly_decreasing_Rmin_simpl : forall f lb ub,
     lb < ub -> strictly_decreasing_interval f lb ub ->
     Rmin (f lb) (f ub) = f ub.
Proof.
intros f lb ub lb_lt_ub f_decr ; assert (flb_lt_fub : f ub < f lb).
 apply f_decr ; [apply interval_l | apply interval_r |] ; intuition.
 unfold Rmin ; destruct (Rle_dec (f lb) (f ub)) ; intuition.
Qed.

Lemma strictly_decreasing_Rmax_simpl : forall f lb ub,
     lb < ub -> strictly_decreasing_interval f lb ub ->
     Rmax (f lb) (f ub) = f lb.
Proof.
intros f lb ub lb_lt_ub f_decr ; assert (flb_lt_fub : f ub < f lb).
 apply f_decr ; [apply interval_l | apply interval_r |] ; intuition.
 unfold Rmax ; destruct (Rle_dec (f lb) (f ub)) ; intuition.
Qed.

Lemma derivable_continuous_interval : forall f lb ub,
	derivable_interval f lb ub -> continuity_interval f lb ub.
Proof.
intros f lb ub H x x_in ; apply derivable_continuous_pt ;
 apply H ; assumption.
Qed.

Lemma continuity_open_interval_opp_rev : forall f lb ub,
      continuity_open_interval (-f)%F lb ub ->
      continuity_open_interval f lb ub.
Proof.
intros f lb ub f_cont b b_in_I eps eps_pos ;
 destruct (f_cont b b_in_I eps eps_pos) as [alpha [alpha_pos Halpha]] ;
 exists alpha ; split.
 assumption.
 intros x Hx ; simpl ; unfold R_dist ; rewrite <- Rabs_Ropp.
 unfold Rminus ; rewrite Ropp_plus_distr.
 simpl in * ; unfold R_dist in * ; apply Halpha ; repeat split ; unfold D_x, no_cond.
 destruct Hx as [[_ x_neq_b] Hxb] ; intuition.
 intuition.
Qed.

Lemma continuity_open_interval_opp_rev2 : forall f lb ub,
      continuity_open_interval (fun x => f(-x)) (-ub) (-lb) ->
      continuity_open_interval f lb ub.
Proof.
intros f lb ub f_cont b b_in_I eps eps_pos.
 assert (b_in_I2 := open_interval_opp_compat _ _ _ b_in_I).
 destruct (f_cont (-b) b_in_I2 eps eps_pos) as [alpha [alpha_pos Halpha]] ;
 exists alpha ; split.
 assumption.
 intros x Hx ; simpl in * ; unfold R_dist in *.
 rewrite Ropp_involutive in Halpha.
 apply Rle_lt_trans with (Rabs (f (-- x) - f b)).
 right ; rewrite Ropp_involutive ; reflexivity.
 apply Halpha ; repeat split ; unfold D_x, no_cond.
 destruct Hx as [[_ x_neq_b] Hxb].
 intro Hf ; apply x_neq_b.
 assert (T := Ropp_eq_compat _ _ Hf) ; repeat rewrite Ropp_involutive in T ; assumption.
 unfold Rminus ; rewrite <- Ropp_plus_distr, Rabs_Ropp ; apply (proj2 Hx).
Qed.

Lemma strictly_increasing_strictly_decreasing_interval : forall f lb ub,
    strictly_increasing_interval f lb ub -> strictly_decreasing_interval (-f)%F lb ub.
Proof.
intros f c r f_incr ; intros x y x_in_B y_in_B x_lt_y.
 assert (H := f_incr _ _ x_in_B y_in_B x_lt_y).
 unfold opp_fct ; intuition.
Qed.

Lemma strictly_increasing_strictly_decreasing_interval2 : forall f lb ub,
       strictly_increasing_interval f lb ub ->
       strictly_decreasing_interval (fun x => f(-x)) (-ub) (-lb).
Proof.
intros f c r f_incr ; intros x y x_in_B y_in_B x_lt_y.
 apply f_incr ; unfold interval in * ; try split ; intuition ; fourier.
Qed.

Lemma strictly_decreasing_strictly_increasing_interval : forall f lb ub,
    strictly_decreasing_interval f lb ub -> strictly_increasing_interval (-f)%F lb ub.
Proof.
intros f c r f_decr ; intros x y x_in_B y_in_B x_lt_y.
 assert (H := f_decr _ _ x_in_B y_in_B x_lt_y).
 unfold opp_fct ; intuition.
Qed.

Lemma strictly_decreasing_strictly_increasing_interval2 : forall f lb ub,
    strictly_decreasing_interval f lb ub -> strictly_increasing_interval (fun x => f(-x)) (-ub) (-lb).
Proof.
intros f c r f_decr ; intros x y x_in_B y_in_B x_lt_y.
 apply f_decr ; unfold interval in * ; try split ; intuition ; fourier.
Qed.


Lemma strictly_increasing_reciprocal_interval_compat : forall f g lb ub,
           strictly_increasing_interval f lb ub ->
	   reciprocal_interval f g (f lb) (f ub) ->
           (forall x, interval (f lb) (f ub) x -> interval lb ub (g x)) ->
           strictly_increasing_interval g (f lb) (f ub).
Proof.
intros f g lb ub f_incr f_recip_g g_ok x y x_in_I y_in_I x_lt_y.
 destruct (Rlt_le_dec (g x) (g y)) as [T | F].
  assumption.
  destruct F as [F | F].
   assert (Hf : y < x).
    unfold reciprocal_interval, id in f_recip_g ; rewrite <- f_recip_g.
    apply Rgt_lt ; rewrite <- f_recip_g.
    unfold comp ; apply f_incr ; [apply g_ok | apply g_ok |] ; assumption.
    assumption.
    assumption.
   apply False_ind ; apply Rlt_irrefl with x ; apply Rlt_trans with y ; assumption.
   assert (Hf : x = y).
    unfold reciprocal_interval, id in f_recip_g ; rewrite <- f_recip_g.
    symmetry ; rewrite <- f_recip_g.
    unfold comp ; rewrite F ; reflexivity.
    assumption.
    assumption.
   rewrite Hf in x_lt_y ; elim (Rlt_irrefl _ x_lt_y).
Qed.


Lemma strictly_increasing_reciprocal_interval_comm : forall f g lb ub,
       strictly_increasing_interval f lb ub ->
       reciprocal_interval f g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) ->
       (forall x, interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) x -> interval lb ub (g x)) ->
       reciprocal_interval g f lb ub.
Proof.
intros f g lb ub f_incr f_recip_g g_right x x_in_I ;
 assert (f_mono : strictly_monotonous_interval f lb ub) by (left ; assumption) ;
 assert (f_inj := strictly_monotonous_injective_interval _ _ _ f_mono).
 assert (f_incr2 := strictly_increasing_increasing_interval _ _ _ f_incr).
 assert (Hrew : forall x, lb <= x <= ub -> f (g (f x)) = f x).
  intros x0 x0_encad ;
   assert (fx0_encad : interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) (f x0)).
   split.
    apply Rle_trans with (f lb) ; [apply Rmin_l | apply f_incr2].
     split ; [right ; reflexivity | apply Rle_trans with x0 ; intuition].
     assumption.
     intuition.
    apply Rle_trans with (f ub) ; [apply f_incr2 | apply RmaxLess2].
     assumption.
     split ; [apply Rle_trans with x0 ; intuition | right ; reflexivity].
     intuition.
  apply f_recip_g ; assumption.
  assert (fx_encad : interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) (f x)).
 split ; unfold interval in x_in_I.
   apply Rle_trans with (f lb) ; [apply Rmin_l | apply f_incr2].
    split ; [right ; reflexivity | apply Rle_trans with x ; intuition].
    assumption.
    intuition.
    apply Rle_trans with (f ub) ; [apply f_incr2 | apply RmaxLess2].
    assumption.
    split ; [apply Rle_trans with x ; intuition | right ; reflexivity].
    intuition.
apply f_inj.
 apply g_right.
    assumption.
    assumption.
    apply f_recip_g.
    assumption.
Qed.

Lemma strictly_increasing_reciprocal_interval_comm2 : forall f g lb ub,
       lb < ub ->
       strictly_increasing_interval f lb ub ->
       reciprocal_interval f g (f lb) (f ub) ->
       (forall x, interval (f lb) (f ub) x -> interval lb ub (g x)) ->
       reciprocal_interval g f lb ub.
Proof.
intros f g lb ub lb_lt_ub f_incr f_recip_g g_right.
 assert (flb_lt_fub : f lb < f ub).
 apply f_incr ; [apply  interval_l | apply interval_r | assumption] ; left ; assumption.
 assert (Hrew_min : Rmin (f lb) (f ub) = f lb).
  unfold Rmin ; destruct (Rle_dec (f lb) (f ub)) ; intuition.
 assert (Hrew_max : Rmax (f lb) (f ub) = f ub).
  unfold Rmax ; destruct (Rle_dec (f lb) (f ub)) ; intuition.
 apply strictly_increasing_reciprocal_interval_comm ;
 try rewrite Hrew_min, Hrew_max ; assumption.
Qed.

Lemma strictly_decreasing_reciprocal_interval_comm : forall f g lb ub,
       strictly_decreasing_interval f lb ub ->
       reciprocal_interval f g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) ->
       (forall x, interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) x -> interval lb ub (g x)) ->
       reciprocal_interval g f lb ub.
Proof.
intros f g lb ub f_decr f_recip_g g_right x x_in_I ;
 assert (f_mono : strictly_monotonous_interval f lb ub) by (right ; assumption) ;
 assert (f_inj := strictly_monotonous_injective_interval _ _ _ f_mono).
 assert (f_decr2 := strictly_decreasing_decreasing_interval _ _ _ f_decr).
 assert (Hrew : forall x, lb <= x <= ub -> f (g (f x)) = f x).
  intros x0 x0_encad ;
   assert (fx0_encad : interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) (f x0)).
   split.
    apply Rle_trans with (f ub) ; [apply Rmin_r | apply f_decr2].
     assumption.
     split ; [apply Rle_trans with x0 ; intuition | right ; reflexivity].
     intuition.
    apply Rle_trans with (f lb) ; [apply f_decr2 | apply RmaxLess1].
     split ; [right ; reflexivity | apply Rle_trans with x0 ; intuition].
     assumption.
     intuition.
  apply f_recip_g ; assumption.
  assert (fx_encad : interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) (f x)).
 split ; unfold interval in x_in_I.
   apply Rle_trans with (f ub) ; [apply Rmin_r | apply f_decr2].
     assumption.
     split ; [apply Rle_trans with x ; intuition | right ; reflexivity].
     intuition.
    apply Rle_trans with (f lb) ; [apply f_decr2 | apply RmaxLess1].
     split ; [right ; reflexivity | apply Rle_trans with x ; intuition].
     assumption.
     intuition.
apply f_inj.
 apply g_right.
    assumption.
    assumption.
    apply f_recip_g.
    assumption.
Qed.

Lemma strictly_monotonous_reciprocal_interval_comm : forall f g lb ub,
       strictly_monotonous_interval f lb ub ->
       reciprocal_interval f g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) ->
       (forall x, interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) x -> interval lb ub (g x)) ->
       reciprocal_interval g f lb ub.
Proof.
intros f g lb ub f_mono f_recip_g g_right ;
 destruct f_mono ;
 [apply strictly_increasing_reciprocal_interval_comm |
 apply strictly_decreasing_reciprocal_interval_comm] ; assumption.
Qed.

Lemma reciprocal_opp_compat_interval : forall f g lb ub,
       reciprocal_interval f g lb ub ->
       reciprocal_interval (fun x =>f(-x)) (-g)%F lb ub.
Proof.
intros f g lb ub f_recip_g x x_in_I.
 unfold comp, opp_fct ; simpl ; rewrite Ropp_involutive ;
 apply f_recip_g ; assumption.
Qed.

Lemma reciprocal_opp_compat_interval2 : forall f g lb ub,
       reciprocal_interval f g lb ub ->
       reciprocal_interval (-f)%F (fun x => g (-x)) (-ub) (-lb).
Proof.
intros f g lb ub f_recip_g x x_in_I.
 unfold comp.
 replace ((- f)%F (g (- x))) with (- (comp f g) (-x)).
 rewrite f_recip_g.
 unfold id ; ring.
 unfold interval in * ; destruct x_in_I.
 split ; fourier.
 reflexivity.
Qed.

Lemma strictly_increasing_interval_image : forall f lb ub b,
       lb <= ub -> increasing_interval f lb ub ->
       interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) b ->
       interval (f lb) (f ub) b.
Proof.
intros f lb ub b lb_le_ub f_incr b_bd.
 assert (Hf : f lb <= f ub).
   apply f_incr.
   split ; [right ; reflexivity | apply lb_le_ub].
   split ; [apply lb_le_ub | right ; reflexivity].
   assumption.
 split.
 apply Rle_trans with (Rmin (f lb) (f ub)).
  right ; unfold Rmin ; destruct (Rle_dec (f lb) (f ub)) as [flb_le_fub | fub_lt_flb].
  reflexivity.
  elim (fub_lt_flb Hf).
  unfold interval in b_bd ; intuition.
 apply Rle_trans with (Rmax (f lb) (f ub)).
   unfold interval in b_bd ; intuition.
  right ; unfold Rmax ; destruct (Rle_dec (f lb) (f ub)) as [flb_le_fub | fub_lt_flb].
  reflexivity.
  elim (fub_lt_flb Hf).
Qed.

Lemma strictly_increasing_open_interval_image : forall f lb ub b,
       lb <= ub -> increasing_interval f lb ub ->
       open_interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) b ->
       open_interval (f lb) (f ub) b.
Proof.
intros f lb ub b lb_le_ub f_incr b_bd.
 assert (Hf : f lb <= f ub).
   apply f_incr.
   split ; [right ; reflexivity | apply lb_le_ub].
   split ; [apply lb_le_ub | right ; reflexivity].
   assumption.
 split.
 apply Rle_lt_trans with (Rmin (f lb) (f ub)).
  right ; unfold Rmin ; destruct (Rle_dec (f lb) (f ub)) as [flb_le_fub | fub_lt_flb].
  reflexivity.
  elim (fub_lt_flb Hf).
  unfold open_interval in b_bd ; intuition.
  apply Rlt_le_trans with (Rmax (f lb) (f ub)).
   unfold open_interval in b_bd ; intuition.
   right ; unfold Rmax ; destruct (Rle_dec (f lb) (f ub)) as [flb_le_fub | fub_lt_flb].
  reflexivity.
  elim (fub_lt_flb Hf).
Qed.

Lemma pr_nu_var2_interv : forall (f g : R -> R) (lb ub x : R) (pr1 : derivable_pt f x)
       (pr2 : derivable_pt g x),
       open_interval lb ub x ->
       (forall h : R, lb < h < ub -> f h = g h) ->
       derive_pt f x pr1 = derive_pt g x pr2.
Proof.
intros f g lb ub x Prf Prg x_encad local_eq.
assert (forall x l, lb < x < ub -> (derivable_pt_abs f x l <-> derivable_pt_abs g x l)).
 intros a l a_encad.
 unfold derivable_pt_abs, derivable_pt_lim.
 split.
 intros Hyp eps eps_pos.
 elim (Hyp eps eps_pos) ; intros delta Hyp2.
 assert (Pos_cond : Rmin delta (Rmin (ub - a) (a - lb)) > 0).
  clear-a lb ub a_encad delta.
  apply Rmin_pos ; [exact (delta.(cond_pos)) | apply Rmin_pos ] ; apply Rlt_Rminus ; intuition.
 exists (mkposreal (Rmin delta (Rmin (ub - a) (a - lb))) Pos_cond).
 intros h h_neq h_encad.
 replace (g (a + h) - g a) with (f (a + h) - f a).
 apply Hyp2 ; intuition.
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))).
 assumption. apply Rmin_l.
 assert (local_eq2 : forall h : R, lb < h < ub -> - f h = - g h).
  intros ; apply Ropp_eq_compat ; intuition.
 rewrite local_eq ; unfold Rminus. rewrite local_eq2. reflexivity.
 assumption.
 assert (Sublemma2 : forall x y, Rabs x < Rabs y -> y > 0 -> x < y).
  intros m n Hyp_abs y_pos. apply Rlt_le_trans with (r2:=Rabs n).
   apply Rle_lt_trans with (r2:=Rabs m) ; [ | assumption] ; apply RRle_abs.
   apply Req_le ; apply Rabs_right ; apply Rgt_ge ; assumption.
 split.
 assert (Sublemma : forall x y z, -z < y - x -> x < y + z).
  intros ; fourier.
 apply Sublemma.
 apply Sublemma2. rewrite Rabs_Ropp.
 apply Rlt_le_trans with (r2:=a-lb) ; [| apply RRle_abs] ;
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 assert (Sublemma : forall x y z, y < z - x -> x + y < z).
  intros ; fourier.
 apply Sublemma.
 apply Sublemma2.
 apply Rlt_le_trans with (r2:=ub-a) ; [| apply RRle_abs] ;
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_l] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_l] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 intros Hyp eps eps_pos.
 elim (Hyp eps eps_pos) ; intros delta Hyp2.
 assert (Pos_cond : Rmin delta (Rmin (ub - a) (a - lb)) > 0).
  clear-a lb ub a_encad delta.
  apply Rmin_pos ; [exact (delta.(cond_pos)) | apply Rmin_pos ] ; apply Rlt_Rminus ; intuition.
 exists (mkposreal (Rmin delta (Rmin (ub - a) (a - lb))) Pos_cond).
 intros h h_neq h_encad.
 replace (f (a + h) - f a) with (g (a + h) - g a).
 apply Hyp2 ; intuition.
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))).
 assumption. apply Rmin_l.
 assert (local_eq2 : forall h : R, lb < h < ub -> - f h = - g h).
  intros ; apply Ropp_eq_compat ; intuition.
 rewrite local_eq ; unfold Rminus. rewrite local_eq2. reflexivity.
 assumption.
 assert (Sublemma2 : forall x y, Rabs x < Rabs y -> y > 0 -> x < y).
  intros m n Hyp_abs y_pos. apply Rlt_le_trans with (r2:=Rabs n).
   apply Rle_lt_trans with (r2:=Rabs m) ; [ | assumption] ; apply RRle_abs.
   apply Req_le ; apply Rabs_right ; apply Rgt_ge ; assumption.
 split.
 assert (Sublemma : forall x y z, -z < y - x -> x < y + z).
  intros ; fourier.
 apply Sublemma.
 apply Sublemma2. rewrite Rabs_Ropp.
 apply Rlt_le_trans with (r2:=a-lb) ; [| apply RRle_abs] ;
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 assert (Sublemma : forall x y z, y < z - x -> x + y < z).
  intros ; fourier.
 apply Sublemma.
 apply Sublemma2.
 apply Rlt_le_trans with (r2:=ub-a) ; [| apply RRle_abs] ;
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_l] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_l] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 unfold derivable_pt in Prf.
  unfold derivable_pt in Prg.
  elim Prf; intros.
  elim Prg; intros.
  assert (Temp := p); rewrite H in Temp.
  unfold derivable_pt_abs in p.
  unfold derivable_pt_abs in p0.
  simpl in |- *.
  apply (uniqueness_limite g x x0 x1 Temp p0).
  assumption.
Qed.