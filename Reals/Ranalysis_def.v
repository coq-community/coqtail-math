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

Local Open Scope R_scope.

(** * Basic notions *)

Definition open_interval (lb ub x:R) := lb < x < ub.
Definition interval (lb ub x:R) := lb <= x <= ub.

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

Definition reciprocal (f g:R -> R) := forall x, (comp f g) x = id x.

(** Manipulation *)

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