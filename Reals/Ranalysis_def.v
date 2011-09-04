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
Require Import Ranalysis1.
Require Import Fourier.
Require Import Rfunctions.
Require Import MyRIneq.
Require Import Ranalysis2.
Require Import Rtopology.
Require Import Rinterval Rfunction_facts.

Require Import Ass_handling.

Local Open Scope R_scope.

(* Alternative definition. TODO: migrate code to it!
Definition continuity_open_interval (f : R -> R) (lb ub:R) :=
  forall x, open_interval lb ub x ->
  continue_in f (open_interval lb ub) x.
Definition continuity_interval (f : R -> R) (lb ub:R) :=
  forall x, interval lb ub x ->
  continue_in f (interval lb ub) x.
*)
Definition continuity_open_interval (f : R -> R) (lb ub:R) := forall x:R,
  open_interval lb ub x -> continue_in f (open_interval lb ub) x.
Definition continuity_interval (f : R -> R) (lb ub:R) := forall x:R,
  interval lb ub x -> continue_in f (interval lb ub) x.
Definition continuity_Rball (f : R -> R) (c r : R) (r_pos : 0 <= r) :=
  forall x, Rball c r r_pos x -> continue_in f (Rball c r r_pos) x.

Lemma continuity_continuity_Rball: forall c r r_pos f,
  continuity f -> continuity_Rball f c r r_pos.
Proof.
intros c r r_pos f f_cont x x_in eps eps_pos ;
 destruct (f_cont x _ eps_pos) as [delta [delta_pos Hdelta]] ;
 exists delta ; split ; [assumption | intros ; apply Hdelta].
 split ; [unfold no_cond, D_x ; split ; [trivial |] |] ; apply H.
Qed.

(** * (Re)defining the derivability predicate. *)

(** The usual definition of the derivability predicate is,
    contrary to the one of the continuity not modular at all.
    Here we define a derivability predicate based on the ideas
    used in the continuity definition.
    We can then now use this new definitions in specific cases
    (intervals, balls). **)

Definition growth_rate f x := (fun y => (f y - f x) / (y - x)).

Definition derivable_pt_lim_in f D x l := limit1_in (growth_rate f x) (D_x D x) l x.

Definition derivable_pt_in f D x := { l | derivable_pt_lim_in f D x l }.

Definition derivable_in f (D : R -> Prop) :=
  forall x, D x -> derivable_pt_in f D x.

Definition derivable_open_interval (f : R -> R) (lb ub:R) :=
  derivable_in f (open_interval lb ub).

Definition derivable_interval (f : R -> R) (lb ub:R) :=
  derivable_in f (interval lb ub).

Definition derivable_Rball (f : R -> R) (c r : R) (r_pos : 0 <= r) :=
  derivable_in f (Rball c r r_pos).

Lemma derivable_pt_lim_open_interval_Rball: forall f x c r r_pos l,
  derivable_pt_lim_in f (open_interval (c - r) (c + r)) x l ->
  derivable_pt_lim_in f (Rball c r r_pos) x l.
Proof.
intros f x c r r_pos l Hl eps eps_pos ;
 destruct (Hl _ eps_pos) as [delta [delta_pos Hdelta]] ;
 exists delta ; split ; [assumption |].
 intros y [[y_in y_neq] y_bd] ; apply Hdelta ; split ;
 [split ; [eapply Rball_interval |] |] ; eassumption.
Qed.

Lemma derivable_pt_lim_Rball_open_interval: forall f x c r r_pos l,
  derivable_pt_lim_in f (Rball c r r_pos) x l ->
  derivable_pt_lim_in f (open_interval (c - r) (c + r)) x l.
Proof.
intros f x lb ub pr l Hl eps eps_pos ;
 destruct (Hl _ eps_pos) as [delta [delta_pos Hdelta]] ;
 exists delta ; split ; [assumption |].
 intros y [[y_in y_neq] y_bd] ; apply Hdelta ; split ;
 [split ; [eapply interval_Rball |] |] ; eassumption.
Qed.

Lemma derivable_open_interval_Rball: forall f c r r_pos,
  derivable_open_interval f (c - r) (c + r) ->
  derivable_Rball f c r r_pos.
Proof.
intros f c r r_pos Hoi x x_in ;
 destruct (Hoi x (Rball_interval _ _ _ _ x_in)) as [l Hl] ;
 exists l ; apply derivable_pt_lim_open_interval_Rball, Hl.
Qed.

Lemma derivable_Rball_open_interval: forall f c r r_pos,
  derivable_Rball f c r r_pos ->
  derivable_open_interval f (c - r) (c + r).
Proof.
intros f c r r_pos Hoi x x_in ;
 destruct (Hoi x (interval_Rball _ _ _ _ x_in)) as [l Hl] ;
 exists l ; eapply derivable_pt_lim_Rball_open_interval, Hl.
Qed.

(** This new definition is obviously related to the old one. *)

Lemma derivable_pt_lim_derivable_pt_lim_in: forall f D x l,
  derivable_pt_lim f x l -> derivable_pt_lim_in f D x l.
Proof.
intros f D x l Hl eps eps_pos ; destruct (Hl _ eps_pos) as [delta Hdelta] ;
 exists delta ; split.
  apply delta.
  intros y [[Dy xny] xy_bd] ; simpl ; unfold R_dist, growth_rate ;
   replace (f y) with (f (x + (y - x))) by (f_equal ; ring) ; apply Hdelta.
   intro Hf ; apply xny ; revert Hf ; clear ; intuition.
   apply xy_bd.
Qed.

Lemma derivable_pt_derivable_pt_in: forall f D x,
  derivable_pt f x -> derivable_pt_in f D x.
Proof.
intros f D x [l Hl] ; exists l ;
 apply derivable_pt_lim_derivable_pt_lim_in ;
 assumption.
Qed.

Lemma derivable_derivable_in : forall f D,
  derivable f -> derivable_in f D.
Proof.
intros f D Hf x Dx ; apply derivable_pt_derivable_pt_in, Hf.
Qed.

(** In specific cases we can come back from the specific case to the one
    with no limitation. *)

Lemma derivable_pt_lim_open_interval_derivable_pt_lim: forall f lb ub x l,
  open_interval lb ub x -> derivable_pt_lim_in f (open_interval lb ub) x l ->
  derivable_pt_lim f x l.
Proof.
intros f lb ub x l pr Hl eps eps_pos ; destruct (Hl _ eps_pos) as [d [d_pos Hd]] ;
 simpl in Hd ; unfold R_dist in Hd.
 pose (delta := Rmin (interval_dist lb ub x) d).
 assert (delta_pos : 0 < delta).
  apply Rmin_pos_lt ; [apply open_interval_dist_pos |] ; assumption.
 exists (mkposreal _ delta_pos) ; intros h h_neq h_bd ;
 specify Hd (x + h) ; unfold growth_rate in * ;
 replace (x + h - x) with h in Hd by ring ; apply Hd ; split.
  split.
   apply interval_dist_bound ; [| eapply Rlt_le_trans ;
   [| eapply Rmin_l]] ; eassumption.
   clear -h_neq ; intro Hf ; apply h_neq, Rplus_eq_reg_l with x ;
   rewrite <- Hf ; ring.
  eapply Rlt_le_trans ; [eassumption | eapply Rmin_r].
Qed.

Lemma derivable_pt_lim_Rball_derivable_pt_lim: forall f c r r_pos x l,
  Rball c r r_pos x -> derivable_pt_lim_in f (Rball c r r_pos) x l ->
  derivable_pt_lim f x l.
Proof.
intros ; eapply derivable_pt_lim_open_interval_derivable_pt_lim ;
 [eapply Rball_interval | eapply derivable_pt_lim_Rball_open_interval] ;
 eassumption.
Qed.

Lemma derivable_open_interval_derivable_pt: forall f lb ub,
  derivable_open_interval f lb ub ->
  forall x, open_interval lb ub x -> derivable_pt f x.
Proof.
intros f lb ub H x Dx ; destruct (H x Dx) as [l Hl] ;
 exists l ; eapply derivable_pt_lim_open_interval_derivable_pt_lim ;
 eassumption.
Qed.

Lemma derivable_Rball_derivable_pt: forall f c r r_pos,
  derivable_Rball f c r r_pos ->
  forall x, Rball c r r_pos x -> derivable_pt f x.
Proof.
intros ; eapply derivable_open_interval_derivable_pt ;
 [eapply derivable_Rball_open_interval | eapply Rball_interval] ;
 eassumption.
Qed.

(** This allows us to get back the unicity of the derivative. *)

Lemma derivable_pt_lim_open_interval_uniqueness: forall f lb ub x l l',
  open_interval lb ub x ->
  derivable_pt_lim_in f (open_interval lb ub) x l ->
  derivable_pt_lim_in f (open_interval lb ub) x l' ->
  l = l'.
Proof.
intros f lb ub x l l' x_in Hl Hl' ; eapply uniqueness_limite ;
 eapply derivable_pt_lim_open_interval_derivable_pt_lim ;
 eassumption.
Qed.

Lemma derivable_pt_lim_Rball_uniqueness: forall f c r r_pos x l l',
  Rball c r r_pos x ->
  derivable_pt_lim_in f (Rball c r r_pos) x l ->
  derivable_pt_lim_in f (Rball c r r_pos) x l' ->
  l = l'.
Proof.
intros f c r r_pos x l l' x_in Hl Hl' ; eapply uniqueness_limite ;
 eapply derivable_pt_lim_Rball_derivable_pt_lim ;
 eassumption.
Qed.

Lemma continuity_pt_continue_in: forall f (D : R -> Prop) x,
  D x -> continuity_pt f x -> continue_in f D x.
Proof.
intros f D x Dx Hf ; intros eps eps_pos ;
 destruct (Hf _ eps_pos) as [delta [delta_pos Hdelta]] ;
 exists delta ; split ; [| intros y [[y_in y_neq] y_bd]] ;
 [| apply Hdelta] ; repeat split ; assumption.
Qed.

Lemma derivable_Rball_continuity_Rball: forall c r r_pos f,
  derivable_Rball f c r r_pos ->
  continuity_Rball f c r r_pos.
Proof.
intros c r r_pos f Hf x x_in ;
 apply continuity_pt_continue_in ;
 [| eapply derivable_continuous_pt, derivable_Rball_derivable_pt] ;
 eassumption.
Qed.

(** We can now define the appropriate projection (aka. derive functions). *)

Definition derive_pt_in f D x (pr : derivable_pt_in f D x) :=
match pr with | exist l _ => l end.

Definition derive_in f D (pr : derivable_in f D) x (Dx: D x) :=
  derive_pt_in f D x  (pr x Dx).

Definition derive_open_interval f lb ub (pr : derivable_open_interval f lb ub) x :=
match in_open_interval_dec lb ub x with
  | left P  => derive_pt_in f (open_interval lb ub) x (pr x P)
  | right P => 0
end.

Definition derive_Rball f c r r_pos (pr : derivable_Rball f c r r_pos) x :=
match in_Rball_dec c r r_pos x with
  | left P  => derive_pt_in f (Rball c r r_pos) x (pr x P)
  | right P => 0
end.

(** Value of the derivative *)

Lemma derivable_pt_lim_derive_pt_Rball: forall f c r r_pos x l pr,
  Rball c r r_pos x ->
  derivable_pt_lim_in f (Rball c r r_pos) x l ->
  derive_pt_in f (Rball c r r_pos) x pr = l.
Proof.
intros f c r r_pos x l [l' Hl'] x_in  Hl ; simpl ;
 eapply derivable_pt_lim_Rball_uniqueness ;
 eassumption.
Qed.

Lemma derivable_pt_lim_derive_Rball: forall f c r r_pos x l pr,
  Rball c r r_pos x ->
  derivable_pt_lim_in f (Rball c r r_pos) x l ->
  derive_Rball f c r r_pos pr x = l.
Proof.
intros f c r r_pos x l pr x_in Hl ; unfold derive_Rball ;
 destruct (in_Rball_dec c r r_pos x) as [x_in2 | x_nin].
 apply derivable_pt_lim_derive_pt_Rball ; assumption.
 contradiction.
Qed.

(** Extensionality of the definitions *)

Lemma derivable_pt_lim_Rball_ext: forall f g c r r_pos,
  Rball_eq c r r_pos f g -> forall x l,
  Rball c r r_pos x ->
  derivable_pt_lim_in f (Rball c r r_pos) x l ->
  derivable_pt_lim_in g (Rball c r r_pos) x l.
Proof.
intros f g c r r_pos Heq x l x_in Hf eps eps_pos ;
 destruct (Hf _ eps_pos) as [delta [delta_pos Hdelta]] ;
 exists delta ; split.
  assumption.
  intros y [[Hy y_neq] y_bd] ; unfold growth_rate ; rewrite <- Heq, <- Heq ;
  [apply Hdelta ; repeat split | |] ; assumption.
Qed.

Lemma derivable_Rball_ext: forall f g c r r_pos,
  Rball_eq c r r_pos f g ->
  derivable_Rball f c r r_pos ->
  derivable_Rball g c r r_pos.
Proof.
intros f g c r r_pos heq Hf x x_in ;
 destruct (Hf _ x_in) as [l Hl] ; exists l ;
 eapply derivable_pt_lim_Rball_ext ; eassumption.
Qed.

Lemma derive_pt_in_Rball_ext: forall f g c r r_pos x
  (prf: derivable_pt_in f (Rball c r r_pos) x)
  (prg: derivable_pt_in g (Rball c r r_pos) x),
  Rball c r r_pos x ->
  Rball_eq c r r_pos f g ->
  derive_pt_in f (Rball c r r_pos) x prf =
  derive_pt_in g (Rball c r r_pos) x prg.
Proof.
intros f g c r r_pos x [l1 Hl1] [l2 Hl2] x_in Heq ; simpl ;
 eapply derivable_pt_lim_Rball_uniqueness ; [eassumption | | eassumption].
 eapply derivable_pt_lim_Rball_ext ; eassumption.
Qed.

Lemma derive_Rball_ext: forall f g c r r_pos
  (prf: derivable_Rball f c r r_pos)
  (prg: derivable_Rball g c r r_pos),
  Rball_eq c r r_pos f g ->
  derive_Rball f c r r_pos prf == derive_Rball g c r r_pos prg.
Proof.
intros f g c r r_pos prf prg Heq x ; unfold derive_Rball ;
 destruct (in_Rball_dec c r r_pos x) as [HT | HF].
 apply derive_pt_in_Rball_ext ; assumption.
 reflexivity.
Qed.

Lemma derive_derive_Rball: forall f c r r_pos pr pr',
  Rball_eq c r r_pos (derive f pr) (derive_Rball f c r r_pos pr').
Proof.
intros f c r r_pos pr pr' x x_in ; unfold derive_Rball ;
 destruct (in_Rball_dec c r r_pos x) as [HT | HF].
 destruct (pr' x HT) as [l Hl] ; simpl ; unfold derive ;
  rewrite derive_pt_eq ; eapply derivable_pt_lim_Rball_derivable_pt_lim ;
  eassumption.
 destruct (HF x_in).
Qed.

(** derivable PI *)

Lemma derivable_Rball_PI: forall (f : R -> R) (c r : R) (r_pos1 r_pos2 : 0 <= r),
  derivable_Rball f c r r_pos1 -> derivable_Rball f c r r_pos2.
Proof.
intros f c r r_pos1 r_pos2 Hdr x x_in ; apply Hdr ; rewrite Rball_PI ;
 eassumption.
Qed.


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

(*

Lemma derivable_in_continue_in : forall f I x,
    derivable_pt_in f I x -> continue_in f I x.
Proof.
intros f I x Hde.
 destruct Hde as (dx, Hder).
 eapply derivable_pt_lim_in_D_in in Hder.
 destruct Hder as (d, Hder).
  eapply cont_deriv; eassumption.
Qed.

Lemma derivable_continuous_open_interval : forall f lb ub,
	derivable_open_interval f lb ub -> continuity_open_interval f lb ub.
Proof.
intros f lb ub H x x_in.
 unfold derivable_open_interval in H. apply derivable_in_continue_in.
 apply H.
 apply x_in.
Qed.
*)

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
 apply Hx. apply Hx. apply Hx.
 destruct Hx as [[_ x_neq_b] Hxb]. intuition.
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
 apply Ropp_gt_lt_contravar. apply Hx.
 apply Ropp_gt_lt_contravar. apply Hx.
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
