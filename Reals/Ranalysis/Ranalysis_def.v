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

Require Import Rbase Rpower Fourier.
Require Import Ranalysis1 Ranalysis2.
Require Import Rfunctions.
Require Import MyRIneq.
Require Import Rtopology.
Require Import Rinterval Rfunction_facts.

Require Import Ass_handling.

Local Open Scope R_scope.

Definition dense (D : R -> Prop) x := forall eps, 0 < eps ->
  exists y, D_x D x y /\ R_dist y x < eps.

(* Alternative definition. TODO: migrate code to it!
Definition continuity_open_interval (f : R -> R) (lb ub:R) :=
  forall x, open_interval lb ub x ->
  continue_in f (open_interval lb ub) x.
Definition continuity_interval (f : R -> R) (lb ub:R) :=
  forall x, interval lb ub x ->
  continue_in f (interval lb ub) x.
*)

Definition continue_pt_in f (D : R -> Prop) x := D x -> limit1_in f D (f x) x.
Definition continue_in f (D : R -> Prop) := forall x, continue_pt_in f D x.
Definition continuity_open_interval (f : R -> R) (lb ub:R) :=
  continue_in f (open_interval lb ub).
Definition continuity_interval (f : R -> R) (lb ub:R) :=
  continue_in f (interval lb ub).
Definition continuity_Rball (f : R -> R) (c r : R) (r_pos : 0 <= r) :=
  continue_in f (Rball c r r_pos).

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

(* Notions of variations *)

Definition injective_interval (f : R -> R) (lb ub:R) := forall (x y:R),
      interval lb ub x -> interval lb ub y -> f x = f y -> x = y.
Definition surjective_interval (f : R -> R) (lb ub:R) := forall y:R,
      interval lb ub y -> exists x:R, y = f x.

Definition injective_open_interval (f : R -> R) (lb ub:R) := forall (x y:R),
      open_interval lb ub x -> open_interval lb ub y -> f x = f y -> x = y.
Definition surjective_open_interval (f : R -> R) (lb ub:R) := forall y:R,
      open_interval lb ub y -> exists x:R, y = f x.

Definition injective (f : R -> R) := forall (x y:R), f x = f y -> x = y.
Definition surjective (f : R -> R) := forall y:R, exists x:R, y = f x.
Definition bijective (f : R -> R) := injective f /\ surjective f.

Definition strictly_increasing_interval (f : R -> R) (lb ub:R) := forall x y,
       interval lb ub x -> interval lb ub y -> x < y -> f x < f y.
Definition strictly_decreasing_interval (f : R -> R) (lb ub:R) := forall x y,
       interval lb ub x -> interval lb ub y -> x < y -> f y < f x.
Definition strictly_monotonous_interval (f : R -> R) (lb ub : R) :=
     {strictly_increasing_interval f lb ub} + {strictly_decreasing_interval f lb ub}.

Definition strictly_increasing_open_interval (f : R -> R) (lb ub:R) :=
  forall x y, open_interval lb ub x -> open_interval lb ub y -> x < y -> f x < f y.
Definition strictly_decreasing_open_interval (f : R -> R) (lb ub:R) :=
  forall x y, open_interval lb ub x -> open_interval lb ub y -> x < y -> f y < f x.
Definition strictly_monotonous_open_interval (f : R -> R) (lb ub : R) :=
  {strictly_increasing_open_interval f lb ub}
  + {strictly_decreasing_open_interval f lb ub}.

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
