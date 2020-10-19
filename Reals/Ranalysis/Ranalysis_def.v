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

Require Import Rbase Rpower Lra.
Require Import Ranalysis1 Ranalysis2.
Require Import Rfunctions.
Require Import MyRIneq.
Require Import Rtopology.
Require Import Rinterval Rfunction_facts.

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

Definition continuity_pt_in (D : R -> Prop) f x := D x -> limit1_in f D (f x) x.
Definition continuity_in (D : R -> Prop) f := forall x, continuity_pt_in D f x.
Definition continuity_open_interval (lb ub : R) (f : R -> R) :=
  continuity_in (open_interval lb ub) f.
Definition continuity_interval (lb ub : R) (f : R -> R) :=
  continuity_in (interval lb ub) f.
Definition continuity_Rball (c r : R) (f : R -> R) :=
  continuity_in (Rball c r) f.

(** * (Re)defining the derivability predicate. *)

(** The usual definition of the derivability predicate is,
    contrary to the one of the continuity not modular at all.
    Here we define a derivability predicate based on the ideas
    used in the continuity definition.
    We can then now use this new definitions in specific cases
    (intervals, balls). **)

Definition growth_rate f x := (fun y => (f y - f x) / (y - x)).

Definition derivable_pt_lim_in D f x l := limit1_in (growth_rate f x) (D_x D x) l x.

Definition derivable_pt_in D f x := { l | derivable_pt_lim_in D f x l }.

Definition derivable_in (D : R -> Prop) f :=
  forall x, D x -> derivable_pt_in D f x.

Definition derivable_open_interval (lb ub : R) (f : R -> R) :=
  derivable_in (open_interval lb ub) f.

Definition derivable_interval (lb ub : R) (f : R -> R) :=
  derivable_in (interval lb ub) f.

Definition derivable_Rball (c r : R) (f : R -> R) :=
  derivable_in (Rball c r) f.

(** We can now define the appropriate projection (aka. derive functions). *)

Definition derive_pt_in D f x (pr : derivable_pt_in D f x) :=
match pr with | exist _ l _ => l end.

Definition derive_in D f (pr : derivable_in D f) x (Dx: D x) :=
  derive_pt_in D f x (pr x Dx).

Definition derive_open_interval lb ub f (pr : derivable_open_interval lb ub f) x :=
match in_open_interval_dec lb ub x with
  | left P  => derive_pt_in (open_interval lb ub) f x (pr x P)
  | right P => 0
end.

Definition derive_Rball c r f (pr : derivable_Rball c r f) x :=
match in_Rball_dec c r x with
  | left P  => derive_pt_in (Rball c r) f x (pr x P)
  | right P => 0
end.

(** * Generic notions (injective, surjective, increasing, reciprocal, etc.) *)

Definition injective_in D (f : R -> R) :=
  forall (x y : R), D x -> D y -> f x = f y -> x = y.
Definition surjective_in D (f : R -> R) := forall y, D y -> exists x, y = f x.

Definition increasing_in D f := forall x y, D x -> D y -> x <= y -> f x <= f y.
Definition decreasing_in D f := forall x y, D x -> D y -> x <= y -> f y <= f x.
Definition monotonous_in D f := { decreasing_in D f } + { increasing_in D f }.
Definition strictly_increasing_in D f := forall x y, D x -> D y -> x < y -> f x < f y.
Definition strictly_decreasing_in D f := forall x y, D x -> D y -> x < y -> f y < f x.
Definition strictly_monotonous_in D f :=
 { strictly_decreasing_in D f } + { strictly_increasing_in D f }.

Definition reciprocal_in D (f g : R -> R) := forall x, D x -> f (g x) = x.

(** The interval case *)

Definition injective_interval (lb ub : R) (f : R -> R) := injective_in (interval lb ub) f.
Definition surjective_interval (lb ub : R) (f : R -> R) := surjective_in (interval lb ub) f.

Definition increasing_interval (lb ub : R) (f : R -> R) := increasing_in (interval lb ub) f.
Definition decreasing_interval (lb ub : R) (f : R -> R) := decreasing_in (interval lb ub) f.
Definition monotonous_interval (lb ub : R) (f : R -> R) := monotonous_in (interval lb ub) f.

Definition strictly_increasing_interval (lb ub : R) (f : R -> R) :=
  strictly_increasing_in (interval lb ub) f.
Definition strictly_decreasing_interval (lb ub : R) (f : R -> R) :=
  strictly_decreasing_in (interval lb ub) f.
Definition strictly_monotonous_interval (lb ub : R) (f : R -> R) :=
  strictly_monotonous_in (interval lb ub) f.

Definition reciprocal_interval (lb ub : R) f g := reciprocal_in (interval lb ub) f g.

(** The open interval case *)

Definition injective_open_interval (lb ub : R) (f : R -> R) :=
  injective_in (open_interval lb ub) f.
Definition surjective_open_interval (lb ub : R) (f : R -> R) :=
  surjective_in (open_interval lb ub) f.

Definition increasing_open_interval (lb ub : R) (f : R -> R) := increasing_in (open_interval lb ub) f.
Definition decreasing_open_interval (lb ub : R) (f : R -> R) := decreasing_in (open_interval lb ub) f.
Definition monotonous_open_interval (lb ub : R) (f : R -> R) := monotonous_in (open_interval lb ub) f.

Definition strictly_increasing_open_interval (lb ub : R) (f : R -> R) :=
  strictly_increasing_in (open_interval lb ub) f.
Definition strictly_decreasing_open_interval (lb ub : R) (f : R -> R) :=
  strictly_decreasing_in (open_interval lb ub) f.
Definition strictly_monotonous_open_interval (lb ub : R) (f : R -> R) :=
  strictly_monotonous_in (open_interval lb ub) f.

Definition reciprocal_open_interval (lb ub : R) f g := reciprocal_in (open_interval lb ub) f g.

(** The whole real line case *)

Definition injective (f : R -> R) := injective_in whole_R f.
Definition surjective (f : R -> R) := surjective_in whole_R f.
Definition bijective (f : R -> R) := injective f /\ surjective f.

Definition increasing (f : R -> R) := increasing_in whole_R f.
Definition decreasing (f : R -> R) := decreasing_in whole_R f.
Definition monotonous (f : R -> R) := monotonous_in whole_R f.

Definition strictly_increasing (f : R -> R) := strictly_increasing_in whole_R f.
Definition strictly_decreasing (f : R -> R) := strictly_decreasing_in whole_R f.
Definition strictly_monotonous (f : R -> R) := strictly_monotonous_in whole_R f.

Definition reciprocal f g := reciprocal_in whole_R f g.
