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

Require Import Cbase.
Require Import Cprop_base.
Require Import Cfunctions.
Require Export Cmet.
Require Import Cderiv.

Local Open Scope C_scope.

Implicit Type f : C -> C.

Definition plus_fct f1 f2 (x:C) : C := f1 x + f2 x.
Definition opp_fct f (x:C) : C := - f x.
Definition mult_fct f1 f2 (x:C) : C := f1 x * f2 x.
Definition mult_real_fct (a:C) f (x:C) : C := a * f x.
Definition minus_fct f1 f2 (x:C) : C := f1 x - f2 x.
Definition div_fct f1 f2 (x:C) : C := f1 x / f2 x.
Definition div_real_fct (a:C) f (x:C) : C := a / f x.
Definition comp f1 f2 (x:C) : C := f1 (f2 x).
Definition inv_fct f (x:C) : C := / f x.
Definition constant f : Prop := forall x y, f x = f y.

Declare Scope Cfun_scope.
Delimit Scope Cfun_scope with F.

Arguments plus_fct f1%Cfun_scope f2%Cfun_scope x%C_scope.
Arguments mult_fct f1%Cfun_scope f2%Cfun_scope x%C_scope.
Arguments minus_fct f1%Cfun_scope f2%Cfun_scope x%C_scope.
Arguments div_fct f1%Cfun_scope f2%Cfun_scope x%C_scope.
Arguments inv_fct f%Cfun_scope x%C_scope.
Arguments opp_fct f%Cfun_scope x%C_scope.
Arguments mult_real_fct a%C_scope f%Cfun_scope x%C_scope.
Arguments div_real_fct a%C_scope f%Cfun_scope x%C_scope.
Arguments comp f1%Cfun_scope f2%Cfun_scope x%C_scope.

Infix "+" := plus_fct : Cfun_scope.
Notation "- x" := (opp_fct x) : Cfun_scope.
Infix "*" := mult_fct : Cfun_scope.
Infix "-" := minus_fct : Cfun_scope.
Infix "/" := div_fct : Cfun_scope.
Local Notation "f1 'o' f2" := (comp f1 f2) (at level 20, right associativity) : Cfun_scope.
Notation "/ x" := (inv_fct x) : Cfun_scope.

Definition fct_cte (a x:C) : C := a.
Definition id (x:C) := x.

Definition no_cond (x:C) : Prop := True.

(**********)
Definition constant_D_eq f (D:C -> Prop) (c:C) : Prop :=
  forall x:C, D x -> f x = c.

(***************************************************)
(** *    Definition of continuity as a limit       *)
(***************************************************)

(**********)
Definition continuity_pt f (z:C) : Prop := continue_in f no_cond z.
Definition continuity f : Prop := forall x:C, continuity_pt f x.
Definition continuity_along_axis_pt f v x := forall eps:R, eps > 0 ->
 exists delta:posreal, forall h:R, Rabs h < delta ->
 dist C_met (f (x + h * v)) (f x) < eps.

Arguments continuity_pt f%Cfun_scope z%C_scope.
Arguments continuity_along_axis_pt f%Cfun_scope v%C_scope x%C_scope.
Arguments continuity f%Cfun_scope.


Definition growth_rate f x := (fun y => (f y - f x) / (y - x)).

(*****************************************************)
(** * Derivative's definition using Landau's kernel  *)
(*****************************************************)

Definition derivable_pt_lim f (x l : C) : Prop := forall eps:R, 0 < eps ->
    exists delta : posreal, forall h : C, h <> 0 ->
    Cnorm h < delta -> Cnorm ((f (x + h) - f x) / h - l) < eps.

Definition derivable_pt_abs f x l : Prop := derivable_pt_lim f x l.

Definition derivable_pt f x := { l | derivable_pt_abs f x l }.
Definition derivable f := forall x, derivable_pt f x.

Definition derive_pt f x (pr:derivable_pt f x) := proj1_sig pr.
Definition derive f (pr:derivable f) x := derive_pt f x (pr x).

Arguments derivable_pt_lim f%Cfun_scope x%C_scope l%C_scope.
Arguments derivable_pt_abs f%Cfun_scope x%C_scope l%C_scope.
Arguments derivable_pt f%Cfun_scope x%C_scope.
Arguments derivable f%Cfun_scope.
Arguments derive_pt f%Cfun_scope x%C_scope pr.
Arguments derive f%Cfun_scope pr x.


(*****************************************************)
(** * Differentiability *)
(*****************************************************)

Definition differentiable_pt_lim f (x v l : C) : Prop := v <> 0 -> forall eps:R, 0 < eps ->
    exists delta:posreal, forall h:R, h <> 0%R ->
    Rabs h < delta -> Cnorm ((f (x + h*v) - f x) / (h*v) - l) < eps.

Definition differentiable_pt_abs f x v l : Prop := differentiable_pt_lim f x v l.

Definition differentiable_pt f x v := { l | differentiable_pt_abs f x v l }.
Definition differentiable f v := forall x, differentiable_pt f x v.
Definition fully_differentiable_pt f x := forall v, differentiable_pt f x v.
Definition fully_differentiable f := forall v, differentiable f v.

Definition differential_pt f x v (pr:differentiable_pt f x v) := proj1_sig pr.
Definition differential f v (pr:differentiable f v) x := differential_pt f x v (pr x).

Arguments differentiable_pt_lim f%Cfun_scope (x v l)%C_scope .
Arguments differentiable_pt_abs f%Cfun_scope (x v l)%C_scope.
Arguments differentiable_pt f%Cfun_scope (x v)%C_scope.
Arguments differentiable f%Cfun_scope v%C_scope.
Arguments fully_differentiable_pt f%Cfun_scope x%C_scope.
Arguments fully_differentiable f%Cfun_scope.
Arguments differential_pt f%Cfun_scope x%C_scope v%C_scope pr.
Arguments differential f%Cfun_scope v%C_scope pr x%C_scope.
