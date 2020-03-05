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

(** Common definitions of real functions sequences. *)
Require Import Reals.
Require Import Rsequence_def.

Declare Scope RFseq_scope.
Delimit Scope RFseq_scope with Rseq.

Local Open Scope R_scope.
Local Open Scope RFseq_scope.

Implicit Type n : nat.
Implicit Type fn gn : nat -> R -> R.
Implicit Type f g : R -> R.

(** * Morphism of functions on R -> R to sequences. *)

Definition RFseq_plus fn gn n := (fn n + gn n)%F.
Definition RFseq_mult fn gn n := (fn n * gn n)%F.
Definition RFseq_opp fn n := (fun x => Ropp (fn n x))%F.
Definition RFseq_inv fn n := (fun x => Rinv (fn n x))%F.

Infix "+" := RFseq_plus : RFseq_scope.
Infix "*" := RFseq_mult : RFseq_scope.
Notation "- u" := (RFseq_opp u) : RFseq_scope.
Notation "/ u" := (RFseq_inv u) : RFseq_scope.

Definition RFseq_minus fn gn n := (fn n - gn n)%F.
Definition RFseq_div fn gn n := (fn n / gn n)%F.

Infix "-" := RFseq_minus : RFseq_scope.
Infix "/" := RFseq_div : RFseq_scope.

(** * Convergence of functions sequences. *)

Definition RFseq_cv fn f := forall x, Rseq_cv (fun n => fn n x) (f x).
Definition RFseq_cv_interv fn f (lb ub : R) :=
  forall x, lb < x -> x < ub -> Rseq_cv (fun n => fn n x) (f x).

Definition RFseq_cvu fn f (x : R) (r : posreal) := forall eps : R, 0 < eps ->
  exists N : nat, forall n (y : R), (N <= n)%nat -> Boule x r y ->
  R_dist (fn n y) (f y) < eps.
