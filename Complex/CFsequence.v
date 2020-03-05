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
Require Import Cbase.
Require Import Cfunctions.
Require Import Csequence.
Require Import Canalysis_def.

Declare Scope CFseq_scope.
Delimit Scope CFseq_scope with Cseq_scope.

Local Open Scope C_scope.
Local Open Scope CFseq_scope.

Implicit Type n : nat.
Implicit Type fn gn : nat -> C -> C.
Implicit Type f g : C -> C.

(** * Morphism of functions on R -> R to sequences. *)

Definition CFseq_plus fn gn n := (fn n + gn n)%F.
Definition CFseq_mult fn gn n := (fn n * gn n)%F.
Definition CFseq_opp fn n := (fun x => Copp (fn n x))%F.
Definition CFseq_inv fn n := (fun x => Cinv (fn n x))%F.

Infix "+" := CFseq_plus : CFseq_scope.
Infix "*" := CFseq_mult : CFseq_scope.
Notation "- u" := (CFseq_opp u) : CFseq_scope.
Notation "/ u" := (CFseq_inv u) : CFseq_scope.

Definition CFseq_minus fn gn n := (fn n - gn n)%F.
Definition CFseq_div fn gn n := (fn n / gn n)%F.

Infix "-" := CFseq_minus : CFseq_scope.
Infix "/" := CFseq_div : CFseq_scope.

(** * Convergence of functions sequences. *)

Definition CFseq_cv fn f := forall x, Cseq_cv (fun n => fn n x) (f x).
Definition CFseq_cv_boule fn f (c : C) (r : posreal) := forall x,  Boule c r x -> Cseq_cv (fun n => fn n x) (f x).

Definition CFseq_cvu fn f (x : C) (r : posreal) := forall eps : R, 0 < eps ->
        exists N : nat, forall n (y : C), (N <= n)%nat -> Boule x r y ->
        C_dist (fn n y) (f y) < eps.

Definition CFpartial_sum (fn : nat -> C) N := sum_f_C0 fn N.
