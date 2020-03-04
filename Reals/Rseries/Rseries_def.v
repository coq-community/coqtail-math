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

(** Common definitions of real series, based on real sequences definitions. *)

Require Import Reals.
Require Import Rsequence_def.
Local Open Scope R_scope.
Local Open Scope Rseq_scope.

Implicit Type Un : Rseq.
(** printing ~	~ *)
(** * Convergence of series *)

Definition Rser_cv Un := Rseq_cv (Rseq_sum Un).

Definition Rser_abs_cv Un := Rseq_cv (Rseq_sum (|Un|)).

Definition Rser_cv_pos_infty Un := Rseq_cv_pos_infty (Rseq_sum Un).

Definition Rser_cv_neg_infty Un := Rseq_cv_neg_infty (Rseq_sum Un).

(** * Bounds *)

Definition Rser_bound_max Un := Rseq_bound_max (Rseq_sum Un).
Definition Rser_bound_min Un := Rseq_bound_min (Rseq_sum Un).
Definition Rser_bound Un := Rseq_bound (Rseq_sum Un).
Definition Rser_abs_bound Un := Rseq_bound (Rseq_sum (|Un|)).

(** * Remainders of series *)

Definition Rser_rem (Un : Rseq) (l : R) (Hcv : Rser_cv Un l) (n : nat) :=  (l - (Rseq_sum Un n))%R.
