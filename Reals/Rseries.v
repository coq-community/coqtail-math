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
Require Import Rsequence.
Open Local Scope R_scope.
Open Local Scope Rseq_scope.

Implicit Type Un : Rseq.

(** * Convergence of series *)

Definition Rser_cv Un l := Rseq_cv (sum_f_R0 Un) l.

Definition Rser_abs_cv Un l := Rseq_cv (sum_f_R0 (|Un|)) l.

Definition Rser_cv_pos_infty Un := Rseq_cv_pos_infty (sum_f_R0 Un).

Definition Rser_cv_neg_infty Un := Rseq_cv_neg_infty (sum_f_R0 Un).

(** * Bounds *)

Definition Rser_bound_max Un M := forall n, sum_f_R0 Un n <= M.

Definition Rser_bound_min Un m := forall n, m <= sum_f_R0 Un n.

Definition Rser_bound Un M := forall n, Rabs (sum_f_R0 Un n) <= M.

Definition Rser_abs_bound Un M := forall n, sum_f_R0 (fun k => Rabs (Un k)) n <= M.


(** * Remainders of series *)

Definition Rser_rem (Un : nat -> R) (l : R) (Hcv : Rser_cv Un l) (n : nat) :=  (l - (sum_f_R0 Un n))%R.
