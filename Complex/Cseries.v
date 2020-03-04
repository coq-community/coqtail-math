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

Require Export Complex.
Require Export Csequence.
Require Import Rsequence_def.
Local Open Scope C_scope.
Local Open Scope Cseq_scope.

(** * Convergence of series *)
Definition Cser_cv Un l := Cseq_cv (sum_f_C0 Un) l.

Definition Cser_abs_cv Un l := Rseq_cv (sum_f_R0 (fun n => Cnorm (Un n))) l.

Definition Cser_cv_infty Un := Rseq_cv_pos_infty (sum_f_R0 (fun n => Cnorm (Un n))).

(** * Bounds *)
Definition Cser_bound Un M := forall n, Cnorm (sum_f_C0 Un n) <= M.

Definition Cser_abs_bound Un M := forall n, sum_f_R0 (fun k => Cnorm (Un k)) n <= M.


(** * Remainders of series *)
Definition Cser_rem (Un : nat -> R) (l : R) (Hcv : Cser_cv Un l) (n : nat) := 
 (l - (sum_f_C0 Un n))%C.
