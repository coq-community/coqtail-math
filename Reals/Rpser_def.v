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

Require Export MyReals.
Require Import Rsequence_def.

Local Open Scope Rseq_scope.

(** * Definitions *)

(** General term of a Power Serie and its absolute value *)

Definition gt_pser An x := An * (pow x).
Definition gt_abs_pser An x := | gt_pser An x |.

(** Formal derivative. *)

Definition An_deriv An := Rseq_shift (INR * An).
Definition An_nth_deriv An k := Rseq_shifts (Rseq_fact * An) k / Rseq_fact.
Definition An_expand An l := (Rseq_pow l * An).

Definition gt_deriv_Pser An x := gt_pser (An_deriv An) x.
Definition gt_nth_deriv_Pser An k x := gt_pser (An_nth_deriv An k) x.

(** Partial sums and convergence predicates. *)

Definition Rseq_pps An x := Rseq_sum (gt_pser An x).
Definition Rseq_pps_abs An x := Rseq_sum (gt_abs_pser An x).
Definition Rpser An x l := Rseq_cv (Rseq_pps An x) l.
Definition Rpser_abs An x l := Rseq_cv (Rseq_pps_abs An x) l.

(** Lower bound on the cv radius *)

Definition Cv_radius_weak An r := has_ub (gt_abs_pser An r).

(** Cv radius definition *)

Definition finite_cv_radius An r := 
    (forall r', 0 <= r' < r -> Cv_radius_weak An r') /\
    (forall r', r < r' -> ~ (Cv_radius_weak An r')).

Definition infinite_cv_radius An := forall r, Cv_radius_weak An r.