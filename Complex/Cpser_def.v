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

Require Import Csequence_def.
Require Import Cpow.

Local Open Scope C_scope.
Local Open Scope Cseq_scope.

(** * Definitions *)

(** General term of a Power Serie and its absolute value *)
Definition gt_pser An z := Cseq_mult An (Cpow z).
Definition gt_norm_pser An z := | gt_pser An z |.

(** Formal derivative *)
Definition An_deriv An := Cseq_shift (INC * An).
Definition gt_deriv_pser An z := gt_pser (An_deriv An) z.

Definition Cpser An z l := Cseq_cv (Cseq_sum (gt_pser An z)) l.
Definition Cpser_norm An z l := Cseq_cv (Cseq_sum (gt_norm_pser An z)) l.

(** Lower bound on the cv radius *)

Definition Cv_radius_weak An r := has_ub (gt_norm_pser An (IRC r)).

(** Cv radius definition *)

Definition finite_cv_radius An r := 
    (forall r', 0 <= r' < r -> Cv_radius_weak An r') /\
    (forall r', r < r' -> ~ (Cv_radius_weak An r')).

Definition infinite_cv_radius An := forall r, Cv_radius_weak An r.


Ltac unfold_gt := unfold gt_norm_pser, gt_pser, Cseq_norm, Cseq_mult.