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

Open Local Scope R_scope.

(** * Definitions *)

(** General term of a Power Serie and its absolute value *)
Definition gt_Pser (An : nat -> R) (x : R) := fun (n:nat) => (An n) * (x ^ n).

Definition gt_abs_Pser (An : nat -> R) (x : R) := fun (n:nat) => Rabs(An n * x ^ n).

Definition An_deriv (An:nat -> R) := fun n => INR (S n) * An (S n).

Definition gt_deriv_Pser (An : nat -> R) (x : R) := gt_Pser (An_deriv An) x.

Definition Pser_abs (An : nat -> R) (x l: R) := 
    Pser (fun n : nat => Rabs (An n)) (Rabs x) l.

(** Lower bound on the cv radius *)

Definition Cv_radius_weak (An : nat -> R) (r:R) := has_ub (gt_abs_Pser An r).

(** Cv radius definition *)

Definition finite_cv_radius (An : nat -> R) (r:R) := 
    (forall r', 0 <= r' < r -> Cv_radius_weak An r') /\
    (forall r', r < r' -> ~ (Cv_radius_weak An r')).

Definition infinite_cv_radius (An : Rseq) := forall (r : R), Cv_radius_weak An r.
