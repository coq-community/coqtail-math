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

Require Export Cbase Cfunctions.

Declare Scope Cseq_scope.
Delimit Scope Cseq_scope with Cseq.

Local Open Scope C_scope.
Local Open Scope Cseq_scope.

Definition Cseq := nat -> C.

Implicit Type n : nat.
Implicit Type z : C.
Implicit Type An Bn : Cseq.

(** * Morphism of functions on C to sequences. *)

Definition Cseq_constant z := (fun n => z).

Definition Cseq_add An Bn n := An n + Bn n.
Definition Cseq_mult An Bn n := An n * Bn n.
Definition Cseq_opp An n := Copp (An n).
Definition Cseq_inv An n := Cinv (An n).
Definition Cseq_sum := sum_f_C0.

Infix "+" := Cseq_add : Cseq_scope.
Infix "*" := Cseq_mult : Cseq_scope.
Notation "- u" := (Cseq_opp u) : Cseq_scope.
Notation "/ u" := (Cseq_inv u) : Cseq_scope.

Definition Cseq_minus An Bn n := An n - Bn n.
Definition Cseq_div An Bn n := An n / Bn n.
Definition Cseq_norm An n := Cnorm (An n).

Notation "'|' An '|'" := (Cseq_norm An) (at level 39, format "'|' An '|'") : Cseq_scope.
Infix "-" := Cseq_minus : Cseq_scope.
Infix "/" := Cseq_div : Cseq_scope.

Definition Cseq_shift An n := An (S n).
Definition Cseq_shifts An N n := An (N + n)%nat.

(** * Various properties. *)

Definition Cseq_eventually (P : Cseq -> Prop) (Un : Cseq) :=
  exists N, P (fun n => Un (N + n)%nat).

Definition Cseq_eventually2 (P : Cseq -> Cseq -> Prop) (Un Vn : Cseq) :=
  exists N, P (fun n => Un (N + n)%nat) (fun n => Vn (N + n)%nat).

Definition Cseq_neq_0 Un := forall n, Un n <> 0.

Definition Cseq_bound (Un:Cseq) (M:R) := forall n, Cnorm (Un n) <= M.

(** * Convergence of sequences. *)

Definition Cseq_cv Un l := forall eps, eps > 0 -> exists N,
 (forall n, (n >= N)%nat -> Cnorm (Un n - l) < eps).

Definition Cauchy_crit (Un : nat -> C) := forall eps : R,
 eps > 0 -> exists N : nat, forall n (m : nat),
 (n >= N)%nat -> (m >= N)%nat -> Cnorm (Un n - Un m) < eps.
