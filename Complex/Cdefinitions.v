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

Require Export Reals.
Require Export Lra.

Open Scope R_scope.

(** ** Definition of C and basic operations over C *)

Definition C : Set := (prod R R).

Definition R_R_to_C (a : R) (b : R) : C := (a, b).

(* Scope for complex (taken from the reals one for coherence reasons)*)

Declare Scope C_scope.
Delimit Scope C_scope with C.

(* Automatically open scope C_scope for arguments of type C *)
Bind Scope C_scope with C.

Open Scope C_scope.

(** ** Basic definitions and notations *)

Definition C0 := R_R_to_C 0 0.
Definition C1 := R_R_to_C 1 0.
Definition Ci := R_R_to_C 0 1.

Notation "0" := C0.
Notation "1" := C1.

Definition Cre (z : C) : R :=
  let (r1, i1) := z in
  r1.

Definition Cim (z : C) : R :=
  let (r1, i1) := z in
  i1.

Definition Cadd (z1 : C) (z2 : C) : C :=
  R_R_to_C (Cre z1 + Cre z2) (Cim z1 + Cim z2).

Definition Cmult (z1 : C) (z2 : C) : C :=
  R_R_to_C (Cre z1 * Cre z2 - Cim z1 * Cim z2) (Cre z1 * Cim z2 + Cim z1 * Cre z2).

Definition Copp (z1 : C) :C :=
  R_R_to_C (-Cre z1) (-Cim z1).

Definition Cinv (z1 : C) : C :=
  R_R_to_C (Cre z1 / (Cre z1 * Cre z1 + Cim z1 * Cim z1)) (-Cim z1 / (Cre z1 * Cre z1 + Cim z1 * Cim z1)).

Definition Cconj (z1 : C) : C :=
  R_R_to_C (Cre z1) (-Cim z1).

Definition Cnorm_sqr (z1 : C) : R := 
  (Cre z1 * Cre z1 + Cim z1 * Cim z1).

Definition Cnorm (z1 : C) : R := 
  (sqrt (Cnorm_sqr z1)).

Definition Cscal (lambda : R) (z : C) : C := 
  R_R_to_C (lambda * Cre z) (lambda * Cim z).


Definition IRC (x : R) : C := (R_R_to_C x 0%R).

Coercion IRC : R >-> C.

Infix "+" := Cadd : C_scope.
Infix "*" := Cmult : C_scope.
Notation "- z" := (Copp z) : C_scope.
Notation "/ z" := (Cinv z) : C_scope.
Infix "`*" := Cscal (at level 0): C_scope.


Definition Cminus (c1 c2 : C) : C := c1 + - c2.

Definition Cdiv (c1 c2 : C) : C := c1 * / c2.

Infix "-" := Cminus : C_scope.
Infix "/" := Cdiv   : C_scope.


Infix " '+i' " := R_R_to_C (at level 60) : C_scope.

(** ** Injection from [N] to [C]*)

Fixpoint INC (n:nat) : C :=
  match n with
  | O => 0
  | S O => 1
  | S n => INC n + 1
  end.

(** ** Injection from [Z] to [C]*)

Definition IZC (z:Z) : C :=
  match z with
  | Z0 => 0
  | Zpos n => INC (nat_of_P n)
  | Zneg n => - INC (nat_of_P n)
  end.
