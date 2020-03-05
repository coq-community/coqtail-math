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

Require Import Coq.Relations.Relation_Definitions.
Require Import SetoidClass.
Require Import Reals.
Require Import Type_class_definition_beta.
Require Import Omega.

(*proof that nat = semiring_commutative*)

(* begin hide *)
Ltac int_hierarchy := match goal with
  | |- forall a, ?b => intro; int_hierarchy
  | |- ?a = ?b => rewrite mult_plus_distr_l; int_hierarchy
  | |- ?a = ?b => rewrite mult_plus_distr_r; int_hierarchy
  | |- ?a = ?b => progress auto
  | |- ?a = ?b => omega
  | |- ?a = ?b => progress auto with *
  | |- ?a = ?b => subst; progress trivial
  | |- _ => constructor; int_hierarchy
  | |- _ => intro; int_hierarchy
end.
(* end hide *)

Open Scope nat_scope.

Lemma aux_plus_0_l : forall x : nat, (fun _ : nat => True) x -> 0 + x = x.
Proof.
intros.
exact (plus_0_l x).
Qed.

Program Instance monoid_nat : Monoid nat (fun n:nat => True) eq plus 0 :=
{monoid_iden_l := aux_plus_0_l}.
Solve All Obligations with int_hierarchy.

Program Instance monoid_commutative_nat : Monoid_Commutative nat (fun n:nat => True) eq plus 0 :=
{monoid_comm_monoid := monoid_nat}.
Solve All Obligations with int_hierarchy.

Lemma aux_mult_1_l : forall x : nat, (fun _ : nat => True) x -> 1 * x = x.
Proof.
intros.
exact (mult_1_l x).
Qed.

Program Instance monoid_nat_mult_1 : Monoid nat (fun n:nat => True) eq mult 1 :=
{monoid_iden_l := aux_mult_1_l }.
Solve All Obligations with int_hierarchy.

Program Instance semiring_nat : SemiRing nat (fun n:nat => True) eq plus mult 0 1 :=
{semiring_monoid_comm := monoid_commutative_nat}.
Solve All Obligations with int_hierarchy.

Program Instance semiring_commutative_nat : SemiRing_Commutative nat (fun n:nat => True) eq plus mult 0 1 :=
{semiring_comm_semiring := semiring_nat}.
Solve All Obligations with int_hierarchy.
