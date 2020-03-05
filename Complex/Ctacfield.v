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

Require Import Nnat.
Require Import Arith.
Require Export Ring Field.
Require Import Cbase.
Require Import Cpow.

Open Scope C_scope.

(** ** Tactics ring and field in the Complex field *)

Lemma Cring : @ring_theory C C0 C1 Cadd Cmult Cminus Copp (eq(A:=C)).
Proof.
  constructor.
  exact Cadd_0_l.
  exact Cadd_comm.
  intros ; rewrite <- Cadd_assoc ; reflexivity.
  exact Cmult_1_l.
  exact Cmult_comm.
  symmetry; apply Cmult_assoc.
  intros; apply Cmult_add_distr_r.
  reflexivity.
  exact Cadd_opp_r.
Qed.

Lemma Cfield :
  @field_theory C C0 C1 Cadd Cmult Cminus Copp Cdiv Cinv (eq(A:=C)).
Proof.
  constructor.
  exact Cring.
  exact C1_neq_C0.
  reflexivity.
  exact Cinv_l.
Qed.

Lemma C_power_theory : power_theory C1 Cmult (eq (A:=C)) nat_of_N Cpow.
Proof.
constructor. 
intros z n ; elim n ; clear n.
 reflexivity.
induction p ; simpl in *.
   rewrite ZL6 ; rewrite Cpow_add ; rewrite IHp ; reflexivity.
  unfold nat_of_P ; rewrite <- IHp ; rewrite <- Cpow_add ; rewrite <- ZL6 ; reflexivity.
 apply Cmult_1_r.
Qed.

Ltac Cpow_tac t := 
  match isnatcst t with
  | false => constr:(InitialRing.NotConstant)
  | _ => constr:(N_of_nat t)
  end. 

Add Ring CRing : Cring( abstract).

Add Field CField : Cfield(power_tac C_power_theory [Cpow_tac]).
