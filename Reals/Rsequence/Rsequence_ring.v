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
Require Export Ring.
Require Import Rsequence_def.
Require Import Reals.
Require Import Setoid.

Open Scope Rseq_scope.

Add Morphism Rseq_plus with signature Rseq_eq ==> Rseq_eq ==> Rseq_eq as Rseq_plus_Rseq_eq_compat.
(*Add Morphism Rseq_plus : Rseq_plus_Rseq_eq_compat.*)
Proof.
unfold Rseq_eq, Rseq_plus.
intros Un Vn Huv Xn Yn Hxy n.
rewrite Huv.
rewrite Hxy.
reflexivity.
Qed.

Add Morphism Rseq_minus with signature Rseq_eq ==> Rseq_eq ==> Rseq_eq as Rseq_minus_Rseq_eq_compat.
(* Add Morphism Rseq_minus : Rseq_minus_Rseq_eq_compat. *)
Proof.
unfold Rseq_eq, Rseq_minus.
intros Un Vn Huv Xn Yn Hxy n.
rewrite Huv.
rewrite Hxy.
reflexivity.
Qed.

Add Morphism Rseq_mult with signature Rseq_eq ==> Rseq_eq ==> Rseq_eq as Rseq_mult_Rseq_eq_compat.
(*Add Morphism Rseq_mult : Rseq_mult_Rseq_eq_compat.*)
Proof.
unfold Rseq_eq, Rseq_mult.
intros Un Vn Huv Xn Yn Hxy n.
rewrite Huv.
rewrite Hxy.
reflexivity.
Qed.

Add Morphism Rseq_opp with signature Rseq_eq ==> Rseq_eq as Rseq_opp_Rseq_eq_compat.
(*Add Morphism Rseq_mult : Rseq_mult_Rseq_eq_compat.*)
Proof.
intros x y H i.
unfold Rseq_eq, Rseq_opp.
rewrite H.
trivial.
Qed.

Lemma Rseq_setoid_theory : Setoid_Theory Rseq Rseq_eq.
Proof.
constructor; unfold Rseq_eq.
unfold Reflexive; trivial.
unfold Symmetric; auto.
unfold Transitive; intros x y z H1 H2 n;
 rewrite H1; rewrite H2; reflexivity.
Qed.

Lemma Rseq_ring_theory : @ring_theory Rseq (0%R) (1%R) Rseq_plus Rseq_mult Rseq_minus Rseq_opp Rseq_eq.
Proof.
  constructor; unfold Rseq_plus, Rseq_mult, Rseq_minus, Rseq_eq, Rseq_constant, Rseq_opp;
intros; ring.
Qed.

Add Setoid Rseq Rseq_eq Rseq_setoid_theory as Rseq_eq_setoid.

Add Ring Rseq_Ring : Rseq_ring_theory(abstract).
