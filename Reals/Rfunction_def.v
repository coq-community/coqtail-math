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

Require Import Reals.

Open Scope Rfun_scope.

(** Extensional equality on functions *)

Definition Rfun_eq (f g : R -> R) := forall x, f x = g x.

Infix "==" := Rfun_eq (at level 70, no associativity) : Rfun_scope.

Lemma Rfun_eq_refl : forall f, f == f.
Proof.
intros f x ; reflexivity.
Qed.

Lemma Rfun_eq_sym : forall f g, f == g -> g == f.
Proof.
intros f g H x ; auto.
Qed.

Lemma Rfun_eq_trans : forall f g h, f == g -> g == h -> f == h.
Proof.
intros f g h Hfg Hgh ; intro x ; rewrite Hfg, Hgh ; reflexivity.
Qed.

Require Setoid.

Add Parametric Relation : (R -> R) Rfun_eq
reflexivity proved by Rfun_eq_refl
symmetry proved by Rfun_eq_sym
transitivity proved by Rfun_eq_trans
as Rf_eq.