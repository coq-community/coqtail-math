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

Require Import Arith.
Require Import Compare.
Open Scope nat_scope.

(** * Additional properties on [le] *)

(** elimination of [le] with [plus] *)
Lemma Nle_plus : forall n k, k <= n -> exists p, n = k + p.
intros n k.
intro.
induction H.
exists 0. auto with arith.
destruct IHle.
rewrite H0.
exists (S x).
auto with arith.
Qed.
