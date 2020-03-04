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

Require Export Finite_sets.
Require Export My_Sets_facts.
Require Export Arith.

Section Finite_sets_facts.

Arguments Union [U] B C _.
Arguments Add [U] B x _.
Arguments Singleton [U] x _.
Arguments Finite [U] _.
Arguments cardinal [U] _ _.
Arguments Disjoint [U] B C.

Variable U:Type.

Lemma cardinal_of_disjoint_union : forall X:Ensemble U, forall n:nat,
  cardinal X n -> forall Y:Ensemble U, forall m:nat,
  cardinal Y m -> Disjoint X Y -> cardinal (Union X Y) (n+m).
Proof.
induction 1.
intros.
rewrite Union_empty_set_left.
rewrite plus_0_l.
auto.

intros.
rewrite Union_add_left.
simpl.
constructor.
apply IHcardinal.
auto.
apply Disjoint_downward_closed with (Add A x).
auto.
unfold Add.
apply included_in_union.
intro.
destruct H2.
apply H2 with x.
split.
apply Union_intror.
constructor.
destruct H3.
contradiction.
auto.
Qed.

End Finite_sets_facts.
