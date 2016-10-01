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
Require Export Rfunction_def.

Open Scope Rfun_scope.

(** Compatibility of extensional equality *)

Ltac extensional_reflexivity H Heq :=
let swap H1 H2 :=
  clear H1;
  assert (H1 := H2);
  clear H2
in
let rec refl_aux H :=
match goal with
| |- forall x, _ =>
  let x := fresh "x" in
  let nH := fresh in
  intros x;
  assert (nH := H x);
  swap H nH;
  refl_aux H
| |- exists x, _ =>
  let x := fresh "x" in
  destruct H as [x H];
  exists x;
  refl_aux H
| |- ?P /\ ?Q =>
  let Hl := fresh "H" in
  let Hr := fresh "H" in
  destruct H as [Hl Hr];
  split; [refl_aux Hl|refl_aux Hr]
| |- ?P \/ ?Q =>
  let Hl := fresh "H" in
  let Hr := fresh "H" in
  destruct H as [Hl|Hr];
  [refl_aux Hl|refl_aux Hr]
| _ =>
  repeat (rewrite <- Heq); apply H
end in
compute in H |- *; refl_aux H.

Section Rfun_eq.

Variables f g : R -> R.
Hypothesis Heq : f == g.

Lemma Rfun_continuity_pt_eq_compat :
  forall x, continuity_pt f x -> continuity_pt g x.
Proof.
  intros x Hct eps H.
  specialize (Hct eps H).
  destruct Hct as (alp & pos & HH).
  exists alp. split; auto.
  intros x0 H0.
  specialize (HH x0 H0).
  eauto.
  repeat rewrite <-Heq.
  auto.
Qed.

Lemma Rfun_continuity_eq_compat :
  continuity f -> continuity g.
Proof.
  intros H i a p.
  destruct (H i a p).
  exists x. intuition.
  repeat rewrite <-Heq.
  eauto.
Qed.

End Rfun_eq.