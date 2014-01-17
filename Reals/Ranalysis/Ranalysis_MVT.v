(*
(C) Copyright 2010--2014, COQTAIL team

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

Require Import Rinterval Ranalysis_def Ranalysis_def_simpl Ranalysis_continuity.
Require Import Ranalysis_derivability Ranalysis_usual Ranalysis_facts.
Require Import Rbase Ranalysis_extend MVT.

Open Scope R_scope.

Lemma MVT : forall (f g : R -> R) (a b : R)
   (pr1 : Ranalysis_def.derivable_open_interval a b f)
   (pr2 : Ranalysis_def.derivable_open_interval a b g ),
   a < b ->
   (Ranalysis_def.continuity_interval a b f) ->
   (Ranalysis_def.continuity_interval a b g) ->
   exists (c : R) (P : open_interval a b c),
    ((g b - g a) * Ranalysis_def.derive_open_interval a b f pr1 c)%R =
    ((f b - f a) * Ranalysis_def.derive_open_interval a b g pr2 c)%R.
Proof.
intros f g a b f_deriv g_deriv altb f_cont g_cont.
 pose (F := extend_continuously f a b) ; pose (G := extend_continuously g a b).
 assert (F_deriv : derivable_open_interval a b F).
  intros ; eapply extend_continuously_derivable_open_interval ; eassumption.
 assert (F_deriv' : forall c, a < c < b -> Ranalysis1.derivable_pt F c).
  intros ; eapply derivable_open_interval_pt ; eassumption.
 assert (G_deriv : derivable_open_interval a b G).
  intros ; eapply extend_continuously_derivable_open_interval ; eassumption.
 assert (G_deriv' : forall c, a < c < b -> Ranalysis1.derivable_pt G c).
  intros ; eapply derivable_open_interval_pt ; eassumption.
 assert (F_cont : forall c, a <= c <= b -> Ranalysis1.continuity_pt F c).
  intros ; eapply extend_continuously_continuous ; [left |] ; assumption.
 assert (G_cont : forall c, a <= c <= b -> Ranalysis1.continuity_pt G c).
  intros ; eapply extend_continuously_continuous ; [left |] ; assumption.
 destruct (MVT F G a b F_deriv' G_deriv' altb F_cont G_cont) as [c [c_in ceq]].
 exists c ; exists c_in.
 assert (a_in : interval a b a) by (apply interval_l ; left ; assumption).
 assert (b_in : interval a b b) by (apply interval_r ; left ; assumption).
 unfold F, G in ceq ;
 do 4 rewrite <- extend_continuously_extends_interval with (a := a) (b := b) in ceq ;
 try assumption.
 rewrite <- extend_continuously_derive_open_interval with (fext_deriv := F_deriv).
 rewrite <- extend_continuously_derive_open_interval with (fext_deriv := G_deriv).
 do 2 (erewrite derive_open_interval_derive_pt ; try eassumption).
Qed.