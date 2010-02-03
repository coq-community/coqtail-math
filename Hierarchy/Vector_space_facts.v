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

Require Import Type_class_definition.
Require Import Coq.Relations.Relation_Definitions.

(* Some generalities on R-vector space *)

Section K_vect_space.

Variable E K : Type.
Variable eqK : relation K.
Variable add mult : operation K.
Variable eps0 eps1 : K.
Variable eqE : relation E.
Variable v_add : operation E.
Variable v_mult : scalar K E.
Variable v_null : E.

Hypothesis E_vspace : Vector_Space E eqE K eqK v_add v_mult add mult v_null eps0 eps1.

(* Proof of 0.x=0 *)
Lemma vector_space_O_x: forall x:E, eqE (v_mult eps0 x) v_null.
Proof.
intro x.
destruct E_vspace as [Hk HE _ Hdistr_l _ _ _ Hvsp_comp_r].
destruct HE as [Hgr _].
destruct Hgr as [Hmon Hgr_rev].
destruct Hmon as [HeqE Hidenl Hidenr Hmon_assoc Hmon_comp_l Hmon_comp_r].
destruct HeqE as [_ HeqE_sym HeqE_trans].
destruct Hk as [Hk _].
destruct Hk as [Hkgr_add _ _ _].
destruct Hkgr_add as [Hkgr_add _].
destruct Hkgr_add as [Hkmon_add _].
destruct Hkmon_add as [Heqk Hid_l _ _ _ _] .
destruct Heqk as [Heqk_refl _ _].
unfold RelationClasses.Transitive in HeqE_trans.
unfold RelationClasses.Reflexive in Heqk_refl.

rewrite <- (Hidenr v_null).
rewrite <- (Hidenr (v_mult eps0 x)).
destruct (Hgr_rev (v_mult eps0 x)) as [x0 Hinv].

apply HeqE_trans with (v_add (v_mult eps0 x) (v_add (v_mult eps0 x) x0)).
apply Hmon_comp_l. apply HeqE_sym. exact Hinv.
apply HeqE_trans with (v_add v_null  (v_add (v_mult eps0 x) x0)).
rewrite Hmon_assoc. rewrite Hmon_assoc. apply Hmon_comp_r.
apply HeqE_sym.
apply HeqE_trans with (v_mult eps0 x). apply Hidenl.
apply HeqE_trans with (v_mult (add eps0 eps0) x).
apply Hvsp_comp_r. rewrite Hid_l. apply Heqk_refl.
apply Hdistr_l.

apply Hmon_comp_l. exact Hinv.
Qed.


(* Proof of a.0 = 0 *)
Lemma vector_space_a_O: forall a:K, eqE (v_mult a v_null) v_null.
Proof.
intro a.
destruct E_vspace as [Hk HE Hdistr_r _ _ _ Hvsp_comp_l _].
destruct HE as [Hgr _].
destruct Hgr as [Hmon Hgr_rev].
destruct Hmon as [HeqE Hidenl Hidenr Hmon_assoc Hmon_comp_l Hmon_comp_r].
destruct HeqE as [Heq_refl HeqE_sym HeqE_trans].
destruct Hk as [Hk _].
destruct Hk as [Hkgr_add _ _ _].
destruct Hkgr_add as [Hkgr_add _].
destruct Hkgr_add as [Hkmon_add _].
destruct Hkmon_add as [Heqk Hid_l _ _ _ _] .
destruct Heqk as [Heqk_refl _ _].
unfold RelationClasses.Transitive in HeqE_trans.
unfold RelationClasses.Reflexive in Heqk_refl.

destruct (Hgr_rev (v_mult a v_null)) as [x0 Hinv].

apply HeqE_trans with (v_add (v_mult a v_null) v_null).
rewrite Hidenr. apply Heq_refl.

apply HeqE_trans with (v_add (v_mult a v_null) (v_add (v_mult a v_null) x0)).
apply Hmon_comp_l. apply HeqE_sym. exact Hinv.

apply HeqE_trans with (v_add (v_add (v_mult a v_null) (v_mult a v_null)) x0).
apply Hmon_assoc.

apply HeqE_trans with (v_add (v_add v_null (v_mult a v_null)) x0).
apply Hmon_comp_r.
apply HeqE_trans with (v_mult a (v_add v_null v_null)).
rewrite Hdistr_r. apply Heq_refl.
apply HeqE_trans with (v_mult a v_null).
apply Hvsp_comp_l. apply (Hidenr v_null).
apply HeqE_sym. apply Hidenl.

rewrite <- Hmon_assoc.
rewrite Hidenl. exact Hinv.
Qed.


(* Proof of -(a.x)=a.(-x) *)
(* Proof of -(a.x) = (-a).x *)




End K_vect_space.