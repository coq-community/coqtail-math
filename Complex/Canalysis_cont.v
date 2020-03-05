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

Require Import Cfunctions.
Require Import Cprop_base.
Require Import Cbase.
Require Import Canalysis_def.

Open Scope C_scope.

(** Compatibility with common operators (continuity at a point) *)

(**********)
Lemma continuity_pt_add : forall f1 f2 z,
    continuity_pt f1 z -> continuity_pt f2 z -> continuity_pt (f1 + f2) z.
Proof.
intros ; apply limit_plus ; assumption.
Qed.

Lemma continuity_pt_opp : forall f z, continuity_pt f z -> continuity_pt (- f) z.
Proof.
intros ; apply limit_opp; assumption.
Qed.

Lemma continuity_pt_minus : forall f1 f2 (z:C),
    continuity_pt f1 z -> continuity_pt f2 z -> continuity_pt (f1 - f2) z.
Proof.
intros ; apply limit_minus; assumption.
Qed.

Lemma continuity_pt_mult : forall f1 f2 z,
    continuity_pt f1 z -> continuity_pt f2 z -> continuity_pt (f1 * f2) z.
Proof.
intros ; apply limit_mul; assumption.
Qed.

Lemma continuity_pt_const : forall f z, constant f -> continuity_pt f z.
Proof.
intros ; exists 1%R ; split ; [apply Rlt_0_1 | intros].
 rewrite H with x z ; simpl.
 rewrite C_dist_eq ; trivial.
Qed.

Lemma continuity_pt_scal : forall f a z,
    continuity_pt f z -> continuity_pt (mult_real_fct a f) z.
Proof.
intros; apply (limit_mul (fun x:C => a) f (D_x no_cond z) a (f z) z).
 intros ; exists 1%R ; split.
  apply Rlt_0_1.
  intros; rewrite C_dist_eq ; intuition.
  assumption.
Qed.

Lemma continuity_pt_inv : forall f z, continuity_pt f z -> f z <> 0 -> continuity_pt (/ f) z.
Proof.
intros f z f_cont Fz_neq ; replace (/ f)%F with (fun z => / f z).
 intros eps eps_pos ; apply limit_inv ; assumption.
 unfold inv_fct ; reflexivity.
Qed.

Lemma div_eq_inv : forall f1 f2, (f1 / f2)%F = (f1 * / f2)%F.
Proof.
  intros; reflexivity.
Qed.

Lemma continuity_pt_div : forall f1 f2 z,
    continuity_pt f1 z -> continuity_pt f2 z -> f2 z <> 0 ->
    continuity_pt (f1 / f2) z.
Proof.
  intros ; rewrite div_eq_inv ; apply continuity_pt_mult ;
    [| apply continuity_pt_inv] ; assumption.
Qed.

Lemma continuity_pt_comp : forall f1 f2 z,
    continuity_pt f1 z -> continuity_pt f2 (f1 z) -> continuity_pt (comp f2 f1) z.
Proof.
intros f1 f2 z Hf1 Hf2 eps eps_pos ; unfold comp.
 cut (limit1_in (fun z => f2 (f1 z)) (Dgf (D_x no_cond z) (D_x no_cond (f1 z)) f1)
       (f2 (f1 z)) z -> limit1_in (fun z => f2 (f1 z)) (D_x no_cond z) (f2 (f1 z)) z).
 intro H ; apply H.
  eapply limit_comp ; [apply Hf1 | apply Hf2].
  assumption.
  intros H eps' eps'_pos ; destruct (H eps' eps'_pos) as (delta,[delta_pos Hdelta]) ;
  clear H ; exists delta ; split ; [assumption |].
  intros z' [H Hz'].
  case (Ceq_dec (f1 z) (f1 z')) ; intro Heq.
  simpl ; unfold C_dist ; rewrite Heq.
  unfold Cminus ; rewrite Cadd_opp_r ; rewrite Cnorm_C0 ; assumption.
  apply Hdelta ; split.
  unfold Dgf ; unfold D_x ; repeat split.
  intro Hf ; apply Heq ; subst ; reflexivity.
  assumption.
  assumption.
Qed.

(** Compatibility with common operators (global continuity) *)

(**********)
Lemma continuity_plus : forall f1 f2,
 continuity f1 -> continuity f2 -> continuity (f1 + f2).
Proof.
unfold continuity ; intros ; apply continuity_pt_add ; intuition.
Qed.

Lemma continuity_opp : forall f, continuity f -> continuity (- f).
Proof.
unfold continuity ; intros; apply continuity_pt_opp ; intuition.
Qed.

Lemma continuity_minus : forall f1 f2,
 continuity f1 -> continuity f2 -> continuity (f1 - f2).
Proof.
unfold continuity ; intros ; apply continuity_pt_minus ; intuition.
Qed.

Lemma continuity_mult : forall f1 f2,
 continuity f1 -> continuity f2 -> continuity (f1 * f2).
Proof.
unfold continuity ; intros ; apply continuity_pt_mult ; intuition.
Qed.

Lemma continuity_const : forall f, constant f -> continuity f.
Proof.
unfold continuity ; intros ; apply continuity_pt_const ; intuition.
Qed.

Lemma continuity_scal : forall f a, continuity f -> continuity (mult_real_fct a f).
Proof.
unfold continuity ; intros ; apply continuity_pt_scal ; intuition.
Qed.

Lemma continuity_inv : forall f, continuity f -> (forall x, f x <> 0) -> continuity (/ f).
Proof.
unfold continuity ; intros f Hf f_neq x ; apply continuity_pt_inv ; intuition.
 eapply f_neq ; eassumption.
Qed.

Lemma continuity_div : forall f1 f2,
    continuity f1 ->  continuity f2 -> (forall x, f2 x <> 0) -> continuity (f1 / f2).
Proof.
unfold continuity ; intros f1 f2 Hf1 Hf2 f2_neq x ; apply continuity_pt_div ; intuition.
 eapply f2_neq ; eassumption.
Qed.

Lemma continuity_comp : forall f1 f2,
 continuity f1 -> continuity f2 -> continuity (comp f2 f1).
Proof.
unfold continuity ; intros ; apply continuity_pt_comp ; intuition.
Qed.
