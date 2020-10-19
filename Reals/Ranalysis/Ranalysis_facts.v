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

Require Import Rbase Rpower.
Require Import Ranalysis.
Require Import Lra.

Require Import Rfunctions Rfunction_def Rextensionality.
Require Import MyRIneq MyR_dist.
Require Import Rtopology.

Require Import Rinterval Ranalysis_def Ranalysis_def_simpl.
Require Export Ranalysis_continuity Ranalysis_derivability Ranalysis_monotonicity.

Local Open Scope R_scope.

(** * Correcting stdlib's mistakes (generic derivable_* proofs) *)

Lemma derive_pt_id : forall x pr, derive_pt id x pr = 1.
Proof.
intros ; rewrite <- derive_pt_id with x ; apply pr_nu_var ; reflexivity.
Qed.

Lemma derive_pt_const : forall x v p, derive_pt (fct_cte v) x p = 0.
Proof.
intros x v p ; transitivity (derive_pt (fct_cte v) x (derivable_pt_const v x)).
 apply derive_pt_ext ; reflexivity.
 apply derive_pt_const.
Qed.

Lemma derive_pt_minus : forall f g x prf prg pr,
  derive_pt (f - g)%F x pr = derive_pt f x prf - derive_pt g x prg.
Proof.
intros f g x prf prg pr ; erewrite pr_nu_var with
 (pr2 := derivable_pt_minus _ _ x prf prg) ;
 [apply derive_pt_minus | reflexivity].
Qed.

Lemma derive_pt_comp : forall f g x prf prg pr,
  derive_pt (comp g f)%F x pr = derive_pt f x prf * derive_pt g (f x) prg.
Proof.
intros f g x prf prg pr ; erewrite pr_nu_var
 with (pr2 := derivable_pt_comp _ _ x prf prg) ;
 [ rewrite Rmult_comm ; apply derive_pt_comp | reflexivity ].
Qed.

(** * Usual functions *)

Lemma derivable_pt_lim_in_id : forall D x, derivable_pt_lim_in D id x 1.
Proof.
intros ; apply derivable_pt_lim_derivable_pt_lim_in,
 derivable_pt_lim_id.
Qed.

(** * Relating variations to the value of the derivative *)

Lemma derive_open_interval_pos_strictly_increasing_open_interval :
  forall f lb ub (pr : derivable_open_interval lb ub f),
  (forall x, open_interval lb ub x -> 0 < derive_open_interval lb ub f pr x) ->
  strictly_increasing_open_interval lb ub f.
Proof.
intros f lb ub pr Df_pos x y x_in y_in Hxy.
 assert (pr1 : forall c : R, open_interval x y c -> derivable_pt f c).
  intros ; eapply derivable_open_interval_pt ; [eapply pr |].
   eapply open_interval_restriction ; try eassumption ;
   apply open_interval_interval ; eassumption.
 assert (pr2 : forall c : R, open_interval x y c -> derivable_pt id c).
  intros ; apply derivable_id.
 destruct (MVT f id x y pr1 pr2 Hxy) as [c [c_in Hc]].
  intros ; eapply derivable_continuous_pt, derivable_open_interval_pt ;
   [eapply pr | apply interval_open_restriction with x y ; assumption].
  intros ; reg.
  unfold id in Hc ; fold id in Hc ; replace (derive_pt id c (pr2 c c_in)) with 1 in Hc ;
   [rewrite Rmult_1_r in Hc |].
  apply Rminus_gt ; rewrite <- Hc ; apply Rmult_lt_0_compat ; [lra |].
   erewrite <- derive_open_interval_derive_pt ; [eapply Df_pos |] ;
    eapply open_interval_restriction ;
    try (eapply open_interval_interval || apply c_in) ; eassumption.
  symmetry ; apply derive_pt_id.
Qed.

Lemma reciprocal_opp_compat_interval : forall f g lb ub,
  reciprocal_interval lb ub f g ->
  reciprocal_interval lb ub (fun x =>f(-x)) (-g)%F.
Proof.
intros f g lb ub f_recip_g x x_in_I.
 unfold comp, opp_fct ; simpl ; rewrite Ropp_involutive ;
 apply f_recip_g ; assumption.
Qed.

Lemma reciprocal_opp_compat_interval2 : forall f g lb ub,
  reciprocal_interval lb ub f g ->
  reciprocal_interval (-ub) (-lb) (-f)%F (fun x => g (-x)).
Proof.
intros f g lb ub f_recip_g x x_in_I.
 unfold opp_fct ; rewrite f_recip_g.
  apply Ropp_involutive.
 unfold interval in * ; destruct x_in_I ; split ; lra.
Qed.
