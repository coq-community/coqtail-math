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
Require Import Fourier.
Require Import Rfunctions.
Require Import MyRIneq.
Require Import Rtopology.
Require Import Rinterval.

Require Import Ass_handling.
Require Import Rfunction_def.
Require Import Ranalysis_def Ranalysis_def_simpl.

Local Open Scope R_scope.

(** Compatibility of derivable_pt_lim_in with common operations. *)

Lemma derivable_pt_lim_in_const: forall D k x,
  derivable_pt_lim_in (fun _ => k) D x 0.
Proof.
intros D k x eps eps_pos ; exists 1 ; intros ; split.
 fourier.
 intros ; simpl ; unfold R_dist, growth_rate, Rminus, Rdiv ;
 rewrite Rplus_opp_r, Rmult_0_l, Rplus_opp_r, Rabs_R0 ;
 assumption.
Qed.

Lemma derivable_pt_lim_in_opp_compat: forall D f x l,
  derivable_pt_lim_in f D x l ->
  derivable_pt_lim_in (- f)%F D x (- l).
Proof.
intros ; eapply limit1_ext.
 intros y Hy ; symmetry ; apply growth_rate_opp_compat ; split ;
  [unfold no_cond ; trivial | apply Hy].
 apply limit_Ropp ; assumption.
Qed.

Lemma derivable_pt_lim_in_plus_compat: forall D f g x l1 l2,
  derivable_pt_lim_in f D x l1 ->
  derivable_pt_lim_in g D x l2 ->
  derivable_pt_lim_in (f + g)%F D x (l1 + l2).
Proof.
intros ; eapply limit1_ext.
 intros y Hy ; symmetry ; apply growth_rate_plus_compat ; split ;
  [unfold no_cond ; trivial | apply Hy].
 apply limit_plus ; assumption.
Qed.

(** For more complicated cases we (at the moment) deal only
    with Rball because this is what we need ultimately. *)

Lemma derivable_pt_lim_Rball_mult_compat: forall c r r_pos f g x l1 l2,
  Rball c r r_pos x ->
  derivable_pt_lim_in f (Rball c r r_pos) x l1 ->
  derivable_pt_lim_in g (Rball c r r_pos) x l2 ->
  derivable_pt_lim_in (f * g)%F (Rball c r r_pos) x (l1 * g x + f x * l2).
Proof.
intros c r r_pos f g x l1 l2 x_in Hf Hg.
 apply derivable_pt_lim_derivable_pt_lim_in, derivable_pt_lim_mult ;
 eapply derivable_pt_lim_Rball_derivable_pt_lim ; eassumption.
Qed.

Lemma derivable_pt_lim_Rball_div_compat: forall c r r_pos f g x l1 l2,
  Rball c r r_pos x -> g x <> 0 ->
  derivable_pt_lim_in f (Rball c r r_pos) x l1 ->
  derivable_pt_lim_in g (Rball c r r_pos) x l2 ->
  derivable_pt_lim_in (f / g)%F (Rball c r r_pos) x ((l1 * g x - f x * l2) / (g x) ^ 2).
Proof.
intros c r r_pos f g x l1 l2 x_in gx_neq Hf Hg.
 replace ((l1 * g x - f x * l2) / g x ^ 2) with ((l1 * g x - l2 * f x) / (g x) ² ).
 apply derivable_pt_lim_derivable_pt_lim_in, derivable_pt_lim_div ; [| | assumption] ;
 eapply derivable_pt_lim_Rball_derivable_pt_lim ; eassumption.
 unfold Rsqr ; simpl ; field ; assumption.
Qed.

Lemma derivable_pt_lim_Rball_inv_compat: forall c r r_pos f x l,
  Rball c r r_pos x -> f x <> 0 ->
  derivable_pt_lim_in f (Rball c r r_pos) x l ->
  derivable_pt_lim_in (/ f)%F (Rball c r r_pos) x (- l / (f x) ^ 2).
Proof.
intros c r r_pos f x l x_in fx_neq Hf ;
 apply limit1_ext with (growth_rate ((fun _ => 1) / f)%F x).
 intros y [y_in y_neq] ; apply growth_rate_ext ; intro u ;
  unfold div_fct, Rdiv, inv_fct ; ring.
 replace (- l / f x ^ 2) with ((0 * f x - (fun _ => 1) x * l) / (f x ^ 2)).
 apply derivable_pt_lim_Rball_div_compat ; try assumption.
 apply derivable_pt_lim_in_const.
 simpl ; field ; assumption.
Qed.

Lemma derivable_pt_lim_Rball_compat_compat: forall c r r_pos f g x l1 l2,
  Rball c r r_pos x ->
  Rball c r r_pos (f x) ->
  derivable_pt_lim_in f (Rball c r r_pos) x l1 ->
  derivable_pt_lim_in g (Rball c r r_pos) (f x) l2 ->
  derivable_pt_lim_in (comp g f) (Rball c r r_pos) x (l1 * l2).
Proof.
intros c r r_pos f g x l1 l2 x_in fx_in Hf Hg ; rewrite Rmult_comm.
 apply derivable_pt_lim_derivable_pt_lim_in, derivable_pt_lim_comp ;
 eapply derivable_pt_lim_Rball_derivable_pt_lim ; eassumption.
Qed.

(* TODO lib inutile sur les derivable_pt_lim ??? *)
(* Bon TODO c'est useless... quelqu'un a envie d'y réfléchir ? *)
(* TODO faire le pendant avec derivable_pt_in_lim... 
parce que la on a l'existence de limite mais on ne sait pas qui elles sont ? *)

Lemma derivable_pt_in_const : forall  D y x0, 
  derivable_pt_in (fun _ => y) D x0.
Proof.
intros D y x0. 
 eapply D_in_derivable_pt_lim_in.
 apply Dconst.
Qed.

Lemma derivable_pt_in_x:
  forall (D : R -> Prop) (x0 : R),
  derivable_pt_in (fun x : R => x) D x0.
Proof.
intros D x0.
 eapply D_in_derivable_pt_lim_in.
 apply Dx.
Qed.

Lemma derivable_pt_in_add:
  forall (D : R -> Prop) (f g : R -> R) (x0 : R),
  derivable_pt_in f D x0 ->
  derivable_pt_in g D x0 ->
  derivable_pt_in (fun x : R => f x + g x) D x0.
Proof.
intros D f g x0 Hdf Hdg.
 destruct Hdf as (df, Hdf).
 destruct Hdg as (dg, Hdg).
 apply derivable_pt_lim_in_D_in in Hdf.
 apply derivable_pt_lim_in_D_in in Hdg.
 destruct Hdf as (ddf, Hdf). destruct Hdg as (ddg, Hdg).
 eapply (D_in_derivable_pt_lim_in _ (fun x => ddf x + ddg x)). eapply Dadd; assumption. 
Qed.

Lemma derivable_pt_in_mul:
  forall (D : R -> Prop) (f g : R -> R) (x0 : R),
  derivable_pt_in f D x0 ->
  derivable_pt_in g D x0 ->
  derivable_pt_in (fun x : R => f x * g x) D x0.
Proof.
intros D f g x0 Hdf Hdg.
 destruct Hdf as (df, Hdf).
 destruct Hdg as (dg, Hdg).
 apply derivable_pt_lim_in_D_in in Hdf.
 apply derivable_pt_lim_in_D_in in Hdg.
 destruct Hdf as (ddf, Hdf). destruct Hdg as (ddg, Hdg).
 eapply (D_in_derivable_pt_lim_in _ (fun x => ddf x * g x + f x * ddg x)). eapply Dmult; assumption. 
Qed.

Lemma derivable_pt_in_mult_const :
  forall (D : R -> Prop) (f : R -> R) (x0 a : R),
  derivable_pt_in f D x0 -> derivable_pt_in (fun x : R => a * f x) D x0.
Proof.
intros D f x0 a Hdf.
 destruct Hdf as (df, Hdf).
 apply derivable_pt_lim_in_D_in in Hdf.
 destruct Hdf as (ddf, Hdf).
 eapply (D_in_derivable_pt_lim_in _ (fun x => a * ddf x)). eapply Dmult_const; assumption. 
Qed.

Lemma derivable_pt_in_Ropp :
  forall (D : R -> Prop) (f : R -> R) (x0 : R),
  derivable_pt_in f D x0 -> derivable_pt_in (fun x : R => - f x) D x0.
Proof.
intros D f x0 Hdf.
 destruct Hdf as (df, Hdf).
 apply derivable_pt_lim_in_D_in in Hdf.
 destruct Hdf as (ddf, Hdf).
 eapply (D_in_derivable_pt_lim_in _ (fun x => - ddf x)). eapply Dopp; assumption. 
Qed.

Lemma derivable_pt_in_Rminus : 
  forall (D : R -> Prop) (f g : R -> R) (x0 : R),
  derivable_pt_in f D x0 ->
  derivable_pt_in g D x0 ->
  derivable_pt_in (fun x : R => f x - g x) D x0.
Proof.
intros D f g x0 Hdf Hdg.
 destruct Hdf as (df, Hdf).
 destruct Hdg as (dg, Hdg).
 apply derivable_pt_lim_in_D_in in Hdf.
 apply derivable_pt_lim_in_D_in in Hdg.
 destruct Hdf as (ddf, Hdf). destruct Hdg as (ddg, Hdg).
 eapply (D_in_derivable_pt_lim_in _ (fun x => ddf x - ddg x)). eapply Dminus; assumption. 
Qed.

Lemma derivable_pt_in_powx_n : 
  forall (n : nat) (D : R -> Prop) (x0 : R),
  derivable_pt_in (fun x : R => x ^ n) D x0.
Proof.
intros n D x0.
 eapply D_in_derivable_pt_lim_in. apply Dx_pow_n.
Qed.


Lemma derivable_pt_in_comp :
  forall (Df Dg : R -> Prop) (f g : R -> R) (x0 : R),
  derivable_pt_in f Df x0 ->
  derivable_pt_in g Dg (f x0) ->
   derivable_pt_in (fun x : R => g (f x)) (Dgf Df Dg f) x0.
Proof.
intros Df Dg f g x0 Hdf Hdg.
 destruct Hdf as (df, Hdf).
 destruct Hdg as (dg, Hdg).
 apply derivable_pt_lim_in_D_in in Hdf.
 apply derivable_pt_lim_in_D_in in Hdg.
 destruct Hdf as (ddf, Hdf). destruct Hdg as (ddg, Hdg).
 eapply (D_in_derivable_pt_lim_in _ (fun x => ddf x * ddg (f x))). eapply Dcomp; assumption. 
Qed.

Lemma derivable_pt_in_pow_n : 
  forall (n : nat) (D : R -> Prop) (x0 : R) (expr : R -> R),
  derivable_pt_in expr D x0 ->
  derivable_pt_in (fun x : R => expr x ^ n) 
    (Dgf D D expr) x0.
Proof.
intros n Df x0 expr Hdf.
 destruct Hdf as (df, Hdf).
 apply derivable_pt_lim_in_D_in in Hdf.
 destruct Hdf as (ddf, Hdf).
 eapply (D_in_derivable_pt_lim_in _ (fun x => INR n * expr x ^ (n - 1) * ddf x)). 
 eapply D_pow_n; assumption. 
Qed.
