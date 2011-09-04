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

(** * Compatibility of derivable_pt_lim_in with common operations. *)

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

Lemma derivable_pt_lim_in_minus_compat: forall D f g x l1 l2,
  derivable_pt_lim_in f D x l1 ->
  derivable_pt_lim_in g D x l2 ->
  derivable_pt_lim_in (f - g)%F D x (l1 - l2).
Proof.
intros ; eapply limit1_ext.
 intros y Hy ; symmetry ; apply growth_rate_minus_compat ; split ;
  [unfold no_cond ; trivial | apply Hy].
 apply limit_minus ; assumption.
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

Lemma derivable_pt_lim_Rball_comp_compat: forall c r r_pos f g x l1 l2,
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

(** * Compatibility of derivable_pt_in with common operations. *)

Lemma derivable_pt_in_const : forall D k x,
  derivable_pt_in (fun _ => k) D x.
Proof.
intros ; eexists ; eapply derivable_pt_lim_in_const.
Qed.

Lemma derivable_pt_in_opp_compat: forall (D : R -> Prop) (f : R -> R) (x : R),
  derivable_pt_in f D x -> derivable_pt_in (- f)%F D x.
Proof.
intros D f x [] ; eexists ;
 eapply derivable_pt_lim_in_opp_compat ;
 eassumption.
Qed.

Lemma derivable_pt_in_plus_compat:
  forall (D : R -> Prop) (f g : R -> R) (x : R),
  derivable_pt_in f D x -> derivable_pt_in g D x ->
  derivable_pt_in (f + g)%F D x.
Proof.
intros D f g x [] []; eexists ;
 eapply derivable_pt_lim_in_plus_compat ;
 eassumption.
Qed.

(** For more complicated cases we (at the moment) deal only
    with Rball because this is what we need ultimately. *)

Lemma derivable_pt_Rball_mult_compat: forall c r r_pos f g x,
  Rball c r r_pos x ->
  derivable_pt_in f (Rball c r r_pos) x ->
  derivable_pt_in g (Rball c r r_pos) x ->
  derivable_pt_in (f * g)%F (Rball c r r_pos) x.
Proof.
intros c r r_pos f g x x_in [] [] ; eexists ;
 eapply derivable_pt_lim_Rball_mult_compat ; eassumption.
Qed.

Lemma derivable_pt_Rball_div_compat: forall c r r_pos f g x,
  Rball c r r_pos x -> g x <> 0 ->
  derivable_pt_in f (Rball c r r_pos) x ->
  derivable_pt_in g (Rball c r r_pos) x ->
  derivable_pt_in (f / g)%F (Rball c r r_pos) x.
Proof.
intros c r r_pos f g x x_in g_neq [] [] ; eexists ;
 eapply derivable_pt_lim_Rball_div_compat ; eassumption.
Qed.

Lemma derivable_pt_Rball_inv_compat: forall c r r_pos f x,
  Rball c r r_pos x -> f x <> 0 ->
  derivable_pt_in f (Rball c r r_pos) x ->
  derivable_pt_in (/ f)%F (Rball c r r_pos) x.
Proof.
intros c r r_pos f x x_in f_neq [] ; eexists ;
 eapply derivable_pt_lim_Rball_inv_compat ; eassumption.
Qed.

Lemma derivable_pt_Rball_comp_compat: forall c r r_pos f g x,
  Rball c r r_pos x ->
  Rball c r r_pos (f x) ->
  derivable_pt_in f (Rball c r r_pos) x ->
  derivable_pt_in g (Rball c r r_pos) (f x) ->
  derivable_pt_in (comp g f) (Rball c r r_pos) x.
Proof.
intros c r r_pos f g x x_in y_in [] [] ; eexists ;
 eapply derivable_pt_lim_Rball_comp_compat ; eassumption.
Qed.

(** * Compatibility of derivable_in with common operations. *)

Lemma derivable_in_const : forall D k,
  derivable_in (fun _ => k) D.
Proof.
intros D k x x_in ; eapply derivable_pt_in_const.
Qed.

Lemma derivable_in_opp_compat: forall (D : R -> Prop) (f : R -> R),
  derivable_in f D -> derivable_in (- f)%F D.
Proof.
intros D f Hf x x_in ; eapply derivable_pt_in_opp_compat, Hf ;
 eassumption.
Qed.

Lemma derivable_in_plus_compat:
  forall (D : R -> Prop) (f g : R -> R),
  derivable_in f D -> derivable_in g D ->
  derivable_in (f + g)%F D.
Proof.
intros D f g Hf Hg x x_in ; eapply derivable_pt_in_plus_compat ;
 [eapply Hf | eapply Hg] ; eassumption.
Qed.

(** For more complicated cases we (at the moment) deal only
    with Rball because this is what we need ultimately. *)

Lemma derivable_Rball_mult_compat: forall c r r_pos f g,
  derivable_Rball f c r r_pos ->
  derivable_Rball g c r r_pos ->
  derivable_Rball (f * g)%F c r r_pos.
Proof.
intros c r r_pos f g Hf Hg x x_in ;
 eapply derivable_pt_Rball_mult_compat ;
 [| eapply Hf | eapply Hg] ; eassumption.
Qed.

Lemma derivable_Rball_div_compat: forall c r r_pos f g,
  (forall x, Rball c r r_pos x -> g x <> 0) ->
  derivable_Rball f c r r_pos ->
  derivable_Rball g c r r_pos ->
  derivable_Rball (f / g)%F c r r_pos.
Proof.
intros c r r_pos f g g_neq Hf Hg x x_in ;
 eapply derivable_pt_Rball_div_compat ;
 [| eapply g_neq | eapply Hf | eapply Hg] ;
 eassumption.
Qed.

Lemma derivable_Rball_inv_compat: forall c r r_pos f,
  (forall x, Rball c r r_pos x -> f x <> 0) ->
  derivable_Rball f c r r_pos ->
  derivable_Rball (/ f)%F c r r_pos.
Proof.
intros c r r_pos f f_neq Hf x x_in ;
 eapply derivable_pt_Rball_inv_compat ;
 [| eapply f_neq | eapply Hf] ; eassumption.
Qed.

(** * Compatibility of derive_pt_in with common operations. *)

Lemma derive_pt_Rball_const : forall k c r r_pos x pr,
  Rball c r r_pos x ->
  derive_pt_in (fun _ => k) (Rball c r r_pos) x pr = 0.
Proof.
intros k c r r_pos x pr x_in ; apply derivable_pt_lim_derive_pt_Rball ;
 [exact x_in | apply derivable_pt_lim_in_const].
Qed.

Lemma derive_pt_Rball_opp_compat: forall f c r r_pos x pr pr',
  Rball c r r_pos x ->
  derive_pt_in (- f)%F (Rball c r r_pos) x pr =
  - derive_pt_in f (Rball c r r_pos) x pr'.
Proof.
intros f c r r_pos x [l Hl] [l' Hl'] x_in ;
 eapply derivable_pt_lim_Rball_uniqueness ;
 [| | eapply derivable_pt_lim_in_opp_compat] ;
 eassumption. 
Qed.

Lemma derive_pt_Rball_plus_compat:
  forall f g c r r_pos x prf prg prfg, Rball c r r_pos x ->
  derive_pt_in (f + g)%F (Rball c r r_pos) x prfg =
  derive_pt_in f (Rball c r r_pos) x prf +
  derive_pt_in g (Rball c r r_pos) x prg.
Proof.
intros f g c r r_pos x [lf Hlf] [lg Hlg] [lfg Hlfg] x_in ;
 eapply derivable_pt_lim_Rball_uniqueness ;
 [| | eapply derivable_pt_lim_in_plus_compat] ;
 eassumption.
Qed.

(** For more complicated cases we (at the moment) deal only
    with Rball because this is what we need ultimately. *)

Lemma derive_pt_Rball_mult_compat:
  forall f g c r r_pos x prf prg prfg,
  Rball c r r_pos x ->
  derive_pt_in (f * g)%F (Rball c r r_pos) x prfg =
  derive_pt_in f (Rball c r r_pos) x prf * g x +
  f x * derive_pt_in g (Rball c r r_pos) x prg.
Proof.
intros f g c r r_pos x [lf Hlf] [lg Hlg] [lfg Hlfg] x_in ;
 eapply derivable_pt_lim_Rball_uniqueness ;
 [| | eapply derivable_pt_lim_Rball_mult_compat] ;
 eassumption.
Qed.

Lemma derive_pt_Rball_div_compat:
  forall f g c r r_pos x prf prg prfg,
  Rball c r r_pos x -> g x <> 0 ->
  derive_pt_in (f / g)%F (Rball c r r_pos) x prfg =
  (derive_pt_in f (Rball c r r_pos) x prf * g x -
  f x * derive_pt_in g (Rball c r r_pos) x prg) / (g x) ^ 2.
Proof.
intros f g c r r_pos x [lf Hlf] [lg Hlg] [lfg Hlfg] x_in gx_neq ;
 eapply derivable_pt_lim_Rball_uniqueness ;
 [| | eapply derivable_pt_lim_Rball_div_compat] ;
 eassumption.
Qed.

Lemma derive_pt_Rball_inv_compat:
  forall f c r r_pos x pr pr',
  Rball c r r_pos x -> f x <> 0 ->
  derive_pt_in (/ f)%F (Rball c r r_pos) x pr =
  (- derive_pt_in f (Rball c r r_pos) x pr') / (f x) ^ 2.
Proof.
intros f c r r_pos x [l Hl] [l' Hl'] x_in fx_neq ;
 eapply derivable_pt_lim_Rball_uniqueness ;
 [| | eapply derivable_pt_lim_Rball_inv_compat] ;
 eassumption.
Qed.

(** * Compatibility of derive_Rball with common operations. *)

Lemma derive_Rball_const : forall k c r r_pos x pr,
  derive_Rball (fun _ => k) c r r_pos pr x = 0.
Proof.
intros k c r r_pos x pr ; unfold derive_Rball ;
 destruct (in_Rball_dec c r r_pos x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_const | reflexivity] ; assumption.
Qed.

Lemma derive_Rball_opp_compat: forall f c r r_pos x pr pr',
  derive_Rball (- f)%F c r r_pos pr x =
  - derive_Rball f c r r_pos pr' x.
Proof.
intros f c r r_pos x pr pr' ; unfold derive_Rball ;
 destruct (in_Rball_dec c r r_pos x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_opp_compat ; assumption
 | rewrite Ropp_0 ; reflexivity].
Qed.

Lemma derive_Rball_plus_compat:
  forall f g c r r_pos x prf prg prfg,
  derive_Rball (f + g)%F c r r_pos prfg x =
  derive_Rball f c r r_pos prf x +
  derive_Rball g c r r_pos prg x.
Proof.
intros f g c r r_pos x prf prg prfg ; unfold derive_Rball ;
 destruct (in_Rball_dec c r r_pos x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_plus_compat ; assumption
 | rewrite Rplus_0_r ; reflexivity].
Qed.

(** For more complicated cases we (at the moment) deal only
    with Rball because this is what we need ultimately. *)

Lemma derive_Rball_mult_compat: forall f g c r r_pos x prf prg prfg,
  derive_Rball (f * g)%F c r r_pos prfg x =
  derive_Rball f c r r_pos prf x * g x +
  f x * derive_Rball g c r r_pos prg x.
Proof.
intros f g c r r_pos x prf prg prfg ; unfold derive_Rball ;
 destruct (in_Rball_dec c r r_pos x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_mult_compat ; assumption
 | rewrite Rmult_0_r, Rmult_0_l, Rplus_0_r ; reflexivity].
Qed.

Lemma derive_Rball_div_compat:
  forall f g c r r_pos x prf prg prfg, g x <> 0 ->
  derive_Rball (f / g)%F c r r_pos prfg x =
  (derive_Rball f c r r_pos prf x * g x -
  f x * derive_Rball g c r r_pos prg x) / (g x) ^ 2.
Proof.
intros f g c r r_pos x prf prg prfg ; unfold derive_Rball ;
 destruct (in_Rball_dec c r r_pos x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_div_compat ; assumption
 | rewrite Rmult_0_r, Rmult_0_l, Rminus_0_r, Rdiv_0_l ; reflexivity].
Qed.

Lemma derive_Rball_inv_compat:
  forall f c r r_pos x pr pr', f x <> 0 ->
  derive_Rball (/ f)%F c r r_pos pr x =
  (- derive_Rball f c r r_pos pr' x) / (f x) ^ 2.
Proof.
Proof.
intros f c r r_pos x pr pr' fx_neq ; unfold derive_Rball ;
 destruct (in_Rball_dec c r r_pos x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_inv_compat ; assumption
 | rewrite Ropp_0, Rdiv_0_l ; reflexivity].
Qed.