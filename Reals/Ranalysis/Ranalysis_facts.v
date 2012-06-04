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

Require Import Rfunctions Rfunction_def Rextensionality.
Require Import MyRIneq MyR_dist.
Require Import Rtopology.

Require Import Ass_handling.
Require Import Rinterval Ranalysis_def Ranalysis_def_simpl.

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

Lemma derivable_pt_lim_in_scal: forall D a f x l,
  derivable_pt_lim_in f D x l ->
  derivable_pt_lim_in (mult_real_fct a f) D x (a * l).
Proof.
intros D a f x l Hf ; destruct (Req_dec a 0).
 subst ; rewrite Rmult_0_l ; eapply derivable_pt_lim_in_ext.
  symmetry ; eapply mult_real_fct_0.
  apply derivable_pt_lim_in_const.
 intros eps eps_pos ; pose (eps' := eps / Rabs a).
 assert (eps'_pos: 0 < eps').
  apply Rlt_mult_inv_pos ; [| apply Rabs_pos_lt] ; assumption.
 destruct (Hf _ eps'_pos) as [alpha [alpha_pos Halpha]].
 exists alpha ; split.
  assumption.
 intros y [[y_in y_neq] y_bd] ;
 rewrite growth_rate_mult_real_fct_compat, R_dist_scal_compat.
 apply Rlt_le_trans with (Rabs a * eps').
  apply Rmult_lt_compat_l ; [apply Rabs_pos_lt |
   apply Halpha ; repeat split] ; assumption.
  right ; unfold eps' ; field ; apply Rabs_no_R0 ; assumption.
  split ; [exact I | assumption].
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

Lemma derivable_pt_lim_in_mult_compat: forall (D : R -> Prop) f g x l1 l2, D x ->
  derivable_pt_lim_in f D x l1 ->
  derivable_pt_lim_in g D x l2 ->
  derivable_pt_lim_in (f * g)%F D x (l1 * g x + f x * l2).
Proof.
intros D f g x l1 l2 Dx Hf Hg ; eapply limit1_in_ext.
  intros y [Dy Hneq] ; symmetry ; apply growth_rate_mult_decomp, Hneq.
  apply limit_plus ; apply limit_mul ; [apply Hf | | | apply Hg].
  apply limit_free.
  apply limit1_imp with D.
   intros y [y_in y_neq] ; exact y_in.
   apply derivable_pt_in_continue_pt_in ; [eexists |] ; eassumption.
Qed.

Lemma continue_non_null: forall f (D : R -> Prop) x,
  D x -> continue_pt_in f D x -> f x <> 0 ->
  exists alp, 0 < alp /\ forall y, D y -> Rabs (y - x) < alp -> f y <> 0.
Proof.
intros f D x Dx Hf Hneq ; pose (eps := Rabs (f x) / 2) ; assert (eps_pos: 0 < eps).
 unfold eps, Rdiv ; apply Rlt_mult_inv_pos ; [apply Rabs_pos_lt ; assumption | fourier].
 destruct (Hf Dx eps eps_pos) as [alp [alp_pos Halp]] ; exists alp ; split.
  assumption.
  intros y Dy y_bd ; apply Rabs_pos_lt_contravar.
  transitivity (Rabs (f x) - eps).
   apply Rlt_le_trans with eps ; [assumption | right ; unfold eps ; field].
   apply Rlt_minus_swap ; apply Rle_lt_trans with (dist R_met (f x) (f y)) ;
   [apply Rabs_triang_inv | rewrite R_dist_sym ; apply Halp ; split ;
   [| unfold R_dist] ; assumption].
Qed.  

Lemma derivable_pt_lim_in_inv_compat: forall (D : R -> Prop) f x l,
  D x -> f x <> 0 ->
  derivable_pt_lim_in f D x l ->
  derivable_pt_lim_in (/ f)%F D x (- l / (f x ^ 2)).
Proof.
intros D f x l Dx Hneq Hf ; assert (f_cont: continue_pt_in f D x)
 by (eapply derivable_pt_in_continue_pt_in ; eexists ; eassumption).
 destruct (continue_non_null _ _ _ Dx f_cont Hneq) as [alp [alp_pos Halp]] ;
 eapply limit1_in_ext_strong.
  eassumption.
  intros y y_bd [y_in y_neq] ; symmetry ; eapply growth_rate_inv_decomp ;
   try assumption.
   apply Halp ; assumption.
  replace (- l / f x ^ 2) with (- (l / f x ^ 2)) by (unfold Rdiv ; ring).
 apply limit_Ropp ; unfold Rdiv ; apply limit_mul ; [apply Hf |].
  apply limit_inv ; [| apply pow_nonzero ; assumption].
   apply limit_mul ; [apply limit_free | rewrite Rmult_1_r] ;
   eapply limit1_imp, f_cont.
    intros y [y_in y_neq] ; assumption.
    assumption.
Qed.

Lemma derivable_pt_lim_in_div_compat: forall (D : R -> Prop) f g x l1 l2,
  D x -> g x <> 0 ->
  derivable_pt_lim_in f D x l1 ->
  derivable_pt_lim_in g D x l2 ->
  derivable_pt_lim_in (f / g)%F D x ((l1 * g x - f x * l2) / g x ^ 2).
Proof.
intros D f g x l1 l2 Dx Hneq Hf Hg ; apply derivable_pt_lim_in_ext with (f * / g)%F.
 intro ; reflexivity.
 replace ((l1 * g x - f x * l2) / g x ^ 2) with ((l1 * (/ g)%F x) + f x * (- l2 / g x ^ 2)).
 eapply derivable_pt_lim_in_mult_compat ; try eassumption.
 eapply derivable_pt_lim_in_inv_compat ; try eassumption.
 unfold inv_fct ; field ; assumption.
Qed.

(** For more complicated cases we (at the moment) deal only
    with Rball because this is what we need ultimately. *)

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

Lemma derivable_pt_in_scal: forall D a f x,
  derivable_pt_in f D x ->
  derivable_pt_in (mult_real_fct a f) D x.
Proof.
intros D a f x [l Hl] ; eexists ;
 eapply derivable_pt_lim_in_scal ; eassumption.
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

Lemma derivable_pt_in_mult_compat: forall (D : R -> Prop) f g x, D x ->
  derivable_pt_in f D x ->
  derivable_pt_in g D x ->
  derivable_pt_in (f * g)%F D x.
Proof.
intros D f g x x_in [] [] ; eexists ;
 eapply derivable_pt_lim_in_mult_compat ; eassumption.
Qed.

Lemma derivable_pt_in_inv_compat: forall (D : R -> Prop) f x,
  D x -> f x <> 0 ->
  derivable_pt_in f D x ->
  derivable_pt_in (/ f)%F D x.
Proof.
intros D f x Dx Hneq [] ; eexists ;
 eapply derivable_pt_lim_in_inv_compat ; eassumption.
Qed.

Lemma derivable_pt_in_div_compat: forall (D : R -> Prop) f g x,
  D x -> g x <> 0 ->
  derivable_pt_in f D x ->
  derivable_pt_in g D x ->
  derivable_pt_in (f / g)%F D x.
Proof.
intros D f g x Dx Hneq [] [] ; eexists ;
 eapply derivable_pt_lim_in_div_compat ; eassumption.
Qed.

(** For more complicated cases we (at the moment) deal only
    with Rball because this is what we need ultimately. *)

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

Lemma derivable_in_scal: forall D a f,
  derivable_in f D ->
  derivable_in (mult_real_fct a f) D.
Proof.
intros D a f Hf x x_in ; specify2 Hf x x_in ;
 apply derivable_pt_in_scal ; assumption.
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

Lemma derivable_in_mult_compat: forall D f g,
  derivable_in f D ->
  derivable_in g D ->
  derivable_in (f * g)%F D.
Proof.
intros D f g Hf Hg x x_in ;
 eapply derivable_pt_in_mult_compat ;
 [| eapply Hf | eapply Hg] ; eassumption.
Qed.

Lemma derivable_in_inv_compat: forall (D : R -> Prop) f,
  (forall x, D x -> f x <> 0) ->
  derivable_in f D ->
  derivable_in (/ f)%F D.
Proof.
intros D f Hneq Hf x x_in ; apply derivable_pt_in_inv_compat ;
 [| apply Hneq | apply Hf] ; assumption.
Qed.

Lemma derivable_in_div_compat: forall (D : R -> Prop) f g,
  (forall x, D x -> g x <> 0) ->
  derivable_in f D ->
  derivable_in g D ->
  derivable_in (f / g)%F D.
Proof.
intros D f g Hneq Hf Hg x x_in ; apply derivable_pt_in_mult_compat ;
 [| apply Hf | apply derivable_in_inv_compat ; [apply Hneq | apply Hg |]] ;
 eassumption.
Qed.

(** Compatibility between derivable and derivable_in *)

Lemma derivable_derivable_open_interval : forall f lb ub,
  derivable f -> derivable_open_interval f lb ub.
Proof.
intros f lb ub pr x x_in ; apply derivable_pt_derivable_pt_in, pr.
Qed.

Lemma derive_pt_derive_open_interval : forall f lb ub x
  (pr1 : derivable_open_interval f lb ub) (pr2 : derivable_pt f x),
  open_interval lb ub x ->
  derive_open_interval f lb ub pr1 x = derive_pt f x pr2.
Proof.
intros f lb ub x pr1 [l Hl] Hx ; unfold derive_open_interval ;
 destruct (in_open_interval_dec lb ub x) as [x_in | x_out].
  destruct (pr1 x x_in) as [l' Hl'] ; apply uniqueness_limite with f x.
   eapply derivable_pt_lim_open_interval_derivable_pt_lim ; eassumption.
   assumption.
  contradiction.
Qed.

Lemma derivable_open_interval_id : forall lb ub, derivable_open_interval id lb ub.
Proof.
intros ; apply derivable_derivable_open_interval, derivable_id.
Qed.


(** * Compatibility of derive_pt_in with common operations. *)

Lemma derive_pt_Rball_const : forall k c r r_pos x pr,
  Rball c r r_pos x ->
  derive_pt_in (fun _ => k) (Rball c r r_pos) x pr = 0.
Proof.
intros k c r r_pos x pr x_in ;
  eapply derivable_pt_lim_derive_pt_Rball with r_pos r_pos ;
 [eexact x_in | eapply derivable_pt_lim_in_const].
Qed.

Lemma derive_pt_Rball_scal: forall a f c r r_pos x pr pr',
  Rball c r r_pos x ->
  derive_pt_in (mult_real_fct a f) (Rball c r r_pos) x pr =
  a * derive_pt_in f (Rball c r r_pos) x pr'.
Proof.
intros a f c r r_pos x pr pr' x_in ;
  eapply derivable_pt_lim_derive_pt_Rball with r_pos r_pos ;
 [eexact x_in | eapply derivable_pt_lim_in_scal].
 destruct pr' ; assumption.
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

Lemma derive_pt_Rball_mult_compat:
  forall f g c r r_pos x prf prg prfg, Rball c r r_pos x ->
  derive_pt_in (f * g)%F (Rball c r r_pos) x prfg =
  derive_pt_in f (Rball c r r_pos) x prf * g x +
  f x * derive_pt_in g (Rball c r r_pos) x prg.
Proof.
intros f g c r r_pos x [lf Hlf] [lg Hlg] [lfg Hlfg] x_in ;
 eapply derivable_pt_lim_Rball_uniqueness ;
 [| | eapply derivable_pt_lim_in_mult_compat] ;
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
 [| | eapply derivable_pt_lim_in_div_compat] ;
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
 [| | eapply derivable_pt_lim_in_inv_compat] ;
 eassumption.
Qed.

(** Compatibility of derive_pt with common operations *)

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

(** * Compatibility of derive_Rball with common operations. *)

Lemma derive_Rball_const : forall k c r r_pos x pr,
  derive_Rball (fun _ => k) c r r_pos pr x = 0.
Proof.
intros k c r r_pos x pr ; unfold derive_Rball ;
 destruct (in_Rball_dec c r r_pos x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_const | reflexivity] ; assumption.
Qed.

Lemma derive_Rball_scal: forall a f c r r_pos x pr pr',
  derive_Rball (mult_real_fct a f) c r r_pos pr x =
  a * derive_Rball f c r r_pos pr' x.
Proof.
intros a f c r r_pos x pr pr' ; unfold derive_Rball ;
 destruct (in_Rball_dec c r r_pos x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_scal ; assumption | symmetry ; apply Rmult_0_r].
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

(** * Relation between derivatives and variations *)

Lemma strictly_increasing_injective_open_interval : forall f lb ub,
  strictly_increasing_open_interval f lb ub -> injective_open_interval f lb ub.
Proof.
intros f lb ub Hf x y x_in y_in Heq ; destruct (Rlt_le_dec x y) as [x_lt_y | y_le_x].
 destruct (Rlt_irrefl (f x)) ; apply Rlt_le_trans with (f y).
  apply Hf ; assumption.
  rewrite Heq ; reflexivity.
 destruct y_le_x as [y_lt_x | y_eq_x] ; [| symmetry ; trivial].
  destruct (Rlt_irrefl (f x)) ; apply Rle_lt_trans with (f y).
   right ; assumption.
   apply Hf ; assumption.
Qed.

Lemma strictly_increasing_open_interval_order : forall f lb ub a b,
  open_interval lb ub a -> open_interval lb ub b ->
  strictly_increasing_open_interval f lb ub ->
  f a < f b -> a < b.
Proof.
intros f lb ub a b a_in b_in Hf Hfafb ; destruct (Rlt_le_dec a b) as [altb | blea].
 assumption.
 destruct blea as [blta | beqa].
  destruct (Rlt_irrefl (f a)) ; transitivity (f b).
   assumption.
   apply Hf ; assumption.
  rewrite beqa in Hfafb ; destruct (Rlt_irrefl _ Hfafb).
Qed.

Lemma strictly_increasing_interval_order : forall f lb ub a b,
  open_interval lb ub a -> open_interval lb ub b ->
  strictly_increasing_open_interval f lb ub ->
  f a <= f b -> a <= b.
Proof.
intros f lb ub a b a_in b_in Hf Hfafb ; destruct (Rle_lt_dec a b) as [aleb | blta].
 assumption.
 destruct (Rlt_irrefl (f a)) ; apply Rle_lt_trans with (f b).
  assumption.
  apply Hf ; assumption.
Qed.

Lemma strictly_increasing_injective_interval : forall f lb ub,
  strictly_increasing_interval f lb ub -> injective_interval f lb ub.
Proof.
intros f lb ub Hf x y x_in y_in Heq ; destruct (Rlt_le_dec x y) as [x_lt_y | y_le_x].
 destruct (Rlt_irrefl (f x)) ; apply Rlt_le_trans with (f y).
  apply Hf ; assumption.
  rewrite Heq ; reflexivity.
 destruct y_le_x as [y_lt_x | y_eq_x] ; [| symmetry ; trivial].
  destruct (Rlt_irrefl (f x)) ; apply Rle_lt_trans with (f y).
   right ; assumption.
   apply Hf ; assumption.
Qed.

Lemma strictly_increasing_increasing : forall f,
  strictly_increasing f -> increasing f.
Proof.
intros f Hf x y [xy_lt | xy_eq].
 left ; apply Hf ; assumption.
 subst ; reflexivity.
Qed.

Lemma x_in_Rball1 : forall x, open_interval (x - 1) (x + 1) x.
Proof.
intro x ; split ; fourier.
Qed.

Lemma continuity_open_interval_continuity : forall f,
  (forall lb ub, continuity_open_interval f lb ub ) ->
  continuity f.
Proof.
intros f Hf x eps eps_pos ;
 destruct (Hf (x - 1) (x + 1) x (x_in_Rball1 x) _ eps_pos) as [delta [delta_pos Hdelta]] ;
 exists (Rmin delta 1) ; split.
  apply Rmin_pos_lt ; fourier.
  simpl ; intros y [[_ y_neq] y_b] ; apply Hdelta ; split.
   rewrite <- (Rball_rewrite _ _ Rle_0_1) ; eapply Rlt_le_trans ; [eassumption | apply Rmin_r].
   eapply Rlt_le_trans ; [eassumption | apply Rmin_l].
Qed.

Lemma derivable_open_interval_derivable : forall f,
  (forall lb ub, derivable_open_interval f lb ub ) ->
  derivable f.
Proof.
intros f Hf x ; eapply derivable_open_interval_derivable_pt,
 x_in_Rball1 ; apply Hf ; fourier.
Qed.

Lemma reciprocal_reciprocal_interval : forall f g lb ub,
  reciprocal f g -> reciprocal_interval f g lb ub.
Proof.
intros f g lb ub Hfg x x_in ; apply Hfg.
Qed.

Lemma reciprocal_reciprocal_open_interval : forall f g lb ub,
  reciprocal f g -> reciprocal_open_interval f g lb ub.
Proof.
intros f g lb ub Hfg x x_in ; apply Hfg.
Qed.

Lemma derive_pt_in_uniqueness : forall f x lb ub pr pr',
  lb < ub -> interval lb ub x ->
  derive_pt_in f (interval lb ub) x pr = derive_pt_in f (interval lb ub) x pr'.
Proof.
intros f x lb ub [l Hl] [l' Hl'] Hlu x_in ;
 apply derivable_pt_lim_interval_uniqueness with f lb ub x ;
 ass_apply.
Qed.

Lemma derivable_pt_lim_in_id : forall D x,
  derivable_pt_lim_in id D x 1.
Proof.
intros ; apply derivable_pt_lim_derivable_pt_lim_in,
 derivable_pt_lim_id.
Qed.

Lemma reciprocal_open_interval_restriction_compat :
  forall (f g : R -> R) (a b a' b' : R),
  open_interval a b a' -> open_interval a b b' ->
  reciprocal_open_interval f g a b ->
  reciprocal_interval f g a' b'.
Proof.
intros f g a b a' b' a'_in b'_in Hf x x_in ;
 eapply Hf, interval_open_restriction_compat ;
 try eapply x_in ; assumption.
Qed.

Lemma continuity_open_interval_continuity_interval : forall f lb ub x y,
  continuity_open_interval f lb ub -> open_interval lb ub x ->
  open_interval lb ub y -> continuity_interval f x y.
Proof.
intros f lb ub x y Hf x_in y_in z z_in ; eapply limit1_imp, Hf.
 intros t t_in ; eapply interval_open_restriction_compat, t_in ; assumption.
 eapply interval_open_restriction_compat, z_in ; assumption.
Qed.

Lemma derive_open_interval_pos_strictly_increasing_open_interval :
  forall f lb ub (pr : derivable_open_interval f lb ub),
  (forall x (x_in : open_interval lb ub x), 0 < derive_open_interval f lb ub pr x) ->
  strictly_increasing_open_interval f lb ub.
Proof.
intros f lb ub pr Df_pos x y x_in y_in Hxy.
 assert (pr1 : forall c : R, x < c < y -> derivable_pt f c).
  intros ; eapply derivable_open_interval_derivable_pt ; [eapply pr |].
   eapply open_interval_restriction_compat ; try eassumption ;
   apply open_interval_interval ; eassumption.
 assert (pr2 : forall c : R, x < c < y -> derivable_pt id c) by (intros ; apply derivable_id).
 destruct (MVT f id x y pr1 pr2) as [c [c_in Hc]].
  assumption.
  intros ; eapply derivable_continuous_pt, derivable_open_interval_derivable_pt ;
   [eapply pr | apply interval_open_restriction_compat with x y ; assumption].
  intros ; reg.
  unfold id in Hc ; fold id in Hc ; replace (derive_pt id c (pr2 c c_in)) with 1 in Hc ;
   [rewrite Rmult_1_r in Hc |].
  apply Rminus_gt ; rewrite <- Hc ; apply Rmult_lt_0_compat ; [fourier |].
   erewrite <- derive_pt_derive_open_interval ; [eapply Df_pos |] ;
    eapply open_interval_restriction_compat ;
    try (eapply open_interval_interval || apply c_in) ; eassumption.
  symmetry ; apply derive_pt_id.
Qed.