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

Require Import Rbase Ranalysis.
Require Import Rinterval Rfunctions Rfunction_def Rfunction_facts.
Require Import Ranalysis_def Ranalysis_def_simpl Ranalysis_continuity.
Require Import MyRIneq MyR_dist Lra.

Require Import Tactics.

Local Open Scope R_scope.

(** * Extensionality of derivable_* *)

Lemma derivable_pt_lim_in_ext: forall f g x D l, f == g ->
  derivable_pt_lim_in D f x l -> derivable_pt_lim_in D g x l.
Proof.
intros f g x D l Heq Hf eps eps_pos ;
 destruct (Hf _ eps_pos) as [alpha [alpha_pos Halpha]] ;
 exists alpha ; split ; [assumption |].
 intros ; erewrite growth_rate_ext ; [eapply Halpha | symmetry] ;
 eassumption.
Qed.

Lemma derivable_pt_lim_in_ext_strong: forall f g x (D : R -> Prop) l,
  D x -> (forall x, D x -> f x = g x) ->
  derivable_pt_lim_in D f x l -> derivable_pt_lim_in D g x l.
Proof.
intros f g x D l Dx Heq Hf eps eps_pos ;
 destruct (Hf _ eps_pos) as [alpha [alpha_pos Halpha]] ;
 exists alpha ; split ; [assumption |].
 intros ; rewrite growth_rate_ext_strong with (g := f) (D := D).
  apply Halpha ; assumption.
   assumption.
   intros ; symmetry ; apply Heq ; assumption.
   destruct H as [[Dy _] _] ; exact Dy.
Qed.

Lemma derivable_pt_in_ext : forall f g D x, f == g ->
  derivable_pt_in D f x -> derivable_pt_in D g x.
Proof.
intros f g D x Heq [l Hl] ; exists l ; eapply derivable_pt_lim_in_ext ; eassumption.
Qed.

Lemma derivable_pt_in_ext_strong : forall f g (D : R -> Prop) x,
  D x -> (forall x, D x -> f x = g x) ->
  derivable_pt_in D f x -> derivable_pt_in D g x.
Proof.
intros f g D x Dx Heq [l Hl] ; exists l ; eapply derivable_pt_lim_in_ext_strong ; eassumption.
Qed.

Lemma derivable_in_ext : forall f g D, f == g ->
  derivable_in D f -> derivable_in D g.
Proof.
intros f g D Heq Hf x Dx ; eapply derivable_pt_in_ext ; [| eapply_assumption] ; eassumption.
Qed.

Lemma derivable_in_ext_strong : forall f g (D : R -> Prop),
  (forall x, D x -> f x = g x) ->
  derivable_in D f -> derivable_in D g.
Proof.
intros f g D Heq Hf x Dx ; eapply derivable_pt_in_ext_strong ; [| | eapply_assumption] ; eassumption.
Qed.

(** Link between the stdlib's definition an ours. *)

Lemma derivable_pt_lim_derivable_pt_lim_in: forall f D x l,
  derivable_pt_lim f x l -> derivable_pt_lim_in D f x l.
Proof.
intros f D x l Hl eps eps_pos ; destruct (Hl _ eps_pos) as [delta Hdelta] ;
 exists delta ; split.
  apply delta.
  intros y [[Dy xny] xy_bd] ; simpl ; unfold R_dist, growth_rate ;
   replace (f y) with (f (x + (y - x))) by (f_equal ; ring) ; apply Hdelta.
   intro Hf ; apply xny ; revert Hf ; clear ; intuition.
   apply xy_bd.
Qed.

Lemma derivable_pt_derivable_pt_in: forall f D x,
  derivable_pt f x -> derivable_pt_in D f x.
Proof.
intros f D x [l Hl] ; exists l ;
 apply derivable_pt_lim_derivable_pt_lim_in ;
 assumption.
Qed.

Lemma derivable_derivable_in : forall f D,
  derivable f -> derivable_in D f.
Proof.
intros f D Hf x Dx ; apply derivable_pt_derivable_pt_in, Hf.
Qed.

(** * Unicity of the derivative *)

Lemma derivable_pt_lim_in_uniqueness:
  forall (D : R -> Prop) f x l l', dense D x ->
  derivable_pt_lim_in D f x l -> derivable_pt_lim_in D f x l' ->
  l = l'.
Proof.
intros D f x l l' Dx Hl ; eapply single_limit ; try eassumption ;
 intros eps eps_pos ; destruct (Dx _ eps_pos) as [y [y_h y_bd]] ;
 exists y.
Qed.

Lemma derivable_pt_lim_interval_uniqueness:
  forall (f : R -> R) (lb ub x l l' : R),
  lb < ub -> interval lb ub x ->
  derivable_pt_lim_in (interval lb ub) f x l ->
  derivable_pt_lim_in (interval lb ub) f x l' -> l = l'.
Proof.
intros ; eapply derivable_pt_lim_in_uniqueness ; try eassumption.
 apply dense_interval ; assumption.
Qed.

Lemma derivable_pt_lim_open_interval_uniqueness: forall f lb ub x l l',
  open_interval lb ub x ->
  derivable_pt_lim_in (open_interval lb ub) f x l ->
  derivable_pt_lim_in (open_interval lb ub) f x l' ->
  l = l'.
Proof.
intros ; eapply derivable_pt_lim_in_uniqueness ; try eassumption.
 apply dense_open_interval.
  eapply open_interval_inhabited ; eassumption.
  eapply open_interval_interval ; eassumption.
Qed.

Lemma derivable_pt_lim_Rball_uniqueness: forall c r f x l l', Rball c r x ->
  derivable_pt_lim_in (Rball c r) f x l ->
  derivable_pt_lim_in (Rball c r) f x l' ->
  l = l'.
Proof.
intros ; eapply derivable_pt_lim_in_uniqueness ; try eassumption ;
 apply dense_Rball ; assumption.
Qed.

Lemma derive_pt_in_open_interval_uniqueness :
  forall f x lb ub pr pr', open_interval lb ub x ->
  derive_pt_in (open_interval lb ub) f x pr =
  derive_pt_in (open_interval lb ub) f x pr'.
Proof.
intros f x lb ub [] [] x_in ;
 eapply derivable_pt_lim_open_interval_uniqueness ; eassumption.
Qed.

(** * In specific cases we can come back from the specific case to the one with no limitation. *)

(** open interval *)

Lemma derivable_pt_lim_open_interval_pt_lim :
  forall lb ub f x l, open_interval lb ub x ->
  derivable_pt_lim_in (open_interval lb ub) f x l -> derivable_pt_lim f x l.
Proof.
intros lb ub f x l x_in Hl eps eps_pos ; destruct (Hl _ eps_pos) as [d [d_pos Hd]] ;
 simpl in Hd ; unfold R_dist in Hd.
 pose (delta := Rmin (interval_dist lb ub x) d).
 assert (delta_pos : 0 < delta).
  apply Rmin_pos_lt ; [apply open_interval_dist_pos |] ; assumption.
 exists (mkposreal _ delta_pos) ; intros h h_neq h_bd ;
 specialize (Hd (x + h)) ; unfold growth_rate in * ;
 replace (x + h - x) with h in Hd by ring ; apply Hd ; split.
  split.
   apply open_interval_dist_bound ; [apply open_interval_interval
   | eapply Rlt_le_trans ; [| eapply Rmin_l]] ; eassumption.
   clear -h_neq ; intro Hf ; apply h_neq, Rplus_eq_reg_l with x ;
   rewrite <- Hf ; ring.
  eapply Rlt_le_trans ; [eassumption | eapply Rmin_r].
Qed.

Lemma derivable_open_interval_pt: forall f lb ub,
  derivable_open_interval lb ub f ->
  forall x, open_interval lb ub x -> derivable_pt f x.
Proof.
intros f lb ub H x Dx ; destruct (H x Dx) as [l Hl] ;
 exists l ; eapply derivable_pt_lim_open_interval_pt_lim ;
 eassumption.
Qed.

Lemma derive_open_interval_unfold : forall a b f f_deriv c (c_in : open_interval a b c),
  derive_open_interval a b f f_deriv c =
  derive_pt_in (open_interval a b) f c (f_deriv c c_in).
Proof.
intros a b f f_deriv c c_in ; unfold derive_open_interval ;
 destruct (in_open_interval_dec a b c) as [c_in' | hf].
 + apply derive_pt_in_open_interval_uniqueness ; assumption.
 + contradiction.
Qed.

Lemma derive_open_interval_pt : forall f lb ub x pr pr',
  open_interval lb ub x ->
  derive_pt_in (open_interval lb ub) f x pr = derive_pt f x pr'.
Proof.
intros f lb ub x [l Hl] [l' Hl'] x_in ; simpl ;
 eapply derivable_pt_lim_open_interval_uniqueness.
  eassumption.
  eassumption.
  eapply derivable_pt_lim_derivable_pt_lim_in ; assumption.
Qed.

Lemma derive_open_interval_derive : forall f lb ub x pr pr',
  open_interval lb ub x ->
  derive_open_interval lb ub f pr x = derive f pr' x.
Proof.
intros f lb ub x pr pr' x_in ; unfold derive_open_interval, derive.
 destruct (in_open_interval_dec lb ub x).
  apply derive_open_interval_pt ; assumption.
  contradiction.
Qed.

Lemma derive_open_interval_derive_pt : forall f lb ub x pr pr',
  open_interval lb ub x ->
  derive_open_interval lb ub f pr x = derive_pt f x pr'.
Proof.
intros f lb ub x pr pr' x_in ; unfold derive_open_interval, derive.
 destruct (in_open_interval_dec lb ub x).
  apply derive_open_interval_pt ; assumption.
  contradiction.
Qed.

(** Rball *)

Lemma derivable_pt_lim_Rball_pt_lim: forall f c r x l,
  Rball c r x -> derivable_pt_lim_in (Rball c r) f x l ->
  derivable_pt_lim f x l.
Proof.
intros ; eapply derivable_pt_lim_open_interval_pt_lim.
 eapply included_Rball_open_interval ; eassumption.
 eapply derivable_pt_lim_in_contravariant.
 eapply included_open_interval_Rball2 ; eassumption.
 eassumption.
Qed.

Lemma derivable_Rball_derivable_pt: forall f c r,
  derivable_Rball c r f ->
  forall x, Rball c r x -> derivable_pt f x.
Proof.
intros f lb ub H x Dx ; destruct (H x Dx) as [l Hl] ;
 exists l ; eapply derivable_pt_lim_Rball_pt_lim ;
 eassumption.
Qed.

Lemma derive_Rball_pt : forall f c r x pr pr',
  Rball c r x ->
  derive_pt_in (Rball c r) f x pr = derive_pt f x pr'.
Proof.
intros f lb ub x [l Hl] [l' Hl'] x_in ; simpl ;
 eapply derivable_pt_lim_Rball_uniqueness.
  eassumption.
  eassumption.
  eapply derivable_pt_lim_derivable_pt_lim_in ; assumption.
Qed.

Lemma derive_Rball_derive : forall f c r x pr pr',
  Rball c r x ->
  derive_Rball c r f pr x = derive f pr' x.
Proof.
intros f c r x pr pr' x_in ; unfold derive_Rball, derive.
 destruct (in_Rball_dec c r x).
  apply derive_Rball_pt ; assumption.
  contradiction.
Qed.

(** Proof by restriction to a local open_interval *)

Lemma derivable_open_interval_derivable : forall f,
  (forall lb ub, derivable_open_interval lb ub f) ->
  derivable f.
Proof.
intros f Hf x ; eapply derivable_open_interval_pt, (center_in_open_interval _ 1).
 apply Hf.
 lra.
Qed.

(** * derivable implies continuous *)

Lemma derivable_pt_in_continuity_pt_in : forall f D x,
    derivable_pt_in f D x -> continuity_pt_in f D x.
Proof.
intros D f x [l Hl] Dx eps eps_pos.
 pose (eps' := Rmin eps (eps / (eps + Rabs l))).
 assert (eps'_pos: 0 < eps').
  apply Rmin_pos_lt, Rlt_mult_inv_pos, Rplus_lt_le_0_compat ;
  [| | | apply Rabs_pos] ; assumption.
 destruct (Hl _ eps'_pos) as [alp [alp_pos Halp]] ;
 exists (Rmin alp eps') ; split ; [apply Rmin_pos_lt ; assumption |].
 intros y [Dy y_bd] ; destruct (Req_dec y x) as [Heq | Hneq].
  subst ; rewrite R_dist_eq ; assumption.
  transitivity ((eps + Rabs l) * Rabs (y - x)).
  apply Rle_lt_trans with (Rabs (growth_rate f x y) * Rabs (y - x)).
   right ; simpl ; unfold R_dist, growth_rate ; rewrite <- Rabs_mult ;
   apply Rabs_eq_compat ; field ; apply Rminus_eq_contra ; assumption.
   apply Rle_lt_trans with ((dist R_met (growth_rate f x y) l + Rabs l) * Rabs (y - x)).
   apply Rmult_le_compat_r ; [apply Rabs_pos |].
   apply Rle_trans with (Rabs (growth_rate f x y - l + l)) ;
   [right ; apply Rabs_eq_compat ; ring | apply Rabs_triang].
   apply Rmult_lt_compat_r ; [apply Rabs_pos_lt, Rminus_eq_contra ; assumption |].
   apply Rplus_lt_compat_r, Rlt_le_trans with eps'.
   apply Halp ; repeat split ; [assumption | symmetry ; assumption |].
   apply Rlt_le_trans with (Rmin alp eps'), Rmin_l ; assumption.
   apply Rmin_l.
   apply Rlt_le_trans with ((eps + Rabs l) * eps').
   apply Rmult_lt_compat_l.
    apply Rplus_lt_le_0_compat ; [assumption | apply Rabs_pos].
    apply Rlt_le_trans with (Rmin alp eps') ; [apply y_bd | apply Rmin_r].
   transitivity ((eps + Rabs l) * (eps / (eps + Rabs l))).
   apply Rmult_le_compat_l, Rmin_r ; apply Rplus_le_le_0_compat ;
   [left ; assumption | apply Rabs_pos].
   right ; field ; apply Rgt_not_eq, Rplus_lt_le_0_compat, Rabs_pos ; assumption.
Qed.

Lemma derivable_in_continuity_in : forall f D,
    derivable_in D f -> continuity_in D f.
Proof.
intros f D Hf x Dx ; apply derivable_pt_in_continuity_pt_in.
 apply Hf ; assumption.
 assumption.
Qed.

(** Value of the derivative *)

Lemma derivable_pt_lim_in_derive_pt_Rball: forall c r f x l pr,
  Rball c r x ->
  derivable_pt_lim_in (Rball c r) f x l ->
  derive_pt_in (Rball c r) f x pr = l.
Proof.
intros c r f x l [l' Hl'] x_in Hl ; eapply derivable_pt_lim_Rball_uniqueness ;
 eassumption.
Qed.

Lemma derivable_pt_lim_in_derive_Rball: forall c r f x l pr, Rball c r x ->
  derivable_pt_lim_in (Rball c r) f x l ->
  derive_Rball c r f pr x = l.
Proof.
intros c r f x l pr x_in Hl ; unfold derive_Rball ;
 destruct (in_Rball_dec c r x) as [x_in2 | x_nin].
 eapply derivable_pt_lim_in_derive_pt_Rball ; eassumption.
 contradiction.
Qed.

Lemma derivable_pt_lim_derive_pt_interval: forall f lb ub x l
  (pr : derivable_pt_in (interval lb ub) f x),
  lb < ub -> interval lb ub x ->
  derivable_pt_lim_in (interval lb ub) f x l ->
  derive_pt_in (interval lb ub) f x pr = l.
Proof.
intros f lb ub x l [l' Hl'] x_in Hl ;
 eapply derivable_pt_lim_interval_uniqueness ;
 eassumption.
Qed.

Lemma derivable_pt_lim_derive_pt_open_interval: forall f lb ub x l
  (pr : derivable_pt_in (open_interval lb ub) f x),
  open_interval lb ub x ->
  derivable_pt_lim_in (open_interval lb ub) f x l ->
  derive_pt_in (open_interval lb ub) f x pr = l.
Proof.
intros f lb ub x l [l' Hl'] x_in Hl ;
 eapply derivable_pt_lim_open_interval_uniqueness ;
 eassumption.
Qed.

Lemma derive_pt_derivable_pt_lim_interval: forall f lb ub x l
  (pr : derivable_pt_in (interval lb ub) f x),
  lb < ub -> interval lb ub x ->
  derive_pt_in (interval lb ub) f x pr = l ->
  derivable_pt_lim_in (interval lb ub) f x l.
Proof.
intros f lb ub x l [l' Hl'] Hlt x_in Hl ; subst ; assumption.
Qed.

(** Extensionality of the derive_* definitions *)

Lemma derive_pt_in_ext:
  forall D f g x (prf: derivable_pt_in D f x) (prg: derivable_pt_in D g x),
  dense D x -> D x -> f == g ->
  derive_pt_in D f x prf = derive_pt_in D g x prg.
Proof.
intros D f g x [l1 Hl1] [l2 Hl2] dD x_in Heq ; simpl ;
 eapply derivable_pt_lim_in_uniqueness ; [eassumption | | eassumption].
 eapply derivable_pt_lim_in_ext ; eassumption.
Qed.

Lemma derive_pt_in_ext_strong: forall (D : R -> Prop) f g x
  (prf: derivable_pt_in D f x) (prg: derivable_pt_in D g x),
  dense D x -> D x -> (forall x, D x -> f x = g x) ->
  derive_pt_in D f x prf = derive_pt_in D g x prg.
Proof.
intros D f g x [l1 Hl1] [l2 Hl2] dD x_in Heq ; simpl ;
 eapply derivable_pt_lim_in_uniqueness ; [eassumption | | eassumption].
 eapply derivable_pt_lim_in_ext_strong ; eassumption.
Qed.

Lemma derive_Rball_ext:
  forall c r f g (prf: derivable_Rball c r f) (prg: derivable_Rball c r g),
  f == g ->
  derive_Rball c r f prf == derive_Rball c r g prg.
Proof.
intros c r f g prf prg Heq x ; unfold derive_Rball ;
 destruct (in_Rball_dec c r x) as [HT1 | HF1].
 eapply derive_pt_in_ext ; [apply dense_Rball | |] ; assumption.
 reflexivity.
Qed.

Lemma derive_Rball_ext_strong:
  forall c r f g (prf: derivable_Rball c r f) (prg: derivable_Rball c r g),
  Rball_eq c r f g ->
  derive_Rball c r f prf == derive_Rball c r g prg.
Proof.
intros c r f g prf prg Heq x ; unfold derive_Rball ;
 destruct (in_Rball_dec c r x) as [HT1 | HF1].
 eapply derive_pt_in_ext_strong ; [apply dense_Rball | |] ; assumption.
 reflexivity.
Qed.

Lemma derive_derive_Rball: forall c r f pr pr',
  Rball_eq c r (derive f pr) (derive_Rball c r f pr').
Proof.
intros c r f pr pr' x x_in ; unfold derive_Rball ;
 destruct (in_Rball_dec c r x) as [HT | HF].
 destruct (pr' x HT) as [l Hl] ; simpl ; unfold derive ;
  rewrite derive_pt_eq ; eapply derivable_pt_lim_Rball_pt_lim ;
  eassumption.
 destruct (HF x_in).
Qed.

(** * Compatibility of derivable_*_in with common operations. *)

(** constant functions *)

Lemma derivable_pt_lim_in_const: forall D k x,
  derivable_pt_lim_in D (fun _ => k) x 0.
Proof.
intros D k x eps eps_pos ; exists 1 ; intros ; split.
 lra.
 intros ; simpl ; unfold R_dist, growth_rate, Rminus, Rdiv ;
 rewrite Rplus_opp_r, Rmult_0_l, Rplus_opp_r, Rabs_R0 ;
 assumption.
Qed.

Lemma derivable_pt_in_const : forall D k x,
  derivable_pt_in D (fun _ => k) x.
Proof.
intros ; eexists ; eapply derivable_pt_lim_in_const.
Qed.

Lemma derivable_in_const : forall D k,
  derivable_in D (fun _ => k).
Proof.
intros D k x x_in ; eapply derivable_pt_in_const.
Qed.

Lemma derive_pt_Rball_const : forall k c r x pr,
  Rball c r x ->
  derive_pt_in (Rball c r) (fun _ => k) x pr = 0.
Proof.
intros k c r x pr x_in ;
  eapply derivable_pt_lim_in_derive_pt_Rball ;
 [eexact x_in | eapply derivable_pt_lim_in_const].
Qed.

Lemma derive_Rball_const : forall k c r x pr,
  derive_Rball c r (fun _ => k) pr x = 0.
Proof.
intros k c r x pr ; unfold derive_Rball ;
 destruct (in_Rball_dec c r x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_const | reflexivity] ; assumption.
Qed.

(** multiplication by a scalar *)

Lemma derivable_pt_lim_in_scal: forall D a f x l,
  derivable_pt_lim_in D f x l ->
  derivable_pt_lim_in D (mult_real_fct a f) x (a * l).
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

Lemma derivable_pt_in_scal: forall D a f x,
  derivable_pt_in D f x ->
  derivable_pt_in D (mult_real_fct a f) x.
Proof.
intros D a f x [l Hl] ; eexists ; eapply derivable_pt_lim_in_scal ; eassumption.
Qed.

Lemma derivable_in_scal: forall D a f,
  derivable_in D f ->
  derivable_in D (mult_real_fct a f).
Proof.
intros D a f Hf x x_in ; specialize (Hf x x_in);
 apply derivable_pt_in_scal ; assumption.
Qed.

Lemma derive_pt_Rball_scal: forall a f c r x pr pr',
  Rball c r x ->
  derive_pt_in (Rball c r) (mult_real_fct a f) x pr =
  a * derive_pt_in (Rball c r) f x pr'.
Proof.
intros a f c r x [] [] x_in ;
 eapply derivable_pt_lim_in_derive_pt_Rball, derivable_pt_lim_in_scal ;
 eassumption.
Qed.

Lemma derive_Rball_scal: forall a f c r x pr pr',
  derive_Rball c r (mult_real_fct a f) pr x =
  a * derive_Rball c r f pr' x.
Proof.
intros ; unfold derive_Rball ; destruct (in_Rball_dec c r x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_scal ; assumption | symmetry ; apply Rmult_0_r].
Qed.

(** opposite of a function *)

Lemma derivable_pt_lim_in_opp: forall D f x l,
  derivable_pt_lim_in D f x l ->
  derivable_pt_lim_in D (- f)%F x (- l).
Proof.
intros ; eapply limit1_ext.
 intros y Hy ; symmetry ; apply growth_rate_opp_compat ; split ;
  [unfold no_cond ; trivial | apply Hy].
 apply limit_Ropp ; assumption.
Qed.

Lemma derivable_pt_in_opp: forall (D : R -> Prop) f x,
  derivable_pt_in D f x -> derivable_pt_in D (- f)%F x.
Proof.
intros D f x [] ; eexists ; eapply derivable_pt_lim_in_opp ; eassumption.
Qed.

Lemma derivable_in_opp: forall (D : R -> Prop) f,
  derivable_in D f -> derivable_in D (- f)%F.
Proof.
intros D f Hf x x_in ; eapply derivable_pt_in_opp, Hf ;
 eassumption.
Qed.

Lemma derive_pt_Rball_opp: forall f c r x pr pr', Rball c r x ->
  derive_pt_in (Rball c r) (- f)%F x pr = - derive_pt_in (Rball c r) f x pr'.
Proof.
intros f c r x [] [] x_in ;
 eapply derivable_pt_lim_Rball_uniqueness, derivable_pt_lim_in_opp ;
 eassumption. 
Qed.

Lemma derive_Rball_opp: forall f c r x pr pr',
  derive_Rball c r (- f)%F pr x = - derive_Rball c r f pr' x.
Proof.
intros ; unfold derive_Rball ; destruct (in_Rball_dec c r x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_opp ; assumption | rewrite Ropp_0 ; reflexivity].
Qed.

(** sum of two functions *)

Lemma derivable_pt_lim_in_plus: forall D f g x l1 l2,
  derivable_pt_lim_in D f x l1 ->
  derivable_pt_lim_in D g x l2 ->
  derivable_pt_lim_in D (f + g)%F x (l1 + l2).
Proof.
intros ; eapply limit1_ext.
 intros y Hy ; symmetry ; apply growth_rate_plus_compat ; split ;
  [unfold no_cond ; trivial | apply Hy].
 apply limit_plus ; assumption.
Qed.

Lemma derivable_pt_in_plus: forall (D : R -> Prop) f g x,
  derivable_pt_in D f x -> derivable_pt_in D g x ->
  derivable_pt_in D (f + g)%F x.
Proof.
intros D f g x [] [] ; eexists ; eapply derivable_pt_lim_in_plus ; eassumption.
Qed.

Lemma derivable_in_plus: forall D f g,
  derivable_in D f -> derivable_in D g ->
  derivable_in D (f + g)%F.
Proof.
intros D f g Hf Hg x x_in ; eapply derivable_pt_in_plus ;
 [eapply Hf | eapply Hg] ; eassumption.
Qed.

Lemma derive_pt_Rball_plus: forall f g c r x prf prg prfg, Rball c r x ->
  derive_pt_in (Rball c r) (f + g)%F x prfg =
  derive_pt_in (Rball c r) f x prf + derive_pt_in (Rball c r) g x prg.
Proof.
intros f g c r x [] [] [] x_in ; eapply derivable_pt_lim_Rball_uniqueness,
 derivable_pt_lim_in_plus ; eassumption.
Qed.

Lemma derive_Rball_plus: forall f g c r x prf prg prfg,
  derive_Rball c r (f + g)%F prfg x =
  derive_Rball c r f prf x + derive_Rball c r g prg x.
Proof.
intros ; unfold derive_Rball ; destruct (in_Rball_dec c r x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_plus ; assumption | rewrite Rplus_0_r ; reflexivity].
Qed.

(** difference of two functions *)

Lemma derivable_pt_lim_in_minus: forall D f g x l1 l2,
  derivable_pt_lim_in D f x l1 -> derivable_pt_lim_in D g x l2 ->
  derivable_pt_lim_in D (f - g)%F x (l1 - l2).
Proof.
intros ; eapply limit1_ext.
 intros y Hy ; symmetry ; apply growth_rate_minus_compat ; split ;
  [unfold no_cond ; trivial | apply Hy].
 apply limit_minus ; assumption.
Qed.

Lemma derivable_pt_in_minus:
  forall (D : R -> Prop) (f g : R -> R) (x : R),
  derivable_pt_in D f x -> derivable_pt_in D g x ->
  derivable_pt_in D (f - g)%F x.
Proof.
intros D f g x [] []; eexists ; eapply derivable_pt_lim_in_minus ; eassumption.
Qed.

Lemma derivable_in_minus: forall D f g,
  derivable_in D f -> derivable_in D g ->
  derivable_in D (f - g)%F.
Proof.
intros D f g Hf Hg x x_in ; eapply derivable_pt_in_minus ;
 [eapply Hf | eapply Hg] ; eassumption.
Qed.

Lemma derive_pt_Rball_minus: forall f g c r x prf prg prfg, Rball c r x ->
  derive_pt_in (Rball c r) (f - g)%F x prfg =
  derive_pt_in (Rball c r) f x prf - derive_pt_in (Rball c r) g x prg.
Proof.
intros f g c r x [] [] [] x_in ; eapply derivable_pt_lim_Rball_uniqueness,
 derivable_pt_lim_in_minus ; eassumption.
Qed.

Lemma derive_Rball_minus: forall f g c r x prf prg prfg,
  derive_Rball c r (f - g)%F prfg x =
  derive_Rball c r f prf x - derive_Rball c r g prg x.
Proof.
intros ; unfold derive_Rball ; destruct (in_Rball_dec c r x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_minus ; assumption | rewrite Rminus_0_r ; reflexivity].
Qed.

(** Product of two functions *)

Lemma derivable_pt_lim_in_mult: forall (D : R -> Prop) f g x l1 l2, D x ->
  derivable_pt_lim_in D f x l1 -> derivable_pt_lim_in D g x l2 ->
  derivable_pt_lim_in D (f * g)%F x (l1 * g x + f x * l2).
Proof.
intros D f g x l1 l2 Dx Hf Hg ; eapply limit1_in_ext.
  intros y [Dy Hneq] ; symmetry ; apply growth_rate_mult_decomp, Hneq.
  apply limit_plus ; apply limit_mul ; [apply Hf | | | apply Hg].
  apply limit_free.
  apply limit1_imp with D.
   intros y [y_in y_neq] ; exact y_in.
   apply derivable_pt_in_continuity_pt_in ; [eexists |] ; eassumption.
Qed.

Lemma derivable_pt_in_mult: forall (D : R -> Prop) f g x, D x ->
  derivable_pt_in D f x -> derivable_pt_in D g x ->
  derivable_pt_in D (f * g)%F x.
Proof.
intros D f g x x_in [] [] ; eexists ; eapply derivable_pt_lim_in_mult ; eassumption.
Qed.

Lemma derivable_in_mult: forall D f g,
  derivable_in D f -> derivable_in D g ->
  derivable_in D (f * g)%F.
Proof.
intros D f g Hf Hg x x_in ; eapply derivable_pt_in_mult ;
 [| eapply Hf | eapply Hg] ; eassumption.
Qed.

Lemma derive_pt_Rball_mult: forall f g c r x prf prg prfg, Rball c r x ->
  derive_pt_in (Rball c r) (f * g)%F x prfg =
  derive_pt_in (Rball c r) f x prf * g x + f x * derive_pt_in (Rball c r) g x prg.
Proof.
intros f g c r x [] [] [] x_in ; eapply derivable_pt_lim_Rball_uniqueness,
 derivable_pt_lim_in_mult ; eassumption.
Qed.

Lemma derive_Rball_mult: forall f g c r x prf prg prfg,
  derive_Rball c r (f * g)%F prfg x =
  derive_Rball c r f prf x * g x + f x * derive_Rball c r g prg x.
Proof.
intros ; unfold derive_Rball ; destruct (in_Rball_dec c r x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_mult ; assumption | ring].
Qed.

(** inverse of a function *)

Lemma derivable_pt_lim_in_inv: forall (D : R -> Prop) f x l,
  D x -> f x <> 0 -> derivable_pt_lim_in D f x l ->
  derivable_pt_lim_in D (/ f)%F x (- l / (f x ^ 2)).
Proof.
intros D f x l Dx Hneq Hf ; assert (f_cont: continuity_pt_in D f x)
 by (eapply derivable_pt_in_continuity_pt_in ; eexists ; eassumption).
 destruct (continuity_not_eq_Rball _ _ _ 0 Dx f_cont Hneq) as [alp [alp_pos Halp]] ;
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

Lemma derivable_pt_in_inv: forall (D : R -> Prop) f x,
  D x -> f x <> 0 -> derivable_pt_in D f x ->
  derivable_pt_in D (/ f)%F x.
Proof.
intros D f x Dx Hneq [] ; eexists ; eapply derivable_pt_lim_in_inv ; eassumption.
Qed.

Lemma derivable_in_inv: forall (D : R -> Prop) f,
  (forall x, D x -> f x <> 0) -> derivable_in D f ->
  derivable_in D (/ f)%F.
Proof.
intros D f Hneq Hf x x_in ; apply derivable_pt_in_inv ;
 [| apply Hneq | apply Hf] ; assumption.
Qed.

Lemma derive_pt_Rball_inv: forall f c r x pr pr',
  Rball c r x -> f x <> 0 ->
  derive_pt_in (Rball c r) (/ f)%F x pr =
  (- derive_pt_in (Rball c r) f x pr') / (f x) ^ 2.
Proof.
intros f c r x [] [] x_in fx_neq ; eapply derivable_pt_lim_Rball_uniqueness,
 derivable_pt_lim_in_inv ; eassumption.
Qed.

Lemma derive_Rball_inv: forall f c r x pr pr', f x <> 0 ->
  derive_Rball c r (/ f)%F pr x = (- derive_Rball c r f pr' x) / (f x) ^ 2.
Proof.
intros ; unfold derive_Rball ; destruct (in_Rball_dec c r x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_inv ; assumption | rewrite Ropp_0, Rdiv_0_l ; reflexivity].
Qed.

(** Division of a function by another *)

Lemma derivable_pt_lim_in_div: forall (D : R -> Prop) f g x l1 l2,
  D x -> g x <> 0 ->
  derivable_pt_lim_in D f x l1 -> derivable_pt_lim_in D g x l2 ->
  derivable_pt_lim_in D (f / g)%F x ((l1 * g x - f x * l2) / g x ^ 2).
Proof.
intros D f g x l1 l2 Dx Hneq Hf Hg ; apply derivable_pt_lim_in_ext with (f * / g)%F.
 intro ; reflexivity.
 replace ((l1 * g x - f x * l2) / g x ^ 2) with ((l1 * (/ g)%F x) + f x * (- l2 / g x ^ 2)).
 eapply derivable_pt_lim_in_mult ; try eassumption.
 eapply derivable_pt_lim_in_inv ; try eassumption.
 unfold inv_fct ; field ; assumption.
Qed.

Lemma derivable_pt_in_div: forall (D : R -> Prop) f g x,
  D x -> g x <> 0 ->
  derivable_pt_in D f x -> derivable_pt_in D g x ->
  derivable_pt_in D (f / g)%F x.
Proof.
intros D f g x Dx Hneq [] [] ; eexists ; eapply derivable_pt_lim_in_div ; eassumption.
Qed.

Lemma derivable_in_div: forall (D : R -> Prop) f g,
  (forall x, D x -> g x <> 0) ->
  derivable_in D f -> derivable_in D g ->
  derivable_in D (f / g)%F.
Proof.
intros D f g Hneq Hf Hg x x_in ; apply derivable_pt_in_div ;
 [| apply Hneq | apply Hf | apply Hg] ; assumption.
Qed.


Lemma derive_pt_Rball_div: forall f g c r x prf prg prfg,
  Rball c r x -> g x <> 0 ->
  derive_pt_in (Rball c r) (f / g)%F x prfg =
  (derive_pt_in (Rball c r) f x prf * g x - f x * derive_pt_in (Rball c r) g x prg) / (g x) ^ 2.
Proof.
intros f g c r x [] [] [] x_in gx_neq ; eapply derivable_pt_lim_Rball_uniqueness,
 derivable_pt_lim_in_div ; eassumption.
Qed.

Lemma derive_Rball_div: forall f g c r x prf prg prfg, g x <> 0 ->
  derive_Rball c r (f / g)%F prfg x =
  (derive_Rball c r f prf x * g x - f x * derive_Rball c r g prg x) / (g x) ^ 2.
Proof.
intros ; unfold derive_Rball ; destruct (in_Rball_dec c r x) as [x_in | x_nin] ;
 [apply derive_pt_Rball_div ; assumption
 | rewrite Rmult_0_r, Rmult_0_l, Rminus_0_r, Rdiv_0_l ; reflexivity].
Qed.

(** For more complicated cases we (at the moment) deal only
    with Rball because this is what we need ultimately. *)

(*TODO: prove that stuff in the general case! *)

Lemma derivable_pt_lim_Rball_comp: forall cf rf cg rg f g x l1 l2,
  Rball cf rf x -> Rball cg rg (f x) ->
  derivable_pt_lim_in (Rball cf rf) f x l1 ->
  derivable_pt_lim_in (Rball cg rg) g (f x) l2 ->
  derivable_pt_lim_in (Rball cf rf) (comp g f) x (l1 * l2).
Proof.
intros cf rf cg rg f g x l1 l2 x_in fx_in Hf Hg ; rewrite Rmult_comm.
 apply derivable_pt_lim_derivable_pt_lim_in, derivable_pt_lim_comp ;
 eapply derivable_pt_lim_Rball_pt_lim ; eassumption.
Qed.

Lemma derivable_pt_Rball_comp: forall cf rf cg rg f g x,
  Rball cf rf x -> Rball cg rg (f x) ->
  derivable_pt_in (Rball cf rf) f x ->
  derivable_pt_in (Rball cg rg) g (f x) ->
  derivable_pt_in (Rball cf rf) (comp g f) x.
Proof.
intros cf rf cg rg f g x x_in y_in [] [] ; eexists ;
 eapply derivable_pt_lim_Rball_comp ; eassumption.
Qed.

Lemma derivable_Rball_comp: forall cf rf cg rg f g,
  (forall x, Rball cf rf x -> Rball cg rg (f x)) ->
  derivable_Rball cf rf f -> derivable_Rball cg rg g ->
  derivable_Rball cf rf (comp g f).
Proof.
intros cf rf cg rg f g g_ok Hf Hg x x_in ;
 eapply derivable_pt_Rball_comp ; [| | eapply Hf | eapply Hg] ;
 try eapply g_ok ; eassumption.
Qed.

