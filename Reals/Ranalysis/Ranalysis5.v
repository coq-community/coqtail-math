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

Require Import Rbase.
Require Import Ranalysis.
Require Import Rfunctions Rfunction_def.
Require Import Rseries_def.
Require Import Fourier.
Require Import RiemannInt.
Require Import SeqProp.
Require Import Max.
Require Import RIneq MyRIneq.
Require Import Ranalysis_def Ranalysis_facts Rinterval.
Require Import RIVT.

Require Import Ass_handling.

Local Open Scope R_scope.

Lemma interval_restriction_compat : forall a b a' b' x,
  interval a b a' -> interval a b b' ->
  interval a' b' x -> interval a b x.
Proof.
intros a b a' b' x [] [] [] ; split ; fourier.
Qed.

Lemma open_interval_restriction_compat : forall a b a' b' x,
  interval a b a' -> interval a b b' ->
  open_interval a' b' x -> open_interval a b x.
Proof.
intros a b a' b' x [] [] [] ; split ; fourier.
Qed.

Lemma interval_open_restriction_compat : forall a b a' b' x,
  open_interval a b a' -> open_interval a b b' ->
  interval a' b' x -> open_interval a b x.
Proof.
intros a b a' b' x [] [] [] ; split ; fourier.
Qed.

Lemma strictly_increasing_interval_restriction_compat :
 forall f a b a' b', interval a b a' -> interval a b b' ->
 strictly_increasing_interval f a b ->
 strictly_increasing_interval f a' b'.
Proof.
intros f a b a' b' a'_in b'_in Hf x y x_in y_in ;
 apply Hf ; apply interval_restriction_compat with a' b' ;
 assumption.
Qed.

Lemma Rlt_minus_sort : forall a b c, a < c + b -> a - c < b.
Proof.
intros ; fourier.
Qed.

Lemma Rlt_minus_sort2 : forall a b c, a - c < b -> - c < b - a.
Proof.
intros ; fourier.
Qed.

(** * Continuity of the reciprocal function *)

Lemma continuity_reciprocal_strictly_increasing_open_interval :
  forall (f g:R->R) (lb ub:R), lb <= ub ->
  strictly_increasing_interval f lb ub -> 
  reciprocal_interval g f lb ub -> continuity_interval f lb ub ->
  continuity_open_interval g (f lb) (f ub).
Proof.
intros f g lb ub lb_le_ub f_incr Hfg Hf b b_in.
 destruct (IVT_interval f lb ub b) as [a [Ia Ha]] ;
  try assumption. apply open_interval_interval ; assumption.
  assert (a_in : open_interval lb ub a).
   apply interval_open_interval ; [assumption | |].
    intro Hfalse ; rewrite Hfalse, Ha in b_in ; apply (Rlt_irrefl b), b_in.
    intro Hfalse ; rewrite Hfalse, Ha in b_in ; apply (Rlt_irrefl b), b_in.
  clear Ia.
  intros eps eps_pos ; pose (xlb := Rmax (a - eps) lb) ;
   pose (xub := Rmin (a + eps) ub).
   assert (xlb_in : interval lb ub xlb).
    split ; [apply RmaxLess2 |].
     unfold xlb ; apply Rmax_le_le_le ; split.
      transitivity a ; [fourier | left ; apply a_in].
      assumption.
   assert (xub_in : interval lb ub xub).
    split ; [| apply Rmin_r].
     unfold xub ; apply Rmin_le_le_le ; split.
      transitivity a ; [left ; apply a_in | fourier].
      assumption.
   assert (a_in' : open_interval xlb xub a).
    split ; [apply Rmax_lt_lt_lt | apply Rmin_lt_lt_lt] ;
    split ; (fourier || apply a_in).
   exists (interval_dist (f xlb) (f xub) (f a)) ; split.
    apply open_interval_dist_pos, strictly_increasing_interval_image.
     eapply strictly_increasing_interval_restriction_compat ; eassumption.
     assumption.
    intros x [x_in x_bd] ; rewrite <- Ha in x_bd.
    destruct (IVT_interval f xlb xub x) as [a' [a'_in Ha']].
     eapply continuity_interval_restriction_compat ; eassumption.
     left ; eapply open_interval_inhabited ; eassumption.
     replace x with (f a + (x - f a)) by ring ; apply interval_dist_bound.
     apply open_interval_interval, strictly_increasing_interval_image ;
     [eapply strictly_increasing_interval_restriction_compat |] ;
     eassumption.
     left ; apply x_bd.
    rewrite <- Ha, <- Ha'.
    assert (Hrew := Hfg a (open_interval_interval _ _ _ a_in)) ;
     unfold comp, id in Hrew ; rewrite Hrew ; clear Hrew.
    assert (Hrew := Hfg a') ; unfold comp, id in Hrew ;
     rewrite Hrew ; clear Hrew.
     simpl ; apply Rabs_def1.
      apply Rlt_minus_sort, Rlt_le_trans with xub ; [| apply Rmin_l].
       apply Rle_neq_lt ; [apply a'_in |].
       intro Hfalse ; rewrite <- Hfalse, <- Ha' in x_bd ;
       apply (Rlt_irrefl (f a' - f a)), Rlt_le_trans with
       (interval_dist (f xlb) (f a') (f a)) ; [| apply Rmin_r].
       eapply Rle_lt_trans, x_bd ; right ; symmetry ; simpl ;
        apply Rabs_right ; left ; apply Rgt_minus, f_incr.
         eapply open_interval_interval, open_interval_restriction_compat with lb ub ;
         try (apply interval_l || apply interval_r || rewrite Hfalse) ; eassumption.
         rewrite Hfalse ; assumption.
         rewrite Hfalse ; apply a_in'.
       apply Rlt_minus_sort2, Rle_lt_trans with xlb ; [apply RmaxLess1 |].
       apply Rle_neq_lt ; [apply a'_in |].
       intro Hfalse ; rewrite Hfalse, <- Ha' in x_bd ;
       apply (Rlt_irrefl (f a - f a')), Rlt_le_trans with
       (interval_dist (f a') (f xub) (f a)) ; [| apply Rmin_l].
       eapply Rle_lt_trans, x_bd ; right ; symmetry ; simpl.
        rewrite R_dist_sym ; apply Rabs_right ; left ; apply Rgt_minus, f_incr.
         rewrite <- Hfalse ; assumption.
         eapply open_interval_interval, open_interval_restriction_compat with lb ub ;
         try (apply interval_l || apply interval_r || rewrite <- Hfalse) ; eassumption.
         rewrite <- Hfalse ; apply a_in'.
       apply interval_restriction_compat with xlb xub ; eassumption.
Qed.

Lemma continuity_open_interval_opp_compat : forall f lb ub,
  continuity_open_interval f lb ub ->
  continuity_open_interval (- f)%F lb ub.
Proof.
intros f lb ub Hf b b_in ; apply limit_Ropp, Hf ; assumption.
Qed.

Lemma continuity_open_interval_ext : forall (f g : R -> R) lb ub,
  (f == g)%F -> continuity_open_interval f lb ub ->
  continuity_open_interval g lb ub.
Proof.
intros f g lb ub Heq Hf b b_in ; eapply limit1_in_ext.
 intros ; apply Heq.
 rewrite <- (Heq b) ; apply Hf ; assumption.
Qed.

Lemma R_dist_Ropp_compat : forall x y,
  R_dist (- x) (- y) = R_dist x y.
Proof.
intros x y ; unfold R_dist, Rminus ; rewrite <- Ropp_plus_distr ;
 apply Rabs_Ropp.
Qed.

Lemma continuity_open_interval_Ropp_compat : forall f lb ub,
  continuity_open_interval f lb ub ->
  continuity_open_interval (fun x => f (- x)) (- ub) (- lb).
Proof.
intros f lb ub Hf b b_in eps eps_pos.
 assert (mb_in : open_interval lb ub (- b)).
  destruct b_in ; split ; fourier.
 destruct (Hf _ mb_in _ eps_pos) as [alpha [alpha_pos Halpha]] ;
 exists alpha ; split ; [assumption | intros x [x_in x_bd]].
 apply Halpha ; split ; simpl.
  destruct x_in ; split ; fourier.
  rewrite R_dist_Ropp_compat ; assumption.
Qed.

Lemma continuity_open_interval_Ropp_compat_rev : forall f lb ub,
  continuity_open_interval (fun x => f (- x)) (- ub) (- lb) ->
  continuity_open_interval f lb ub.
Proof.
intros f lb ub Hf ; pose (F := fun x => f (- x)) ;
 apply continuity_open_interval_ext with (fun x => F (- x)).
 intro x ; unfold F ; f_equal ; apply Ropp_involutive.
  rewrite <- (Ropp_involutive lb), <- (Ropp_involutive ub) ;
  apply continuity_open_interval_Ropp_compat, Hf.
Qed.

Lemma continuity_reciprocal_strictly_decreasing_open_interval :
  forall (f g:R->R) (lb ub:R), lb <= ub ->
  strictly_decreasing_interval f lb ub -> 
  reciprocal_interval g f lb ub -> continuity_interval f lb ub ->
  continuity_open_interval g (f ub) (f lb).
Proof.
intros f g lb ub lb_le_ub f_incr Hfg Hf ;
 apply continuity_open_interval_Ropp_compat_rev.
 apply (continuity_reciprocal_strictly_increasing_open_interval (- f)%F).
  assumption.
  apply strictly_decreasing_strictly_increasing_interval ; assumption.
  apply reciprocal_opp_compat_interval ; assumption.
  apply continuity_interval_opp_compat ; assumption.
Qed.

Lemma continuity_reciprocal_strictly_monotonous_open_interval :
  forall (f g:R->R) (lb ub:R), lb <= ub ->
  strictly_monotonous_interval f lb ub -> 
  reciprocal_interval g f lb ub -> continuity_interval f lb ub ->
  continuity_open_interval g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)).
Proof.
intros f g lb ub lb_le_ub f_mono f_eq_g f_cont_interv.
 destruct f_mono as [f_incr | f_decr].
 rewrite strictly_increasing_Rmax_simpl, strictly_increasing_Rmin_simpl ;
 try assumption ; apply continuity_reciprocal_strictly_increasing_open_interval ;
 assumption.
 rewrite strictly_decreasing_Rmax_simpl, strictly_decreasing_Rmin_simpl ;
 try assumption ; apply continuity_reciprocal_strictly_decreasing_open_interval ;
 assumption.
Qed.

Lemma Rplus_pos_lt : forall x h, 0 < h -> x < x + h.
Proof.
intros ; fourier.
Qed.

Lemma Rminus_pos_lt : forall x h, 0 < h -> x - h < x.
Proof.
intros ; fourier.
Qed.

Lemma Rplus_pos_neq : forall x h, 0 < h -> x <> x + h.
Proof.
intros ; apply Rlt_not_eq, Rplus_pos_lt ; assumption.
Qed.

Lemma R_dist_Rplus_compat: forall x h, R_dist (x + h) x = Rabs h.
Proof.
intros ; apply Rabs_eq_compat ; ring.
Qed.

Lemma R_dist_Rminus_compat: forall x h, R_dist (x - h) x = Rabs h.
Proof.
intros ; rewrite <- Rabs_Ropp ; apply Rabs_eq_compat ; ring.
Qed.

Lemma dense_interval: forall lb ub x, lb < ub ->
  interval lb ub x -> dense (interval lb ub) x.
Proof.
intros lb ub x Hlt [xlb xub] eps eps_pos ; destruct xlb as [xlb | xeq].
 destruct xub as [xub | xeq].
  pose (h := Rmin (eps / 2) (interval_dist lb ub x)) ;
  assert (h_pos : 0 < h).
   apply Rmin_pos_lt, open_interval_dist_pos ;
   [fourier | split ; assumption].
  exists (x + h) ; split.
   split.
    apply interval_dist_bound ; [split ; left ; assumption |].
    rewrite Rabs_right ; [apply Rmin_r | left ; assumption].
    apply Rplus_pos_neq ; assumption.
   rewrite R_dist_Rplus_compat, Rabs_right ; [| left ; assumption].
    apply Rle_lt_trans with (eps / 2) ; [apply Rmin_l | fourier].
  pose (h := Rmin (eps / 2) (ub - lb)) ;
  assert (h_pos : 0 < h) by (apply Rmin_pos_lt ; fourier).
   exists (x - h) ; split. split. split.
    transitivity (x - (ub - lb)).
     right ; subst ; ring.
     apply Rplus_le_compat_l, Ropp_le_contravar, Rmin_r.
     left ; subst ; apply Rminus_pos_lt ; assumption.
     subst ; apply Rgt_not_eq, Rminus_pos_lt ; assumption.
     rewrite R_dist_Rminus_compat, Rabs_right ; [| left ; assumption].
     apply Rle_lt_trans with (eps / 2) ; [apply Rmin_l | fourier].
  pose (h := Rmin (eps / 2) (ub - lb)) ;
  assert (h_pos : 0 < h) by (apply Rmin_pos_lt ; fourier).
   exists (x + h) ; split. split. split.
    left ; rewrite xeq ; apply Rplus_pos_lt ; assumption.
    transitivity (x + (ub - lb)) ; [| right ; rewrite xeq ; ring].
     apply Rplus_le_compat_l, Rmin_r.
     apply Rlt_not_eq, Rplus_pos_lt ; assumption.
     rewrite R_dist_Rplus_compat, Rabs_right ; [| left ; assumption].
     apply Rle_lt_trans with (eps / 2) ; [apply Rmin_l | fourier].
Qed.  

Lemma derivable_pt_lim_interval_uniqueness:
  forall (f : R -> R) (lb ub x l l' : R),
  lb < ub -> interval lb ub x ->
  derivable_pt_lim_in f (interval lb ub) x l ->
  derivable_pt_lim_in f (interval lb ub) x l' -> l = l'.
Proof.
intros ; eapply derivable_pt_lim_in_uniqueness ; try eassumption.
 apply dense_interval ; assumption.
Qed.

Lemma derivable_pt_lim_derive_pt_interval: forall f lb ub x l
  (pr : derivable_pt_in f (interval lb ub) x),
  lb < ub -> interval lb ub x ->
  derivable_pt_lim_in f (interval lb ub) x l ->
  derive_pt_in f (interval lb ub) x pr = l.
Proof.
intros f lb ub x l [l' Hl'] x_in Hl ;
 eapply derivable_pt_lim_interval_uniqueness ;
 eassumption.
Qed.

Lemma derivable_pt_lim_derive_pt_open_interval: forall f lb ub x l
  (pr : derivable_pt_in f (open_interval lb ub) x),
  open_interval lb ub x ->
  derivable_pt_lim_in f (open_interval lb ub) x l ->
  derive_pt_in f (open_interval lb ub) x pr = l.
Proof.
intros f lb ub x l [l' Hl'] x_in Hl ;
 eapply derivable_pt_lim_open_interval_uniqueness ;
 eassumption.
Qed.

Lemma derive_pt_derivable_pt_lim_interval: forall f lb ub x l
  (pr : derivable_pt_in f (interval lb ub) x),
  lb < ub -> interval lb ub x ->
  derive_pt_in f (interval lb ub) x pr = l ->
  derivable_pt_lim_in f (interval lb ub) x l.
Proof.
intros f lb ub x l [l' Hl'] Hlt x_in Hl ; subst ; assumption.
Qed.

(** * Derivability of the reciprocal function *)

Lemma derivable_pt_lim_in_reciprocal_open_interval : forall f g lb ub,
  reciprocal_interval f g lb ub -> forall x Df_g,
  open_interval (g lb) (g ub) (g x) ->
  continue_pt_in g (open_interval lb ub) x -> open_interval lb ub x ->
  derive_open_interval f (g lb) (g ub) Df_g (g x) <> 0 ->
  derivable_pt_lim_in g (open_interval lb ub) x
    (/ derive_open_interval f (g lb) (g ub) Df_g (g x)).
Proof.
intros f g lb ub Hfg x Df_g gx_in Hgx x_in df_neq ;
 assert (glbub := open_interval_inhabited _ _ _ gx_in).
 apply limit1_in_ext with (fun y => / ((f (g y) - f (g x)) / (g y - g x))).
  unfold reciprocal_interval, comp in Hfg ; intros y [y_in y_neq] ;
  unfold growth_rate ; rewrite Rinv_Rdiv.
  do 2 (rewrite Hfg ; [| apply open_interval_interval ; assumption]) ;
   reflexivity.
  do 2 (rewrite Hfg ; [| apply open_interval_interval ; assumption]).   
  apply Rminus_eq_contra ; symmetry ; assumption.
  apply Rminus_eq_contra ; intro Hf ; apply y_neq ; fold (id y) (id x) ;
  do 2 (rewrite <- Hfg ;  [| apply open_interval_interval ; assumption]) ;
  rewrite Hf ; reflexivity.
 apply limit_inv ; [| assumption].
 unfold derive_open_interval ; destruct (in_open_interval_dec (g lb) (g ub) (g x))
  as [x_in' |] ; [| contradiction] ; destruct (Df_g _ x_in') as [l Hl] ;
  intros eps eps_pos ; destruct (Hl _ eps_pos) as [alpha [alpha_pos Halpha]].
 pose (beta := Rmin (interval_dist (g lb) (g ub) (g x)) alpha) ;
 assert (beta_pos : 0 < beta) by (apply Rmin_pos_lt ;
 [apply open_interval_dist_pos |] ; assumption) ;
 destruct (Hgx x_in _ beta_pos) as [delta [delta_pos Hdelta]] ;
 exists delta ; split ; [assumption |].
 intros y [[y_in y_neq] y_bd] ;
 rewrite (derivable_pt_lim_derive_pt_open_interval _ _ _ _ _ _ gx_in Hl) ;
  apply Halpha ; split. split.
   replace (g y) with (g x + (g y - g x)) by ring ; apply open_interval_dist_bound.
   apply open_interval_interval ; assumption.
   apply Rlt_le_trans with beta ; [simpl in Hdelta ; apply Hdelta |
   apply Rmin_l] ; split ; assumption.
   intro Hf ; apply y_neq ; replace x with (id x) by reflexivity ;
    replace y with (id y) by reflexivity ; rewrite <- Hfg, <- Hfg.
     unfold comp ; rewrite Hf ; reflexivity.
     apply open_interval_interval ; assumption.
     apply open_interval_interval ; assumption.
     apply Rlt_le_trans with beta ; [apply Hdelta | apply Rmin_r] ;
      split ; assumption.
Qed.


Lemma derivable_pt_lim_in_reciprocal_interval : forall f g lb ub,
  reciprocal_interval f g lb ub -> forall x Df_gx,
  open_interval (g lb) (g ub) (g x) ->
  continue_pt_in g (open_interval lb ub) x -> open_interval lb ub x ->
  derive_pt_in f (interval (g lb) (g ub)) (g x) Df_gx <> 0 ->
  derivable_pt_lim_in g (open_interval lb ub) x
    (/ derive_pt_in f _ (g x) Df_gx).
Proof.
intros f g lb ub Hfg x Df_gx gx_in Hgx x_in df_neq ;
 assert (gx_in' := open_interval_interval _ _ _ gx_in) ;
 assert (glbub := open_interval_inhabited _ _ _ gx_in).
 apply limit1_in_ext with (fun y => / ((f (g y) - f (g x)) / (g y - g x))).
  unfold reciprocal_interval, comp in Hfg ; intros y [y_in y_neq] ;
  unfold growth_rate ; rewrite Rinv_Rdiv.
  do 2 (rewrite Hfg ; [| apply open_interval_interval ; assumption]) ;
   reflexivity.
  do 2 (rewrite Hfg ; [| apply open_interval_interval ; assumption]).   
  apply Rminus_eq_contra ; symmetry ; assumption.
  apply Rminus_eq_contra ; intro Hf ; apply y_neq ; fold (id y) (id x) ;
  do 2 (rewrite <- Hfg ;  [| apply open_interval_interval ; assumption]) ;
  rewrite Hf ; reflexivity.
 apply limit_inv ; [| assumption].
 destruct Df_gx as [l Hl] ; intros eps eps_pos ;
 destruct (Hl _ eps_pos) as [alpha [alpha_pos Halpha]].
 pose (beta := Rmin (interval_dist (g lb) (g ub) (g x)) alpha) ;
 assert (beta_pos : 0 < beta) by (apply Rmin_pos_lt ;
 [apply open_interval_dist_pos |] ; assumption) ;
 destruct (Hgx x_in _ beta_pos) as [delta [delta_pos Hdelta]] ;
 exists delta ; split ; [assumption |].
 intros y [[y_in y_neq] y_bd] ;
 rewrite (derivable_pt_lim_derive_pt_interval _ _ _ _ _ _ glbub gx_in' Hl) ;
  apply Halpha ; split. split.
   replace (g y) with (g x + (g y - g x)) by ring ; apply interval_dist_bound.
   assumption. transitivity beta ; [left ; simpl in Hdelta ; apply Hdelta |
   apply Rmin_l] ; split ; assumption.
   intro Hf ; apply y_neq ; replace x with (id x) by reflexivity ;
    replace y with (id y) by reflexivity ; rewrite <- Hfg, <- Hfg.
     unfold comp ; rewrite Hf ; reflexivity.
     apply open_interval_interval ; assumption.
     apply open_interval_interval ; assumption.
     apply Rlt_le_trans with beta ; [apply Hdelta | apply Rmin_r] ;
      split ; assumption.
Qed.

Lemma derivable_pt_in_reciprocal_interval : forall f g lb ub,
  reciprocal_interval f g lb ub -> forall x Df_gx,
  open_interval (g lb) (g ub) (g x) ->
  continue_pt_in g (open_interval lb ub) x -> open_interval lb ub x ->
  derive_pt_in f (interval (g lb) (g ub)) (g x) Df_gx <> 0 ->
  derivable_pt_in g (open_interval lb ub) x.
Proof.
intros ; eexists ; eapply derivable_pt_lim_in_reciprocal_interval ;
 eassumption.
Qed.

Lemma derivable_pt_lim_in_imp_compat: forall f (D E : R -> Prop) x l,
  (forall y, E y -> D y) -> derivable_pt_lim_in f D x l->
  derivable_pt_lim_in f E x l.
Proof.
intros ; eapply limit1_imp ; [| eassumption].
 intros z [z_in z_neq] ; split ; [ass_apply |] ; assumption.
Qed.

Lemma derivable_pt_in_imp_compat: forall f (D E : R -> Prop) x,
  (forall y, E y -> D y) -> derivable_pt_in f D x ->
  derivable_pt_in f E x.
Proof.
intros f D E x EinD [l Hl] ; exists l ;
 eapply derivable_pt_lim_in_imp_compat ; eassumption.
Qed.

Lemma derivable_pt_in_reciprocal_interval_rev: forall f g lb ub,
  (forall x : R, interval (f lb) (f ub) x -> interval lb ub (g x)) ->
  forall x, interval (f lb) (f ub) x -> derivable_interval f lb ub ->
  derivable_pt_in f (interval lb ub) (g x).
Proof.
intros f g lb ub g_ok x x_in Df ; apply Df, g_ok ; assumption.
Qed.

Lemma derivable_pt_recip_interv : forall f g lb ub x, lb < ub ->
  open_interval (f lb) (f ub) x ->
  reciprocal_interval f g (f lb) (f ub) ->
  (forall x : R, interval (f lb) (f ub) x -> interval lb ub (g x)) ->
  strictly_increasing_interval f lb ub ->
  derivable_interval f lb ub ->
  forall (pr : derivable_pt_in f (interval lb ub) (g x)),
  derive_pt_in f _ (g x) pr <> 0 ->
  derivable_pt_in g (open_interval (f lb) (f ub)) x.
Proof.
intros f g lb ub x lbltub x_in Hfg g_ok Hf Df Dfgx Df_neq ;
 assert (gfub: g (f ub) = ub).
  fold (comp g f ub) ; erewrite strictly_increasing_reciprocal_interval_comm ;
  try eassumption ; [reflexivity | apply interval_r ; left ; assumption].
 assert (gflb: g (f lb) = lb).
  fold (comp g f lb) ; erewrite strictly_increasing_reciprocal_interval_comm ;
  try eassumption ; [reflexivity | apply interval_l ; left ; assumption].
 assert (Df_gx' : derivable_pt_in f (interval (g (f lb)) (g (f ub))) (g x))
  by (rewrite gflb, gfub ; assumption).
 apply derivable_pt_in_reciprocal_interval with f Df_gx' ; try eassumption.
 rewrite gflb, gfub ; apply interval_open_interval.
  apply g_ok, open_interval_interval, x_in.
  intro Hfalse ; destruct (Rlt_irrefl (f lb)).
   apply Rlt_le_trans with x ; [apply x_in | right].
   rewrite Hfalse ; fold ((comp f g) x) ; rewrite Hfg ; [reflexivity |].
   apply open_interval_interval, x_in.
  intro Hfalse ; destruct (Rlt_irrefl (f ub)).
   apply Rle_lt_trans with x ; [right | apply x_in].
   rewrite Hfalse ; fold ((comp f g) x) ; rewrite Hfg ; [reflexivity |].
   apply open_interval_interval, x_in.
 apply continuity_reciprocal_strictly_increasing_open_interval.
  left ; assumption.
  assumption.
 apply strictly_increasing_reciprocal_interval_comm ; try eassumption.
 apply derivable_continuous_interval ; assumption.
 intro Hfalse ; apply Df_neq.
  apply derivable_pt_lim_derive_pt_interval ;
   [| apply g_ok, open_interval_interval |] ; try assumption.
  apply derivable_pt_lim_in_imp_compat with (interval (g (f lb)) (g (f ub))).
  intros y y_in ; rewrite gflb, gfub ; assumption.
  eapply derive_pt_derivable_pt_lim_interval ; try eassumption ;
   rewrite gflb, gfub ; [| apply g_ok, open_interval_interval] ; assumption.
Qed.

(****************************************************)
(** *   Value of the derivative of the reciprocal function        *)
(****************************************************)

Lemma derive_pt_recip_interv_prelim0 : forall (f g:R->R) (lb ub x:R)
  (Prf:derivable_pt f (g x)) (Prg:derivable_pt g x),
  open_interval lb ub x -> reciprocal_open_interval f g lb ub ->
  derive_pt f (g x) Prf <> 0 ->
  derive_pt g x Prg = 1 / (derive_pt f (g x) Prf).
Proof.
intros f g lb ub x Df Dg x_in_I local_recip Df_neq.
 replace (derive_pt g x Dg) with
  ((derive_pt g x Dg) * (derive_pt f (g x) Df) * / (derive_pt f (g x) Df))
  by (field ; assumption).
 unfold Rdiv ; apply Rmult_eq_compat_r.
 rewrite Rmult_comm, <- derive_pt_comp.
 erewrite pr_nu_var2_interv ; [eapply derive_pt_id | |] ; eassumption.
Qed.

Lemma derive_pt_recip_interv_prelim1_0 : forall f g lb ub x, lb <= ub ->
  open_interval (f lb) (f ub) x -> strictly_increasing_interval f lb ub ->
  (forall x : R, interval (f lb) (f ub) x -> interval lb ub (g x)) ->
  reciprocal_interval f g (f lb) (f ub) -> open_interval lb ub (g x).
Proof.
intros f g lb ub x lb_lt_ub x_in_I f_incr g_ok f_recip_g ;
 assert (f lb <= f ub).
  eapply strictly_increasing_increasing_interval ;
  [| apply interval_l | apply interval_r |] ; assumption.
 assert (Hrew := strictly_increasing_reciprocal_interval_comm f g lb ub g_ok
        f_incr f_recip_g) ;
 assert (g_incr := strictly_increasing_reciprocal_interval_compat
            _ _ _ _ f_incr f_recip_g g_ok).
 split ; unfold reciprocal_interval, comp, id in Hrew ;
  [rewrite <- (Hrew lb) | rewrite <- Hrew].
 apply g_incr ; [apply interval_l | apply open_interval_interval |
 apply (proj1 x_in_I)] ; assumption.
 apply interval_l ; assumption.
 apply g_incr ; [apply open_interval_interval | apply interval_r |
 apply (proj2 x_in_I)] ; assumption.
 apply interval_r ; assumption.
Qed.

Lemma derive_pt_recip_interv_prelim1_1 : forall f g lb ub x, lb <= ub ->
  open_interval (f lb) (f ub) x -> strictly_increasing_interval f lb ub ->
  (forall x : R, interval (f lb) (f ub) x  -> interval lb ub (g x)) ->
  reciprocal_interval f g (f lb) (f ub) -> interval lb ub (g x).
Proof.
intros ; eapply open_interval_interval, derive_pt_recip_interv_prelim1_0 ;
 eassumption.
Qed.

Definition interval_size lb ub (pr : lb < ub) : posreal.
 apply mkposreal with ((ub - lb) / 2), Rlt_mult_inv_pos ; fourier.
Defined.

Lemma interval_size_Boule_middle : forall lb ub c (pr : lb < ub),
  open_interval lb ub c -> Boule (middle lb ub) (interval_size lb ub pr) c.
Proof.
intros ; unfold Boule, interval_size, middle ; simpl ; apply Rabs_def1.
 apply Rlt_minus_sort ; do 2 (field_simplify ; unfold Rdiv) ;
  rewrite Rinv_1 ; do 2 rewrite Rmult_1_r ; ass_apply.
 apply Rlt_minus_sort2 ; do 2 (field_simplify ; unfold Rdiv) ;
  rewrite Rinv_1 ; do 2 rewrite Rmult_1_r ; ass_apply.
Qed. 

Require Import Rsequence_def.

Lemma Rneq_lt_gt_dec : forall a b, a <> b -> { a < b } + { b < a }.
Proof.
intros a b ab_neq ; destruct (Rlt_le_dec a b).
 left ; assumption.
 right ; apply Rle_neq_lt ; [| symmetry] ; assumption.
Qed.

Lemma Dfn_CVU_implies_Df_exists :
  forall (fn fn' : nat -> R -> R) f g x lb ub (pr : lb < ub),
  open_interval lb ub x -> (forall n x, open_interval lb ub x ->
  derivable_pt_lim_in (fn n) (open_interval lb ub) x (fn' n x)) ->
  (forall x, open_interval lb ub x -> Rseq_cv (fun n => fn n x) (f x)) ->
  (CVU fn' g (middle lb ub) (interval_size lb ub pr)) ->
  (continue_in g (open_interval lb ub)) ->
  derivable_pt_lim f x (g x).
Proof.
intros fn fn' f g x lb ub pr x_in Dfn_eq_fn' fn_CV_f fn'_CVU_g g_cont eps eps_pos.
 assert (eps_6_pos : 0 < (eps / 3) / 2).
  apply  Rlt_mult_inv_pos ; [apply Rlt_mult_inv_pos |] ; fourier.
 destruct (g_cont _ x_in _ eps_6_pos) as [d1 [d1_pos Hd1]].
 pose (delta := Rmin (interval_dist lb ub x) d1) ; assert (delta_pos : 0 < delta).
  apply Rmin_pos_lt ; [apply open_interval_dist_pos |] ; assumption.
 exists (mkposreal _ delta_pos) ; intros h h_neq h_bd.
 pose (eps1 := Rabs h * eps / 3) ; assert (eps1_pos : 0 < eps1).
  unfold eps1 ; repeat apply Rmult_lt_0_compat ;
  [apply Rabs_pos_lt ; assumption | |] ; fourier.
 destruct (fn_CV_f x x_in _ eps1_pos) as [N1 HN1].
 assert (xh_in : open_interval lb ub (x + h)).
  apply open_interval_dist_bound.
   apply open_interval_interval ; assumption.
   eapply Rlt_le_trans ; [eassumption | apply Rmin_l].
 destruct (fn_CV_f (x + h) xh_in _ eps1_pos) as [N2 HN2].
 destruct (fn'_CVU_g _ eps_6_pos) as [N3 HN3].
 pose (N := max (max N1 N2) N3).
 apply Rle_lt_trans with (Rabs ((f (x + h) - f x) - h * g x) * Rabs (/ h)).
 right ; rewrite <- Rabs_mult ; apply Rabs_eq_compat ; field ; assumption.
 apply Rlt_le_trans with (Rabs h * eps * Rabs (/ h)).
 apply Rmult_lt_compat_r ; [apply Rabs_pos_lt, Rinv_neq_0_compat ; assumption |].
 apply Rle_lt_trans with (Rabs (f (x + h) - fn N (x + h) + - (f x - fn N x)
                          + ((fn N (x + h) - fn N x) - h * g x))).
 right ; apply Rabs_eq_compat ; ring.
 eapply Rle_lt_trans ; [eapply Rabs_triang |].
 eapply Rle_lt_trans ; [eapply Rplus_le_compat_r, Rabs_triang |].
 rewrite Rabs_Ropp.
 destruct (Rneq_lt_gt_dec _ _ h_neq) as [h_neg | h_pos].
 assert (c_deduc : forall c, interval (x + h) x c -> open_interval lb ub c).
  intros ; eapply interval_open_restriction_compat ; [| | eassumption].
   apply open_interval_dist_bound ; [apply open_interval_interval
   | eapply Rlt_le_trans, Rmin_l] ; eassumption.
   assumption.
 assert (pr1 : forall c : R, x + h < c < x -> derivable_pt (fn N) c).
  intros c c_encad ; exists (fn' N c) ;
   apply derivable_pt_lim_open_interval_derivable_pt_lim with lb ub, Dfn_eq_fn' ;
   apply c_deduc ; apply open_interval_interval ; assumption.
 assert (pr2 : forall c : R, x + h < c < x -> derivable_pt id c).
  intros ; apply derivable_pt_id.
 destruct (MVT (fn N) id (x + h) x pr1 pr2) as [c [c_in H]].
  fourier.
  intros c c_encad ; apply derivable_continuous_pt ; exists (fn' N c) ;
   apply derivable_pt_lim_open_interval_derivable_pt_lim with lb ub,
   Dfn_eq_fn' ; apply c_deduc ; assumption.
  intros ; apply derivable_continuous, derivable_id.
  unfold id in H ; rewrite (derive_pt_eq_0 _ _ _ _ (derivable_pt_lim_id c)), Rmult_1_r in H ;
  ring_simplify in H.
 assert (Hc : fn N (x + h) - fn N x = h * derive_pt (fn N) c (pr1 c c_in)).
  apply Rmult_eq_reg_l with (-1) ; [| apply Ropp_neq_0_compat, R1_neq_R0] ;
   unfold Rminus in H ; ring_simplify ; rewrite H ; apply Rplus_comm.
 rewrite Hc ; clear Hc H.
 replace (derive_pt (fn N) c (pr1 c c_in)) with (fn' N c).
 replace (h * fn' N c - h * g x) with (h * (fn' N c - g x)) by ring.
 rewrite Rabs_mult.
 transitivity (eps1 + Rabs (f x - fn N x) + Rabs h * Rabs (fn' N c - g x)).
 do 2 apply Rplus_lt_compat_r ; rewrite Rabs_minus_sym ; apply HN2.
 apply le_trans with (max N1 N2) ; [apply le_max_r | apply le_max_l].
 transitivity (eps1 + eps1 + Rabs h * Rabs (fn' N c - g x)).
 apply Rplus_lt_compat_r, Rplus_lt_compat_l ; unfold R_dist in HN1 ;
 rewrite Rabs_minus_sym ; apply HN1, le_trans with (max N1 N2) ; apply le_max_l.
 replace (fn' N c - g x)  with ((fn' N c - g c) +  (g c - g x)) by ring.
 apply Rle_lt_trans with (eps1 + eps1 + Rabs h * Rabs (fn' N c - g c) + Rabs h * Rabs (g c - g x)).
 do 3 rewrite Rplus_assoc ; do 2 apply Rplus_le_compat_l ; rewrite <- Rmult_plus_distr_l ;
 apply Rmult_le_compat_l ; [apply Rabs_pos | apply Rabs_triang].
 apply Rlt_trans with (eps1 + eps1 + Rabs h * ((eps / 3) / 2) +
          Rabs h * Rabs (g c - g x)).
 apply Rplus_lt_compat_r, Rplus_lt_compat_l, Rmult_lt_compat_l.
  apply Rabs_pos_lt ; assumption.
  rewrite Rabs_minus_sym ; apply HN3 ; [apply le_max_r |].
   apply interval_size_Boule_middle, c_deduc, open_interval_interval ; assumption.
 apply Rlt_le_trans with (eps1 + eps1 + Rabs h * (eps / 3 / 2) + Rabs h * (eps / 3 / 2)) ;
  [| right ; unfold eps1 ; field] ; repeat rewrite Rplus_assoc ;
  do 3 apply Rplus_lt_compat_l ; apply Rmult_lt_compat_l ; [apply Rabs_pos_lt ; assumption |].
 simpl in Hd1 ; apply Hd1 ; split.
  apply c_deduc, open_interval_interval ; assumption.
  transitivity (Rabs h) ; [| apply Rlt_le_trans with delta ; [apply h_bd | apply Rmin_r]].
  rewrite Rabs_left ; [| assumption] ; apply Rabs_def1 ; clear -c_in h_neg ;
   destruct c_in ; [transitivity 0 |] ; fourier.
 destruct (pr1 c c_in) as [l Hl] ; eapply uniqueness_limite ; eauto.
 eapply derivable_pt_lim_open_interval_derivable_pt_lim, Dfn_eq_fn' ;
  apply c_deduc, open_interval_interval ; assumption.

 assert (c_deduc : forall c, interval x (x + h) c -> open_interval lb ub c).
  intros ; eapply interval_open_restriction_compat ; [| | eassumption].
   assumption.
   apply open_interval_dist_bound ; [apply open_interval_interval
   | eapply Rlt_le_trans, Rmin_l] ; eassumption.
 assert (pr1 : forall c : R, x < c < x + h -> derivable_pt (fn N) c).
  intros c c_encad ; exists (fn' N c) ;
   apply derivable_pt_lim_open_interval_derivable_pt_lim with lb ub, Dfn_eq_fn' ;
   apply c_deduc ; apply open_interval_interval ; assumption.
 assert (pr2 : forall c : R, x < c < x + h -> derivable_pt id c).
  intros ; apply derivable_pt_id.
 destruct (MVT (fn N) id x (x + h) pr1 pr2) as [c [c_in Hc]].
  fourier.
  intros c c_encad ; apply derivable_continuous_pt ; exists (fn' N c) ;
   apply derivable_pt_lim_open_interval_derivable_pt_lim with lb ub,
   Dfn_eq_fn' ; apply c_deduc ; assumption.
  intros ; apply derivable_continuous, derivable_id.
  unfold id in Hc ; rewrite (derive_pt_eq_0 _ _ _ _ (derivable_pt_lim_id c)),
   Rmult_1_r in Hc ; ring_simplify in Hc.
 rewrite <- Hc ; clear Hc.
 replace (derive_pt (fn N) c (pr1 c c_in)) with (fn' N c).
 replace (h * fn' N c - h * g x) with (h * (fn' N c - g x)) by ring.
 rewrite Rabs_mult.
 transitivity (eps1 + Rabs (f x - fn N x) + Rabs h * Rabs (fn' N c - g x)).
 do 2 apply Rplus_lt_compat_r ; rewrite Rabs_minus_sym ; apply HN2.
 apply le_trans with (max N1 N2) ; [apply le_max_r | apply le_max_l].
 transitivity (eps1 + eps1 + Rabs h * Rabs (fn' N c - g x)).
 apply Rplus_lt_compat_r, Rplus_lt_compat_l ; unfold R_dist in HN1 ;
 rewrite Rabs_minus_sym ; apply HN1, le_trans with (max N1 N2) ; apply le_max_l.
 replace (fn' N c - g x)  with ((fn' N c - g c) +  (g c - g x)) by ring.
 apply Rle_lt_trans with (eps1 + eps1 + Rabs h * Rabs (fn' N c - g c) + Rabs h * Rabs (g c - g x)).
 do 3 rewrite Rplus_assoc ; do 2 apply Rplus_le_compat_l ; rewrite <- Rmult_plus_distr_l ;
 apply Rmult_le_compat_l ; [apply Rabs_pos | apply Rabs_triang].
 apply Rlt_trans with (eps1 + eps1 + Rabs h * ((eps / 3) / 2) +
          Rabs h * Rabs (g c - g x)).
 apply Rplus_lt_compat_r, Rplus_lt_compat_l, Rmult_lt_compat_l.
  apply Rabs_pos_lt ; assumption.
  rewrite Rabs_minus_sym ; apply HN3 ; [apply le_max_r |].
   apply interval_size_Boule_middle, c_deduc, open_interval_interval ; assumption.
 apply Rlt_le_trans with (eps1 + eps1 + Rabs h * (eps / 3 / 2) + Rabs h * (eps / 3 / 2)) ;
  [| right ; unfold eps1 ; field] ; repeat rewrite Rplus_assoc ;
  do 3 apply Rplus_lt_compat_l ; apply Rmult_lt_compat_l ; [apply Rabs_pos_lt ; assumption |].
 simpl in Hd1 ; apply Hd1 ; split.
  apply c_deduc, open_interval_interval ; assumption.
  transitivity (Rabs h) ; [| apply Rlt_le_trans with delta ; [apply h_bd | apply Rmin_r]].
  rewrite Rabs_right ; [| left ; assumption] ; apply Rabs_def1 ; clear -c_in h_pos ;
   destruct c_in ; [| transitivity 0] ; fourier.
 destruct (pr1 c c_in) as [l Hl] ; eapply uniqueness_limite ; eauto.
 eapply derivable_pt_lim_open_interval_derivable_pt_lim, Dfn_eq_fn' ;
  apply c_deduc, open_interval_interval ; assumption.

 right ; rewrite (Rabs_Rinv _ h_neq) ; field ; apply Rabs_no_R0 ; assumption.
Qed.


(* Hint Rewrite for derive_pt *)
(* TODO to place elsewhere *)
(* Warning ! This is also a matching over the proof inside derive_pt (weak)*)

Hint Rewrite derive_pt_plus : derive_hint.
Hint Rewrite derive_pt_opp : derive_hint.
Hint Rewrite derive_pt_minus : derive_hint.
Hint Rewrite derive_pt_mult : derive_hint.
Hint Rewrite derive_pt_const : derive_hint.
Hint Rewrite derive_pt_scal : derive_hint.
Hint Rewrite derive_pt_id : derive_hint.
Hint Rewrite derive_pt_Rsqr : derive_hint.
Hint Rewrite derive_pt_comp : derive_hint.
Hint Rewrite derive_pt_pow : derive_hint.
Hint Rewrite derive_pt_div : derive_hint.
Hint Rewrite derive_pt_inv : derive_hint.
(* std lib function *)
Hint Rewrite derive_pt_exp : derive_hint.
Hint Rewrite derive_pt_cosh : derive_hint.
Hint Rewrite derive_pt_sinh : derive_hint.