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
Require Import Rfunctions.
Require Import Rseries_def.
Require Import Fourier.
Require Import RiemannInt.
Require Import SeqProp.
Require Import Max.
Require Import RIneq MyRIneq.
Require Import Ranalysis_def Rinterval.
Require Import RIVT.

Local Open Scope R_scope.

(** The image of an interval by a continuous function is an interval *)

Lemma continuity_interval_image_interval : forall (f:R->R) (lb ub y:R),
 lb <= ub -> interval (f lb) (f ub) y ->
 continuity_interval f lb ub -> {x | interval lb ub x /\ f x = y}.
Proof.
intros f lb ub y lb_le_ub y_in Hf ;
 destruct (IVT_interval (f - (fun _ => y))%F lb ub) as [z [z_in Hz]].
  apply continuity_interval_minus_compat ;
  [assumption | apply continuity_interval_const].
  assumption.
  apply interval_minus_compat_0 ; assumption.
  exists z ; split ; [assumption |].
  apply Rminus_diag_uniq, Hz.
Qed.

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
 destruct (continuity_interval_image_interval f lb ub b) as [a [Ia Ha]] ;
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
    destruct (continuity_interval_image_interval f xlb xub x) as [a' [a'_in Ha']].
     left ; eapply open_interval_inhabited ; eassumption.
     replace x with (f a + (x - f a)) by ring ;
     apply open_interval_interval, interval_dist_bound.
     apply strictly_increasing_interval_image ;
     [eapply strictly_increasing_interval_restriction_compat |] ;
     eassumption.
     apply x_bd.
     eapply continuity_interval_restriction_compat ; eassumption.
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

Lemma continuity_reciprocal_strictly_decreasing_interval : forall (f g:R->R) (lb ub:R),
       lb <= ub ->
       strictly_decreasing_interval f lb ub -> 
       reciprocal_interval g f lb ub ->
       continuity_interval f lb ub ->
       continuity_open_interval g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)).
Proof.
intros f g lb ub lb_le_ub f_decr f_eq_g f_cont_interv.
 assert (f_incr := strictly_decreasing_strictly_increasing_interval2 _ _ _ f_decr).
 assert (ub_le_lb : - ub <= - lb) by fourier.
 assert ( T : reciprocal_interval (- g)%F (fun x : R => f (- x)) (- ub) (- lb)).
  intros x x_in_I ; unfold comp ; simpl.
  replace ((- g)%F (f (- x))) with (- (comp g f) (-x)).
  rewrite f_eq_g.
  unfold id ; simpl ; ring.
  unfold interval in * ; split ; destruct x_in_I ;
  fourier.
  reflexivity.

 assert (T2 : continuity_interval (fun x : R => f (- x)) (- ub) (- lb)).
  intros x x_in_I eps eps_pos.
  assert (x_interv : interval lb ub (-x)).
   unfold interval in * ; split ; intuition ; fourier.
  destruct (f_cont_interv (-x) x_interv eps eps_pos) as [alpha [alpha_pos Halpha]] ;
  exists alpha.
  split.
  assumption.
  intros a Ha.
  case (Req_dec x a) ; intro Hxa.
  subst ; simpl ; unfold R_dist ; unfold Rminus ; rewrite Rplus_opp_r, Rabs_R0 ;
  assumption.
  apply Halpha ; split.
  unfold D_x, no_cond ; split.
  intuition.
  intro Hf ; apply Hxa.
  replace x with (- -x) by (apply Ropp_involutive).
  replace a with (- - a) by (apply Ropp_involutive).
  apply Ropp_eq_compat ; assumption.
  simpl ; unfold R_dist, Rminus ; rewrite <- Ropp_plus_distr, Rabs_Ropp ;
  apply (proj2 Ha).


 assert (H := continuity_reciprocal_strictly_increasing_interval
  (fun x => f(-x)) (-g)%F (-ub) (-lb) ub_le_lb f_incr T T2).
 simpl in H ; repeat rewrite Ropp_involutive in H.
 
apply continuity_open_interval_opp_rev ; rewrite Rmin_comm, Rmax_comm ;
assumption.
Qed.

Lemma continuity_reciprocal_strictly_monotonous_interval : forall (f g:R->R) (lb ub:R),
       lb <= ub ->
       strictly_monotonous_interval f lb ub -> 
       reciprocal_interval g f lb ub ->
       continuity_interval f lb ub ->
       continuity_open_interval g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)).
Proof.
intros f g lb ub lb_le_ub f_mono f_eq_g f_cont_interv.
 destruct f_mono as [f_incr | f_decr] ;
 [apply continuity_reciprocal_strictly_increasing_interval |
 apply continuity_reciprocal_strictly_decreasing_interval] ; assumption.
Qed.

(** * Derivability of the reciprocal function *)

Lemma derivable_pt_lim_reciprocal_interval : forall (f g:R->R) (lb ub:R)
       (f_deriv : derivable_interval f (g lb) (g ub)),
       reciprocal_interval f g lb ub ->
       forall x (g_incr : interval (g lb) (g ub) (g x)),
       continuity_pt g x ->
       open_interval lb ub x ->
       derive_pt f (g x) (f_deriv (g x) g_incr) <> 0 ->
       derivable_pt_lim g x (1 / derive_pt f (g x) (f_deriv (g x) g_incr)).
Proof.
intros f g lb ub f_deriv f_recip_g x g_incr g_cont x_in_I df_neq ; pose (y := g x) ;
 assert (x_encad2 := open_interval_interval _ _ _ x_in_I) ;
 elim (f_deriv (g x)); simpl; intros l Hl ; assert (l_neq : l <> 0) by (intro l_null ;
 rewrite l_null in Hl ; apply df_neq ; rewrite derive_pt_eq ; assumption) ;
 intros eps eps_pos ; fold y.
 assert (Hlinv := limit_inv).
 destruct (Hl eps eps_pos) as [delta Hdelta] ; simpl in Hlinv ; unfold R_dist in Hlinv.
 assert (Hlinv' := Hlinv (fun h => (f (y+h) - f y)/h) (fun h => h <>0) l 0).
 unfold limit1_in, limit_in in Hlinv' ; simpl in Hlinv' ; unfold R_dist in Hlinv'.
 assert (Premisse : (forall eps:R, eps > 0 -> exists alp : R,
     alp > 0 /\ (forall x : R, (fun h => h <>0) x /\ Rabs (x - 0) < alp ->
     Rabs ((f (y + x) - f y) / x - l) < eps))).
  intros eps0 eps0_pos ; elim (Hl eps0 eps0_pos) ; intros delta2 Hdelta2 ;
  exists delta2 ; split ; [apply delta2.(cond_pos) |].
 intros h [h_neq h_bd] ; rewrite Rminus_0_r in h_bd ; apply Hdelta2 ; assumption.
  destruct (Hlinv' Premisse l_neq eps eps_pos) as [alpha [alpha_neq Halpha]] ;
  clear Premisse Hlinv Hlinv' Hl.
  pose (mydelta := Rmin delta alpha) ; assert (mydelta_pos : 0 < mydelta).
   unfold mydelta ; apply Rmin_pos_lt ; [apply delta.(cond_pos) | assumption].
   destruct (g_cont mydelta mydelta_pos) as [delta' [delta'_pos Hdelta']].
  pose (mydelta'' := Rmin delta' (Rmin (x - lb) (ub - x))) ; assert(mydelta''_pos : mydelta'' > 0).
   unfold mydelta'' ; repeat apply Rmin_pos_lt ; [assumption | |] ; unfold open_interval in * ;
   intuition ; fourier.
  pose (delta'' := mkposreal mydelta'' mydelta''_pos) ; exists delta'' ; intros h h_neq h_bd.
  assert (Sublemma2 : forall x y, Rabs x < Rabs y -> y > 0 -> x < y).
   intros m n Hyp_abs y_pos ; apply Rlt_le_trans with (r2:=Rabs n).
   apply Rle_lt_trans with (r2:=Rabs m) ; [ | assumption] ; apply RRle_abs.
   apply Req_le ; apply Rabs_right ; apply Rgt_ge ; assumption.
  assert (xh_encad : interval lb  ub (x +h)).
   split.
   assert (Sublemma : forall x y z, -z <= y - x -> x <= y + z) by (intros ; fourier) ;
   apply Sublemma ; apply Rlt_le ; apply Sublemma2.
   rewrite Rabs_Ropp.
   apply Rlt_le_trans with (r2:=x-lb) ; [| apply RRle_abs] ;
   apply Rlt_le_trans with (r2:=Rmin (x - lb) (ub - x)) ; [| apply Rmin_l] ;
   apply Rlt_le_trans with (r2:=Rmin delta' (Rmin (x - lb) (ub - x))).
   assumption.
   apply Rmin_r.
   unfold open_interval in * ; intuition ; fourier.
   assert (Sublemma : forall x y z, y <= z - x -> x + y <= z) by (intros ; fourier) ;
   apply Sublemma ; apply Rlt_le ; apply Sublemma2.
   apply Rlt_le_trans with (r2:=ub-x) ; [| apply RRle_abs] ;
   apply Rlt_le_trans with (r2:=Rmin (x - lb) (ub - x)) ; [| apply Rmin_r] ;
   apply Rlt_le_trans with (r2:=Rmin delta' (Rmin (x - lb) (ub - x))) ; [| apply Rmin_r] ; assumption.
   unfold open_interval in * ; intuition ; fourier.
  assert (g(x+h) - y <> 0).
   intro Hf ; apply Rminus_diag_uniq in Hf.
   assert (Hfalse : (comp f g) (x+h) = (comp f g) x).
    intros ; unfold comp ; rewrite Hf ; trivial.
   do 2 rewrite f_recip_g in Hfalse ; unfold id in Hfalse.
   apply Rplus_0_r_uniq in Hfalse ; apply h_neq ; assumption.
   assumption. assumption. assumption.
  replace ((g (x + h) - y) / h) with (1/ (h / (g (x + h) - y))).
  assert (Hrew : h = (comp f g ) (x+h) - (comp f g) x).
  repeat rewrite f_recip_g ; unfold id ; [ring | |] ; assumption.
  rewrite Hrew at 1 ; unfold comp ; replace (g(x+h)) with (y + (g (x+h) - y)) by ring ;
  pose (h':=g (x+h) - y) ; fold y h' ; replace (y + h' - y) with h' by ring.
  apply Rle_lt_trans with (Rabs (/ ((f (y + h') - f y) / h') - / l)) ;
  [right ; apply Rabs_eq_compat ; field |] ; repeat split.
  assumption. assumption.
  unfold h' ; intro Hf ; replace (y + (g (x+h) -y)) with (g (x+h)) in Hf.
  unfold reciprocal_interval, comp in f_recip_g ; unfold y in Hf ;
  do 2 rewrite f_recip_g in Hf ; unfold id in Hf.
  apply h_neq ; ring_simplify in Hf ; assumption.
  assumption. assumption. assumption.
  unfold y ; ring.
  apply Halpha ; split.
  assumption.
  apply Rlt_le_trans with mydelta ; [| apply Rmin_r].
  rewrite Rminus_0_r ; simpl in Hdelta' ; unfold R_dist, y in * ; apply Hdelta' ;
  split.
  unfold D_x, no_cond ; split ; [trivial |].
  intro Hf ; apply h_neq ; apply Rplus_eq_reg_l with x ; rewrite Rplus_0_r ;
  symmetry ; assumption.
  replace (x + h - x) with h by ring ; apply Rlt_le_trans with mydelta''.
  assumption.
  apply Rmin_l.
  field ; split ; assumption.
Qed.

Lemma derivable_pt_reciprocal_interval : forall (f g:R->R) (lb ub:R)
       (f_deriv : derivable_interval f (g lb) (g ub)),
       reciprocal_interval f g lb ub ->
       forall x (g_incr : interval (g lb) (g ub) (g x)),
       continuity_pt g x ->
       open_interval lb ub x ->
       derive_pt f (g x) (f_deriv (g x) g_incr) <> 0 ->
       derivable_pt g x.
Proof.
intros ; exists (1 / derive_pt f (g x) (f_deriv (g x) g_incr)) ;
 apply derivable_pt_lim_reciprocal_interval ;
 assumption.
Qed.

Lemma derivable_pt_reciprocal_interval_rev :forall (f g:R->R) (lb ub x : R),
         lb < ub ->
         open_interval (f lb) (f ub) x ->
         reciprocal_interval f g (f lb) (f ub) ->
         (forall x : R, interval (f lb) (f ub) x -> interval lb ub (g x)) ->
         strictly_increasing_interval f lb ub ->
         derivable_interval f lb ub ->
         derivable_pt f (g x).
Proof.
intros f g lb ub x lb_lt_ub x_encad f_eq_g g_ok f_incr f_derivable.
 apply f_derivable.
 assert (Left_inv :=  strictly_increasing_reciprocal_interval_comm f g lb ub f_incr) ;
 assert (f_incr' : f lb < f ub) by (apply Rlt_trans with x ; unfold open_interval in x_encad ;
 intuition).
 assert (Hrew_min : Rmin (f lb) (f ub) = f lb).
  unfold Rmin ; destruct (Rle_dec (f lb) (f ub)) ; [reflexivity | elim (n (Rlt_le _ _ f_incr'))].
 assert (Hrew_max : Rmax (f lb) (f ub) = f ub).
  unfold Rmax ; destruct (Rle_dec (f lb) (f ub)) ; [reflexivity | elim (n (Rlt_le _ _ f_incr'))].
 replace lb with ((comp g f) lb).
 replace ub with ((comp g f) ub).
 unfold comp.
 assert (Temp:= strictly_increasing_reciprocal_interval_compat  f g lb ub f_incr f_eq_g g_ok).
 split ; apply Rlt_le ; apply Temp ; unfold interval, open_interval in * ; intuition ;
 apply Rle_trans with x ; left ; assumption.
 apply Left_inv ; try rewrite Hrew_min, Hrew_max ; intuition ; apply interval_r ; intuition.
 apply Left_inv ; try rewrite Hrew_min, Hrew_max ; intuition ; apply interval_l ; intuition.
Qed.

Lemma derivable_pt_recip_interv : forall (f g:R->R) (lb ub x : R)
         (lb_lt_ub : lb < ub) (x_encad : open_interval (f lb) (f ub) x)
         (f_eq_g : reciprocal_interval f g (f lb) (f ub))
         (g_wf : forall x : R, interval (f lb) (f ub) x -> interval lb ub (g x))
        (f_incr : strictly_increasing_interval f lb ub)
         (f_derivable : derivable_interval f lb ub),
         derive_pt f (g x)
              (derivable_pt_reciprocal_interval_rev f g lb ub x lb_lt_ub x_encad
              f_eq_g g_wf f_incr f_derivable)  <> 0 ->
         derivable_pt g x.
Proof.
intros f g lb ub x lb_lt_ub x_encad f_eq_g g_wf f_incr f_derivable Df_neq.
 assert(g_incr : g (f lb) < g x < g (f ub)).
  assert (Temp:= strictly_increasing_reciprocal_interval_compat f g lb ub f_incr f_eq_g g_wf).
   assert (x_encad2 := x_encad) ; destruct x_encad2 ; split ; apply Temp ;
   try ((apply interval_l || apply interval_r) ; apply Rle_trans with x ; left ; assumption) ;
   try (apply open_interval_interval) ; try assumption.
 assert (g_eq_f := strictly_increasing_reciprocal_interval_comm2  f g lb ub
                  lb_lt_ub f_incr f_eq_g g_wf).
 assert (f_derivable2 : derivable_interval f (g (f lb)) (g (f ub))).
  intros a a_encad ; apply f_derivable.
  unfold reciprocal_interval, comp, id in g_eq_f ; rewrite g_eq_f in a_encad ;
  rewrite g_eq_f in a_encad ; try apply interval_l ; try apply interval_r ; intuition.
  assert (H := derivable_pt_reciprocal_interval f g (f lb) (f ub)).
  unfold reciprocal_interval, comp, id in g_eq_f.
  rewrite (g_eq_f lb), (g_eq_f ub) in H.
  assert (H' := H f_derivable f_eq_g x (g_wf _ (open_interval_interval _ _ _ x_encad))) ;
  apply H' ; clear H H'.
  assert (H := continuity_reciprocal_strictly_increasing_interval _ _ _ _ (Rlt_le _ _ lb_lt_ub)
                    f_incr g_eq_f (derivable_continuous_interval _ _ _ f_derivable)).
  rewrite strictly_increasing_Rmin_simpl, strictly_increasing_Rmax_simpl in H ;
  intuition.
  assumption.
  intro Hf ; apply Df_neq.
  rewrite <- Hf.
  apply pr_nu_var2_interv with lb ub.
  do 2 rewrite g_eq_f in g_incr ; try apply interval_l ; try apply interval_r ; try (left ; assumption).
  apply g_incr.
  trivial.
  apply interval_r ; left ; assumption.
  apply interval_l ; left ; assumption.
Qed.

Lemma derivable_pt_reciprocal_interval2 : forall (f g:R->R) (lb ub x : R)
         (x_in_I : open_interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) x)
         (f_recip_g : reciprocal_interval f g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)))
         (g_ok : forall x, interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) x -> interval lb ub (g x))
         (f_deriv : derivable_interval f lb ub), lb < ub ->
         strictly_monotonous_interval f lb ub ->
         derive_pt f (g x) (f_deriv (g x) (g_ok x (open_interval_interval _ _ _ x_in_I)))
         <> 0 ->
         derivable_pt g x.
Proof.
assert (Main : forall (f g:R->R) (lb ub x : R)
         (x_in_I : open_interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) x)
         (f_recip_g : reciprocal_interval f g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)))
         (g_ok : forall x, interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) x -> interval lb ub (g x))
         (f_deriv : derivable_interval f lb ub), lb < ub ->
         strictly_increasing_interval f lb ub ->
         derive_pt f (g x) (f_deriv (g x) (g_ok x (open_interval_interval _ _ _ x_in_I)))
         <> 0 ->
         derivable_pt g x).
intros f g lb ub x x_in_I f_recip_g g_ok f_deriv lb_lt_ub f_incr Df_neq.
 assert (f lb < f ub).
  apply f_incr ; [apply interval_l | apply interval_r |] ; intuition.
 assert (x_in_I' := x_in_I) ; rewrite Rmin_eq_l, Rmax_eq_r in x_in_I' ;
 assert (x_in_I'' := x_in_I') ; unfold open_interval in x_in_I' ; [| intuition | intuition].
 assert(g_incr : open_interval (g (f lb)) (g (f ub)) (g x)).
  assert (g_ok' := g_ok) ; rewrite Rmin_eq_l, Rmax_eq_r in f_recip_g, g_ok' ;
  try (left ; assumption).
  assert (Temp:= strictly_increasing_reciprocal_interval_compat
             f g lb ub f_incr f_recip_g g_ok').
  split ; apply Temp ; try apply interval_l ; try apply interval_r ; intuition ;
  apply open_interval_interval ; assumption.
  assert(g_incr2 : interval (g (f lb)) (g (f ub)) (g x)) by (apply open_interval_interval ;
  assumption).
 assert (g_eq_f := strictly_increasing_reciprocal_interval_comm f g lb ub f_incr f_recip_g g_ok).
 unfold reciprocal_interval, comp, id in g_eq_f.
 assert (f_derivable2 : forall a : R, interval (g (f lb)) (g (f ub)) a -> derivable_pt f a).
  intros a a_encad ; apply f_deriv.
  rewrite g_eq_f in a_encad ; rewrite g_eq_f in a_encad ; intuition ;
  try apply interval_l || apply interval_r ; intuition.
 apply derivable_pt_reciprocal_interval with (f:=f) (lb:=f lb) (ub:=f ub)
     (f_deriv:=f_derivable2) (g_incr:=g_incr2) ; try assumption.
rewrite Rmin_eq_l, Rmax_eq_r in f_recip_g ; intuition.
assert (T := continuity_reciprocal_strictly_increasing_interval f g lb ub
      (Rlt_le _ _ lb_lt_ub) f_incr g_eq_f (derivable_continuous_interval _ _ _ f_deriv)) ;
apply T ; assumption.
rewrite pr_nu_var2 with (g:=f) (pr2:=f_deriv (g x)
              (g_ok x (open_interval_interval (Rmin (f lb) (f ub))
              (Rmax (f lb) (f ub)) x x_in_I))) ; intuition.

intros f g lb ub x x_in_I f_recip_g g_ok f_deriv lb_lt_ub [f_incr | f_decr] Df_neq.
 eapply Main ; eassumption.
 assert (f ub < f lb).
  apply f_decr ; [apply interval_l | apply interval_r |] ; intuition.
 assert (x_in_I' := x_in_I) ; rewrite Rmin_eq_r, Rmax_eq_l in x_in_I' ; intuition.
 assert (x_in_I'' : open_interval (Rmin ((- f)%F lb) ((- f)%F ub))
                 (Rmax ((- f)%F lb) ((- f)%F ub)) (- x)).
  rewrite Rmin_eq_l, Rmax_eq_r ; intuition ; try (unfold opp_fct ; intuition).
  clear - x_in_I' ; unfold open_interval in * ; intuition ; fourier.
 assert (f_recip_g' : reciprocal_interval (- f)%F (fun x : R => g (- x))
      (Rmin ((- f)%F lb) ((- f)%F ub)) (Rmax ((- f)%F lb) ((- f)%F ub))).
  unfold opp_fct ; rewrite Rmin_opp_opp_Rmax, Rmax_opp_opp_Rmin ;
  apply reciprocal_opp_compat_interval2 ; assumption.
 assert (g_ok' : forall x : R,
              interval (Rmin ((- f)%F lb) ((- f)%F ub))
              (Rmax ((- f)%F lb) ((- f)%F ub)) x ->
              interval lb ub ((fun x0 : R => g (- x0)) x)).
  clear -g_ok ; intros x x_in_I ; apply g_ok.
  unfold opp_fct, interval in x_in_I ; rewrite Rmin_opp_opp_Rmax, Rmax_opp_opp_Rmin in x_in_I.
  split ; intuition ; fourier.
 assert (f_deriv' : derivable_interval (- f)%F lb ub).
  intros a Ha ; reg ; apply f_deriv ; assumption.
 assert (f_incr : strictly_increasing_interval (- f)%F lb ub) by
  (apply strictly_decreasing_strictly_increasing_interval ; assumption).

assert (Df_neq' : derive_pt (- f) ((fun x : R => g (- x)) (- x))
       (f_deriv' ((fun x : R => g (- x)) (- x))
          (g_ok' (- x)
             (open_interval_interval (Rmin ((- f)%F lb) ((- f)%F ub))
                (Rmax ((- f)%F lb) ((- f)%F ub)) (- x) x_in_I''))) = 0 ->
     False).
intro Hf.
apply Df_neq.
destruct (f_deriv' (g (- - x))
          (g_ok' (- x)
          (open_interval_interval (Rmin ((- f)%F lb) ((- f)%F ub))
          (Rmax ((- f)%F lb) ((- f)%F ub)) (- x) x_in_I''))) as (l1, Hl1).
destruct (f_deriv (g x)
          (g_ok x
          (open_interval_interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) x
          x_in_I))) as (l2, Hl2).
assert (Hl1' := Hl1) ; rewrite Ropp_involutive in Hl1'.
assert (Hl1'' := derivable_pt_lim_opp _ _ _ Hl2).
assert (l1 = -l2) by (eapply uniqueness_limite ; eassumption).
assert (l1 = 0).
 rewrite derive_pt_eq in Hf.
 eapply uniqueness_limite ; [apply Hl1 | apply Hf].
rewrite H1 in H0.
assert (l2 = 0) by (clear -H0 ; symmetry ; rewrite <- Ropp_involutive, <- H0 ; intuition).
subst ; simpl ; reflexivity.

assert (L := Main (-f)%F (fun x => g(-x)) lb ub (-x) x_in_I''
           f_recip_g' g_ok' f_deriv' lb_lt_ub f_incr Df_neq').
clear - L ; destruct L as (l, Hl) ; exists (-l) ; intros eps eps_pos ;
 destruct (Hl eps eps_pos) as (delta, Hdelta) ; exists delta ;
 intros h h_neq h_bd.
 assert (R := Hdelta (-h)).
 rewrite Ropp_plus_distr, Ropp_involutive in R.
 apply Rle_lt_trans with (Rabs ((g (x + - - h) - g x) / - h - l)).
 right ; rewrite <- Rabs_Ropp ; apply Rabs_eq_compat.
 unfold Rminus, Rdiv ; rewrite Ropp_plus_distr ;
 repeat rewrite Ropp_involutive ; field ; assumption.
 apply R.
 intro Hf ; apply h_neq.
 symmetry ; rewrite <- Ropp_involutive ; intuition.
 rewrite Rabs_Ropp ; assumption.

Qed.

(****************************************************)
(** *   Value of the derivative of the reciprocal function        *)
(****************************************************)

Lemma derive_pt_recip_interv_prelim0 : forall (f g:R->R) (lb ub x:R)
       (Prf:derivable_pt f (g x)) (Prg:derivable_pt g x),
       lb < x < ub ->
       reciprocal_open_interval f g lb ub ->
       derive_pt f (g x) Prf <> 0 ->
       derive_pt g x Prg = 1 / (derive_pt f (g x) Prf).
Proof.
intros f g lb ub x Df Dg x_in_I local_recip Df_neq.
 replace (derive_pt g x Dg) with
  ((derive_pt g x Dg) * (derive_pt f (g x) Df) * / (derive_pt f (g x) Df))
  by (field ; assumption).
 unfold Rdiv ; apply Rmult_eq_compat_r.
 rewrite Rmult_comm, <- derive_pt_comp.
 assert (x_encad2 : lb <= x <= ub) by intuition.
 rewrite pr_nu_var2_interv with (g:=id)
  (pr2:= derivable_pt_id x) (lb:=lb) (ub:=ub).
  reg.
  assumption.
 assumption.
Qed.

Lemma derive_pt_recip_interv_prelim1_0 : forall (f g:R->R) (lb ub x:R), 
       lb <= ub -> open_interval (f lb) (f ub) x ->
       strictly_increasing_interval f lb ub ->
       (forall x : R, interval (f lb) (f ub) x -> interval lb ub (g x)) ->
       reciprocal_interval f g (f lb) (f ub) ->
       open_interval lb ub (g x).
Proof.
intros f g lb ub x lb_lt_ub x_in_I f_incr g_ok f_recip_g ;
 assert (f_incr2 := strictly_increasing_increasing_interval _ _ _ f_incr) ;
 assert (H : f lb <= f ub).
  apply f_incr2 ; [apply interval_l | apply interval_r |] ; assumption.
 assert (f_recip_g2 : reciprocal_interval f g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub))).
  rewrite Rmin_eq_l, Rmax_eq_r ; assumption.
 assert (g_ok2 : forall x : R,
        interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) x ->
        interval lb ub (g x)).
  rewrite Rmin_eq_l, Rmax_eq_r ; assumption.
 assert (Hrew := strictly_increasing_reciprocal_interval_comm
            f g lb ub f_incr f_recip_g2 g_ok2).
 assert (g_incr := strictly_increasing_reciprocal_interval_compat
            _ _ _ _ f_incr f_recip_g g_ok).
 split ; unfold reciprocal_interval, comp, id in Hrew ;
  [rewrite <- Hrew with (x := lb) | rewrite <- Hrew].
 apply g_incr ; [apply interval_l | apply open_interval_interval |
 apply (proj1 x_in_I)] ; assumption.
 apply interval_l ; assumption.
 apply g_incr ; [apply open_interval_interval | apply interval_r |
 apply (proj2 x_in_I)] ; assumption.
 apply interval_r ; assumption.
Qed.


Lemma derive_pt_recip_interv_prelim1_1 : forall (f g:R->R) (lb ub x:R), 
       lb <= ub ->
       open_interval (f lb) (f ub) x ->
       strictly_increasing_interval f lb ub ->
       (forall x : R, interval (f lb) (f ub) x  -> interval lb ub (g x)) ->
       reciprocal_interval f g (f lb) (f ub) ->
       interval lb ub (g x).
Proof.
intros f g lb ub x lb_le_ub x_encad f_incr g_wf f_eq_g.
 assert (Temp := derive_pt_recip_interv_prelim1_0 f g lb ub x lb_le_ub x_encad
 f_incr g_wf f_eq_g).
 split ; apply Rlt_le ; unfold interval, open_interval in * ; intuition.
Qed.

Lemma ub_lt_2_pos : forall x ub lb, lb < x -> x < ub -> 0 < (ub-lb)/2.
Proof.
intros x ub lb lb_lt_x x_lt_ub.
 assert (T : 0 < ub - lb).
  fourier.
 unfold Rdiv ; apply Rlt_mult_inv_pos ; intuition.
Qed.

Definition mkposreal_lb_ub : forall (x lb ub:R) (x_in_I : open_interval lb ub x), posreal.
intros x lb ub x_in_I.
 apply (mkposreal ((ub-lb)/2) (ub_lt_2_pos x ub lb (proj1 x_in_I) (proj2 x_in_I))).
Defined.

Require Import Rsequence_def.

Lemma Dfn_CVU_implies_Df_exists : forall (fn fn':nat -> R -> R) (f g:R->R)
      (x lb ub:R) (x_in_I : open_interval lb ub x),
      (forall (x:R) (n:nat), open_interval lb ub x -> derivable_pt_lim (fn n) x (fn' n x)) ->
      (forall (x:R), open_interval lb ub x -> Rseq_cv (fun n => fn n x) (f x)) ->
      (CVU fn' g ((lb + ub)/2) (mkposreal_lb_ub x lb ub x_in_I)) ->
      (forall (x:R), open_interval lb ub x -> continuity_pt g x) ->
      derivable_pt_lim f x (g x).
Proof.
intros fn fn' f g x lb ub x_in_I Dfn_eq_fn' fn_CV_f fn'_CVU_g g_cont eps eps_pos.
 assert (eps_8_pos : 0 < eps / 8) by fourier.
 elim (g_cont x x_in_I (eps/8) eps_8_pos) ; clear g_cont ; intros delta1 Hdelta1 ;
 destruct Hdelta1 as (delta1_pos, g_cont).
 assert (delta_pos : 0 < Rmin (Rmin ((x-lb)/2) ((ub-x)/2)) delta1).
  apply Rmin_pos_lt ; [apply Rmin_pos_lt | intuition] ; unfold Rdiv ;
  apply Rlt_mult_inv_pos ; intuition ; apply Rlt_Rminus ;
  [apply (proj1 x_in_I) | apply (proj2 x_in_I)].
 pose (delta := mkposreal (Rmin (Rmin ((x-lb)/2) ((ub-x)/2)) delta1) (delta_pos)).
 exists delta ; intros h h_neq h_ub.
 assert (eps'_pos : 0 < (Rabs h) * eps / 4).
  unfold Rdiv ; rewrite Rmult_assoc ; apply Rmult_lt_0_compat.
  apply Rabs_pos_lt ; assumption.
  fourier.
 elim (fn_CV_f x x_in_I ((Rabs h) * eps / 4) eps'_pos) ; intros N2 fnx_CV_fx.
 assert(lb_lt_xh : lb < x + h).
  apply Rlt_trans with (x - delta).
  unfold delta.
  assert (Temp : forall a b c, a + c < b -> a < b - c).
   intros ; fourier.
  apply Temp ; clear Temp ; apply Rle_lt_trans with (lb + Rmin ((x - lb) / 2) ((ub - x) / 2)).
  apply Rplus_le_compat_l ; apply Rmin_l.
  apply Rle_lt_trans with (lb + (x - lb) / 2).
  apply Rplus_le_compat_l ; apply Rmin_l.
  replace (lb + (x - lb) / 2) with ((lb + x)/2) by field.
  assert (Temp : forall a b, a < b -> (a+b)/2 < b).
   clear ; intros a b a_lt_b.
   unfold Rdiv ; rewrite Rmult_plus_distr_r.
   fourier.
  apply Temp ; apply (proj1 x_in_I).
  apply Rplus_lt_compat_l. 
  exact (proj2 (Rabs_def2 h delta h_ub)).
 assert(xh_lt_ub : x + h < ub).
  apply Rlt_trans with (x + delta).
  apply Rplus_lt_compat_l. 
  exact (proj1 (Rabs_def2 h delta h_ub)).
  unfold delta.
  apply Rle_lt_trans with (x + Rmin ((x - lb) / 2) ((ub - x) / 2)).
  apply Rplus_le_compat_l ; apply Rmin_l.
  apply Rle_lt_trans with (x + (ub - x) / 2).
  apply Rplus_le_compat_l ; apply Rmin_r.
  replace (x + (ub - x) / 2) with ((ub + x)/2) by field.
  assert (Temp : forall a b, a < b -> (b+a)/2 < b).
   clear ; intros a b a_lt_b.
   unfold Rdiv ; rewrite Rmult_plus_distr_r.
   fourier.
  apply Temp ; apply (proj2 x_in_I).
  assert (xh_in_I : open_interval lb ub (x+h)) by (split ; assumption).
 elim (fn_CV_f (x+h) xh_in_I ((Rabs h) * eps / 4) eps'_pos) ;
 clear fn_CV_f ; intros N1 fnxh_CV_fxh.
 elim (fn'_CVU_g (eps/8) eps_8_pos) ; intros N3 fn'c_CVU_gc.
 pose (N := max (max N1 N2) N3).
 assert (Main : Rabs ((f (x+h) - fn N (x+h)) - (f x - fn N x) + (fn N (x+h) - fn N x - h * (g x))) < (Rabs h)*eps).
 apply Rle_lt_trans with (Rabs (f (x + h) - fn N (x + h) - (f x - fn N x)) +  Rabs ((fn N (x + h) - fn N x - h * g x))).
 apply Rabs_triang.
 apply Rle_lt_trans with (Rabs (f (x + h) - fn N (x + h)) + Rabs (- (f x - fn N x)) + Rabs (fn N (x + h) - fn N x - h * g x)).
 apply Rplus_le_compat_r ; apply Rabs_triang.
 rewrite Rabs_Ropp.
 case (Rlt_le_dec h 0) ; intro sgn_h.
 assert (pr1 : forall c : R, x + h < c < x -> derivable_pt (fn N) c).
  intros c c_encad ; unfold derivable_pt.
  assert (lb_lt_c : lb < c).
   apply Rlt_trans with (x+h) ; intuition.
  assert (c_lt_ub : c < ub).
   apply Rlt_trans with x ; intuition ; apply (proj2 x_in_I).
 exists (fn' N c) ; apply Dfn_eq_fn' ; split ; assumption.
 assert (pr2 : forall c : R, x + h < c < x -> derivable_pt id c).
  intros c c_encad ; apply derivable_id.
 assert (xh_x : x+h < x).
  fourier.
 assert (pr3 : forall c : R, x + h <= c <= x -> continuity_pt (fn N) c).
  intros c c_encad ; apply derivable_continuous_pt.
  exists (fn' N c) ; apply Dfn_eq_fn' ; split.
  apply Rlt_le_trans with (x+h) ; intuition.
  apply Rle_lt_trans with x ; intuition ; apply (proj2 x_in_I).
 assert (pr4 : forall c : R, x + h <= c <= x -> continuity_pt id c).
  intros c c_encad ; apply derivable_continuous ; apply derivable_id.
 elim (MVT (fn N) id (x+h) x pr1 pr2 xh_x pr3 pr4) ; intros c Hc ; elim Hc ; clear Hc ; intros P Hc.
 assert (Hc' : h * derive_pt (fn N) c (pr1 c P) = (fn N (x+h) - fn N x)).
  apply Rmult_eq_reg_l with (-1).
  replace (-1 * (h * derive_pt (fn N) c (pr1 c P))) with (-h * derive_pt (fn N) c (pr1 c P)) by field.
  replace (-1 * (fn N (x + h) - fn N x)) with (- (fn N (x + h) - fn N x)) by field.
  replace (-h) with (id x - id (x + h)).
  rewrite <- Rmult_1_r ; replace 1 with (derive_pt id c (pr2 c P)) by reg.
  replace (- (fn N (x + h) - fn N x)) with (fn N x - fn N (x + h)) by field.
  assumption.
  unfold id ; field.
  apply Rlt_not_eq ; intuition.
 clear Hc.
 rewrite <- Hc'.
 replace (derive_pt (fn N) c (pr1 c P)) with (fn' N c).
 replace (h * fn' N c - h * g x) with (h * (fn' N c - g x)) by field.
 rewrite Rabs_mult.
 apply Rlt_trans with (Rabs h * eps / 4 + Rabs (f x - fn N x) + Rabs h * Rabs (fn' N c - g x)).
 apply Rplus_lt_compat_r ; apply Rplus_lt_compat_r ; unfold R_dist in fnxh_CV_fxh ;
 rewrite Rabs_minus_sym ; apply fnxh_CV_fxh.
 unfold N ; apply le_trans with (max N1 N2) ; apply le_max_l.
 apply Rlt_trans with (Rabs h * eps / 4 + Rabs h * eps / 4 + Rabs h * Rabs (fn' N c - g x)).
 apply Rplus_lt_compat_r ; apply Rplus_lt_compat_l.
 unfold R_dist in fnx_CV_fx ; rewrite Rabs_minus_sym ; apply fnx_CV_fx.
 unfold N ; apply le_trans with (max N1 N2) ; [apply le_max_r | apply le_max_l].
 replace (fn' N c - g x)  with ((fn' N c - g c) +  (g c - g x)) by field.
 apply Rle_lt_trans with (Rabs h * eps / 4 + Rabs h * eps / 4 +
          Rabs h * Rabs (fn' N c - g c) + Rabs h * Rabs (g c - g x)).
 rewrite Rplus_assoc ; rewrite Rplus_assoc ; rewrite Rplus_assoc ;
 apply Rplus_le_compat_l ; apply Rplus_le_compat_l ; rewrite <- Rmult_plus_distr_l ;
 apply Rmult_le_compat_l. apply Rabs_pos.
 apply Rabs_triang.
 apply Rlt_trans with (Rabs h * eps / 4 + Rabs h * eps / 4 + Rabs h * (eps / 8) +
          Rabs h * Rabs (g c - g x)).
 apply Rplus_lt_compat_r ; apply Rplus_lt_compat_l ; apply Rmult_lt_compat_l.
 apply Rabs_pos_lt ; assumption.
 rewrite Rabs_minus_sym ; apply fn'c_CVU_gc.
 unfold N ; apply le_max_r.
 unfold Boule.
 assert (Rabs (c - (lb + ub) / 2) < (ub - lb) / 2).
  apply Rabs_def1.
  assert (Temp : forall a b c, a < b + c -> a - b < c). intros ; fourier.
  apply Temp ; clear Temp ; replace ((lb + ub) / 2 + (ub - lb) / 2) with ub by field.
  apply Rlt_trans with x ; [exact (proj2 P) | intuition ; apply (proj2 x_in_I)].
  assert (Temp : forall a b c, a - b < c -> - b < c - a) by (intros ; fourier).
  apply Temp ; clear Temp ; replace ((lb + ub) / 2 - ((ub - lb) / 2)) with lb by field.
  apply Rlt_trans with (x+h) ; [intuition | exact (proj1 P)].
  assumption.
 apply Rlt_trans with (Rabs h * eps / 4 + Rabs h * eps / 4 + Rabs h * (eps / 8) +
         Rabs h * (eps / 8)).
 rewrite Rplus_assoc ; rewrite Rplus_assoc ; rewrite Rplus_assoc ; rewrite Rplus_assoc ;
 apply Rplus_lt_compat_l ; apply Rplus_lt_compat_l ; rewrite <- Rmult_plus_distr_l ;
 rewrite <- Rmult_plus_distr_l ; apply Rmult_lt_compat_l.
 apply Rabs_pos_lt ; assumption.
 apply Rplus_lt_compat_l ; simpl in g_cont ; apply g_cont ; split ; [unfold D_x ; split |].
 unfold no_cond ; intuition. apply Rgt_not_eq ; exact (proj2 P).
 unfold R_dist. apply Rlt_trans with (Rabs h).
 apply Rabs_def1. apply Rlt_trans with 0.
 assert (Temp : forall a b, a < b -> a - b < 0).
  intros ; fourier.
 apply Temp ; exact (proj2 P).
 apply Rabs_pos_lt ; assumption.
 apply Rle_lt_trans with h.
 rewrite Rabs_left1.
 apply Req_le ; field.
 apply Rlt_le ; assumption.
 assert (Temp : forall a b c, a + b < c -> b < c - a). intros ; fourier.
 apply Temp ; clear Temp ; exact (proj1 P).
 apply Rlt_le_trans with delta ; [intuition | unfold delta ; apply Rmin_r].
 rewrite Rplus_assoc ; rewrite Rplus_assoc ; rewrite <- Rmult_plus_distr_l.
 replace (Rabs h * eps / 4 + (Rabs h * eps / 4 + Rabs h * (eps / 8 + eps / 8))) with
      (Rabs h * (eps / 4 + eps / 4 + eps / 8 + eps / 8)) by field.
 apply Rmult_lt_compat_l. 
 apply Rabs_pos_lt ; assumption.
 fourier.
 assert (lb_lt_c : lb < c).
   apply Rlt_trans with (x+h) ; intuition ; exact (proj1 P).
  assert (c_lt_ub : c < ub).
   apply Rlt_trans with x ; intuition ; [exact (proj2 P) | exact (proj2 x_in_I)].
 assert (H := pr1 c P) ; elim H ; clear H ; intros l Hl.
 assert (Temp : l = fn' N c).
  assert (c_in_I : open_interval lb ub c) by (split ; assumption).
  assert (Hl' := Dfn_eq_fn' c N c_in_I).
  unfold derivable_pt_abs in Hl.
  clear -Hl Hl'.
  apply uniqueness_limite with (f:= fn N) (x:=c) ; assumption.
  rewrite <- Temp.
  assert (Hl' : derivable_pt (fn N) c).
   exists l ; apply Hl.
  rewrite pr_nu_var with (g:= fn N) (pr2:=Hl').
  elim Hl' ; clear Hl' ; intros l' Hl'.
  assert (Main : l = l').
 apply uniqueness_limite with (f:= fn N) (x:=c) ; assumption.
 rewrite Main ; reflexivity.
 reflexivity.
 assert (h_pos : h > 0).
  case sgn_h ; intro Hyp.
  assumption.
  apply False_ind ; apply h_neq ; symmetry ; assumption.
 clear sgn_h.
 assert (pr1 : forall c : R, x < c < x + h -> derivable_pt (fn N) c).
  intros c c_encad ; unfold derivable_pt.
  assert (lb_lt_c : lb < c).
   apply Rlt_trans with x ; intuition ; apply (proj1 x_in_I).
  assert (c_lt_ub : c < ub).
   apply Rlt_trans with (x+h) ; intuition.
  exists (fn' N c) ; apply Dfn_eq_fn' ; split ; assumption.
 assert (pr2 : forall c : R, x < c < x + h -> derivable_pt id c).
  intros c c_encad ; apply derivable_id.
 assert (xh_x : x < x + h).
  fourier.
 assert (pr3 : forall c : R, x <= c <= x + h -> continuity_pt (fn N) c).
  intros c c_encad ; apply derivable_continuous_pt.
  exists (fn' N c) ; apply Dfn_eq_fn' ; intuition.
  split.
  apply Rlt_le_trans with x ; [exact (proj1 x_in_I) | assumption].
  apply Rle_lt_trans with (x+h) ; intuition.
 assert (pr4 : forall c : R, x <= c <= x + h -> continuity_pt id c).
  intros c c_encad ; apply derivable_continuous ; apply derivable_id.
 elim (MVT (fn N) id x (x+h) pr1 pr2 xh_x pr3 pr4) ; intros c Hc ; elim Hc ; clear Hc ; intros P Hc.
 assert (Hc' : h * derive_pt (fn N) c (pr1 c P) = (fn N (x+h) - fn N x)).
  replace (h * derive_pt (fn N) c (pr1 c P)) with ((id (x+h) - id x)* derive_pt (fn N) c (pr1 c P)).
  rewrite <- Rmult_1_r ; replace 1 with (derive_pt id c (pr2 c P)) by reg.
  assumption.
  unfold id ; field.
 clear Hc.
 rewrite <- Hc'.
 replace (derive_pt (fn N) c (pr1 c P)) with (fn' N c).
 replace (h * fn' N c - h * g x) with (h * (fn' N c - g x)) by field.
 rewrite Rabs_mult.
 apply Rlt_trans with (Rabs h * eps / 4 + Rabs (f x - fn N x) + Rabs h * Rabs (fn' N c - g x)).
 apply Rplus_lt_compat_r ; apply Rplus_lt_compat_r ; unfold R_dist in fnxh_CV_fxh ;
 rewrite Rabs_minus_sym ; apply fnxh_CV_fxh.
 unfold N ; apply le_trans with (max N1 N2) ; apply le_max_l.
 apply Rlt_trans with (Rabs h * eps / 4 + Rabs h * eps / 4 + Rabs h * Rabs (fn' N c - g x)).
 apply Rplus_lt_compat_r ; apply Rplus_lt_compat_l.
 unfold R_dist in fnx_CV_fx ; rewrite Rabs_minus_sym ; apply fnx_CV_fx.
 unfold N ; apply le_trans with (max N1 N2) ; [apply le_max_r | apply le_max_l].
 replace (fn' N c - g x)  with ((fn' N c - g c) +  (g c - g x)) by field.
 apply Rle_lt_trans with (Rabs h * eps / 4 + Rabs h * eps / 4 +
          Rabs h * Rabs (fn' N c - g c) + Rabs h * Rabs (g c - g x)).
 rewrite Rplus_assoc ; rewrite Rplus_assoc ; rewrite Rplus_assoc ;
 apply Rplus_le_compat_l ; apply Rplus_le_compat_l ; rewrite <- Rmult_plus_distr_l ;
 apply Rmult_le_compat_l. apply Rabs_pos.
 apply Rabs_triang.
 apply Rlt_trans with (Rabs h * eps / 4 + Rabs h * eps / 4 + Rabs h * (eps / 8) +
          Rabs h * Rabs (g c - g x)).
 apply Rplus_lt_compat_r ; apply Rplus_lt_compat_l ; apply Rmult_lt_compat_l.
 apply Rabs_pos_lt ; assumption.
 rewrite Rabs_minus_sym ; apply fn'c_CVU_gc.
 unfold N ; apply le_max_r.
 unfold Boule.
 assert (Rabs (c - (lb + ub) / 2) < (ub - lb) / 2).
  apply Rabs_def1.
  assert (Temp : forall a b c, a < b + c -> a - b < c). intros ; fourier.
  apply Temp ; clear Temp ; replace ((lb + ub) / 2 + (ub - lb) / 2) with ub by field.
  apply Rlt_trans with (x+h) ; [exact (proj2 P) | intuition].
  assert (Temp : forall a b c, a - b < c -> - b < c - a). intros ; fourier.
  apply Temp ; clear Temp ; replace ((lb + ub) / 2 - ((ub - lb) / 2)) with lb by field.
  apply Rlt_trans with x ; [intuition | exact (proj1 P)].
  exact (proj1 x_in_I).
  apply H.
 apply Rlt_trans with (Rabs h * eps / 4 + Rabs h * eps / 4 + Rabs h * (eps / 8) +
         Rabs h * (eps / 8)).
 repeat rewrite Rplus_assoc ; repeat apply Rplus_lt_compat_l ;
 repeat rewrite <- Rmult_plus_distr_l.
 apply Rmult_lt_compat_l.
 apply Rabs_pos_lt ; assumption.
 simpl in g_cont ; apply g_cont ; split ; [unfold D_x ; split |].
 unfold no_cond ; intuition. apply Rlt_not_eq ; exact (proj1 P).
 unfold R_dist. apply Rlt_trans with (Rabs h).
 apply Rabs_def1.
 assert (Temp : forall a b c, c < a + b -> c - a < b). intros ; fourier.
 apply Temp ; clear Temp ; rewrite Rabs_right. exact (proj2 P).
 apply Rgt_ge ; assumption.
 assert (Temp : forall a b, a - b < c -> - b < c - a). intros ; fourier.
 apply Temp ; apply Rlt_trans with x ; [| exact (proj1 P)].
 rewrite <- Rplus_0_r.
 apply Rplus_lt_compat_l.
 apply Ropp_lt_gt_0_contravar ; apply Rabs_pos_lt ; apply Rgt_not_eq ; assumption.
 apply Rle_lt_trans with h.
 rewrite Rabs_right. apply Req_le ; reflexivity.
 fourier.
 apply Rlt_le_trans with delta ; [intuition | unfold delta ; apply Rmin_r].
 rewrite Rabs_right in h_ub ; intuition.
 rewrite Rplus_assoc ; rewrite Rplus_assoc ; rewrite <- Rmult_plus_distr_l.
 replace (Rabs h * eps / 4 + (Rabs h * eps / 4 + Rabs h * (eps / 8 + eps / 8))) with
      (Rabs h * (eps / 4 + eps / 4 + eps / 8 + eps / 8)) by field.
 apply Rmult_lt_compat_l. 
 apply Rabs_pos_lt ; assumption.
 fourier.
 assert (lb_lt_c : lb < c).
   apply Rlt_trans with x ; intuition ; [exact (proj1 x_in_I) | exact (proj1 P)].
  assert (c_lt_ub : c < ub).
   apply Rlt_trans with (x+h) ; intuition ; exact (proj2 P).
 assert (H := pr1 c P) ; elim H ; clear H ; intros l Hl.
 assert (Temp : l = fn' N c).
  assert (c_in_I : open_interval lb ub c) by (split ; assumption) ;
   assert (Hl' := Dfn_eq_fn' c N c_in_I).
  unfold derivable_pt_abs in Hl.
  clear -Hl Hl'.
  apply uniqueness_limite with (f:= fn N) (x:=c) ; assumption.
  rewrite <- Temp.
  assert (Hl' : derivable_pt (fn N) c).
   exists l ; apply Hl.
  rewrite pr_nu_var with (g:= fn N) (pr2:=Hl').
  elim Hl' ; clear Hl' ; intros l' Hl'.
  assert (Main : l = l').
 apply uniqueness_limite with (f:= fn N) (x:=c) ; assumption.
 rewrite Main ; reflexivity.
 reflexivity.
 replace ((f (x + h) - f x) / h - g x) with ((/h) * ((f (x + h) - f x) - h * g x)). 
 rewrite Rabs_mult ; rewrite Rabs_Rinv.
 replace eps with (/ Rabs h * (Rabs h * eps)).
 apply Rmult_lt_compat_l.
 apply Rinv_0_lt_compat ; apply Rabs_pos_lt ; assumption.
 replace (f (x + h) - f x - h * g x) with (f (x + h) - fn N (x + h) - (f x - fn N x) +
          (fn N (x + h) - fn N x - h * g x)) by field.
 assumption.
 field ; apply Rgt_not_eq ; apply Rabs_pos_lt ; assumption.
 assumption.
 field. assumption.
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

(* TODO example of use *)
Goal forall x, derive_pt ((- exp) * cosh) x 
  (derivable_pt_mult _ _ _ (derivable_pt_opp  _ _ (derivable_pt_exp x)) (derivable_pt_cosh x)) 
  = derive_pt (comp sinh exp) x (derivable_pt_comp _ _ _ (derivable_pt_exp x) (derivable_pt_sinh (exp x))).
intros.
autorewrite with derive_hint.
Admitted.
