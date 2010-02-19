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
Require Import Rseries.
Require Import Fourier.
Require Import RiemannInt.
Require Import SeqProp.
Require Import Max.
Require Import MyRIneq.
Require Import Ranalysis_def.
Require Import RIVT.


Local Open Scope R_scope.



(* begin hide *)
Ltac case_le H :=
   let t := type of H in 
   let h' := fresh in 
      match t with ?x <= ?y => case (total_order_T x y);
         [intros h'; case h'; clear h' | 
          intros h'; clear -H h'; elimtype False; fourier ] end.
(* end hide *)

(** The image of an interval by a continuous function is an interval *)

Lemma continuity_interval_image_interval : forall (f:R->R) (lb ub y:R),
       lb <= ub ->
       interval (f lb) (f ub) y ->
       continuity_interval f lb ub ->
       {x | interval lb ub x /\ f x = y}.
Proof.
intros f lb ub y lb_le_ub y_encad f_cont_interv.
 case (Rle_lt_or_eq_dec _ _ lb_le_ub) ; clear lb_le_ub ; intro lb_lt_ub.
 case y_encad ; intro y_encad1.
   case_le y_encad1 ; intros y_encad2 y_encad3 ; case_le y_encad3.
    intro y_encad4.
     clear y_encad y_encad1 y_encad3.
     assert (Cont : forall a : R, lb <= a <= ub -> continuity_pt (fun x => f x - y) a).
      intros a a_encad. unfold continuity_pt, continue_in, limit1_in, limit_in ; simpl ; unfold R_dist.
      intros eps eps_pos. elim (f_cont_interv a a_encad eps eps_pos).
      intros alpha alpha_pos. destruct alpha_pos as (alpha_pos,Temp).
      exists alpha. split.
      assumption. intros x  x_cond.
      replace (f x - y - (f a - y)) with (f x - f a) by field.
      exact (Temp x x_cond).
     assert (H1 : interval (f lb - y) (f ub - y) 0).
      split ; left ; [apply Rlt_minus | apply Rgt_minus] ; assumption.
     destruct (IVT_interv (fun x => f x - y) lb ub Cont lb_lt_ub H1) as (x,Hx).
     exists x.
     destruct Hx as (Hyp,Result).
     split ; [assumption | intuition].
     intro H ; exists ub ; repeat split ; intuition.
     intro H ; exists lb ; repeat split ; intuition.
     intro H ; exists ub ; repeat split ; intuition.
     exists lb ; repeat split ; intuition.
     subst ; apply Rle_antisym ; unfold interval in * ; intuition.
Qed.

(** * Continuity of the reciprocal function *)

Lemma continuity_reciprocal_strictly_increasing_interval : forall (f g:R->R) (lb ub:R),
       lb <= ub ->
       strictly_increasing_interval f lb ub -> 
       reciprocal_interval g f lb ub ->
       continuity_interval f lb ub ->
       continuity_open_interval g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)).
Proof.
intros f g lb ub lb_le_ub f_incr f_eq_g f_cont_interv b b_encad.
 (*destruct f_mono as [f_incr | f_decr].*)
  assert (f_incr2 := strictly_increasing_increasing_interval _ _ _ f_incr).
  intros eps eps_pos ; simpl ; unfold R_dist.
   assert (b_encad2 : open_interval (f lb) (f ub) b).
    apply strictly_increasing_open_interval_image ; assumption.
   assert (b_encad3 := open_interval_interval _ _ _ b_encad2).
   elim (continuity_interval_image_interval f lb ub b lb_le_ub b_encad3 f_cont_interv) ;
   intros x [x_encad f_x_b].
   assert (x_encad2 : open_interval lb ub x).
    split.
    assert (Temp : x <> lb).
     intro Hfalse ; rewrite Hfalse in f_x_b.
     assert (Temp' : b <> f lb).
      apply Rgt_not_eq ; exact (proj1 b_encad2).
     apply Temp' ; symmetry ; assumption.
    apply Rle_neq_lt ; split ; unfold interval in * ; intuition.
    assert (Temp : x <> ub).
    intro Hfalse ; rewrite Hfalse in f_x_b.
    assert (Temp' : b <> f ub).
     apply Rlt_not_eq ; exact (proj2 b_encad2).
    apply Temp' ; symmetry ; assumption.
    apply Rle_neq_lt ; split ; unfold interval in * ; intuition.
   pose (x1 := Rmax (x - eps) lb).
   pose (x2 := Rmin (x + eps) ub).
   assert (x1_encad : interval lb ub x1).
    split. apply RmaxLess2.
    apply Rlt_le. unfold x1 ; rewrite Rmax_lt_lt_lt ;
    split ; apply Rlt_trans with (r2:=x).
    fourier.
    apply (proj2 x_encad2).
    apply (proj1 x_encad2).
    apply (proj2 x_encad2).
  assert (x2_encad : interval lb ub x2).
   split. apply Rlt_le ; unfold x2 ; apply Rgt_lt ; rewrite Rmin_gt_gt_gt ;
   split ; apply Rgt_trans with (r2:=x).
   fourier.
   apply (proj1 x_encad2).
   apply (proj2 x_encad2).
   apply (proj1 x_encad2).
   apply Rmin_r.
 assert (x_lt_x2 : x < x2).
  unfold x2 ; apply Rgt_lt ; rewrite Rmin_gt_gt_gt ;
  split ; unfold open_interval in * ; intuition ; fourier.
 assert (x1_lt_x : x1 < x).
  unfold x1 ; rewrite Rmax_lt_lt_lt ; split ; unfold open_interval in * ; intuition ; fourier.
 exists (Rmin (f x - f x1) (f x2 - f x)).
 split. apply Rmin_pos ; apply Rgt_minus. apply f_incr ; assumption.
 apply f_incr ; assumption.
 intros y [_ y_cond].
  rewrite <- f_x_b in y_cond.
  assert (Temp : forall x y d1 d2, d1 > 0 -> d2 > 0 -> Rabs (y - x) < Rmin d1 d2 -> x - d1 <= y <= x + d2).
   intros.
    split. assert (H10 : forall x y z, x - y <= z -> x - z <= y). intuition. fourier.
    apply H10. apply Rle_trans with (r2:=Rabs (y0 - x0)).
    replace (Rabs (y0 - x0)) with (Rabs (x0 - y0)). apply RRle_abs.
    rewrite <- Rabs_Ropp. unfold Rminus ; rewrite Ropp_plus_distr. rewrite Ropp_involutive.
    intuition.
    apply Rle_trans with (r2:= Rmin d1 d2). apply Rlt_le ; assumption.
    apply Rmin_l.
    assert (H10 : forall x y z, x - y <= z -> x <= y + z). intuition. fourier.
    apply H10. apply Rle_trans with (r2:=Rabs (y0 - x0)). apply RRle_abs.
    apply Rle_trans with (r2:= Rmin d1 d2). apply Rlt_le ; assumption.
    apply Rmin_r.
  assert (Temp' := Temp (f x) y (f x - f x1) (f x2 - f x)).
  replace (f x - (f x - f x1)) with (f x1) in Temp' by field.
  replace (f x + (f x2 - f x)) with (f x2) in Temp' by field.
  assert (T : f x - f x1 > 0).
   apply Rgt_minus. apply f_incr ; assumption.
  assert (T' : f x2 - f x > 0).
   apply Rgt_minus. apply f_incr ; assumption.
  assert (Main := Temp' T T' y_cond).
  clear Temp Temp' T T'.
  assert (x1_lt_x2 : x1 < x2).
   apply Rlt_trans with (r2:=x) ; assumption.
   assert (f_cont_myinterv : forall a : R, x1 <= a <= x2 -> continuity_pt f a).
    intros ; apply f_cont_interv ; split ; unfold interval in *.
    apply Rle_trans with (r2 := x1) ; intuition.
    apply Rle_trans with (r2 := x2) ; intuition.
    assert (x1_le_x2 : x1 <= x2) by intuition.
    assert (f_cont_interv2 : continuity_interval f x1 x2).
     intros a a_in_I ; apply f_cont_interv.
     split ; unfold interval in *.
     apply Rle_trans with (r2 := x1) ; intuition.
     apply Rle_trans with (r2 := x2) ; intuition.
   destruct (continuity_interval_image_interval f x1 x2 y x1_le_x2 Main f_cont_interv2) as
   [x' [x'_encad f_x'_y]].
   rewrite <- f_x_b ; rewrite <- f_x'_y.
   unfold reciprocal_interval, comp in f_eq_g.
   repeat rewrite f_eq_g.
   unfold id.
   assert (x'_encad2 : interval (x - eps) (x + eps) x').
    split ; unfold interval in *.
    apply Rle_trans with (r2:=x1) ; [ apply RmaxLess1|] ; intuition.
    apply Rle_trans with (r2:=x2) ; [ | apply Rmin_l] ; intuition.
   assert (x1_neq_x' : x1 <> x').
    intro Hfalse. rewrite Hfalse, f_x'_y in y_cond.
    assert (Hf : Rabs (y - f x) < f x - y).
     apply Rlt_le_trans with (r2:=Rmin (f x - y) (f x2 - f x)). fourier.
     apply Rmin_l.
     assert(Hfin : f x - y < f x - y).
      apply Rle_lt_trans with (r2:=Rabs (y - f x)).
      rewrite Rabs_minus_sym ; apply RRle_abs.
      assumption.
      elim (Rlt_irrefl _ Hfin).
           assert (x'_lb : x - eps < x').
    apply Rle_neq_lt.
      split ; unfold interval in *. intuition. apply Rlt_not_eq.
      apply Rle_lt_trans with (r2:=x1) ; [ apply RmaxLess1|].
      apply Rle_neq_lt ; split ; intuition.
      assert (x2_neq_x' : x2 <> x').
      intro Hfalse ; assert (Hf : Rabs (y - f x) < y - f x).
      rewrite Hfalse, f_x'_y in y_cond.
      apply Rlt_le_trans with (r2:=Rmin (f x - f x1) (y - f x)). fourier.
       apply Rmin_r.
      assert(Hfin : y - f x < y - f x).
       apply Rle_lt_trans with (r2:=Rabs (y - f x)). apply RRle_abs. fourier.
      elim (Rlt_irrefl _ Hfin).
     assert (x'_ub : x' < x + eps).
   apply Rle_neq_lt.
      split ; unfold interval in *. intuition. apply Rlt_not_eq.
      apply Rlt_le_trans with (r2:=x2).
      apply Rle_neq_lt ; split ; intuition.
      apply Rmin_l.
    apply Rabs_def1 ; fourier.
    assumption.
    split ; [apply Rle_trans with x1 | apply Rle_trans with x2] ; unfold interval in * ;
    intuition.
Qed.

Lemma continuity_reciprocal_strictly_monotonous_interval : forall (f g:R->R) (lb ub:R),
       lb <= ub ->
       strictly_monotonous_interval f lb ub -> 
       reciprocal_interval g f lb ub ->
       continuity_interval f lb ub ->
       continuity_open_interval g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)).
Proof.
intros f g lb ub lb_le_ub f_mono f_eq_g f_cont_interv.
 destruct f_mono as [f_incr | f_decr].
 apply continuity_reciprocal_strictly_increasing_interval ; assumption.
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

Lemma derivable_pt_lim_reciprocal_interv : forall (f g:R->R) (lb ub:R)
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
   unfold mydelta ; apply Rmin_pos ; [apply delta.(cond_pos) | assumption].
   destruct (g_cont mydelta mydelta_pos) as [delta' [delta'_pos Hdelta']].
  pose (mydelta'' := Rmin delta' (Rmin (x - lb) (ub - x))) ; assert(mydelta''_pos : mydelta'' > 0).
   unfold mydelta'' ; repeat apply Rmin_pos ; [assumption | |] ; unfold open_interval in * ;
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

Lemma derivable_pt_reciprocal_interv : forall (f g:R->R) (lb ub:R)
       (f_deriv : derivable_interval f (g lb) (g ub)),
       reciprocal_interval f g lb ub ->
       forall x (g_incr : interval (g lb) (g ub) (g x)),
       continuity_pt g x ->
       open_interval lb ub x ->
       derive_pt f (g x) (f_deriv (g x) g_incr) <> 0 ->
       derivable_pt g x.
Proof.
intros ; exists (1 / derive_pt f (g x) (f_deriv (g x) g_incr)) ;
 apply derivable_pt_lim_reciprocal_interv ;
 assumption.
Qed.

Lemma derivable_pt_reciprocal_interv2 : forall (f g:R->R) (lb ub x : R)
         (x_in_I : open_interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) x)
         (f_recip_g : reciprocal_interval f g (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)))
         (g_ok : forall x, interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) x -> interval lb ub (g x))
         (f_deriv : derivable_interval f lb ub), lb < ub ->
         strictly_monotonous_interval f lb ub ->
         derive_pt f (g x) (f_deriv (g x) (g_ok x (open_interval_interval _ _ _ x_in_I)))
         <> 0 ->
         derivable_pt g x.
Proof.
intros f g lb ub x x_in_I f_recip_g g_ok f_deriv lb_lt_ub [f_incr | f_decr] Df_neq.
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
 assert (f_mono := strictly_increasing_strictly_monotonous_interval _ _ _ f_incr).
 assert (g_eq_f := strictly_monotonous_recip_interval_comm f g lb ub f_mono f_recip_g g_ok).
 unfold reciprocal_interval, comp, id in g_eq_f.
 assert (f_derivable2 : forall a : R, interval (g (f lb)) (g (f ub)) a -> derivable_pt f a).
  intros a a_encad ; apply f_deriv.
  rewrite g_eq_f in a_encad ; rewrite g_eq_f in a_encad ; intuition ;
  try apply interval_l || apply interval_r ; intuition.
 apply derivable_pt_reciprocal_interv with (f:=f) (lb:=f lb) (ub:=f ub)
     (f_deriv:=f_derivable2) (g_incr:=g_incr2) ; try assumption.
rewrite Rmin_eq_l, Rmax_eq_r in f_recip_g ; intuition.
assert (T := continuity_reciprocal_strictly_increasing_interval f g lb ub
      (Rlt_le _ _ lb_lt_ub) f_incr g_eq_f (derivable_continuous_interval _ _ _ f_deriv)) ;
apply T ; assumption.
rewrite pr_nu_var2 with (g:=f) (pr2:=f_deriv (g x)
              (g_ok x (open_interval_interval (Rmin (f lb) (f ub))
              (Rmax (f lb) (f ub)) x x_in_I))) ; intuition.

admit.

Qed.
