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

(** Properties of real functions sequences. *)

Require Import Reals.
Require Import RFsequence.
Require Import Lra.
Require Import Max.

Open Scope R_scope.

(* begin hide *)
Lemma ub_lt_2_pos : forall x ub lb, lb < x -> x < ub -> 0 < (ub-lb)/2.
Proof.
intros x ub lb lb_lt_x x_lt_ub.
 assert (T : 0 < ub - lb).
  lra.
 unfold Rdiv ; apply Rlt_mult_inv_pos ; intuition.
Qed.

Definition mkposreal_lb_ub : forall (x lb ub:R) (lb_lt_x:lb<x) (x_lt_ub:x<ub), posreal.
intros x lb ub lb_lt_x x_lt_ub.
 apply (mkposreal ((ub-lb)/2) (ub_lt_2_pos x ub lb lb_lt_x x_lt_ub)).
Defined.
(* end hide *)

Lemma RFseq_cvu_derivable : forall (fn fn':nat -> R -> R) (f g:R->R)
      (x lb ub:R) (lb_lt_x:lb < x) (x_lt_ub:x < ub), 
      (forall (x:R) (n:nat), lb < x -> x < ub -> derivable_pt_lim (fn n) x (fn' n x)) ->
      (RFseq_cv_interv fn f lb ub) ->
      (RFseq_cvu fn' g ((lb + ub)/2) (mkposreal_lb_ub x lb ub lb_lt_x x_lt_ub)) ->
      (forall (x:R), lb < x -> x < ub -> continuity_pt g x) ->
      derivable_pt_lim f x (g x).
Proof.
intros fn fn' f g x lb ub lb_lt_x x_lt_ub Dfn_eq_fn' fn_CV_f fn'_CVU_g g_cont eps eps_pos.
 assert (eps_8_pos : 0 < eps / 8) by lra.
 destruct (g_cont x lb_lt_x x_lt_ub (eps/8)%R eps_8_pos) as (delta1, Hdelta1) ; clear g_cont ;
 destruct Hdelta1 as (delta1_pos, g_cont).
 assert (delta_pos : 0 < Rmin (Rmin ((x-lb)/2) ((ub-x)/2)) delta1).
  apply Rmin_pos ; [apply Rmin_pos | intuition] ; unfold Rdiv ;
  apply Rlt_mult_inv_pos ; intuition ; apply Rlt_Rminus ; intuition.
 pose (delta := mkposreal (Rmin (Rmin ((x-lb)/2) ((ub-x)/2)) delta1) (delta_pos)).
 exists delta ; intros h h_neq h_ub.
 assert (eps'_pos : 0 < (Rabs h) * eps / 4).
  unfold Rdiv ; rewrite Rmult_assoc ; apply Rmult_lt_0_compat.
  apply Rabs_pos_lt ; assumption.
  lra.
 elim (fn_CV_f x lb_lt_x x_lt_ub ((Rabs h) * eps / 4)%R eps'_pos) ; intros N2 fnx_CV_fx.
 assert(lb_lt_xh : lb < x + h).
  apply Rlt_trans with (x - delta)%R.
  unfold delta.
  assert (Temp : forall a b c, a + c < b -> a < b - c).
   intros ; lra.
  apply Temp ; clear Temp ; apply Rle_lt_trans with (lb + Rmin ((x - lb) / 2) ((ub - x) / 2))%R.
  apply Rplus_le_compat_l ; apply Rmin_l.
  apply Rle_lt_trans with (lb + (x - lb) / 2)%R.
  apply Rplus_le_compat_l ; apply Rmin_l.
  replace (lb + (x - lb) / 2) with ((lb + x)/2) by field.
  assert (Temp : forall a b, a < b -> (a+b)/2 < b).
   clear ; intros a b a_lt_b.
   unfold Rdiv ; rewrite Rmult_plus_distr_r.
   lra.
  apply Temp ; assumption.
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
   lra.
  apply Temp ; assumption.
 elim (fn_CV_f (x+h) lb_lt_xh xh_lt_ub ((Rabs h) * eps / 4) eps'_pos) ;
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
   apply Rlt_trans with x ; intuition.
  exists (fn' N c) ; apply Dfn_eq_fn' ; intuition.
 assert (pr2 : forall c : R, x + h < c < x -> derivable_pt id c).
  intros c c_encad ; apply derivable_id.
 assert (xh_x : x+h < x).
  lra.
 assert (pr3 : forall c : R, x + h <= c <= x -> continuity_pt (fn N) c).
  intros c c_encad ; apply derivable_continuous_pt.
  exists (fn' N c) ; apply Dfn_eq_fn' ; intuition.
  apply Rlt_le_trans with (x+h) ; intuition.
  apply Rle_lt_trans with x ; intuition.
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
 apply fn'c_CVU_gc.
 unfold N ; apply le_max_r.
 unfold Boule.
 assert (Rabs (c - (lb + ub) / 2) < (ub - lb) / 2).
  apply Rabs_def1.
  assert (Temp : forall a b c, a < b + c -> a - b < c). intros ; lra.
  apply Temp ; clear Temp ; replace ((lb + ub) / 2 + (ub - lb) / 2) with ub by field.
  apply Rlt_trans with x ; [exact (proj2 P) | intuition].
  assert (Temp : forall a b c, a - b < c -> - b < c - a). intros ; lra.
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
  intros ; lra.
 apply Temp ; exact (proj2 P).
 apply Rabs_pos_lt ; assumption.
 apply Rle_lt_trans with h.
 rewrite Rabs_left1.
 apply Req_le ; field.
 apply Rlt_le ; assumption.
 assert (Temp : forall a b c, a + b < c -> b < c - a). intros ; lra.
 apply Temp ; clear Temp ; exact (proj1 P).
 apply Rlt_le_trans with delta ; [intuition | unfold delta ; apply Rmin_r].
 rewrite Rplus_assoc ; rewrite Rplus_assoc ; rewrite <- Rmult_plus_distr_l.
 replace (Rabs h * eps / 4 + (Rabs h * eps / 4 + Rabs h * (eps / 8 + eps / 8))) with
      (Rabs h * (eps / 4 + eps / 4 + eps / 8 + eps / 8)) by field.
 apply Rmult_lt_compat_l. 
 apply Rabs_pos_lt ; assumption.
 lra.
 assert (lb_lt_c : lb < c).
   apply Rlt_trans with (x+h) ; intuition ; exact (proj1 P).
  assert (c_lt_ub : c < ub).
   apply Rlt_trans with x ; intuition ; exact (proj2 P).
 assert (H := pr1 c P) ; elim H ; clear H ; intros l Hl.
 assert (Temp : l = fn' N c).
  assert (Hl' := Dfn_eq_fn' c N lb_lt_c c_lt_ub).
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
   apply Rlt_trans with x ; intuition.
  assert (c_lt_ub : c < ub).
   apply Rlt_trans with (x+h) ; intuition.
  exists (fn' N c) ; apply Dfn_eq_fn' ; intuition.
 assert (pr2 : forall c : R, x < c < x + h -> derivable_pt id c).
  intros c c_encad ; apply derivable_id.
 assert (xh_x : x < x + h).
  lra.
 assert (pr3 : forall c : R, x <= c <= x + h -> continuity_pt (fn N) c).
  intros c c_encad ; apply derivable_continuous_pt.
  exists (fn' N c) ; apply Dfn_eq_fn' ; intuition.
  apply Rlt_le_trans with x ; intuition.
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
 apply fn'c_CVU_gc.
 unfold N ; apply le_max_r.
 unfold Boule.
 assert (Rabs (c - (lb + ub) / 2) < (ub - lb) / 2).
  apply Rabs_def1.
  assert (Temp : forall a b c, a < b + c -> a - b < c). intros ; lra.
  apply Temp ; clear Temp ; replace ((lb + ub) / 2 + (ub - lb) / 2) with ub by field.
  apply Rlt_trans with (x+h) ; [exact (proj2 P) | intuition].
  assert (Temp : forall a b c, a - b < c -> - b < c - a). intros ; lra.
  apply Temp ; clear Temp ; replace ((lb + ub) / 2 - ((ub - lb) / 2)) with lb by field.
  apply Rlt_trans with x ; [intuition | exact (proj1 P)].
  assumption.
 apply Rlt_trans with (Rabs h * eps / 4 + Rabs h * eps / 4 + Rabs h * (eps / 8) +
         Rabs h * (eps / 8)).
 rewrite Rplus_assoc ; rewrite Rplus_assoc ; rewrite Rplus_assoc ; rewrite Rplus_assoc ;
 apply Rplus_lt_compat_l ; apply Rplus_lt_compat_l ; rewrite <- Rmult_plus_distr_l ;
 rewrite <- Rmult_plus_distr_l ; apply Rmult_lt_compat_l.
 apply Rabs_pos_lt ; assumption.
 apply Rplus_lt_compat_l ; simpl in g_cont ; apply g_cont ; split ; [unfold D_x ; split |].
 unfold no_cond ; intuition. apply Rlt_not_eq ; exact (proj1 P).
 unfold R_dist. apply Rlt_trans with (Rabs h).
 apply Rabs_def1. 
 assert (Temp : forall a b c, c < a + b -> c - a < b). intros ; lra.
 apply Temp ; clear Temp ; rewrite Rabs_right. exact (proj2 P).
 apply Rgt_ge ; assumption.
 assert (Temp : forall a b, a - b < c -> - b < c - a). intros ; lra.
 apply Temp ; apply Rlt_trans with x ; [| exact (proj1 P)].
 rewrite <- Rplus_0_r.
 apply Rplus_lt_compat_l.
 apply Ropp_lt_gt_0_contravar ; apply Rabs_pos_lt ; apply Rgt_not_eq ; assumption.
 apply Rle_lt_trans with h.
 rewrite Rabs_right. apply Req_le ; reflexivity.
 lra.
 apply Rlt_le_trans with delta ; [intuition | unfold delta ; apply Rmin_r].
 rewrite Rabs_right in h_ub ; intuition.
 rewrite Rplus_assoc ; rewrite Rplus_assoc ; rewrite <- Rmult_plus_distr_l.
 replace (Rabs h * eps / 4 + (Rabs h * eps / 4 + Rabs h * (eps / 8 + eps / 8))) with
      (Rabs h * (eps / 4 + eps / 4 + eps / 8 + eps / 8)) by field.
 apply Rmult_lt_compat_l. 
 apply Rabs_pos_lt ; assumption.
 lra.
 assert (lb_lt_c : lb < c).
   apply Rlt_trans with x ; intuition ; exact (proj1 P).
  assert (c_lt_ub : c < ub).
   apply Rlt_trans with (x+h) ; intuition ; exact (proj2 P).
 assert (H := pr1 c P) ; elim H ; clear H ; intros l Hl.
 assert (Temp : l = fn' N c).
  assert (Hl' := Dfn_eq_fn' c N lb_lt_c c_lt_ub).
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

Definition SFL_interv : forall (fn:nat -> R -> R) (r:posreal)
  (cv:forall x:R, Boule 0 r x -> {l:R | Un_cv (fun N:nat => SP fn N x) l }) (y:R), R.
Proof.
intros fn r cv x.
 case (Rlt_le_dec x r) ; intro x_bd1.
 case (Rlt_le_dec (-r) x) ; intro x_bd2.
 assert (x_bd : Boule 0 r x).
  apply Rabs_def1 ; rewrite Rminus_0_r ; assumption.
 destruct (cv _ x_bd) as (l, _) ; apply l.
 exact 0.
 exact 0.
Defined.

Lemma SFL_interv_right : forall fn r cv y, Boule 0 r y ->
     Un_cv (fun N:nat => SP fn N y) (SFL_interv fn r cv y).
Proof.
intros fn r cv y y_bd ; unfold SFL_interv ; case (Rlt_le_dec y r) ; intro y_bd1.
 case (Rlt_le_dec (- r) y) ; intro y_bd2.
 destruct (cv y
       (Rabs_def1 (y - 0) r
          (eq_ind_r (fun r0 : R => r0 < r) y_bd1 (Rminus_0_r y))
          (eq_ind_r (fun r0 : R => - r < r0) y_bd2 (Rminus_0_r y)))) as (l', Hl').
  assumption.
  clear -y_bd y_bd1 y_bd2 ;
  destruct (Rabs_def2 _ _ y_bd) as [H1 H2] ; rewrite Rminus_0_r in H1, H2 ;
  apply False_ind ; apply Rlt_irrefl with (-r) ; apply Rlt_le_trans with y ; assumption.
  clear -y_bd y_bd1; destruct (Rabs_def2 _ _ y_bd) as [H1 H2] ;
  rewrite Rminus_0_r in H1, H2 ; apply False_ind ; apply Rlt_irrefl with y ;
  apply Rlt_le_trans with r ; assumption.
Qed.

(** In a complete space, normal convergence implies uniform convergence *)
Lemma CVN_CVU_interv : forall (fn:nat -> R -> R) (r:posreal)
    (cv:forall x:R, Boule 0 r x -> {l:R | Un_cv (fun N:nat => SP fn N x) l }),
    CVN_r fn r -> CVU (fun n:nat => SP fn n) (SFL_interv fn r cv) 0 r.
Proof.
  intros; unfold CVU in |- *; intros.
  unfold CVN_r in X.
  elim X; intros An X0.
  elim X0; intros s H0.
  elim H0; intros.
  cut (Un_cv (fun n:nat => sum_f_R0 (fun k:nat => Rabs (An k)) n - s) 0).
  intro; unfold Un_cv in H3.
  elim (H3 eps H); intros N0 H4.
  exists N0; intros.
  apply Rle_lt_trans with (Rabs (sum_f_R0 (fun k:nat => Rabs (An k)) n - s)).
  rewrite <- (Rabs_Ropp (sum_f_R0 (fun k:nat => Rabs (An k)) n - s)).
    rewrite Ropp_minus_distr';
      rewrite (Rabs_right (s - sum_f_R0 (fun k:nat => Rabs (An k)) n)).
  eapply sum_maj1.
  unfold SFL in |- *; case (cv y H6) ; intro.
  unfold SFL_interv.
  case (Rlt_le_dec y r) ; intro y_bd1.
  case (Rlt_le_dec (- r) y) ; intro y_bd2.
  destruct (cv y
         (Rabs_def1 (y - 0) r
            (eq_ind_r (fun r0 : R => r0 < r) y_bd1 (Rminus_0_r y))
            (eq_ind_r (fun r0 : R => - r < r0) y_bd2 (Rminus_0_r y)))) as (l, Hl).
   trivial.
   clear -H6 y_bd1 y_bd2 ;
   destruct (Rabs_def2 _ _ H6) as [H1 H2] ; rewrite Rminus_0_r in H1, H2 ;
   apply False_ind ; apply Rlt_irrefl with (-r) ; apply Rlt_le_trans with y ; assumption.
   clear -H6 y_bd1; destruct (Rabs_def2 _ _ H6) as [H1 H2] ;
   rewrite Rminus_0_r in H1, H2 ; apply False_ind ; apply Rlt_irrefl with y ;
   apply Rlt_le_trans with r ; assumption.
   apply H1.
  intro; elim H0; intros.
  rewrite (Rabs_right (An n0)).
  apply H8; apply H6.
  apply Rle_ge; apply Rle_trans with (Rabs (fn n0 y)).
  apply Rabs_pos.
  apply H8; apply H6.
  apply Rle_ge;
    apply Rplus_le_reg_l with (sum_f_R0 (fun k:nat => Rabs (An k)) n).
  rewrite Rplus_0_r; unfold Rminus in |- *; rewrite (Rplus_comm s);
    rewrite <- Rplus_assoc; rewrite Rplus_opp_r; rewrite Rplus_0_l;
      apply sum_incr.
  apply H1.
  intro; apply Rabs_pos.
  unfold R_dist in H4; unfold Rminus in H4; rewrite Ropp_0 in H4.
  assert (H7 := H4 n H5).
  rewrite Rplus_0_r in H7; apply H7.
  unfold Un_cv in H1; unfold Un_cv in |- *; intros.
  elim (H1 _ H3); intros.
  exists x; intros.
  unfold R_dist in |- *; unfold R_dist in H4.
  rewrite Rminus_0_r; apply H4; assumption.
Qed.
