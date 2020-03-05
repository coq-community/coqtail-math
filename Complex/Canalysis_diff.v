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

Require Import Cprop_base.
Require Import Cnorm.
Require Import Ctacfield.
Require Import Canalysis_def.

Open Scope C_scope.

(**********)
Lemma uniqueness_step1 : forall f (x v l1 l2 : C), v <> 0 ->
    limit1_in (fun u => (f (x + u) - f x) / u) (fun u => u <> 0 /\ exists h:R, h * u = v) l1 0 ->
    limit1_in (fun u => (f (x + u) - f x) / u) (fun u => u <> 0 /\ exists h:R, h * u = v) l2 0 ->
    l1 = l2.
Proof.
intros f x v l1 l2 v_neq Hl1 Hl2 ;
 apply (single_limit (fun u => (f (x + u) - f x) / u) (fun u => u <> 0 /\ exists h:R, h * u = v) l1 l2 0);
 try assumption.
 intros alp alp_pos.
  case (Rlt_le_dec (Cnorm v) alp) ; intro alp_bd.
  exists v ; repeat split.
  assumption.
  exists 1%R ; CusingR_f.
  unfold C_dist ; rewrite Cminus_0_r ; assumption.
  exists (v * ((alp / 2) / Cnorm v)) ; repeat split.
  unfold Cdiv ; repeat apply Cmult_integral_contrapositive_currified.
  assumption.
  apply IRC_neq_0_compat ; apply Rgt_not_eq ; assumption.
  apply Cinv_neq_0_compat ; apply IRC_neq_0_compat ;
  apply Rgt_not_eq ; lra.
  apply Cinv_neq_0_compat ; apply IRC_neq_0_compat ;
  apply Cnorm_no_R0 ; assumption.
  exists (2 * Cnorm v / alp)%R.
  unfold Rdiv, Cdiv.
  CusingR_f ; try split.
  apply Cnorm_no_R0 ; assumption.
  apply Rgt_not_eq ; assumption.
  apply Cnorm_no_R0 ; assumption.
  apply Rgt_not_eq ; assumption.
  unfold C_dist ; rewrite Cminus_0_r.
  unfold Cdiv ; rewrite Cmult_comm ; repeat rewrite Cnorm_Cmult.
  repeat rewrite Cnorm_inv.
  rewrite Cnorm_invol, Rmult_assoc, Rinv_l.
  rewrite Rmult_1_r ; rewrite <- Cnorm_inv.
  rewrite <- Cnorm_Cmult.
  replace (alp * / 2)%C with (IRC (alp / 2)%R).
  rewrite Cnorm_IRC_Rabs, Rabs_right.
  lra.
  lra.
  clear ; CusingR_f.
  apply IRC_neq_0_compat ; apply Rgt_not_eq ; lra.
  apply Cnorm_no_R0 ; assumption.
  apply IRC_neq_0_compat ; apply Cnorm_no_R0 ; assumption.
  apply IRC_neq_0_compat ; apply Rgt_not_eq ; lra.
Qed.

Lemma uniqueness_step2 : forall f (x : C) (v : C) (l : C), v <> 0 ->
    differentiable_pt_lim f x v l ->
    limit1_in (fun u => (f (x + u) - f x) / u) (fun u => u <> 0 /\ exists h:R, h * u = v) l 0.
Proof. 
unfold derivable_pt_lim, limit1_in, limit_in.
intros f x v l v_neq Hf_deriv eps eps_pos ; destruct (Hf_deriv v_neq eps eps_pos) as
 ([alpha alpha_pos], Halpha) ; clear Hf_deriv ; exists (alpha * Cnorm v)%R ; split.
 apply Rmult_lt_0_compat ; [| apply Cnorm_pos_lt]; eauto with *.
 intros h [[h_neq [u h_rew]] Hh] ; simpl in * ; unfold C_dist in *.
 assert (u_neq : (u <> 0)%R).
  intro Hf ; apply v_neq ; rewrite <- h_rew, Hf ; CusingR_f.
 replace h with ((/u)%R * v).
 apply (Halpha (/u)%R).
 apply Rinv_neq_0_compat ; assumption.
 rewrite Cminus_0_r in Hh.
 replace (Rabs (/u))%R with (Cnorm h / Cnorm v)%R.
 apply Rlt_le_trans with (alpha * Cnorm v * / Cnorm v)%R.
 unfold Rdiv ; apply Rmult_lt_compat_r.
 apply Rinv_0_lt_compat ; apply Cnorm_pos_lt ; assumption.
 assumption.
 right ; field ; apply Cnorm_no_R0 ; assumption.
 rewrite <- h_rew.
 unfold Rdiv ; rewrite <- Cnorm_inv.
 rewrite <- Cnorm_Cmult.
 replace (h * / (u * h)) with (IRC (/ u)).
 apply Cnorm_IRC_Rabs.
 rewrite Cinv_mult_distr, Cmult_comm, Cmult_assoc, Cinv_l, Cmult_1_r.
 clear -u_neq ; CusingR ; field ; assumption.
 assumption.
 apply IRC_neq_0_compat ; assumption.
 assumption.
 apply Cmult_integral_contrapositive_currified ; [apply IRC_neq_0_compat |] ;
 assumption.
 rewrite <- h_rew.
 replace (IRC (/ u)) with (/ u).
 field ; apply IRC_neq_0_compat ; assumption.
 CusingR_f ; assumption.
Qed.

Lemma uniqueness_step3 : forall f x v l,
    limit1_in (fun u => (f (x + u) - f x) / u) (fun u => u <> 0 /\ exists h:R, h * u = v) l 0 ->
    differentiable_pt_lim f x v l.
Proof.
unfold limit1_in, derivable_pt_lim, limit_in, C_dist ; simpl ; unfold C_dist ;
intros f x v l Hf_lim v_neq eps eps_pos ; destruct (Hf_lim eps eps_pos) as
 (alpha, [alpha_pos Halpha]) ; clear Hf_lim.
 assert (alpha'_pos : 0 < alpha / Cnorm v).
  unfold Rdiv ; apply Rlt_mult_inv_pos ; [| apply Cnorm_pos_lt] ;
  assumption.
 exists (mkposreal (alpha / Cnorm v)%R alpha'_pos) ; intros h h_neq Hyp ;
 apply Halpha ; rewrite Cminus_0_r ; repeat split.
 apply Cmult_integral_contrapositive_currified ; [apply IRC_neq_0_compat |] ;
 assumption.
 exists (/h)%R.
 rewrite <- Cmult_assoc.
 replace ((/ h)%R * h) with C1.
 apply Cmult_1_l.
 CusingR_f ; assumption.
 rewrite Cnorm_Cmult ; apply Rlt_le_trans with (alpha / Cnorm v * Cnorm v)%R.
 apply Rmult_lt_compat_r.
 apply Cnorm_pos_lt ; assumption.
 rewrite Cnorm_IRC_Rabs ; apply Hyp.
 right ; field ; apply Cnorm_no_R0 ; assumption.
Qed.

Lemma uniqueness_limite : forall f (x v l1 l2 : C), v <> 0 ->
    differentiable_pt_lim f x v l1 -> differentiable_pt_lim f x v l2 -> l1 = l2.
Proof.
intros f x v l1 l2 v_neq Hf_deriv1 Hf_deriv2 ;
 assert (H1 := uniqueness_step2 _ _ _ _ v_neq Hf_deriv1) ;
 assert (H2 := uniqueness_step2 _ _ _ _ v_neq Hf_deriv2) ;
 apply uniqueness_step1 with f x v ; assumption.
Qed.

Lemma differential_pt_eq : forall f x v l (pr:differentiable_pt f x v), v <> 0 ->
    (differential_pt f x v pr = l <-> differentiable_pt_lim f x v l).
Proof.
intros f x v l pr v_neq ; split ; intro Hf_deriv.
 assert (H := proj2_sig pr) ; unfold derive_pt in Hf_deriv ;
 rewrite Hf_deriv in H ; assumption.
 assert (H := proj2_sig pr) ; unfold derivable_pt_abs in H.
 assert (H' := uniqueness_limite _ _ _ _ (proj1_sig pr) v_neq Hf_deriv H) ;
 symmetry ; assumption.
Qed.

(**********)
Lemma differential_pt_eq_0 : forall f x v l (pr:differentiable_pt f x v),
    v <> 0 -> differentiable_pt_lim f x v l -> differential_pt f x v pr = l.
Proof.
intros f x v l pr v_neq ; destruct (differential_pt_eq f x v l pr) ; assumption.
Qed.

(**********)
Lemma differential_pt_eq_1 : forall f x v l (pr:differentiable_pt f x v),
    v <> 0 -> differential_pt f x v pr = l -> differentiable_pt_lim f x v l.
Proof.
intros f x v l pr v_neq ; destruct (differential_pt_eq f x v l pr) ; assumption.
Qed.

(***********************************)
(** * differentiability -> continuity along an axis *)
(***********************************)

Lemma differentiable_continuous_along_axis : forall f (x v : C),
      differentiable_pt f x v -> continuity_along_axis_pt f v x.
Proof.
intros f x v f_diff.
 destruct (Ceq_dec v C0) as [v_eq | v_neq] ; intros eps eps_pos.
  exists (mkposreal R1 Rlt_0_1) ;
   intros h h_ub ; simpl ; unfold C_dist, Cminus ; rewrite v_eq, Cmult_0_r,
    Cadd_0_r, Cadd_opp_r, Cnorm_C0 ; assumption.
   destruct f_diff as (l, f_diff) ; destruct (Ceq_dec l C0) as [l_eq | l_neq].
  assert (eps_2_pos : eps / 2 > 0) by lra ;
  destruct (f_diff v_neq (eps / 2)%R eps_2_pos) as ([alpha alpha_pos], Halpha).
  assert (delta_pos : 0 < Rmin (/ (2 * Cnorm v)) alpha).
   apply Rmin_pos.
   rewrite Rinv_mult_distr.
   apply Rlt_mult_inv_pos ; [lra | apply Cnorm_pos_lt ; assumption].
   apply Rgt_not_eq ; lra.
   apply Rgt_not_eq ; apply Cnorm_pos_lt ; assumption.
   assumption.
  exists (mkposreal (Rmin (/(2 * Cnorm v)) alpha) delta_pos).
  intros h h_ub ; simpl ; unfold C_dist ; destruct (Ceq_dec h 0) as [h_eq | h_neq].
  rewrite h_eq, Cmult_0_l, Cadd_0_r,
  Cminus_diag_eq ; [| reflexivity] ; rewrite Cnorm_C0 ; assumption.
   apply Rlt_trans with (Cnorm (h * v) *eps)%R.
   apply Rle_lt_trans with (Cnorm (f (x + h * v)%C - f x) * (/ Cnorm (h * v) * Cnorm (h * v)))%R.
   right ; field ; apply Rgt_not_eq ; apply Cnorm_pos_lt ;
   apply Cmult_integral_contrapositive_currified ; assumption.
   unfold Rdiv ; rewrite  <- Rmult_assoc ; rewrite <- Cnorm_inv, <- Cnorm_Cmult.
   rewrite Rmult_comm ; apply Rmult_lt_compat_l.
   apply Cnorm_pos_lt ; apply Cmult_integral_contrapositive_currified ; assumption.
   replace ((f (x + h * v) - f x) * / (h * v)) with ((f (x + h * v) - f x) / (h *v) - l). 
   apply Rlt_trans with (eps / 2)%R.
   apply Halpha.
   intro Hf ; apply h_neq ; rewrite Hf ; intuition.
   subst ; apply Rlt_le_trans with (Rmin (/(2* Cnorm v)) alpha) ; [apply h_ub | apply Rmin_r].
   lra.
   rewrite l_eq ; field ; split ; assumption.
   apply Cmult_integral_contrapositive_currified ; assumption.
   rewrite Cnorm_Cmult.
   apply Rlt_trans with ((Rmin (/(2 * Cnorm v)) alpha) * Cnorm v * eps)%R.
   repeat apply Rmult_lt_compat_r ; [| apply Cnorm_pos_lt | rewrite Cnorm_IRC_Rabs] ;
   assumption.
   apply Rle_lt_trans with (eps / 2)%R.
   unfold Rdiv ; rewrite Rmult_comm ; apply Rmult_le_compat_l ; intuition ;
   apply Rle_trans with (/(2*Cnorm v) * Cnorm v)%R.
   apply Rmult_le_compat_r ; [apply Cnorm_pos | apply Rmin_l].
   right ; field.
   apply Rgt_not_eq ; apply Cnorm_pos_lt ; assumption.
   lra.
   assert (eps_2_pos : eps / 2 > 0) by lra ; 
   destruct (f_diff v_neq (eps / 2)%R eps_2_pos) as ([alpha alpha_pos], Halpha).
   pose (delta1 := Rmin (eps / (2 * Cnorm l)) (Rmin (1/2) alpha)).
   assert (delta1_pos : 0 < delta1).
    unfold delta1 ; repeat apply Rmin_pos.
    apply Rlt_mult_inv_pos ; [| apply Rmult_lt_0_compat] ;
    [| lra | apply Cnorm_pos_lt] ; assumption.
    lra.
    assumption.
   pose (delta := Rmin (delta1 / Cnorm v)%R delta1).
   assert (delta_pos : 0 < delta).
    unfold delta ; apply Rmin_pos.
    unfold Rdiv ; apply Rlt_mult_inv_pos ; [| apply Cnorm_pos_lt] ; assumption.
    assumption.
   exists (mkposreal delta delta_pos) ; intros h h_ub ; simpl ; unfold C_dist, Cminus.
   destruct (Ceq_dec h 0) as [h_eq | h_neq].
   rewrite h_eq, Cmult_0_l, Cadd_0_r, Cadd_opp_r, Cnorm_C0 ; assumption.
  apply Rlt_trans with (Cnorm (h * v) * eps + Cnorm (h * v) * Cnorm l )%R.
  apply Rle_lt_trans with (Cnorm (f (x + h * v)%C - f x) * (/ Cnorm (h * v) * Cnorm (h * v)))%R.
  right ; rewrite Rinv_l, Rmult_1_r ; [reflexivity |].
  apply Cnorm_no_R0 ; apply Cmult_integral_contrapositive_currified ;
  assumption.
   unfold Rdiv ; rewrite  <- Rmult_assoc ; rewrite <- Cnorm_inv, <- Cnorm_Cmult.
   apply Rle_lt_trans with ((Cnorm ((f (x + h * v)%C - f x) * / (h * v)) + (- Cnorm l + Cnorm l)) * Cnorm (h*v))%R.
   right ; field.
   repeat rewrite Rmult_plus_distr_r.
   replace (Cnorm l * Cnorm (h * v))%R with (Cnorm (h *v) * Cnorm l)%R
      by (apply Rmult_comm).
   rewrite <- Rplus_assoc ; apply Rplus_lt_compat_r.
   apply Rle_lt_trans with (Cnorm ((f (x +h * v)%C - f x) / (h * v) - l)* Cnorm (h * v))%R.
   rewrite <- Rmult_plus_distr_r ; apply Rmult_le_compat_r ;
   [apply Cnorm_pos | apply Cnorm_triang_rev_l].
   rewrite Rmult_comm ; apply Rmult_lt_compat_l.
   apply Cnorm_pos_lt ; apply Cmult_integral_contrapositive_currified ; assumption.
   apply Rlt_trans with (eps /2)%R ; [apply Halpha | lra].
   intro Hf ; apply h_neq ; rewrite Hf ; intuition.
   apply Rlt_le_trans with delta ; [apply h_ub |].
   apply Rle_trans with delta1 ; [apply Rmin_r |].
   apply Rle_trans with (Rmin (1/2) alpha) ; apply Rmin_r.
   apply Cmult_integral_contrapositive_currified ; assumption.
   apply Rlt_trans with (eps / 2 + Cnorm (h*v) * Cnorm l)%R.
   apply Rplus_lt_compat_r.
   unfold Rdiv ; rewrite Rmult_comm ; apply Rmult_lt_compat_l ;
   [assumption |].
   apply Rlt_le_trans with delta1.
   unfold delta1.
   apply Rlt_le_trans with (delta * Cnorm v)%R.
   rewrite Cnorm_Cmult ; apply Rmult_lt_compat_r ; [apply Cnorm_pos_lt ; assumption |] ;
   rewrite Cnorm_IRC_Rabs ; assumption.
   apply Rle_trans with (delta1 / Cnorm v * Cnorm v)%R. 
   apply Rmult_le_compat_r ; [apply Cnorm_pos | apply Rmin_l].
   unfold Rdiv ; rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
   right ; reflexivity.
   apply Cnorm_no_R0 ; assumption.
 apply Rle_trans with (Rmin (1/2) alpha) ; [apply Rmin_r | apply Rle_trans with (1/2)%R ;
   [apply Rmin_l | right ; field]].
   apply Rlt_le_trans with (eps / 2 + eps / 2)%R ; [apply Rplus_lt_compat_l | right ; field].
   replace (eps / 2)%R with ((eps / (2 * Cnorm l)) * Cnorm l)%R
       by (field ; apply Cnorm_no_R0 ; assumption).
   apply Rmult_lt_compat_r.
   apply Cnorm_pos_lt ; assumption.
   apply Rlt_le_trans with (Rmin (eps / (2 * Cnorm l)) (Rmin (1 / 2) alpha)).
   apply Rlt_le_trans with (delta * Cnorm v)%R.
   rewrite Cnorm_Cmult ; apply Rmult_lt_compat_r ; [apply Cnorm_pos_lt ; assumption |] ;
   rewrite Cnorm_IRC_Rabs ; assumption.
   apply Rle_trans with (delta1 / Cnorm v * Cnorm v)%R. 
   apply Rmult_le_compat_r ; [apply Cnorm_pos | apply Rmin_l].
   unfold Rdiv ; rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
   right ; reflexivity.
   apply Cnorm_no_R0 ; assumption.
   apply Rmin_l.
Qed.

(****************************************************************)
(** *                    Main rules                             *)
(****************************************************************)

Lemma differentiable_pt_lim_plus : forall f1 f2 x v l1 l2, v <> C0 ->
    differentiable_pt_lim f1 x v l1 -> differentiable_pt_lim f2 x v l2 ->
    differentiable_pt_lim (f1 + f2) x v (l1 + l2).
Proof.
intros f1 f2 x v l1 l2 v_neq H H0.
 apply uniqueness_step3.
 assert (H1 := uniqueness_step2 _ _ _ _ v_neq H).
 assert (H2 := uniqueness_step2 _ _ _ _ v_neq H0).
 unfold plus_fct in |- *.
  cut
    (forall h,
      (f1 (x + h) + f2 (x + h) - (f1 x + f2 x)) / h =
      (f1 (x + h) - f1 x) / h + (f2 (x + h) - f2 x) / h).
  intro H3 ; generalize
    (limit_plus (fun h' => (f1 (x + h') - f1 x) / h')
    (fun h' => (f2 (x + h') - f2 x) / h')
    (fun u => u <> 0 /\ (exists h : R, h * u = v)) l1 l2 0 H1 H2).
 intros H4 eps eps_pos.
  elim (H4 eps eps_pos); intros x0 Hx0.
  exists x0.
  destruct Hx0 as [x0_pos Hx0'].
  split.
  assumption.
  intros; rewrite H3; apply Hx0'; assumption.
  intro; unfold Cdiv ; ring.
Qed.

Lemma differentiable_pt_lim_opp : forall f x v l,
     v <> C0 -> differentiable_pt_lim f x v l ->
     differentiable_pt_lim (- f) x v (- l).
Proof. 
intros f x v l v_neq H.
 apply uniqueness_step3.
 assert (H1 := uniqueness_step2 _ _ _ _ v_neq H).
  unfold opp_fct in |- * ;
  cut (forall h, (- f (x + h) - - f x) / h = - ((f (x + h) - f x) / h)).
  intro.
  generalize
    (limit_opp (fun h => (f (x + h) - f x) / h)
    (fun u => u <> 0 /\ (exists h : R, h * u = v)) l 0 H1).
  unfold limit1_in in |- *; unfold limit_in in |- *; unfold dist in |- *;
    simpl in |- *; unfold R_dist in |- *; intros.
  elim (H2 eps H3); intros.
  exists x0.
  elim H4; intros.
  split.
  assumption.
  intros; rewrite H0; apply H6; assumption.
  intro; unfold Cdiv in |- *; ring.
Qed.

Lemma differentiable_pt_lim_minus : forall f1 f2 x v l1 l2, v <> C0 ->
    differentiable_pt_lim f1 x v l1 -> differentiable_pt_lim f2 x v l2 ->
    differentiable_pt_lim (f1 - f2) x v (l1 - l2).
Proof.
  intros f1 f2 x v l1 l2 v_neq H H0.
  apply uniqueness_step3.
  assert (H1 := uniqueness_step2 _ _ _ _ v_neq H).
  assert (H2 := uniqueness_step2 _ _ _ _ v_neq H0).
  unfold minus_fct in |- *.
  cut
    (forall h,
      (f1 (x + h) - f1 x) / h - (f2 (x + h) - f2 x) / h =
      (f1 (x + h) - f2 (x + h) - (f1 x - f2 x)) / h).
  intro.
  generalize
    (limit_minus (fun h' => (f1 (x + h') - f1 x) / h')
      (fun h' => (f2 (x + h') - f2 x) / h')
      (fun u => u <> 0 /\ (exists h : R, h * u = v)) l1 l2 0 H1 H2).
  unfold limit1_in in |- *; unfold limit_in in |- *; unfold dist in |- *;
    simpl in |- *; unfold R_dist in |- *; intros.
  elim (H4 eps H5); intros.
  exists x0.
  elim H6; intros.
  split.
  assumption.
  intros; rewrite <- H3; apply H8; assumption.
  intro; unfold Cdiv in |- *; ring.
Qed.

Lemma differentiable_pt_lim_const : forall a x v, differentiable_pt_lim (fct_cte a) x v 0.
Proof.
  intros; unfold fct_cte, derivable_pt_lim in |- *.
  intros; exists (mkposreal 1 Rlt_0_1); intros; unfold Cminus in |- *;
  rewrite Cadd_opp_r; unfold Cdiv in |- * ; rewrite Cmult_0_l;
  rewrite Cadd_opp_r; rewrite Cnorm_C0; assumption.
Qed.

Lemma differentiable_pt_lim_mult : forall f1 f2 x v l1 l2,
    differentiable_pt_lim f1 x v l1 ->
    differentiable_pt_lim f2 x v l2 ->
    differentiable_pt_lim (f1 * f2) x v (l1 * f2 x + f1 x * l2).
Proof.
intros f1 f2 x v l1 l2 Hf1 Hf2 v_neq eps eps_pos.
 assert (Hrew : forall h, h <> 0 -> ((f1 * f2)%F (x + h * v) - (f1 * f2)%F x) / (h * v) -
     (l1 * f2 x + f1 x * l2) = ((f1 (x + h * v) - f1 x) / (h * v)) * f2 (x + h * v)
     - l1 * f2 (x + h * v) + l1 * f2 (x + h * v) - l1 * f2 x + (f1 x) * (f2 (x + h * v) - f2 x) / (h * v) - (f1 x) * l2).
  clear - v_neq.
  intros h h_neq.
  unfold Cminus, Cdiv, mult_fct ; ring.
 assert (Main : forall h : C, h <> 0 ->((f1 * f2)%F (x + h * v) - (f1 * f2)%F x) / (h * v) -
     (l1 * f2 x + f1 x * l2) = ((f1 (x + h * v) - f1 x) / (h * v) - l1) * f2 x +
     ((f1 (x + h * v) - f1 x) / (h * v) - l1) * (f2 (x + h*v) - f2 x) +
     l1 * (f2 (x + h * v) - f2 x) + f1 x * ((f2 (x + h * v) - f2 x) / (h * v) - l2)).
   clear - v_neq Hrew.
   intros h h_neq.
   unfold Cminus, Cdiv, mult_fct ; ring.
  clear Hrew.
  destruct (Ceq_dec l1 0) as [l1_eq | l1_neq].
  destruct (Ceq_dec (f1 x) 0) as [f1_eq | f1_neq].
  destruct (Ceq_dec (f2 x) 0) as [f2_eq | f2_neq].
  assert (Hf2' : differentiable_pt f2 x v).
   exists l2 ; apply Hf2.
  destruct (Rle_dec 1 eps) as [eps_lb | eps_ub].
  destruct (Hf1 v_neq (Rmin 1 eps)) as [delta1 Hdelta1] ; [apply Rmin_pos ; lra |].
  destruct (differentiable_continuous_along_axis f2 x v Hf2' (Rmin 1 eps)%R) as
  [delta2 Hdelta2] ; [apply Rmin_pos ; lra |].
  pose (delta := Rmin delta1 delta2) ; assert (delta_pos : 0 < delta) by
  (apply Rmin_pos ; [apply delta1 | apply delta2]).
  exists (mkposreal delta delta_pos) ; intros h h_neq h_ub.
  rewrite Main ; clear Main ; repeat rewrite l1_eq, f1_eq, f2_eq in * ;
  repeat rewrite Cmult_0_r ; repeat rewrite Cmult_0_l ;
  repeat rewrite Cadd_0_l ; repeat rewrite Cadd_0_r.
  apply Rlt_le_trans with 1%R ; [| assumption].
  rewrite Cnorm_Cmult ; apply Rle_lt_trans with (Cnorm (f2 (x + h * v) - 0)).
  rewrite <- Rmult_1_l ; apply Rmult_le_compat_r ; [apply Cnorm_pos |].
  apply Rle_trans with (Rmin 1 eps) ; [left ; apply Hdelta1 | apply Rmin_l].
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_l].
  apply Rlt_le_trans with (Rmin 1 eps) ; [simpl in Hdelta2 ; unfold C_dist in Hdelta2 ;
  apply Hdelta2 | apply Rmin_l].
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_r].
  apply IRC_neq_0_compat ; assumption.
  assert (eps_lt_1 := Rnot_le_lt _ _ eps_ub) ; clear eps_ub.
  assert (eps_2_lt_eps : eps * eps < eps).
   rewrite <- Rmult_1_r ; apply Rmult_lt_compat_l ; assumption.
  destruct (Hf1 v_neq eps eps_pos) as [delta1 Hdelta1].
  destruct (differentiable_continuous_along_axis f2 x v Hf2' eps eps_pos) as
  [delta2 Hdelta2].
  pose (delta := Rmin delta1 delta2) ; assert (delta_pos : 0 < delta) by
  (apply Rmin_pos ; [apply delta1 | apply delta2]).
  exists (mkposreal delta delta_pos) ; intros h h_neq h_ub ;
  rewrite Main ; [| apply IRC_neq_0_compat ; assumption] ;
  clear Main ; repeat rewrite l1_eq, f1_eq, f2_eq in * ;
  repeat rewrite Cmult_0_r ; repeat rewrite Cmult_0_l ;
  repeat rewrite Cadd_0_l ; repeat rewrite Cadd_0_r.
  rewrite Cnorm_Cmult ; apply Rlt_trans with (eps * eps)%R ;
  [| assumption] ; clear eps_lt_1 eps_2_lt_eps.
  apply Rle_lt_trans with (eps * Cnorm (f2 (x + h * v)%C - C0))%R.
  apply Rmult_le_compat_r ; [apply Cnorm_pos |].
  left ; apply Hdelta1.
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_l].
  apply Rmult_lt_compat_l ; [assumption |].
  simpl in Hdelta2 ; unfold C_dist in Hdelta2 ; apply Hdelta2.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_r].
  destruct (Hf1 v_neq (Rmin (eps/2)%R ((eps/2) / Cnorm (f2 x)))) as [delta1 Hdelta1].
  apply Rmin_pos ; [lra |].
  apply Rmult_lt_0_compat ; [lra | apply Rinv_0_lt_compat ; apply Cnorm_pos_lt] ;
  assumption.
  assert (Hf2' : differentiable_pt f2 x v).
   exists l2 ; apply Hf2.
  destruct (differentiable_continuous_along_axis f2 x v Hf2' R1 Rlt_0_1)
  as [delta2 Hdelta2].
  pose (delta := Rmin delta1 delta2) ; assert (delta_pos : 0 < delta) by
  (apply Rmin_pos ; [apply delta1 | apply delta2]).
  exists (mkposreal delta delta_pos) ; intros h h_neq h_ub ;
  rewrite Main ; [| apply IRC_neq_0_compat ; assumption] ;
  clear Main ; repeat rewrite l1_eq, f1_eq in * ;
  repeat rewrite Cmult_0_r ; repeat rewrite Cmult_0_l ;
  repeat rewrite Cadd_0_l ; repeat rewrite Cadd_0_r ;
  repeat rewrite Cminus_0_r in *.
  apply Rle_lt_trans with (Cnorm (f1 (x + h * v)%C / (h * v) * f2 x) +
   Cnorm (f1 (x + h * v)%C / (h * v) * (f2 (x + h * v)%C - f2 x)))%R.
  apply Cnorm_triang.
  apply Rlt_trans with (Cnorm (f1 (x + h * v)%C / (h * v) * f2 x) + eps / 2)%R.
  apply Rplus_lt_compat_l.
  rewrite Cnorm_Cmult.
  apply Rle_lt_trans with (Cnorm (f1 (x + h * v)%C / (h * v)))%R.
  rewrite <- Rmult_1_r ; apply Rmult_le_compat_l ; [apply Cnorm_pos |].
  left ; simpl in Hdelta2 ; unfold C_dist in Hdelta2 ; apply Hdelta2.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_r].
  apply Rlt_le_trans with (Rmin (eps / 2) (eps / 2 / Cnorm (f2 x))) ; [| apply Rmin_l].
  apply Rle_lt_trans with (Cnorm ((f1 (x + h * v) - 0) / (h * v) - 0)).
  right ; repeat rewrite Cminus_0_r ; reflexivity.
  apply Hdelta1.
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_l].
  apply Rlt_le_trans with (eps / 2 + eps / 2)%R ; [| right ; field].
  apply Rplus_lt_compat_r.
  apply Rlt_le_trans with ((eps / 2 / Cnorm (f2 x)) * Cnorm (f2 x))%R.
  rewrite Cnorm_Cmult ; apply Rmult_lt_compat_r ; [apply Cnorm_pos_lt ; assumption |].
  apply Rlt_le_trans with (Rmin (eps / 2) (eps / 2 / Cnorm (f2 x))) ; [| apply Rmin_r].
  apply Rle_lt_trans with (Cnorm ((f1 (x + h * v)%C - 0) / (h * v) - 0))%R ;
  [right ; repeat rewrite Cminus_0_r ; reflexivity |] ; apply Hdelta1.
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_l].
  right ; unfold Rdiv ; repeat rewrite Rmult_assoc ; rewrite Rinv_l.
  ring.
  apply Cnorm_no_R0 ; assumption.
  destruct (Ceq_dec (f2 x) 0) as [f2_eq | f2_neq].
  destruct (Hf1 v_neq (eps/2)%R) as [delta1 Hdelta1] ; [lra |].
  destruct (Hf2 v_neq ((eps / 2) / Cnorm (f1 x))%R) as [delta2 Hdelta2].
  apply Rmult_lt_0_compat ; [lra | apply Rinv_0_lt_compat ; apply Cnorm_pos_lt] ;
  assumption.
  assert (Hf2' : differentiable_pt f2 x v).
   exists l2 ; apply Hf2.
  destruct (differentiable_continuous_along_axis f2 x v Hf2' R1 Rlt_0_1)
  as [delta3 Hdelta3].
  pose (delta := Rmin delta1 (Rmin delta2 delta3)) ; assert (delta_pos : 0 < delta) by
  (repeat apply Rmin_pos ; [apply delta1 | apply delta2 | apply delta3]).
  exists (mkposreal delta delta_pos) ; intros h h_neq h_ub ;
  rewrite Main ; [| apply IRC_neq_0_compat ; assumption] ;
  clear Main ; repeat rewrite l1_eq, f2_eq in * ;
  repeat rewrite Cmult_0_r ; repeat rewrite Cmult_0_l ;
  repeat rewrite Cadd_0_l ; repeat rewrite Cadd_0_r ;
  repeat rewrite Cminus_0_r in *.
  apply Rle_lt_trans with (Cnorm ((f1 (x + h * v)%C - f1 x) / (h * v) * f2 (x + h * v)%C) +
   Cnorm (f1 x * (f2 (x + h * v)%C / (h * v) - l2)))%R ; [apply Cnorm_triang |].
  apply Rlt_trans with (eps / 2 + Cnorm (f1 x * (f2 (x + h * v)%C / (h * v) - l2)))%R.
  apply Rplus_lt_compat_r.
  rewrite Cnorm_Cmult ; apply Rle_lt_trans with (eps / 2 * Cnorm (f2 (x + h * v)%C))%R.
  apply Rmult_le_compat_r ; [apply Cnorm_pos |].
  apply Rle_trans with (Cnorm ((f1 (x + h * v)%C - f1 x) / (h * v) - C0))%R ;
  [right ; rewrite Cminus_0_r ; reflexivity | left ; apply Hdelta1].
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_l].
  rewrite <- Rmult_1_r ; apply Rmult_lt_compat_l ; [lra |].
  apply Rle_lt_trans with (dist C_met (f2 (x + h * v)) C0) ; [right ; simpl ; unfold C_dist ;
  rewrite Cminus_0_r ; reflexivity | apply Hdelta3].
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rle_trans with (Rmin delta2 delta3) ;
  [apply Rmin_r | apply Rmin_r]].
  apply Rlt_le_trans with (eps / 2 + eps / 2)%R ; [| right ; field].
  apply Rplus_lt_compat_l ; rewrite Cnorm_Cmult.
  apply Rlt_le_trans with (Cnorm (f1 x) * (/Cnorm (f1 x) * eps / 2))%R.
  apply Rmult_lt_compat_l ; [apply Cnorm_pos_lt ; assumption |].
  apply Rlt_le_trans with (eps / 2 / Cnorm (f1 x))%R ; [| right ; field].
  apply Rle_lt_trans with (Cnorm ((f2 (x + h * v) - 0) / (h * v) - l2)) ; [right ;
  rewrite Cminus_0_r ; reflexivity |] ; apply Hdelta2.
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rle_trans with (Rmin delta2 delta3) ;
  [apply Rmin_r | apply Rmin_l]].
  apply Cnorm_no_R0 ; assumption.
  right ; field ; apply Cnorm_no_R0 ; assumption.
  destruct (Hf1 v_neq (Rmin(eps/3) ((eps/3) / Cnorm (f2 x)))%R) as [delta1 Hdelta1].
  apply Rmin_pos ; [lra |] ; apply Rmult_lt_0_compat ;
  [lra | apply Rinv_0_lt_compat ; apply Cnorm_pos_lt] ; assumption.
  destruct (Hf2 v_neq ((eps / 3) / Cnorm (f1 x))%R) as [delta2 Hdelta2].
  apply Rmult_lt_0_compat ;
  [lra | apply Rinv_0_lt_compat ; apply Cnorm_pos_lt] ; assumption.
  assert (Hf2' : differentiable_pt f2 x v).
   exists l2 ; apply Hf2.
  destruct (differentiable_continuous_along_axis f2 x v Hf2' R1 Rlt_0_1)
  as [delta3 Hdelta3].
  pose (delta := Rmin delta1 (Rmin delta2 delta3)) ; assert (delta_pos : 0 < delta) by
  (repeat apply Rmin_pos ; [apply delta1 | apply delta2 | apply delta3]).
  exists (mkposreal delta delta_pos) ; intros h h_neq h_ub ;
  rewrite Main ; [| apply IRC_neq_0_compat ; assumption] ;
  clear Main ; repeat rewrite l1_eq in * ;
  repeat rewrite Cmult_0_r ; repeat rewrite Cmult_0_l ;
  repeat rewrite Cadd_0_l ; repeat rewrite Cadd_0_r ;
  repeat rewrite Cminus_0_r in *.
  apply Rlt_le_trans with (eps/3 + eps/3 + eps/3)%R ; [| right ; field].
  apply Rle_lt_trans with (Cnorm ((f1 (x + h * v)%C - f1 x) / (h * v) * f2 x +
   (f1 (x + h * v)%C - f1 x) / (h * v) * (f2 (x + h * v)%C - f2 x)) +
   Cnorm (f1 x * ((f2 (x + h * v)%C - f2 x) / (h * v) - l2)))%R ; [apply Cnorm_triang |].
  apply Rlt_trans with (Cnorm ((f1 (x + h * v)%C - f1 x) / (h * v) * f2 x +
   (f1 (x + h * v)%C - f1 x) / (h * v) * (f2 (x + h * v)%C - f2 x)) + eps / 3)%R.
  apply Rplus_lt_compat_l.
  rewrite Cnorm_Cmult ; apply Rlt_le_trans with (Cnorm (f1 x) * (eps / 3 / Cnorm (f1 x)))%R.
  apply Rmult_lt_compat_l ; [apply Cnorm_pos_lt ; assumption |].
  apply Hdelta2.
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rle_trans with (Rmin delta2 delta3) ;
  [apply Rmin_r | apply Rmin_l]].
  right ; field ; apply Cnorm_no_R0 ; assumption.
  apply Rplus_lt_compat_r.
  apply Rle_lt_trans with (Cnorm ((f1 (x + h * v)%C - f1 x) / (h * v) * f2 x) +
   Cnorm ((f1 (x + h * v)%C - f1 x) / (h * v) * (f2 (x + h * v)%C - f2 x)))%R ;
  [apply Cnorm_triang |].
 apply Rlt_trans with (Cnorm ((f1 (x + h * v)%C - f1 x) / (h * v) * f2 x) + eps / 3)%R.
 apply Rplus_lt_compat_l.
 rewrite Cnorm_Cmult ; apply Rle_lt_trans with (eps / 3 * Cnorm (f2 (x + h * v)%C - f2 x))%R.
 apply Rmult_le_compat_r ; [apply Cnorm_pos |].
 apply Rle_trans with (Rmin (eps / 3) (eps / 3 / Cnorm (f2 x))) ; [| apply Rmin_l].
 apply Rle_trans with (Cnorm ((f1 (x + h * v)%C - f1 x) / (h * v) - 0))%R ;
 [right ; rewrite Cminus_0_r ; reflexivity |] ; left ; apply Hdelta1.
 assumption.
 apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_l].
 rewrite <- Rmult_1_r ; apply Rmult_lt_compat_l ; [lra |] ;
 simpl in Hdelta3 ; unfold C_dist in Hdelta3 ; apply Hdelta3.
 apply Rlt_le_trans with delta ; [apply h_ub | apply Rle_trans with (Rmin delta2 delta3) ;
 apply Rmin_r].
 apply Rplus_lt_compat_r ; rewrite Cnorm_Cmult.
 apply Rlt_le_trans with ((eps / 3 / Cnorm (f2 x)) * Cnorm (f2 x))%R.
 apply Rmult_lt_compat_r ; [apply Cnorm_pos_lt ; assumption |].
 apply Rlt_le_trans with (Rmin (eps / 3) (eps / 3 / Cnorm (f2 x))) ; [| apply Rmin_r].
 apply Rle_lt_trans with (Cnorm ((f1 (x + h * v) - f1 x) / (h * v) - 0)) ; [right ;
 rewrite Cminus_0_r ; reflexivity |].
 apply Hdelta1.
 assumption.
 apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_l].
 right ; field ; apply Cnorm_no_R0 ; assumption.
  destruct (Ceq_dec (f1 x) 0) as [f1_eq | f1_neq].
  destruct (Ceq_dec (f2 x) 0) as [f2_eq | f2_neq].
  destruct (Hf1 v_neq (eps / 2)%R) as [delta1 Hdelta1] ; [lra |].
  assert (Hf2' : differentiable_pt f2 x v).
   exists l2 ; apply Hf2.
  destruct (differentiable_continuous_along_axis f2 x v Hf2'
  (Rmin R1 ((eps / 2) / Cnorm l1))) as [delta2 Hdelta2].
  apply Rmin_pos ; [lra |].
  apply Rmult_lt_0_compat ; [lra | apply Rinv_0_lt_compat ;
  apply Cnorm_pos_lt ; assumption].
  pose (delta := Rmin delta1 delta2) ; assert (delta_pos : 0 < delta) by
  (apply Rmin_pos ; [apply delta1 | apply delta2]) ; exists (mkposreal delta
  delta_pos) ; intros h h_neq h_ub ;
  rewrite Main ; [| apply IRC_neq_0_compat ; assumption] ;
  clear Main ; repeat rewrite f1_eq, f2_eq in * ;
  repeat rewrite Cmult_0_r ; repeat rewrite Cmult_0_l ;
  repeat rewrite Cadd_0_l ; repeat rewrite Cadd_0_r ;
  repeat rewrite Cminus_0_r in *.
  apply Rle_lt_trans with (Cnorm ((f1 (x + h * v)%C / (h * v) - l1) * f2 (x + h * v)%C) +
  Cnorm (l1 * f2 (x + h * v)%C))%R ; [apply Cnorm_triang |].
  apply Rlt_le_trans with (eps / 2 +  eps / 2)%R ; [| right ; field].
  apply Rle_lt_trans with (Cnorm ((f1 (x + h * v)%C / (h * v) - l1) *
  f2 (x + h * v)%C) + eps / 2)%R.
  apply Rplus_le_compat_l.
  rewrite Cnorm_Cmult ; apply Rle_trans with (Cnorm l1 * ((eps / 2) / Cnorm l1))%R.
  apply Rmult_le_compat_l ; [apply Cnorm_pos |].
  apply Rle_trans with (Rmin 1 (eps / 2 / Cnorm l1)) ; [| apply Rmin_r].
  apply Rle_trans with (dist C_met (f2 (x + h * v)) C0) ; [simpl ; unfold C_dist ; right ;
  rewrite Cminus_0_r ; reflexivity | left ; apply Hdelta2].
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_r].
  right ; field ; apply Cnorm_no_R0 ; assumption.
  apply Rplus_lt_compat_r ; rewrite Cnorm_Cmult ; apply Rle_lt_trans with
  (eps / 2 * Cnorm (f2 (x + h * v)%C))%R.
  apply Rmult_le_compat_r ; [apply Cnorm_pos |].
  apply Rle_trans with (Cnorm ((f1 (x + h * v) - 0) / (h * v) - l1)) ; [rewrite Cminus_0_r ;
  right ; reflexivity | left ; apply Hdelta1].
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_l].
  rewrite <- Rmult_1_r ; apply Rmult_lt_compat_l ; [lra |].
  apply Rle_lt_trans with (dist C_met (f2 (x + h * v)) C0) ; [simpl ; unfold C_dist ;
  rewrite Cminus_0_r ; right ; reflexivity |].
  apply Rlt_le_trans with (Rmin 1 (eps / 2 / Cnorm l1)) ; [apply Hdelta2 |
  apply Rmin_l].
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_r].
  destruct (Hf1 v_neq (Rmin (eps / 3) (eps / 3 / Cnorm (f2 x)))) as [delta1 Hdelta1].
  apply Rmin_pos ; [lra |] ; apply Rmult_lt_0_compat ;
  [lra | apply Rinv_0_lt_compat ; apply Cnorm_pos_lt] ; assumption.
  assert (Hf2' : differentiable_pt f2 x v).
   exists l2 ; apply Hf2.
  destruct (differentiable_continuous_along_axis f2 x v Hf2' (Rmin 1 (eps / 3 / Cnorm l1)))
  as [delta2 Hdelta2].
  apply Rmin_pos ; [apply Rlt_0_1 | apply Rmult_lt_0_compat ;
  [lra | apply Rinv_0_lt_compat ; apply Cnorm_pos_lt] ; assumption].
  pose (delta := Rmin delta1 delta2) ; assert (delta_pos : 0 < delta) by
  (apply Rmin_pos ; [apply delta1 | apply delta2]) ;
  exists (mkposreal delta delta_pos) ; intros h h_neq h_ub ;
  rewrite Main ; [| apply IRC_neq_0_compat ; assumption] ;
  clear Main ; repeat rewrite f1_eq in * ;
  repeat rewrite Cmult_0_r ; repeat rewrite Cmult_0_l ;
  repeat rewrite Cadd_0_l ; repeat rewrite Cadd_0_r ;
  repeat rewrite Cminus_0_r in *.
  apply Rle_lt_trans with (Cnorm ((f1 (x + h * v)%C / (h * v) - l1) * f2 x) +
   Cnorm ((f1 (x + h * v)%C / (h * v) - l1) * (f2 (x + h * v)%C - f2 x) +
   l1 * (f2 (x + h * v)%C - f2 x)))%R ; [rewrite Cadd_assoc ; apply Cnorm_triang |].
  apply Rle_lt_trans with (Cnorm ((f1 (x + h * v)%C / (h * v) - l1) * f2 x) +
   Cnorm ((f1 (x + h * v)%C / (h * v) - l1) * (f2 (x + h * v)%C - f2 x)) +
   Cnorm (l1 * (f2 (x + h * v)%C - f2 x)))%R.
  rewrite Rplus_assoc ; apply Rplus_le_compat_l ; apply Cnorm_triang.
  apply Rlt_trans with (eps/3 + Cnorm ((f1 (x + h * v)%C / (h * v) - l1) *
  (f2 (x + h * v)%C - f2 x)) + Cnorm (l1 * (f2 (x + h * v)%C - f2 x)))%R.
  repeat apply Rplus_lt_compat_r ; rewrite Cnorm_Cmult ;
  apply Rlt_le_trans with ((eps / 3 / Cnorm (f2 x)) * Cnorm (f2 x))%R.
  apply Rmult_lt_compat_r ; [apply Cnorm_pos_lt ; assumption |].
  apply Rlt_le_trans with (Rmin (eps / 3) (eps / 3 / Cnorm (f2 x))) ;
  [| apply Rmin_r].
  apply Rle_lt_trans with (Cnorm ((f1 (x + h * v) - 0) / (h * v) - l1)) ;
  [rewrite Cminus_0_r ; right ; reflexivity | apply Hdelta1].
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_l].
  right ; field ; apply Cnorm_no_R0 ; assumption.
  apply Rlt_trans with (eps / 3 + eps / 3 + Cnorm (l1 * (f2 (x + h * v)%C - f2 x)))%R ;
  [apply Rplus_lt_compat_r ; apply Rplus_lt_compat_l |].
  rewrite Cnorm_Cmult ; apply Rle_lt_trans with
  (eps / 3 * Cnorm ((f2 (x + h * v)%C - f2 x)))%R ; [apply Rmult_le_compat_r ;
  [apply Cnorm_pos |]|].
  apply Rle_trans with (Rmin (eps / 3) (eps / 3 / Cnorm (f2 x))) ; [| apply Rmin_l] ;
  apply Rle_trans with (Cnorm ((f1 (x + h * v)%C - C0) / (h * v) - l1))%R ; [right ;
  rewrite Cminus_0_r ; reflexivity | left ; apply Hdelta1].
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_l].
  rewrite <- Rmult_1_r ; apply Rmult_lt_compat_l ; [lra |].
  apply Rle_lt_trans with (dist C_met (f2 (x + h * v)) (f2 x)) ; [right ;
  simpl ; unfold C_dist ; reflexivity |].
  apply Rlt_le_trans with (Rmin 1 (eps / 3 / Cnorm l1)) ; [apply Hdelta2 | apply Rmin_l].
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_r].
  apply Rlt_le_trans with (eps / 3 + eps / 3 + eps / 3)%R ; [apply Rplus_lt_compat_l |
  right ; field].
  rewrite Cnorm_Cmult ; apply Rlt_le_trans with (Cnorm l1 * (eps / 3 / Cnorm l1))%R.
  apply Rmult_lt_compat_l ; [apply Cnorm_pos_lt ; assumption |].
  apply Rle_lt_trans with (dist C_met (f2 (x + h * v)) (f2 x)) ; [simpl ; unfold C_dist ;
  right ; reflexivity | apply Rlt_le_trans with (Rmin 1 (eps / 3 / Cnorm l1)) ;
  [apply Hdelta2 | apply Rmin_r]].
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_r].
  right ; field ; apply Cnorm_no_R0 ; assumption.
  destruct (Ceq_dec (f2 x) 0) as [f2_eq | f2_neq].
  destruct (Hf1 v_neq (eps / 3)%R) as [delta1 Hdelta1] ; [lra |].
  destruct (Hf2 v_neq (eps / 3 / Cnorm (f1 x))%R) as [delta2 Hdelta2].
  apply Rmult_lt_0_compat ; [lra | apply Rinv_0_lt_compat ;
  apply Cnorm_pos_lt] ; assumption.
  assert (Hf2' : differentiable_pt f2 x v).
   exists l2 ; apply Hf2.
  destruct (differentiable_continuous_along_axis f2 x v Hf2' (Rmin 1 (eps / 3 / Cnorm l1)))
  as [delta3 Hdelta3].
  apply Rmin_pos ; [apply Rlt_0_1 |] ; apply Rmult_lt_0_compat ;
  [lra | apply Rinv_0_lt_compat ; apply Cnorm_pos_lt] ; assumption.
  pose (delta := Rmin delta1 (Rmin delta2 delta3)) ; assert (delta_pos : 0 < delta) by
  (repeat apply Rmin_pos ; [apply delta1 | apply delta2 | apply delta3]) ;
  exists (mkposreal delta delta_pos) ; intros h h_neq h_ub ;
  rewrite Main ; [| apply IRC_neq_0_compat ; assumption] ;
  clear Main ; repeat rewrite f2_eq in * ;
  repeat rewrite Cmult_0_r ; repeat rewrite Cmult_0_l ;
  repeat rewrite Cadd_0_l ; repeat rewrite Cadd_0_r ;
  repeat rewrite Cminus_0_r in *.
  apply Rle_lt_trans with (Cnorm (((f1 (x + h * v)%C - f1 x) / (h * v) - l1) * f2 (x + h * v)%C +
   l1 * f2 (x + h * v)%C) + Cnorm (f1 x * (f2 (x + h * v)%C / (h * v) - l2)))%R ;
   [apply Cnorm_triang |] ; apply Rle_lt_trans with (Cnorm
   (((f1 (x + h * v)%C - f1 x) / (h * v) - l1) * f2 (x + h * v)%C) +
   Cnorm (l1 * f2 (x + h * v)%C) + Cnorm (f1 x * (f2 (x + h * v)%C / (h * v) - l2)))%R ;
   [apply Rplus_le_compat_r ; apply Cnorm_triang |].
  apply Rle_lt_trans with (eps / 3 + Cnorm (l1 * f2 (x + h * v)%C) +
  Cnorm (f1 x * (f2 (x + h * v)%C / (h * v) - l2)))%R ; [repeat apply Rplus_le_compat_r |].
  rewrite Cnorm_Cmult ; apply Rle_trans with (eps / 3 * Cnorm (f2 (x + h * v)%C))%R ;
  [apply Rmult_le_compat_r ; [apply Cnorm_pos | left ; apply Hdelta1] |].
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_l].
  rewrite <- Rmult_1_r ; apply Rmult_le_compat_l ; [lra |] ;
  apply Rle_trans with (dist C_met (f2 (x + h * v)) C0) ; [simpl ; unfold C_dist ; rewrite
  Cminus_0_r ; right ; reflexivity |] ; apply Rle_trans with (Rmin 1 (eps / 3 / Cnorm l1)) ;
  [left ; apply Hdelta3 | apply Rmin_l].
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rle_trans with (Rmin delta2 delta3) ;
  apply Rmin_r].
  apply Rle_lt_trans with (eps / 3 + eps / 3 +
  Cnorm (f1 x * (f2 (x + h * v)%C / (h * v) - l2)))%R ;
  [apply Rplus_le_compat_r ; apply Rplus_le_compat_l |].
  rewrite Cnorm_Cmult ; apply Rle_trans with (Cnorm l1 * (eps / 3 / Cnorm l1))%R ;
  [apply Rmult_le_compat_l ; [apply Cnorm_pos|] |].
  apply Rle_trans with (dist C_met (f2 (x + h * v)) C0) ; [simpl ; unfold C_dist ; rewrite
  Cminus_0_r ; right ; reflexivity |] ; apply Rle_trans with (Rmin 1 (eps / 3 / Cnorm l1)) ;
  [left ; apply Hdelta3 | apply Rmin_r].
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rle_trans with (Rmin delta2 delta3) ;
  apply Rmin_r].
  right ; field ; apply Cnorm_no_R0 ; assumption.
  apply Rlt_le_trans with (eps / 3 + eps / 3 + eps /3)%R ; [repeat rewrite Rplus_assoc ;
  repeat apply Rplus_lt_compat_l | right ; field].
  rewrite Cnorm_Cmult ; apply Rlt_le_trans with (Cnorm (f1 x) * (eps / 3 / Cnorm (f1 x)))%R.
  apply Rmult_lt_compat_l ; [apply Cnorm_pos_lt ; assumption |].
  apply Rle_lt_trans with (Cnorm ((f2 (x + h * v)%C - 0) / (h * v) - l2))%R ;
  [rewrite Cminus_0_r ; right ; reflexivity | apply Hdelta2].
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rle_trans with (Rmin delta2 delta3) ;
  [apply Rmin_r | apply Rmin_l]].
  right ; field ; apply Cnorm_no_R0 ; assumption.
  destruct (Hf1 v_neq (Rmin (eps / 4) (eps / 4 / Cnorm (f2 x)))) as [delta1 Hdelta1].
  apply Rmin_pos ; [lra |] ; apply Rmult_lt_0_compat ; [lra | apply Rinv_0_lt_compat ;
  apply Cnorm_pos_lt] ; assumption.
  destruct (Hf2 v_neq (eps / 4 / Cnorm (f1 x))%R) as [delta2 Hdelta2].
  apply Rmult_lt_0_compat ; [lra | apply Rinv_0_lt_compat ;
  apply Cnorm_pos_lt] ; assumption.
  assert (Hf2' : differentiable_pt f2 x v).
   exists l2 ; apply Hf2.
  destruct (differentiable_continuous_along_axis f2 x v Hf2' (Rmin 1 (eps / 4 / Cnorm l1)))
  as [delta3 Hdelta3].
  apply Rmin_pos ; [apply Rlt_0_1 |] ; apply Rmult_lt_0_compat ;
  [lra | apply Rinv_0_lt_compat ; apply Cnorm_pos_lt] ; assumption.
  pose (delta := Rmin delta1 (Rmin delta2 delta3)) ; assert (delta_pos : 0 < delta) by
  (repeat apply Rmin_pos ; [apply delta1 | apply delta2 | apply delta3]) ;
  exists (mkposreal delta delta_pos) ; intros h h_neq h_ub ;
  rewrite Main ; [| apply IRC_neq_0_compat ; assumption] ;
  clear Main.
  apply Rle_lt_trans with (Cnorm (((f1 (x + h * v)%C - f1 x) / (h * v) - l1) * f2 x +
   ((f1 (x + h * v)%C - f1 x) / (h * v) - l1) * (f2 (x + h * v)%C - f2 x) +
   l1 * (f2 (x + h * v)%C - f2 x)) + Cnorm (f1 x * ((f2 (x + h * v)%C - f2 x) / (h * v) - l2)))%R ;
  [apply Cnorm_triang |].
  apply Rle_lt_trans with (Cnorm (((f1 (x + h * v)%C - f1 x) / (h * v) - l1) * f2 x +
   ((f1 (x + h * v)%C - f1 x) / (h * v) - l1) * (f2 (x + h * v)%C - f2 x)) + Cnorm (
   l1 * (f2 (x + h * v)%C - f2 x)) + Cnorm (f1 x * ((f2 (x + h * v)%C - f2 x) / (h * v) - l2)))%R ;
  [apply Rplus_le_compat_r ; apply Cnorm_triang |].
  apply Rle_lt_trans with (Cnorm (((f1 (x + h * v)%C - f1 x) / (h * v) - l1) * f2 x) +
   Cnorm (((f1 (x + h * v)%C - f1 x) / (h * v) - l1) * (f2 (x + h * v)%C - f2 x)) + Cnorm (
   l1 * (f2 (x + h * v)%C - f2 x)) + Cnorm (f1 x * ((f2 (x + h * v)%C - f2 x) / (h * v) - l2)))%R ;
  [repeat apply Rplus_le_compat_r ; apply Cnorm_triang |].
  apply Rle_lt_trans with (eps / 4 +
  Cnorm (((f1 (x + h * v)%C - f1 x) / (h * v) - l1) * (f2 (x + h * v)%C - f2 x)) +
  Cnorm (l1 * (f2 (x + h * v)%C - f2 x)) +
  Cnorm (f1 x * ((f2 (x + h * v)%C - f2 x) / (h * v) - l2)))%R ;
  [repeat apply Rplus_le_compat_r |].
  rewrite Cnorm_Cmult ; apply Rle_trans with ((eps / 4 / Cnorm (f2 x)) * Cnorm (f2 x))%R ;
  [apply Rmult_le_compat_r ; [apply Cnorm_pos |] |].
  apply Rle_trans with (Rmin (eps / 4) (eps / 4 / Cnorm (f2 x))) ; [left ; apply Hdelta1 |
  apply Rmin_r].
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_l].
  right ; field ; apply Cnorm_no_R0 ; assumption.
  apply Rle_lt_trans with (eps / 4 + eps / 4 + Cnorm (l1 * (f2 (x + h * v)%C - f2 x)) +
  Cnorm (f1 x * ((f2 (x + h * v)%C - f2 x) / (h * v) - l2)))%R ;
  [repeat apply Rplus_le_compat_r ; apply Rplus_le_compat_l |].
  rewrite Cnorm_Cmult ; apply Rle_trans with (eps / 4 *
  Cnorm ((f2 (x + h * v)%C - f2 x)))%R ; [apply Rmult_le_compat_r ;
  [apply Cnorm_pos |] |].
  apply Rle_trans with (Rmin (eps / 4) (eps / 4 / Cnorm (f2 x))) ; [left ;
  apply Hdelta1 | apply Rmin_l].
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rmin_l].
  rewrite <- Rmult_1_r ; apply Rmult_le_compat_l ; [lra |] ;
  apply Rle_trans with (Rmin 1 (eps / 4 / Cnorm l1)) ; [| apply Rmin_l].
  apply Rle_trans with (dist C_met (f2 (x + h * v)) (f2 x)) ; [simpl ; unfold C_dist ;
  right ; reflexivity | left ; apply Hdelta3].
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rle_trans with
  (Rmin delta2 delta3) ; apply Rmin_r].
  apply Rle_lt_trans with (eps / 4 + eps / 4 + eps / 4 +
  Cnorm (f1 x * ((f2 (x + h * v)%C - f2 x) / (h * v) - l2)))%R ;
  [repeat apply Rplus_le_compat_r ; apply Rplus_le_compat_l |].
  rewrite Cnorm_Cmult ; apply Rle_trans with (Cnorm l1 * (eps / 4 / Cnorm l1))%R ;
  [apply Rmult_le_compat_l ; [apply Cnorm_pos |] | right ; field ;
  apply Cnorm_no_R0 ; assumption].
  apply Rle_trans with (Rmin 1 (eps / 4 / Cnorm l1)) ; [| apply Rmin_r].
  apply Rle_trans with (dist C_met (f2 (x + h * v)) (f2 x)) ; [simpl ;
  unfold C_dist ; right ; reflexivity | left ; apply Hdelta3].
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rle_trans with
  (Rmin delta2 delta3) ; apply Rmin_r].
  apply Rlt_le_trans with (eps / 4 + eps / 4 + eps / 4 + eps / 4)%R ; [| right ; field].
  apply Rplus_lt_compat_l.
  rewrite Cnorm_Cmult ; apply Rlt_le_trans with (Cnorm (f1 x) *
  (eps / 4 / Cnorm (f1 x)))%R ; [apply Rmult_lt_compat_l  ; [apply Cnorm_pos_lt ;
  assumption |] | right ; field ; apply Cnorm_no_R0 ; assumption] ;
  apply Hdelta2.
  assumption.
  apply Rlt_le_trans with delta ; [apply h_ub | apply Rle_trans with
  (Rmin delta2 delta3) ; [apply Rmin_r | apply Rmin_l]].
Qed.

Lemma differentiable_pt_lim_scal : forall f a x v l, v <> C0 ->
    differentiable_pt_lim f x v l -> differentiable_pt_lim (fun x => a * f x) x v (a * l).
Proof.
  intros f a x v l v_neq f_diff.
  assert (H0 := differentiable_pt_lim_const a x v).
  replace (mult_real_fct a f) with (fct_cte a * f)%F.
  replace (a * l) with (C0 * f x + a * l); [ idtac | ring ].
  apply (differentiable_pt_lim_mult (fct_cte a) f x v 0 l) ; assumption.
  unfold mult_real_fct, mult_fct, fct_cte in |- *; reflexivity.
Qed.

Lemma differentiable_pt_lim_id : forall x v, differentiable_pt_lim id x v C1.
Proof.
  intros x v v_neq ; unfold differentiable_pt_lim in |- *.
  intros eps Heps; exists (mkposreal eps Heps); intros h H1 H2;
    unfold id in |- *; replace ((x + h * v - x) / (h * v) - C1) with C0.
    rewrite Cnorm_C0 ; assumption.
    replace (x + h * v - x) with (h * v) by ring.
  replace (h *v / (h *v)) with C1.
  unfold Cminus ; rewrite Cadd_opp_r ; reflexivity.
  unfold Cdiv ; rewrite Cinv_r ; trivial.
  apply Cmult_integral_contrapositive_currified ; [apply IRC_neq_0_compat |] ;
  assumption.
Qed.
