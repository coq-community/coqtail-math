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

Require Import MyRIneq.
Require Import Rinterval Ranalysis_def Ranalysis_def_simpl Ranalysis_continuity.
Require Import Ranalysis_derivability Ranalysis_usual Ranalysis_facts Ranalysis_MVT.
Require Import Canalysis_diff.
Require Import Cprop_base.
Require Import Cnorm.
Require Import Ctacfield.
Require Import Cmet.
Require Import Canalysis_def.
Require Import Cderiv.

Open Scope C_scope.

(**********)
Lemma uniqueness_step1 : forall f x l1 l2,
    limit1_in (fun h => (f (x + h) - f x) / h) (fun h => h <> 0) l1 0 ->
    limit1_in (fun h => (f (x + h) - f x) / h) (fun h => h <> 0) l2 0 ->
    l1 = l2.
Proof.
intros f x l1 l2 Hl1 Hl2 ;
 apply (single_limit (fun h => (f (x + h) - f x) / h) (fun h => h <> 0) l1 l2 0);
 try assumption.
 intros alpha alpha_pos ; exists (IRC (alpha / 2)) ; split.
 apply (proj2 (C0_neq_R0_neq _)) ; left ; simpl ; apply Rgt_not_eq ; lra.
 unfold C_dist ; rewrite Cminus_0_r ; rewrite Cnorm_IRC_Rabs ;
 rewrite Rabs_right ; lra.
Qed.

Lemma uniqueness_step2 : forall f x l,
    derivable_pt_lim f x l ->
    limit1_in (fun h => (f (x + h) - f x) / h) (fun h : C => h <> C0) l C0.
Proof. 
unfold derivable_pt_lim, limit1_in, limit_in.
intros f x l Hf_deriv eps eps_pos ; destruct (Hf_deriv eps eps_pos)
 as ([alpha alpha_pos], Halpha) ; clear Hf_deriv ; exists alpha ; split ;
 [assumption |] ; intros h [h_neq Hh] ; simpl in * ; unfold C_dist in Hh ;
 rewrite Cminus_0_r in Hh. unfold C_dist. apply Halpha ; intuition.
Qed.

Lemma uniqueness_step3 : forall f x l,
    limit1_in (fun h => (f (x + h) - f x) / h) (fun h => h <> 0) l 0 ->
    derivable_pt_lim f x l.
Proof.
unfold limit1_in, derivable_pt_lim, limit_in, C_dist ; simpl ; unfold C_dist ;
intros f x l Hf_lim eps eps_pos ; destruct (Hf_lim eps eps_pos) as
 (alpha, [alpha_pos Halpha]) ; clear Hf_lim ;
 exists (mkposreal alpha alpha_pos) ; intros h h_neq Hyp ;
 apply Halpha ; rewrite Cminus_0_r ; split ; assumption.
Qed.

Lemma uniqueness_limite : forall f x l1 l2,
    derivable_pt_lim f x l1 -> derivable_pt_lim f x l2 -> l1 = l2.
Proof.
intros f x l1 l2 Hf_deriv1 Hf_deriv2 ;
 assert (H1 := uniqueness_step2 _ _ _ Hf_deriv1) ;
 assert (H2 := uniqueness_step2 _ _ _ Hf_deriv2) ;
 apply uniqueness_step1 with f x ; assumption.
Qed.

Lemma derive_pt_eq : forall f x l (pr:derivable_pt f x),
    derive_pt f x pr = l <-> derivable_pt_lim f x l.
Proof.
intros f x l pr ; split ; intro Hf_deriv.
 assert (H := proj2_sig pr) ; unfold derive_pt in Hf_deriv ;
 rewrite Hf_deriv in H ; assumption.
 assert (H := proj2_sig pr) ; unfold derivable_pt_abs in H ;
 assert (H' := uniqueness_limite _ _ _ _ Hf_deriv H) ;
 symmetry ; assumption.
Qed.

(**********)
Lemma derive_pt_eq_0 : forall f x l (pr:derivable_pt f x),
    derivable_pt_lim f x l -> derive_pt f x pr = l.
Proof.
intros f x l pr ; destruct (derive_pt_eq f x l pr) ; assumption.
Qed.

(**********)
Lemma derive_pt_eq_1 : forall f x l (pr:derivable_pt f x),
    derive_pt f x pr = l -> derivable_pt_lim f x l.
Proof.
intros f x l pr ; destruct (derive_pt_eq f x l pr) ; assumption.
Qed.

(**********************************************************************)
(** * Equivalence of this definition with the one using limit concept *)
(**********************************************************************)
Lemma derive_pt_D_in : forall (f df:C -> C) (x:C) (pr:derivable_pt f x),
    D_in f df no_cond x <-> derive_pt f x pr = df x.
Proof.
intros f df x pr ; split.
 unfold D_in, limit1_in, limit_in ; simpl ; unfold C_dist ; intros.
 apply derive_pt_eq_0.
 intros eps eps_pos ; destruct (H eps eps_pos) as [alpha [alpha_pos Halpha]] ;
 exists (mkposreal alpha alpha_pos) ; intros h h_neq h_bd.
 fold C in h ; assert (Hrew : h = (x + h) - x) by ring ; rewrite Hrew at 2.
 apply Halpha ; split.
 unfold D_x, no_cond ; split ; [trivial |].
 intro Hf ; apply h_neq ; clear -Hf.
 apply Cadd_eq_reg_l with x ; rewrite Cadd_0_r ; symmetry ; assumption.
 rewrite <- Hrew ; assumption.
intro H.
 assert (H0 := derive_pt_eq_1 f x (df x) pr H).
 intros eps eps_pos.
 destruct (H0 eps eps_pos) as [alpha Halpha] ; exists alpha ; split.
 exact (cond_pos alpha).
  intros a [Ha a_bd] ; unfold D_x in Ha ; destruct Ha as [_ Ha] ;
  assert (Temp : a - x <> 0) by (auto with complex).
  generalize (Halpha (a - x) Temp a_bd); replace (x + (a - x)) with a.
  intro; assumption.
  auto with complex.
Qed.

Lemma derivable_pt_lim_D_in : forall f (df:C -> C) (x:C),
    D_in f df no_cond x <-> derivable_pt_lim f x (df x).
Proof.
intros f df x ; split.
 unfold D_in, limit1_in, limit_in ; simpl ; unfold C_dist ; intros H eps eps_pos.
 destruct (H eps eps_pos) as [alpha [alpha_pos Halpha]].
 exists (mkposreal alpha alpha_pos) ; intros h h_neq h_bd ; fold C in h ;
 assert (Hrew : h = (x + h) - x) by ring ; rewrite Hrew at 2 ;
 apply Halpha ; unfold D_x, no_cond ; repeat split.
  intro Hf ; apply h_neq ; clear -Hf.
 apply Cadd_eq_reg_l with x ; rewrite Cadd_0_r ; symmetry ; assumption.
 rewrite <- Hrew ; assumption.
 intro.
  unfold derivable_pt_lim in H.
  unfold D_in in |- *; unfold limit1_in in |- *; unfold limit_in in |- *;
    unfold dist in |- *; simpl in |- *; unfold R_dist in |- *; 
      intros.
  elim (H eps H0); intros alpha H2; exists (pos alpha); split.
  apply (cond_pos alpha).
  intros.
  elim H1; intros; unfold D_x in H3; elim H3; intros; cut (x0 - x <> 0).
  intro; generalize (H2 (x0 - x) H7 H4); replace (x + (x0 - x)) with x0.
  intro; assumption.
  ring.
  auto with complex.
Qed.

(***********************************)
(** * derivability -> continuity   *)
(***********************************)
(**********)
Lemma derivable_derive : forall f x (pr:derivable_pt f x),
 exists l, derive_pt f x pr = l.
Proof.
intros f x pr ; exists (proj1_sig pr) ; reflexivity.
Qed.

Theorem derivable_continuous_pt : forall f x,
 derivable_pt f x -> continuity_pt f x.
Proof.
intros f x Hf_deriv eps eps_pos ; destruct Hf_deriv as (l, Hl).
 case (Ceq_or_neq_C0 l) ; intro Hl_0.
  assert (eps_2_pos : eps / 2 > 0) by lra ;
  destruct (Hl (eps / 2)%R eps_2_pos) as ([alpha alpha_pos], Halpha) ;
  exists (Rmin (1/2) alpha) ; split ; [apply Rmin_pos ; lra|] ;
  intros x' [_ x'_bd] ; simpl ; simpl in Halpha ; unfold C_dist in *.
  pose (h := x' - x) ; replace x' with (x + h) by (unfold h ; intuition).
   case (Ceq_or_neq_C0 h) ; intro Hh_0.
   rewrite Hh_0, Cadd_0_r, Cminus_diag_eq ; [| reflexivity] ;
   rewrite Cnorm_C0 ; assumption.
   apply Rlt_trans with (Cnorm h*eps)%R.
   apply Rle_lt_trans with (Cnorm (f (x + h)%C - f x) * (/ Cnorm h * Cnorm h))%R.
   right ; field ; apply Rgt_not_eq ; apply Cnorm_pos_lt ; assumption.
   unfold Rdiv ; rewrite  <- Rmult_assoc ; rewrite <- Cnorm_inv, <- Cnorm_Cmult.
   rewrite Rmult_comm ; apply Rmult_lt_compat_l.
   apply Cnorm_pos_lt ; assumption.
   replace ((f (x + h) - f x) * / h) with ((f (x + h) - f x) / h - l). 
   apply Rlt_trans with (eps / 2)%R ; [apply Halpha ; intuition | lra].
   subst ; apply Rlt_le_trans with (Rmin (1/2) alpha) ; [apply x'_bd | apply Rmin_r].
   rewrite Hl_0. rewrite Cminus_0_r. auto. assumption.
   apply Rlt_trans with ((Rmin (1/2) alpha) * eps)%R.
   apply Rmult_lt_compat_r ; assumption.
   apply Rle_lt_trans with (eps / 2)%R.
   unfold Rdiv ; rewrite Rmult_comm ; apply Rmult_le_compat_l ; intuition ;
   apply Rle_trans with (1 * /2)%R ; [apply Rmin_l | right ; field].
   lra.
   assert (eps_2_pos : eps / 2 > 0) by lra ; 
   destruct (Hl (eps / 2)%R eps_2_pos) as ([alpha alpha_pos], Halpha).
   exists (Rmin (eps / (2 * Cnorm l)) (Rmin (1/2) alpha)) ; split ; [apply Rmin_pos |].
  unfold Rdiv ; rewrite Rinv_mult_distr ; repeat apply Rmult_lt_0_compat.
  assumption.
  lra.
  apply Rinv_0_lt_compat ; apply Cnorm_pos_lt ; assumption.
  apply Rgt_not_eq ; lra.
  apply Rgt_not_eq ; apply Cnorm_pos_lt ; assumption.
  apply Rmin_pos ; lra.
 intros x' [_ x'_bd] ; simpl ; unfold C_dist.
  pose (h := x' - x) ; replace x' with (x+h) by (unfold h ; intuition) ;
  case (Ceq_or_neq_C0 h) ; intro Hh_0.
  rewrite Hh_0, Cadd_0_r, Cminus_diag_eq ; [| reflexivity] ;
  rewrite Cnorm_C0 ; assumption.
  apply Rlt_trans with (Cnorm h * eps + Cnorm h * Cnorm l )%R.
  apply Rle_lt_trans with (Cnorm (f (x + h)%C - f x) * (/ Cnorm h * Cnorm h))%R.
   right ; field ; apply Rgt_not_eq ; apply Cnorm_pos_lt ; assumption.
   unfold Rdiv ; rewrite  <- Rmult_assoc ; rewrite <- Cnorm_inv, <- Cnorm_Cmult.
   apply Rle_lt_trans with ((Cnorm ((f (x + h)%C - f x) * / h) + (- Cnorm l + Cnorm l)) * Cnorm h)%R.
   right ; field.
   repeat rewrite Rmult_plus_distr_r.
   replace (Cnorm l * Cnorm h)%R with (Cnorm h * Cnorm l)%R by (apply Rmult_comm).
   rewrite <- Rplus_assoc ; apply Rplus_lt_compat_r.
   apply Rle_lt_trans with (Cnorm ((f (x +h)%C - f x) / h - l)* Cnorm h)%R.
   rewrite <- Rmult_plus_distr_r ; apply Rmult_le_compat_r ;
   [apply Cnorm_pos | apply Cnorm_triang_rev_l].
   rewrite Rmult_comm ; apply Rmult_lt_compat_l.
   apply Cnorm_pos_lt ; assumption.
   apply Rlt_trans with (eps /2)%R ; [apply Halpha | lra].
   assumption.
   unfold h ; apply Rlt_le_trans with (Rmin (eps / (2 * Cnorm l)) (Rmin (1/2) alpha)) ;
   [apply x'_bd |].
   apply Rle_trans with (Rmin (1/2) alpha) ; apply Rmin_r.
   assumption.
   apply Rlt_trans with (eps / 2 + Cnorm h * Cnorm l)%R.
   apply Rplus_lt_compat_r ; unfold h.
   unfold Rdiv ; rewrite Rmult_comm ; apply Rmult_lt_compat_l ;
   [assumption |].
   apply Rlt_le_trans with (Rmin (eps / (2 * Cnorm l)) (Rmin (1 / 2) alpha)).
   assumption.
   apply Rle_trans with (Rmin (1/2) alpha) ; [apply Rmin_r | apply Rle_trans with (1/2)%R ;
   [apply Rmin_l | right ; field]].
   apply Rlt_le_trans with (eps / 2 + eps / 2)%R ; [apply Rplus_lt_compat_l | right ; field].
   replace (eps / 2)%R with ((eps / (2 * Cnorm l)) * Cnorm l)%R
       by (field ; apply Cnorm_no_R0 ; assumption).
   apply Rmult_lt_compat_r.
   apply Cnorm_pos_lt ; assumption.
   unfold h ; apply Rlt_le_trans with (Rmin (eps / (2 * Cnorm l)) (Rmin (1 / 2) alpha)).
   apply x'_bd.
   apply Rmin_l.
Qed.

Theorem derivable_continuous : forall f, derivable f -> continuity f.
Proof.
  unfold derivable, continuity in |- *; intros f X x.
  apply (derivable_continuous_pt f x (X x)).
Qed.

(***********************************)
(** * derivability -> differentiability  *)
(***********************************)

Lemma derivable_differentiable_pt_abs : forall f x l,
   derivable_pt_abs f x l -> forall v, differentiable_pt_abs f x v l.
Proof.
intros f x l Hl v v_neq eps eps_pos ;
 destruct (Hl eps eps_pos) as [delta Hdelta] ;
 assert (delta'_pos : (0 < delta / Cnorm v)%R). 
  apply Rlt_mult_inv_pos ; [apply delta |
  apply Cnorm_pos_lt ; assumption].
  pose (delta' := mkposreal (delta / Cnorm v)%R delta'_pos) ;
 exists delta' ; intros h h_neq h_ub ; apply Hdelta.
 apply Cmult_integral_contrapositive_currified ;
 [apply IRC_neq_0_compat |] ; assumption.
 rewrite Cnorm_Cmult.
 apply Rlt_le_trans with (delta' * Cnorm v)%R.
 apply Rmult_lt_compat_r.
 apply Cnorm_pos_lt ; assumption.
 rewrite Cnorm_IRC_Rabs ; assumption.
 unfold delta', Rdiv ; simpl ; rewrite Rmult_assoc, Rinv_l.
 right ; field.
 apply Cnorm_no_R0 ; assumption.
Qed.

Theorem derivable_differentiable_pt : forall f x,
 derivable_pt f x -> forall v, differentiable_pt f x v.
Proof.
intros f x [l Hl] v ; exists l ; apply derivable_differentiable_pt_abs ;
 assumption.
Qed.

(****************************************************************)
(** *                    Main rules                             *)
(****************************************************************)

Lemma derivable_pt_lim_add : forall f1 f2 x l1 l2,
    derivable_pt_lim f1 x l1 -> derivable_pt_lim f2 x l2 ->
    derivable_pt_lim (f1 + f2) x (l1 + l2).
Proof.
intros f1 f2 x l1 l2 H H0.
 apply uniqueness_step3.
 assert (H1 := uniqueness_step2 _ _ _ H).
 assert (H2 := uniqueness_step2 _ _ _ H0).
 unfold plus_fct in |- *.
  cut
    (forall h,
      (f1 (x + h) + f2 (x + h) - (f1 x + f2 x)) / h =
      (f1 (x + h) - f1 x) / h + (f2 (x + h) - f2 x) / h).
  intro H3 ; generalize
    (limit_plus (fun h' => (f1 (x + h') - f1 x) / h')
      (fun h' => (f2 (x + h') - f2 x) / h') (fun h => h <> 0) l1 l2 0 H1 H2).
 intros H4 eps eps_pos.
  elim (H4 eps eps_pos); intros x0 Hx0.
  exists x0.
  destruct Hx0 as [x0_pos Hx0'].
  split.
  assumption.
  intros; rewrite H3; apply Hx0'; assumption.
  intro; unfold Cdiv ; ring.
Qed.

Lemma derivable_pt_lim_opp : forall f x l, derivable_pt_lim f x l ->
     derivable_pt_lim (- f) x (- l).
Proof. 
intros f x l H.
 apply uniqueness_step3.
 assert (H1 := uniqueness_step2 _ _ _ H).
  unfold opp_fct in |- * ;
  cut (forall h, (- f (x + h) - - f x) / h = - ((f (x + h) - f x) / h)).
  intro.
  generalize
    (limit_opp (fun h => (f (x + h) - f x) / h) (fun h => h <> 0) l 0 H1).
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

Lemma derivable_pt_lim_minus : forall f1 f2 x l1 l2,
    derivable_pt_lim f1 x l1 -> derivable_pt_lim f2 x l2 ->
    derivable_pt_lim (f1 - f2) x (l1 - l2).
Proof.
  intros.
  apply uniqueness_step3.
  assert (H1 := uniqueness_step2 _ _ _ H).
  assert (H2 := uniqueness_step2 _ _ _ H0).
  unfold minus_fct in |- *.
  cut
    (forall h,
      (f1 (x + h) - f1 x) / h - (f2 (x + h) - f2 x) / h =
      (f1 (x + h) - f2 (x + h) - (f1 x - f2 x)) / h).
  intro.
  generalize
    (limit_minus (fun h' => (f1 (x + h') - f1 x) / h')
      (fun h' => (f2 (x + h') - f2 x) / h') (fun h => h <> 0) l1 l2 0 H1 H2).
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

Lemma derivable_pt_lim_const : forall a x, derivable_pt_lim (fct_cte a) x 0.
Proof.
  intros; unfold fct_cte, derivable_pt_lim in |- *.
  intros; exists (mkposreal 1 Rlt_0_1); intros; unfold Cminus in |- *;
  rewrite Cadd_opp_r; unfold Cdiv in |- * ; rewrite Cmult_0_l;
  rewrite Cadd_opp_r; rewrite Cnorm_C0; assumption.
Qed.

Lemma derivable_pt_lim_mult : forall f1 f2 x l1 l2,
    derivable_pt_lim f1 x l1 ->
    derivable_pt_lim f2 x l2 ->
    derivable_pt_lim (f1 * f2) x (l1 * f2 x + f1 x * l2).
Proof.
  intros.
  assert (H1 := derivable_pt_lim_D_in f1 (fun y => l1) x).
  elim H1; intros.
  assert (H4 := H3 H).
  assert (H5 := derivable_pt_lim_D_in f2 (fun y => l2) x).
  elim H5; intros.
  assert (H8 := H7 H0).
  clear H1 H2 H3 H5 H6 H7.
  assert
    (H1 :=
      derivable_pt_lim_D_in (f1 * f2)%F (fun y => l1 * f2 x + f1 x * l2) x).
  elim H1; intros.
  clear H1 H3.
  apply H2.
  unfold mult_fct in |- *.
  apply (Dmult no_cond (fun y => l1) (fun y => l2) f1 f2 x); assumption.
Qed.

Lemma derivable_pt_lim_scal : forall f a x l,
    derivable_pt_lim f x l -> derivable_pt_lim (fun x => a * f x) x (a * l).
Proof.
  intros.
  assert (H0 := derivable_pt_lim_const a x).
  replace (mult_real_fct a f) with (fct_cte a * f)%F.
  replace (a * l) with (C0 * f x + a * l); [ idtac | ring ].
  apply (derivable_pt_lim_mult (fct_cte a) f x 0 l); assumption.
  unfold mult_real_fct, mult_fct, fct_cte in |- *; reflexivity.
Qed.

Lemma derivable_pt_lim_id : forall x:C, derivable_pt_lim id x C1.
Proof.
  intro; unfold derivable_pt_lim in |- *.
  intros eps Heps; exists (mkposreal eps Heps); intros h H1 H2;
    unfold id in |- *; replace ((x + h - x) / h - C1) with C0.
  rewrite Cnorm_C0 ; assumption.
  fold C in h.
  replace (x + h - x) with h by ring.
  replace (h / h) with C1.
  unfold Cminus ; rewrite Cadd_opp_r ; reflexivity.
  unfold Cdiv ; rewrite Cinv_r ; trivial.
Qed.

(*
Lemma derivable_pt_lim_Csqr : forall x:R, derivable_pt_lim Csqr x (2 * x).
Proof.
  intro; unfold derivable_pt_lim in |- *.
  unfold Rsqr in |- *; intros eps Heps; exists (mkposreal eps Heps);
    intros h H1 H2; replace (((x + h) * (x + h) - x * x) / h - 2 * x) with h.
  assumption.
  replace ((x + h) * (x + h) - x * x) with (2 * x * h + h * h);
  [ idtac | ring ].
  unfold Rdiv in |- *; rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_assoc.
  repeat rewrite <- Rinv_r_sym; [ idtac | assumption ].
  ring.
Qed.
*)

Lemma derivable_pt_lim_comp : forall f1 f2 (x l1 l2:C),
    derivable_pt_lim f1 x l1 ->
    derivable_pt_lim f2 (f1 x) l2 -> derivable_pt_lim (comp f2 f1) x (l2 * l1).
Proof.
  intros; assert (H1 := derivable_pt_lim_D_in f1 (fun y:C => l1) x).
  elim H1; intros.
  assert (H4 := H3 H).
  assert (H5 := derivable_pt_lim_D_in f2 (fun y:C => l2) (f1 x)).
  elim H5; intros.
  assert (H8 := H7 H0).
  clear H1 H2 H3 H5 H6 H7.
  assert (H1 := derivable_pt_lim_D_in (comp f2 f1)%F (fun y:C => l2 * l1) x).
  elim H1; intros.
  clear H1 H3; apply H2.
  unfold comp in |- *;
    cut
      (D_in (fun x0:C => f2 (f1 x0)) (fun y:C => l2 * l1)
        (Dgf no_cond no_cond f1) x ->
        D_in (fun x0:C => f2 (f1 x0)) (fun y:C => l2 * l1) no_cond x).
  intro; apply H1.
  rewrite Cmult_comm;
    apply (Dcomp no_cond no_cond (fun y:C => l1) (fun y:C => l2) f1 f2 x);
      assumption.
  unfold Dgf, D_in, no_cond in |- *; unfold limit1_in in |- *;
    unfold limit_in in |- *; unfold dist in |- *; simpl in |- *;
      unfold R_dist in |- *; intros.
  elim (H1 eps H3); intros.
  exists x0; intros; split.
  elim H5; intros; assumption.
  intros; elim H5; intros; apply H9; split.
  unfold D_x in |- *; split.
  split; trivial.
  elim H6; intros; unfold D_x in H10; elim H10; intros; assumption.
  elim H6; intros; assumption.
Qed.


(***********************************)
(** * derivable_pt compatibility lemmas *)
(***********************************)

Lemma derivable_pt_add : forall f1 f2 (x:C),
    derivable_pt f1 x -> derivable_pt f2 x -> derivable_pt (f1 + f2) x.
Proof.
  unfold derivable_pt in |- *; intros f1 f2 x X X0.
  elim X; intros.
  elim X0; intros.
  exists (x0 + x1).
  apply derivable_pt_lim_add; assumption.
Qed.

Lemma derivable_pt_opp : forall f (x:C), derivable_pt f x -> derivable_pt (- f) x.
Proof.
  unfold derivable_pt in |- *; intros f x X.
  elim X; intros.
  exists (- x0).
  apply derivable_pt_lim_opp; assumption.
Qed.

Lemma derivable_pt_minus : forall f1 f2 (x:C),
    derivable_pt f1 x -> derivable_pt f2 x -> derivable_pt (f1 - f2) x.
Proof.
  unfold derivable_pt in |- *; intros f1 f2 x X X0.
  elim X; intros.
  elim X0; intros.
  exists (x0 - x1).
  apply derivable_pt_lim_minus; assumption.
Qed.

Lemma derivable_pt_mult : forall f1 f2 (x:C),
    derivable_pt f1 x -> derivable_pt f2 x -> derivable_pt (f1 * f2) x.
Proof.
  unfold derivable_pt in |- *; intros f1 f2 x X X0.
  elim X; intros.
  elim X0; intros.
  exists (x0 * f2 x + f1 x * x1).
  apply derivable_pt_lim_mult; assumption.
Qed.

Lemma derivable_pt_const : forall a x:C, derivable_pt (fct_cte a) x.
Proof.
  intros; unfold derivable_pt in |- *.
  exists 0.
  apply derivable_pt_lim_const.
Qed.

Lemma derivable_pt_scal : forall f (a x:C), derivable_pt f x ->
 derivable_pt (mult_real_fct a f) x.
Proof.
  unfold derivable_pt in |- *; intros f1 a x X.
  elim X; intros.
  exists (a * x0).
  apply derivable_pt_lim_scal; assumption.
Qed.

Lemma derivable_pt_id : forall x:C, derivable_pt id x.
Proof.
  unfold derivable_pt in |- *; intro.
  exists 1.
  apply derivable_pt_lim_id.
Qed.

(***********************************)
(** * derivable compatibility lemmas *)
(***********************************)

Lemma derivable_add : forall f1 f2,
    derivable f1 -> derivable f2 -> derivable (f1 + f2).
Proof.
intros f1 f2 Hf1 Hf2 z ; apply derivable_pt_add ; intuition.
Qed.

Lemma derivable_opp : forall f, derivable f -> derivable (- f).
Proof.
intros f1 Hf1 z ; apply derivable_pt_opp ; intuition.
Qed.

Lemma derivable_minus : forall f1 f2,
    derivable f1 -> derivable f2 -> derivable (f1 - f2).
Proof.
intros f1 f2 Hf1 Hf2 z ; apply derivable_pt_minus ; intuition.
Qed.

Lemma derivable_mult : forall f1 f2,
    derivable f1 -> derivable f2 -> derivable (f1 * f2).
Proof.
intros f1 f2 Hf1 Hf2 z ; apply derivable_pt_mult ; intuition.
Qed.

Lemma derivable_const : forall a, derivable (fct_cte a).
Proof.
 intros a z ; apply derivable_pt_const.
Qed.

Lemma derivable_scal : forall f a, derivable f ->
 derivable (mult_real_fct a f).
Proof.
 intros f a Hf z ; apply derivable_pt_scal ; intuition.
Qed.

Lemma derivable_id : derivable id.
Proof.
intro z ; apply derivable_pt_id.
Qed.

(***********************************)
(** * fully differentiability -/-> derivability *)
(***********************************)

Theorem fully_differentiable_pt_not_derivable_pt :
     (forall f x, fully_differentiable_pt f x -> derivable_pt f x) -> False.
Proof.
intro H.
 assert (Main : forall (x y : R), differentiable_pt_abs (fun z1 => (Cre z1 * Cre z1 +
            Cim z1 * Cim z1)%R) 1 (x +i y) (2 * x / (x +i y))).
  intros x y v_neq eps eps_pos.
  pose (delta := (eps / Cnorm (x +i y))%R) ; assert (delta_pos : 0 < delta).
   unfold Rdiv ; apply Rlt_mult_inv_pos ; [| apply Cnorm_pos_lt] ; assumption.
  exists (mkposreal delta delta_pos) ; intros h h_neq h_bd ; simpl.
  repeat rewrite Rmult_0_l ; repeat rewrite Rminus_0_r ; repeat rewrite Rplus_0_r ;
  repeat rewrite Rplus_0_l.
  apply Rle_lt_trans with (Cnorm (h * (h * (x ^ 2) + h * (y ^ 2) + 2 * x)%R / (h * (x, y)) - 2 * x / (x, y))).
  right ; apply Cnorm_eq_compat.
  unfold Cminus ; apply Cadd_eq_compat_r ; apply Cmult_eq_compat_r.
  rewrite Rmult_plus_distr_l ; repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_1_r ; repeat rewrite Rmult_1_l.
  apply (proj1 (Ceq _ _)) ; split ; simpl ; ring.
  apply Rle_lt_trans with (Cnorm ((h * x ^ 2 + h * y ^ 2 + 2 * x)%R / (x, y) - 2 * x / (x, y))).
  right ; apply Cnorm_eq_compat.
  apply Cadd_eq_compat_r.
  rewrite Cmult_comm ; unfold Cdiv ; repeat rewrite Cmult_assoc ;
  apply Cmult_eq_compat_l ; field ; split ; [| apply IRC_neq_compat] ; assumption.
  apply Rle_lt_trans with (Cnorm ((h * x ^ 2 + h * y ^ 2)%R / (x, y))).
  right ; apply Cnorm_eq_compat ; apply (proj1 (Ceq _ _)) ; split ; simpl ; ring.
  rewrite <- Rmult_plus_distr_l ; unfold Cdiv ; rewrite Cmult_IRC_Rmult ;
  repeat rewrite Cnorm_Cmult.
  apply Rlt_le_trans with (eps * Cnorm_sqr (x, y) * (/ Cnorm (x, y)) ^ 2)%R. 
  simpl ; repeat rewrite Rmult_1_r ; rewrite <- Rmult_assoc, Cnorm_inv.
  apply Rmult_lt_compat_r.
  apply Rinv_0_lt_compat ; apply Cnorm_pos_lt ; assumption.
  replace (Cnorm_sqr (x, y))%R with (Cnorm (x * x + y * y)%R).
  apply Rlt_le_trans with (eps * / Cnorm (x, y)* Cnorm (x * x + y * y)%R)%R.
  apply Rmult_lt_compat_r.
  apply Cnorm_pos_lt ; intro Hf ; apply v_neq.
  apply HC0_norm_R0.
  unfold Cnorm_sqr ; simpl.
  destruct (proj2 (Ceq _ _) Hf) as [Hf' _] ; apply Hf'.
  rewrite Cnorm_IRC_Rabs ; apply h_bd.
  right ; field.
  apply Cnorm_no_R0 ; assumption.
  unfold Cnorm_sqr ; rewrite Cnorm_IRC_Rabs, Rabs_right ; [reflexivity |].
  apply Rle_ge ; apply Cnorm_sqr_pos.
  assumption.
  right ; rewrite <- Rmult_1_r, Rmult_assoc ; apply Rmult_eq_compat_l.
  unfold Cnorm, Cnorm_sqr.
  simpl.
  rewrite Rmult_1_r, <- Rinv_mult_distr, sqrt_sqrt, Rinv_r.
  reflexivity.
  apply Rgt_not_eq.
  apply Cnorm_sqr_pos_lt ; assumption.
  apply Cnorm_sqr_pos.
  apply Rgt_not_eq ; apply sqrt_lt_R0 ; apply Cnorm_sqr_pos_lt ; assumption.
  apply Rgt_not_eq ; apply sqrt_lt_R0 ; apply Cnorm_sqr_pos_lt ; assumption.
 assert (Main2 : fully_differentiable_pt Cnorm_sqr 1).
  intros v ; unfold Cnorm_sqr ; destruct v as [x y] ; exists (2 * x / (x, y)) ;
  apply Main.
 assert (Main3 : derivable_pt Cnorm_sqr C1 -> False).
   intros [l Hl].
   assert (H1 := derivable_differentiable_pt_abs Cnorm_sqr 1 l Hl (0,1)%R).
   assert (H1' := Main R0 R1).
   assert (H2 := derivable_differentiable_pt_abs Cnorm_sqr 1 l Hl (1,0)%R).
   assert (H2' := Main R1 R0).
   unfold differentiable_pt_abs in *.
   assert (H1_neq : (R0, R1) <> C0).
    apply HintC0_neq_R0_neq ; right ; simpl ; apply Rgt_not_eq ; apply Rlt_0_1.
   assert (H2_neq : (R1, R0) <> C0).
    apply HintC0_neq_R0_neq ; left ; simpl ; apply Rgt_not_eq ; apply Rlt_0_1.
   assert (Hf1 := Canalysis_diff.uniqueness_limite _ _ _ _ _ H1_neq H1 H1').
   assert (Hf2 := Canalysis_diff.uniqueness_limite _ _ _ _ _ H2_neq H2 H2').
   subst.
   unfold Cdiv in Hf2 ; repeat rewrite Cmult_assoc in Hf2.
   assert (Hneq : IRC 2 <> IRC 0) by (apply IRC_neq_compat ; apply Rgt_not_eq ; lra) ;
   assert (T := Cmult_eq_reg_l _ _ _ Hneq Hf2).
   clear -T H1_neq H2_neq.
   do 2 rewrite Cinv_rew in T.
   destruct (proj2 (Ceq _ _) T) as [H _] ; clear T.
   simpl in H ; ring_simplify in H.
   repeat rewrite Rmult_0_l in H ; repeat rewrite Rmult_1_l in H ;
   rewrite Rplus_0_r, Rinv_1 in H.
   lra.
   assumption.
   assumption.
   assumption.
   apply Main3 ; apply H ; apply Main2.
Qed.

(** * MVT (weak version : the strong one is false when f has complex values *)
(* see http://planetmath.org/encyclopedia/ProofOfComplexMeanValueTheorem.html for the proof *)

Theorem MVT_Cre : forall (f : C -> C) (z h : C)
    (f_deriv : forall (t : R), interval 0 1 t -> derivable_pt f (z + t*h)), h <> 0 ->
    exists u : R, exists u_in_I : interval 0 1 u,
    Cre ((f (z + h) - f z) / h) = Cre (derive_pt f (z + u * h) (f_deriv u u_in_I)).
Proof.
intros f z h f_deriv h_neq.
 pose (H := fun (t : R) => Cre ((f (z + t*h) - f z) / h)).
 assert (H0_0 : (H 0 = 0)%R).
  unfold H ; unfold Cminus, Cdiv ; rewrite Cmult_0_l, Cadd_0_r, Cadd_opp_r, Cmult_0_l ; reflexivity.
 assert (H1_d : H R1  = Cre ((f (z + h) - f z) / h)).
  unfold H ; rewrite Cmult_1_l ; reflexivity.
 assert (H_deriv : forall (t:R) (t_in : interval 0 1 t),
                    Ranalysis_def.derivable_pt_lim_in (interval 0 1) H t (Cre (derive_pt f (z + t * h) (f_deriv t t_in)))).
{  intros t t_in ; destruct (f_deriv t t_in) as [f' Hf'] ;
  intros eps eps_pos ; destruct (Hf' _ eps_pos) as [delta Hdelta].
  pose (delta' := (delta / Cnorm h)%R) ; assert (delta'_pos : 0 < delta').
   unfold delta', Rdiv ; apply Rlt_mult_inv_pos ; [destruct delta | apply Cnorm_pos_lt] ;
   assumption.
  exists delta' ; split ; [assumption |].
  simpl ; intros u [[u_in ut_neq] u_bd] ;
   replace (Ranalysis_def.growth_rate H t u)
   with (Cre (growth_rate f (z + t * h) (z + u * h))).
  + unfold R_dist ; rewrite Cre_minus_compat ; eapply Rle_lt_trans.
    - eapply Cre_le_Cnorm.
    - unfold growth_rate.
      replace (z + IRC u * h - (z + IRC t * h)) with (IRC (u - t) * h).
      replace (IRC u * h) with (IRC t * h + IRC (u - t) * h).
      rewrite <- Cadd_assoc ; apply Hdelta.
       * apply Cmult_integral_contrapositive_currified.
          apply IRC_neq_compat, Rminus_eq_contra ; symmetry ; assumption.
          assumption.
       * rewrite Cnorm_Cmult, Cnorm_IRC_Rabs ; apply Rlt_le_trans with (delta' * Cnorm h)%R.
         apply Rmult_lt_compat_r ; [apply Cnorm_pos_lt |] ; assumption.
         unfold delta', Rdiv ; rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
          reflexivity.
          apply Rgt_not_eq, Cnorm_pos_lt ; assumption.
       * rewrite <- IRC_minus_compat ; ring.
       * rewrite <- IRC_minus_compat ; ring.
  + unfold growth_rate, Ranalysis_def.growth_rate, H.
    rewrite Cre_minus_compat, <- Cre_div_compat.
    rewrite <- IRC_minus_compat ; apply Cre_eq_compat ; field ; repeat split.
     assumption.
     rewrite IRC_minus_compat ; apply IRC_neq_compat, Rminus_eq_contra ; symmetry ; assumption.
     ring_simplify (z + IRC u * h - (z + IRC t * h)) ; rewrite Cmult_comm, <- Cmult_minus_distr_l.
     apply Cmult_integral_contrapositive_currified.
      assumption.
      rewrite IRC_minus_compat ; apply IRC_neq_compat, Rminus_eq_contra ; symmetry ; assumption.
      apply Rminus_eq_contra ; symmetry ; assumption.
}

 assert (H_deriv2 : derivable_open_interval 0 1 H).
  intros a a_in ;
  exists (Cre (derive_pt f (z + a * h) (f_deriv a (open_interval_interval _ _ _ a_in)))).
  eapply derivable_pt_lim_in_contravariant, H_deriv.
  unfold included ; apply open_interval_interval ; assumption.


 assert (id_deriv : derivable_open_interval 0 1 Ranalysis1.id).
  apply derivable_in_id.

 assert (H_cont : Ranalysis_def.continuity_interval 0 1 H).
  apply derivable_in_continuity_in ; intros x x_in ;
   eexists ; apply (H_deriv _ x_in).

 assert (id_cont : Ranalysis_def.continuity_interval 0 1 Ranalysis1.id).
  apply derivable_in_continuity_in, derivable_in_id.

  destruct (Ranalysis_MVT.MVT H (Ranalysis1.id) 0 1 H_deriv2 id_deriv Rlt_0_1 H_cont id_cont) as [c [c_in Hc]] ;
  exists c ; exists (open_interval_interval _ _ _ c_in).
  assert (Hrew := Rminus_0_r (H R1)) ; rewrite <- H0_0 in Hrew.
  rewrite <- H1_d, <- Hrew ; clear Hrew.

  unfold Ranalysis1.id in Hc ; rewrite Rminus_0_r, Rmult_1_l in Hc.
  rewrite derive_open_interval_unfold with (f := fun x => x) (c_in := c_in) in Hc.
  rewrite derive_pt_open_interval_id, Rmult_1_r in Hc ; [| assumption].
  rewrite derive_open_interval_unfold with (f := H) (c_in := c_in) in Hc.


  erewrite derivable_pt_lim_derive_pt_open_interval in Hc.

  change R0 with (IZR 0).
  change R1 with (IZR 1).
  rewrite <- Hc.
  reflexivity.
  assumption.
  apply derivable_pt_lim_in_contravariant with (interval 0 1), H_deriv.
   apply included_open_interval_interval.
Qed.

Theorem MVT_Cim : forall (f : C -> C) (z h : C)
    (f_deriv : forall (t : R), interval 0 1 t -> derivable_pt f (z + t*h)), h <> 0 ->
    exists u : R, exists u_in_I : interval 0 1 u, Cim ((f (z + h) - f z) / h) = Cim (derive_pt f (z + u * h) (f_deriv u u_in_I)).
Proof.
intros f z h f_deriv h_neq.
 pose (H := fun (t : R) => Cim ((f (z + t*h) - f z) / h)).
 assert (H0_0 : (H 0 = 0)%R).
  unfold H ; unfold Cminus, Cdiv ; rewrite Cmult_0_l, Cadd_0_r, Cadd_opp_r, Cmult_0_l ; reflexivity.
 assert (H1_d : H R1  = Cim ((f (z + h) - f z) / h)).
  unfold H ; rewrite Cmult_1_l ; reflexivity.
 assert (H_deriv : forall (t:R) (t_in : interval 0 1 t),
                    Ranalysis_def.derivable_pt_lim_in (interval 0 1) H t (Cim (derive_pt f (z + t * h) (f_deriv t t_in)))).
{  intros t t_in ; destruct (f_deriv t t_in) as [f' Hf'] ;
  intros eps eps_pos ; destruct (Hf' _ eps_pos) as [delta Hdelta].
  pose (delta' := (delta / Cnorm h)%R) ; assert (delta'_pos : 0 < delta').
   unfold delta', Rdiv ; apply Rlt_mult_inv_pos ; [destruct delta | apply Cnorm_pos_lt] ;
   assumption.
  exists delta' ; split ; [assumption |].
  simpl ; intros u [[u_in ut_neq] u_bd] ;
   replace (Ranalysis_def.growth_rate H t u)
   with (Cim (growth_rate f (z + t * h) (z + u * h))).
  + unfold R_dist ; rewrite Cim_minus_compat ; eapply Rle_lt_trans.
    - eapply Cim_le_Cnorm.
    - unfold growth_rate.
      replace (z + IRC u * h - (z + IRC t * h)) with (IRC (u - t) * h).
      replace (IRC u * h) with (IRC t * h + IRC (u - t) * h).
      rewrite <- Cadd_assoc ; apply Hdelta.
       * apply Cmult_integral_contrapositive_currified.
          apply IRC_neq_compat, Rminus_eq_contra ; symmetry ; assumption.
          assumption.
       * rewrite Cnorm_Cmult, Cnorm_IRC_Rabs ; apply Rlt_le_trans with (delta' * Cnorm h)%R.
         apply Rmult_lt_compat_r ; [apply Cnorm_pos_lt |] ; assumption.
         unfold delta', Rdiv ; rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
          reflexivity.
          apply Rgt_not_eq, Cnorm_pos_lt ; assumption.
       * rewrite <- IRC_minus_compat ; ring.
       * rewrite <- IRC_minus_compat ; ring.
  + unfold growth_rate, Ranalysis_def.growth_rate, H.
    rewrite Cim_minus_compat, <- Cim_div_compat.
    rewrite <- IRC_minus_compat ; apply Cim_eq_compat ; field ; repeat split.
     assumption.
     rewrite IRC_minus_compat ; apply IRC_neq_compat, Rminus_eq_contra ; symmetry ; assumption.
     ring_simplify (z + IRC u * h - (z + IRC t * h)) ; rewrite Cmult_comm, <- Cmult_minus_distr_l.
     apply Cmult_integral_contrapositive_currified.
      assumption.
      rewrite IRC_minus_compat ; apply IRC_neq_compat, Rminus_eq_contra ; symmetry ; assumption.
      apply Rminus_eq_contra ; symmetry ; assumption.
}

 assert (H_deriv2 : derivable_open_interval 0 1 H).
  intros a a_in ;
  exists (Cim (derive_pt f (z + a * h) (f_deriv a (open_interval_interval _ _ _ a_in)))).
  eapply derivable_pt_lim_in_contravariant, H_deriv.
  unfold included ; apply open_interval_interval ; assumption.


 assert (id_deriv : derivable_open_interval 0 1 Ranalysis1.id).
  apply derivable_in_id.

 assert (H_cont : Ranalysis_def.continuity_interval 0 1 H).
  apply derivable_in_continuity_in ; intros x x_in ;
   eexists ; apply (H_deriv _ x_in).

 assert (id_cont : Ranalysis_def.continuity_interval 0 1 Ranalysis1.id).
  apply derivable_in_continuity_in, derivable_in_id.

  destruct (Ranalysis_MVT.MVT H (Ranalysis1.id) 0 1 H_deriv2 id_deriv Rlt_0_1 H_cont id_cont) as [c [c_in Hc]] ;
  exists c ; exists (open_interval_interval _ _ _ c_in).
  assert (Hrew := Rminus_0_r (H R1)) ; rewrite <- H0_0 in Hrew.
  rewrite <- H1_d, <- Hrew ; clear Hrew.

  unfold Ranalysis1.id in Hc ; rewrite Rminus_0_r, Rmult_1_l in Hc.
  rewrite derive_open_interval_unfold with (f := fun x => x) (c_in := c_in) in Hc.
  rewrite derive_pt_open_interval_id, Rmult_1_r in Hc ; [| assumption].
  rewrite derive_open_interval_unfold with (f := H) (c_in := c_in) in Hc.


  erewrite derivable_pt_lim_derive_pt_open_interval in Hc.

  change R0 with (IZR 0).
  change R1 with (IZR 1).
  rewrite <- Hc.
  reflexivity.
  assumption.
  apply derivable_pt_lim_in_contravariant with (interval 0 1), H_deriv.
   apply included_open_interval_interval.
Qed.
