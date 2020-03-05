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

Require Import Rlimit.
Require Export Cbase.
Require Import Ctacfield.
Require Import Cnorm.
Require Import Cprop_base.
Require Import Rsequence_def.
Require Import Csequence.
Require Import Csequence_facts.
Require Import Cfunctions.

Open Scope C_scope.

(** Definition of the distance in C *)

Definition C_dist a b := Cnorm (a - b).

Lemma C_dist_pos : forall a b, C_dist a b >= 0.
Proof.
intros ; unfold C_dist ; apply Rle_ge ; apply Cnorm_pos.
Qed.

Lemma C_dist_sym : forall a b, C_dist a b = C_dist b a.
Proof.
intros ; unfold C_dist ; rewrite Cnorm_minus_sym ; reflexivity.
Qed.

Lemma C_dist_refl : forall a b, C_dist a b = 0%R <-> a = b.
Proof.
intros a b ; split ; intro H.
 assert (M := Cnorm_0 _ H) ; apply Cminus_diag_uniq ; assumption.
 unfold C_dist ; subst ; unfold Cminus ; rewrite Cadd_opp_r ; apply Cnorm_C0.
Qed.

Lemma C_dist_tri : forall a b c, C_dist a b <= C_dist a c + C_dist c b.
Proof.
intros ; unfold C_dist ; replace (a - b) with ((a - c) + (c - b)) by field ;
 apply Cnorm_triang.
Qed.

Lemma C_dist_plus : forall a b c d, C_dist (a + c) (b + d) <= C_dist a b + C_dist c d.
Proof.
intros a b c d ; unfold C_dist ; replace (a + c - (b+d)) with ((a-b) + (c-d)) by ring ;
 apply Cnorm_triang.
Qed.

Lemma C_dist_eq : forall a b, a = b -> C_dist a b = 0%R.
Proof.
intros ; apply (proj2 (C_dist_refl _ _)) ; assumption.
Qed.

(** C metric space *)

Definition C_met : Metric_Space :=
 Build_Metric_Space C C_dist C_dist_pos C_dist_sym C_dist_refl C_dist_tri.

Definition limit1_in (f:C->C) (D:C -> Prop) (l z:C) : Prop :=
  limit_in C_met C_met f D z l.

Definition Boule (c : C) (r : posreal) (x : C) := dist C_met c x < r.

Definition CVN_r (fn : nat -> C -> C) (r : posreal) := {An : nat -> C & 
	{l : R |
	Rseq_cv (fun n : nat => sum_f_R0 (fun k : nat => Cnorm (An k)) n) l /\
	(forall (n : nat) (y : C), Boule 0 r y -> Cnorm (fn n y) <= Cnorm (An n))}}.

(*********)
Definition D_x (D:C -> Prop) (y x:C) : Prop := D x /\ y <> x.

Definition Dgf (Df Dg:C -> Prop) (f:C->C) (z:C) := Df z /\ Dg (f z).

Definition adhDa (D:C -> Prop) (a:C) : Prop := forall alp:R, alp > 0 ->
  exists x, D x /\ C_dist x a < alp.

(** Compatibility of limit with operators *)

(*********)
Lemma single_limit : forall f D l l' x,
	adhDa D x -> limit1_in f D l x -> limit1_in f D l' x ->
	l = l'.
Proof.
unfold limit1_in, limit_in ; intros f D l l' x HD Hl Hl' ;
 cut (forall eps:R, eps > 0 -> dist C_met l l' < eps).
 simpl ; unfold C_dist ; intro Hforall.
 apply Cseq_cv_unique with (fun _ => l).
 apply Cseq_cst_cv.
 intros eps eps_pos ; exists 0%nat ; intros n n_lb ; apply Hforall ; assumption.
 intros eps eps_pos ; assert (eps_2_pos : eps / 2 > 0) by lra ;
 destruct (Hl (eps / 2)%R eps_2_pos) as (alpha1, [alpha1_pos Halpha1]) ;
 destruct (Hl' (eps / 2)%R eps_2_pos) as (alpha2, [alpha2_pos Halpha2]) ;
 assert (alpha'_pos : Rmin alpha1 alpha2 > 0) by (apply Rmin_pos ; assumption) ;
 destruct (HD (Rmin alpha1 alpha2)%R alpha'_pos) as (x', [Dx' Hx']) ;  clear Hl Hl' HD.
 apply Rle_lt_trans with (Cnorm (l - (f x')) + Cnorm (f x' - l'))%R.
 simpl ; unfold C_dist.
 replace (Cnorm (l - l')) with (Cnorm ((l - f x') + (f x' - l')))
 by (apply Cnorm_eq_compat ; field) ; apply Cnorm_triang.
 apply Rlt_le_trans with (eps / 2 + eps / 2)%R ; [| right ; field] ;
 apply Rlt_trans with (Cnorm (l - f x') + eps / 2)%R.
 apply Rplus_lt_compat_l ; simpl in Halpha2 ; apply Halpha2 ; split ;
 [| apply Rlt_le_trans with (Rmin alpha1 alpha2) ; [| apply Rmin_r]] ; assumption.
 apply Rplus_lt_compat_r ; simpl in Halpha1 ; rewrite Cnorm_minus_sym ;
 apply Halpha1 ; split ; [| apply Rlt_le_trans with (Rmin alpha1 alpha2) ;
 [| apply Rmin_l]] ; assumption.
Qed.

(*********)
Lemma limit_plus : forall (f g:C -> C) (D:C -> Prop) (l l' z:C),
    limit1_in f D l z ->
    limit1_in g D l' z -> limit1_in (fun x:C => f x + g x) D (l + l') z.
Proof.
  intros; unfold limit1_in in |- *; unfold limit_in in |- *; simpl in |- *;
    intros; elim (H (eps * / 2)%R (eps2_Rgt_R0 eps H1));
      elim (H0 (eps * / 2)%R (eps2_Rgt_R0 eps H1)); simpl in |- *; 
        clear H H0; intros; elim H; elim H0; clear H H0; intros;
          split with (Rmin x0 x); split.
  apply Rmin_Rgt_r ; split ; assumption.
  intros; elim H4; clear H4; intros;
    cut (C_dist (f x1) l + C_dist (g x1) l' < eps).
  cut (C_dist (f x1 + g x1) (l + l') <= C_dist (f x1) l + C_dist (g x1) l').
  apply Rle_lt_trans.
  apply C_dist_plus.
  elim (Rmin_Rgt_l x0 x (C_dist x1 z) H5); clear H5; intros.
  generalize (H3 x1 (conj H4 H6)); generalize (H0 x1 (conj H4 H5)); intros;
    replace eps with (eps * / 2 + eps * / 2)%R.
  apply Rplus_lt_compat ; assumption.
  apply eps2.
Qed.

(*********)
Lemma limit_opp : forall (f:C -> C) (D:C -> Prop) (l x0:C),
    limit1_in f D l x0 -> limit1_in (fun x:C => - f x) D (- l) x0.
Proof.
  unfold limit1_in in |- *; unfold limit_in in |- *; simpl in |- *; intros;
    elim (H eps H0); clear H; intros; elim H; clear H; 
      intros; split with x; split; auto; intros; generalize (H1 x1 H2); 
        clear H1; intro; unfold C_dist in |- *; unfold Cminus in |- *;
          rewrite (Copp_involutive l); rewrite (Cadd_comm (- f x1) l);
            fold (l - f x1) in |- *; fold (C_dist l (f x1)) in |- *; 
              rewrite C_dist_sym; assumption.
Qed.

(*********)
Lemma limit_minus : forall (f g:C -> C) (D:C -> Prop) (l l' x0:C),
    limit1_in f D l x0 ->
    limit1_in g D l' x0 -> limit1_in (fun x:C => f x - g x) D (l - l') x0.
Proof.
  intros; unfold Cminus in |- *; generalize (limit_opp g D l' x0 H0); intro;
    exact (limit_plus f (fun x:C => - g x) D l (- l') x0 H H1).
Qed.

(*********)
Lemma limit_free : forall (f:C -> C) (D:C -> Prop) (x x0:C),
    limit1_in (fun h:C => f x) D (f x) x0.
Proof.
  unfold limit1_in in |- *; unfold limit_in in |- *; simpl in |- *; intros;
    split with eps; split; auto; intros; elim (C_dist_refl (f x) (f x));
      intros a b; rewrite (b (refl_equal (f x))); unfold Rgt in H; 
        assumption.
Qed.

(*********)
Lemma limit_mul : forall (f g:C -> C) (D:C -> Prop) (l l' x0:C),
    limit1_in f D l x0 ->
    limit1_in g D l' x0 -> limit1_in (fun x:C => f x * g x) D (l * l') x0.
Proof.
  intros f g D l l' z Hf Hg eps eps_pos.
      elim (Hf (Rmin 1 (eps * mul_factor (Cnorm l) (Cnorm l')))
             (mul_factor_gt_f eps (Cnorm l) (Cnorm l') eps_pos)) ;
      elim (Hg (eps * mul_factor (Cnorm l) (Cnorm l'))%R
             (mul_factor_gt eps (Cnorm l) (Cnorm l') eps_pos)) ;
      clear Hf Hg ; simpl ; intros x Hf y Hg ; elim Hf ; elim Hg ;
      clear Hf Hg ; intros y_pos Hx x_pos Hy ; split with (Rmin y x) ;
      split ; [apply Rmin_Rgt_r ; split ; assumption |].
  intros z' [Dz' Hz'] ; unfold C_dist ;  replace (f z' * g z' - l * l') with
      (f z' * (g z' - l') + l' * (f z' - l)).
  cut (Cnorm (f z' * (g z' - l')) + Cnorm (l' * (f z' - l)) < eps). 
  cut
    (Cnorm (f z' * (g z' - l') + l' * (f z' - l)) <=
      Cnorm (f z' * (g z' - l')) + Cnorm (l' * (f z' - l))).
  apply Rle_lt_trans.
  apply Cnorm_triang.
  repeat (rewrite Cnorm_Cmult) ;
    cut ((1 + Cnorm l) * (eps * mul_factor (Cnorm l) (Cnorm l'))
          + Cnorm l' * (eps * mul_factor (Cnorm l) (Cnorm l')) <= eps).
  cut (Cnorm (f z') * Cnorm (g z' - l') + Cnorm l' * Cnorm (f z' - l) <
      (1 + Cnorm l) * (eps * mul_factor (Cnorm l) (Cnorm l'))
      + Cnorm l' * (eps * mul_factor (Cnorm l) (Cnorm l'))).
  apply Rlt_le_trans.
  elim (Rmin_Rgt_l y x (C_dist z' z) Hz'); intros Hx2 Hy2.
  apply Rplus_lt_le_compat.
  apply Rmult_ge_0_gt_0_lt_compat.
  apply Rle_ge ; apply Cnorm_pos.
  rewrite Rplus_comm ; unfold Rgt in |- *; apply Rle_lt_0_plus_1;
    apply Cnorm_pos.
  apply Rplus_lt_reg_l with (- Cnorm l)%R.
  rewrite <- Rplus_assoc ; rewrite (Rplus_comm (- Cnorm l) 1).
  rewrite (Rplus_assoc 1 (- Cnorm l) (Cnorm l)) ; rewrite Rplus_opp_l ;
  rewrite (proj1 (Rplus_ne 1)) ; rewrite (Rplus_comm (- Cnorm l) (Cnorm (f z'))) ;
  cut (Cnorm (f z' - l) < 1) ; cut (Cnorm (f z') - Cnorm l <= Cnorm (f z' - l)).
  apply Rle_lt_trans.
  apply Cnorm_triang_rev_l.
  intros _ ; apply Rlt_le_trans with (Rmin 1 (eps * mul_factor (Cnorm l) (Cnorm l'))) ;
  [apply Hx ; split ; assumption | apply Rmin_l].
  apply Cnorm_triang_rev_l.
  apply Hy ; split ; assumption.
  apply Rmult_le_compat.
  apply Cnorm_pos.
  apply Cnorm_pos.
  right ; trivial.
  apply Rlt_le ; apply Rlt_le_trans with (Rmin 1 (eps * mul_factor (Cnorm l) (Cnorm l'))) ;
  [apply Hx | apply Rmin_r] ; split ; assumption.
  rewrite (Rmult_comm (1 + Cnorm l) (eps * mul_factor (Cnorm l) (Cnorm l')));
  rewrite (Rmult_comm (Cnorm l') (eps * mul_factor (Cnorm l) (Cnorm l')));
  rewrite <- (Rmult_plus_distr_l (eps * mul_factor (Cnorm l) (Cnorm l'))
       (1 + Cnorm l) (Cnorm l')) ;
  rewrite (Rmult_assoc eps (mul_factor (Cnorm l) (Cnorm l')) (1 + Cnorm l + Cnorm l'));
  rewrite (Rplus_assoc 1 (Cnorm l) (Cnorm l')).
  unfold mul_factor ; right.
  repeat rewrite Rabs_Cnorm.
  rewrite Rinv_l.
  field.
  apply Rgt_not_eq.
  rewrite Rplus_comm ; apply Rle_lt_0_plus_1 ; apply Rplus_le_le_0_compat ;
  apply Cnorm_pos.
  field.
Qed.

Lemma limit_inv : forall f D l z,
    limit1_in f D l z -> l <> 0 -> limit1_in (fun x => / f x) D (/ l) z.
Proof.
intros f D l z Hf l_neq ; intros eps eps_pos ; elim (Hf ((Cnorm l) / 2)%R).
 intros delta1 [delta1_pos Hdelta1] ; elim (Hf (eps * (Rsqr (Cnorm l) / 2))%R).
 intros delta2 [delta2_pos Hdelta2] ; exists (Rmin delta1 delta2) ; split.
 unfold Rmin ; case (Rle_dec delta1 delta2); intro H ; assumption.
 intro x ; generalize (Hdelta2 x); clear Hdelta2 ; intro Hdelta2 ;
 generalize (Hdelta1 x); clear Hdelta1 ; intro Hdelta1 ; simpl in x.
 intros [Dx xz_bd] ; cut (D x /\ Cnorm (x - z) < delta1).
  cut (D x /\ Cnorm (x - z) < delta2).
  intros H2 H1 ; generalize (Hdelta1 H1) ; clear Hdelta1 ; intro Hdelta1 ;
  generalize (Hdelta2 H2) ; clear Hdelta2 ; intro Hdelta2.
  simpl in * ; unfold C_dist in * ; generalize (Cnorm_triang_rev_l l (f x)) ; intro H ;
  rewrite Cnorm_minus_sym in Hdelta1 ; generalize
  (Rle_lt_trans (Cnorm l - Cnorm (f x)) (Cnorm (l - f x)) (Cnorm l / 2) H Hdelta1) ;
  intro H'.
  generalize (Rplus_lt_compat_l (Cnorm (f x) - Cnorm l / 2) (Cnorm l - Cnorm (f x))
                (Cnorm l / 2) H');
  replace (Cnorm (f x) - Cnorm l / 2 + (Cnorm l - Cnorm (f x)))%R with
                (Cnorm l / 2)%R by field.
  unfold Rminus ; rewrite Rplus_assoc ; rewrite Rplus_opp_l ;
    rewrite Rplus_0_r ; intro H'' ; cut (f x <> 0).
  intro fx_neq ; replace (/ f x - / l) with ((l - f x) * / (l * f x)).
  rewrite Cnorm_Cmult; rewrite Cnorm_inv.
  cut (/ Cnorm (l * f x) < 2 / Rsqr (Cnorm l)).
  intro H3; rewrite Cnorm_minus_sym in Hdelta2; cut (0 <= / Cnorm (l * f x)).
  intro H4 ; generalize
      (Rmult_le_0_lt_compat (Cnorm (l - f x)) (eps * (Rsqr (Cnorm l) / 2))
      (/ Cnorm (l * f x)) (2 / Rsqr (Cnorm l)) (Cnorm_pos ((l - f x))) H4 Hdelta2 H3);
      replace (eps * (Rsqr (Cnorm l) / 2) * (2 / Rsqr (Cnorm l)))%R with eps.
  trivial.
  field ; unfold Rsqr.
  apply Rmult_integral_contrapositive_currified ; apply Cnorm_no_R0 ; assumption.
  left ; apply Rinv_0_lt_compat ; apply Cnorm_pos_lt ;
  apply Cmult_integral_contrapositive_currified ; assumption.
 rewrite Cmult_comm; rewrite Cnorm_Cmult ; rewrite Rinv_mult_distr.
 unfold Rsqr, Rdiv ; rewrite Rinv_mult_distr ; repeat rewrite <- Rmult_assoc.
 apply Rmult_lt_compat_r.
 apply Rinv_0_lt_compat; apply Cnorm_pos_lt; assumption.
 apply Rmult_lt_reg_l with (Cnorm (f x) * Cnorm l * / 2)%R.
 repeat apply Rmult_lt_0_compat ; [| | lra] ; apply Cnorm_pos_lt; assumption.
 rewrite Rmult_comm ; repeat rewrite <- Rmult_assoc ; rewrite Rinv_l.
 rewrite Rmult_1_l ; repeat rewrite Rmult_assoc ;
 replace (Cnorm l * (/ 2 * (2 * / Cnorm l)))%R with 1%R.
 rewrite Rmult_1_r ; assumption.
 field ; apply Cnorm_no_R0 ; assumption.
 apply Cnorm_no_R0 ; assumption.
 apply Cnorm_no_R0 ; assumption.
 apply Cnorm_no_R0 ; assumption.
 apply Cnorm_no_R0 ; assumption.
 apply Cnorm_no_R0 ; assumption.
 apply Cmult_integral_contrapositive_currified ; assumption.
 field ; split ; assumption.
 apply Cnorm_gt_not_eq ; apply Rlt_gt ; apply Rle_lt_trans with (Cnorm l / 2)%R ;
 [assert (Temp := Cnorm_pos l) ; lra | assumption].
 split ; [| apply Rlt_le_trans with (Rmin delta1 delta2) ; [| apply Rmin_r]] ; assumption.
 split ; [| apply Rlt_le_trans with (Rmin delta1 delta2) ; [| apply Rmin_l]] ; assumption.
 unfold Rdiv ; repeat apply Rmult_lt_0_compat ; intuition ;
 apply Cnorm_pos_lt ; assumption.
 unfold Rdiv ; repeat apply Rmult_lt_0_compat ; intuition ;
 apply Cnorm_pos_lt ; assumption.
Qed.

Lemma limit_comp : forall f g Df Dg l l' z,
    limit1_in f Df l z -> limit1_in g Dg l' l -> limit1_in (fun z => g (f z)) (Dgf Df Dg f) l' z.
Proof.
  unfold limit1_in, limit_in, Dgf in |- *; simpl in |- *.
  intros f g Df Dg l l' x0 Hf Hg eps eps_pos.
  elim (Hg eps eps_pos).
  intros alpg lg.
  elim (Hf alpg).
  2: tauto.
  intros alpf lf.
  exists alpf.
  intuition.
Qed.
