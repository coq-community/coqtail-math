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

Require Import Ctacfield.
Require Import Cnorm.
Require Import Cprop_base.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.
Require Import Cmet.

Local Open Scope C_scope.

(*********)
Definition D_x (D:C -> Prop) (y x:C) : Prop := D x /\ y <> x.

(*********)
Definition continue_in (f:C -> C) (D:C -> Prop) (z:C) : Prop :=
  limit1_in f (D_x D z) (f z) z.

(*********)
Definition D_in (f d:C -> C) (D:C -> Prop) (x0:C) : Prop :=
  limit1_in (fun x:C => (f x - f x0) / (x - x0)) (D_x D x0) (d x0) x0.

Lemma cont_deriv : forall (f d:C -> C) (D:C -> Prop) (z:C),
    D_in f d D z -> continue_in f D z.
Proof.
intros f d D z Hf_D eps eps_pos ; unfold continue_in, D_in, limit1_in,
 limit_in, Cdiv in Hf_D ; simpl.
 case (Ceq_dec (d z) 0) ; intro dz_0.
  elim (Hf_D eps eps_pos) ; clear Hf_D ; intros alpha [alpha_pos Hf_D].
  pose (delta := Rmin 1 alpha) ; exists delta ; split.
  apply Rmin_pos ; auto with real.
  intros x [Hx x_bd] ; simpl in Hf_D ; unfold C_dist in *.
   destruct (Ceq_dec x z) as [x_eq_z | x_neq_z].
   rewrite x_eq_z ; unfold Cminus ; rewrite Cadd_opp_r.
   rewrite Cnorm_C0 ; assumption.
   replace (Cnorm (f x - f z)) with ((Cnorm (f x - f z)) * Cnorm (x - z) * / Cnorm (x - z))%R.
   apply Rlt_le_trans with (eps * Cnorm (x - z))%R.
   rewrite Rmult_assoc ; rewrite Rmult_comm ; rewrite Rmult_assoc ;
   rewrite <- Cnorm_inv.
   rewrite <- Cnorm_Cmult ; rewrite Rmult_comm ; apply Rmult_lt_compat_r.
   apply Cnorm_pos_lt ; auto with complex.
   rewrite Cmult_comm ; replace ((f x - f z) * / (x - z)) with ((f x - f z) * / (x - z) - 0)
   by auto with complex ; rewrite <- dz_0 ; apply Hf_D ; split ; auto with complex.
   apply Rlt_le_trans with delta ; [assumption | apply Rmin_r].
   auto with complex.
   apply Rle_trans with (eps * delta)%R.
   apply Rmult_le_compat_l ; auto with real.
   rewrite <- Rmult_1_r ; apply Rmult_le_compat_l ; [auto with real | apply Rmin_l].
   field ; apply Rgt_not_eq ; apply Cnorm_pos_lt ; auto with complex.
  assert (eps_2_pos : 0 < eps / 2) by lra ;
  elim (Hf_D (eps / 2)%R eps_2_pos) ; clear Hf_D ; intros alpha [alpha_pos Hf_D].
  pose (delta := Rmin (eps / (2 * Cnorm (d z))) (Rmin (1/2) alpha)) ; exists delta ;
  split ; [apply Rmin_pos |].
  unfold Rdiv ; rewrite Rinv_mult_distr ; repeat apply Rmult_lt_0_compat.
  assumption.
  lra.
  apply Rinv_0_lt_compat ; apply Cnorm_pos_lt ; assumption.
  apply Rgt_not_eq ; lra.
  apply Rgt_not_eq ; apply Cnorm_pos_lt ; assumption.
  apply Rmin_pos ; lra.
  intros x' [[Dx' z_neq_x'] x'_bd] ; simpl ; unfold C_dist.
  apply Rlt_trans with (Cnorm (x' - z) * eps + Cnorm (x' - z) * Cnorm (d z))%R.
  apply Rle_lt_trans with (Cnorm (f x' - f z) * (/ Cnorm (x' - z) * Cnorm (x' - z)))%R.
   right ; field ; apply Rgt_not_eq ; apply Cnorm_pos_lt ; auto with complex.
   unfold Rdiv ; rewrite  <- Rmult_assoc ; rewrite <- Cnorm_inv, <- Cnorm_Cmult.
   apply Rle_lt_trans with ((Cnorm ((f x' - f z) * / (x' - z)) + (- Cnorm (d z) + Cnorm (d z)))
       * Cnorm (x' - z))%R.
   right ; field.
   repeat rewrite Rmult_plus_distr_r.
   replace (Cnorm (d z) * Cnorm (x' - z))%R with (Cnorm (x' - z) * Cnorm (d z))%R
   by (apply Rmult_comm).
   rewrite <- Rplus_assoc ; apply Rplus_lt_compat_r.
   apply Rle_lt_trans with (Cnorm ((f x' - f z) / (x' - z) - d z)* Cnorm (x' - z))%R.
   rewrite <- Rmult_plus_distr_r ; apply Rmult_le_compat_r ;
   [apply Cnorm_pos | apply Cnorm_triang_rev_l].
   rewrite Rmult_comm ; apply Rmult_lt_compat_l.
   apply Cnorm_pos_lt ; auto with complex.
   apply Rlt_trans with (eps /2)%R ; [simpl in Hf_D ; apply Hf_D | lra] ;
   repeat split ; [| | apply Rlt_le_trans with delta ;
   [| apply Rle_trans with (Rmin (1 / 2) alpha)%R ; apply Rmin_r]] ; assumption.
   auto with complex.
   apply Rlt_trans with (eps / 2 + Cnorm (x' - z) * Cnorm (d z))%R.
   apply Rplus_lt_compat_r.
   unfold Rdiv ; rewrite Rmult_comm ; apply Rmult_lt_compat_l ;
   [assumption |].
   apply Rlt_le_trans with (Rmin (eps / (2 * Cnorm (d z))) (Rmin (1 / 2) alpha)).
   unfold C_dist, delta in x'_bd ; apply x'_bd.
   apply Rle_trans with (Rmin (1/2) alpha) ; [apply Rmin_r | apply Rle_trans with (1/2)%R ;
   [apply Rmin_l | right ; field]].
   apply Rlt_le_trans with (eps / 2 + eps / 2)%R ; [apply Rplus_lt_compat_l | right ; field].
   replace (eps / 2)%R with ((eps / (2 * Cnorm (d z))) * Cnorm (d z))%R
       by (field ; apply Cnorm_no_R0 ; assumption).
   apply Rmult_lt_compat_r.
   apply Cnorm_pos_lt ; assumption.
   apply Rlt_le_trans with (Rmin (eps / (2 * Cnorm (d z))) (Rmin (1 / 2) alpha)).
   apply x'_bd.
   apply Rmin_l.
Qed.

Lemma Dmult : forall (D:C -> Prop) (df dg f g:C -> C) (z:C),
    D_in f df D z -> D_in g dg D z ->
    D_in (fun z:C => f z * g z) (fun z:C => df z * g z + f z * dg z) D z.
Proof.
  intros; unfold D_in in |- *; generalize H H0; intros; unfold D_in in H, H0;
    generalize (cont_deriv f df D z H1); unfold continue_in in |- *; 
      intro;
        generalize
          (limit_mul (fun x:C => (g x - g z) * / (x - z)) (
          fun z:C => f z) (D_x D z) (dg z) (f z) z H0 H3); 
          intro; cut (limit1_in (fun x:C => g z) (D_x D z) (g z) z).
  intro; generalize
      (limit_mul (fun x:C => (f x - f z) * / (x - z)) (
      fun _:C => g z) (D_x D z) (df z) (g z) z H H5);
      clear H H0 H1 H2 H3 H5; intro;
        generalize
          (limit_plus (fun x:C => (f x - f z) * / (x - z) * g z)
            (fun x:C => (g x - g z) * / (x - z) * f x) (
              D_x D z) (df z * g z) (dg z * f z) z H H4); 
          clear H4 H; intro; unfold limit1_in in H; unfold limit_in in H; 
            simpl in H; unfold limit1_in in |- *; unfold limit_in in |- *; 
              simpl in |- *; intros; elim (H eps H0); clear H; intros; 
                elim H; clear H; intros; split with x; split; auto; 
                  intros; generalize (H1 x0 H2); clear H1; intro;
                    rewrite (Cmult_comm (f x0 - f z) (/ (x0 - z))) in H1;
                      rewrite (Cmult_comm (g x0 - g z) (/ (x0 - z))) in H1;
                        rewrite (Cmult_assoc (/ (x0 - z)) (f x0 - f z) (g z)) in H1;
                          rewrite (Cmult_assoc (/ (x0 - z)) (g x0 - g z) (f x0)) in H1.
                            rewrite <- (Cmult_add_distr_l (/ (x0 - z)) ((f x0 - f z) * g z)
                                ((g x0 - g z) * f x0)) in H1;
                              rewrite
                                (Cmult_comm (/ (x0 - z)) ((f x0 - f z) * g z + (g x0 - g z) * f x0))
                                in H1; rewrite (Cmult_comm (dg z) (f z)) in H1;
                                  cut
                                    ((f x0 - f z) * g z + (g x0 - g z) * f x0 = f x0 * g x0 - f z * g z).
 intro; rewrite H3 in H1; assumption.
 ring.
 unfold limit1_in in |- *; unfold limit_in in |- *; simpl in |- *; intros;
    split with eps; split; auto; intros; elim (C_dist_refl (g z) (g z));
      intros a b; rewrite (b (refl_equal (g z))); unfold Rgt in H; 
        assumption.
Qed.

(*********)
Lemma Dconst : forall (D:C -> Prop) (y x0:C), D_in (fun x:C => y) (fun x:C => C0) D x0.
Proof.
  unfold D_in in |- *; intros; unfold limit1_in in |- *;
    unfold limit_in in |- *; unfold Cdiv in |- *; intros; 
      simpl in |- *; split with eps; split; auto.
  intros; rewrite (Cminus_diag_eq y y (refl_equal y)) ; rewrite Cmult_0_l;
    unfold C_dist in |- *; rewrite (Cminus_diag_eq C0 C0 (refl_equal _)).
    rewrite Cnorm_C0 ; assumption.
Qed.

(*********)
Lemma Dx : forall (D:C -> Prop) (x0:C), D_in (fun x:C => x) (fun x:C => 1) D x0.
Proof.
  unfold D_in in |- *; unfold Cdiv in |- *; intros; unfold limit1_in in |- *;
    unfold limit_in in |- *; intros; simpl in |- *; split with eps; 
      split; auto.
  intros; elim H0; clear H0; intros; unfold D_x in H0; elim H0; intros;
    rewrite (Cinv_r (x - x0) (Cminus_eq_contra x x0 (sym_not_eq H3)));
      unfold C_dist in |- *; rewrite (Cminus_diag_eq _ _ (refl_equal _)).
    rewrite Cnorm_C0 ; assumption.
Qed.

(*********)
Lemma Dadd : forall (D:C -> Prop) (df dg f g:C -> C) (x0:C),
    D_in f df D x0 ->
    D_in g dg D x0 ->
    D_in (fun x:C => f x + g x) (fun x:C => df x + dg x) D x0.
Proof.
  unfold D_in in |- *; intros;
    generalize
      (limit_plus (fun x:C => (f x - f x0) * / (x - x0))
        (fun x:C => (g x - g x0) * / (x - x0)) (D_x D x0) (
          df x0) (dg x0) x0 H H0); clear H H0; unfold limit1_in in |- *;
      unfold limit_in in |- *; simpl in |- *; intros; elim (H eps H0); 
        clear H; intros; elim H; clear H; intros; split with x; 
          split; auto; intros; generalize (H1 x1 H2); clear H1; 
            intro; rewrite (Cmult_comm (f x1 - f x0) (/ (x1 - x0))) in H1;
              rewrite (Cmult_comm (g x1 - g x0) (/ (x1 - x0))) in H1;
                rewrite <- (Cmult_add_distr_l (/ (x1 - x0)) (f x1 - f x0) (g x1 - g x0)) in H1;
                  rewrite (Cmult_comm (/ (x1 - x0)) (f x1 - f x0 + (g x1 - g x0))) in H1;
                    cut (f x1 - f x0 + (g x1 - g x0) = f x1 + g x1 - (f x0 + g x0)).
  intro; rewrite H3 in H1; assumption.
  ring.
Qed.

(*********)
Lemma Dmult_const : forall (D:C -> Prop) (f df:C -> C) (x0 a:C),
    D_in f df D x0 -> D_in (fun x:C => a * f x) (fun x:C => a * df x) D x0.
Proof.
  intros;
    generalize (Dmult D (fun _:C => C0) df (fun _:C => a) f x0 (Dconst D a x0) H);
      unfold D_in in |- *; intros; rewrite (Cmult_0_l (f x0)) in H0.
      rewrite Cadd_0_l in H0.
assumption.
Qed.

(*********)
Lemma Dopp : forall (D:C -> Prop) (f df:C -> C) (x0:C),
    D_in f df D x0 -> D_in (fun x:C => - f x) (fun x:C => - df x) D x0.
Proof.
  intros; generalize (Dmult_const D f df x0 (-1) H); unfold D_in in |- *;
    unfold limit1_in in |- *; unfold limit_in in |- *; 
      intros; generalize (H0 eps H1); clear H0; intro; elim H0; 
        clear H0; intros; elim H0; clear H0; simpl in |- *; 
          intros; split with x; split; auto.
  intros; generalize (H2 x1 H3); clear H2; intro ;
  repeat rewrite Cmult_opp_1_opp in H2 ;  assumption.
Qed.

(*********)
Lemma Dminus : forall (D:C -> Prop) (df dg f g:C -> C) (x0:C),
    D_in f df D x0 ->
    D_in g dg D x0 ->
    D_in (fun x:C => f x - g x) (fun x:C => df x - dg x) D x0.
Proof.
  unfold Rminus in |- *; intros; generalize (Dopp D g dg x0 H0); intro;
    apply (Dadd D df (fun x:C => - dg x) f (fun x:C => - g x) x0); 
      assumption. 
Qed.

(*********)
Lemma Dcomp : forall (Df Dg:C -> Prop) (df dg f g:C -> C) (x0:C),
    D_in f df Df x0 ->
    D_in g dg Dg (f x0) ->
    D_in (fun x:C => g (f x)) (fun x:C => df x * dg (f x)) (Dgf Df Dg f) x0.
Proof.
  intros Df Dg df dg f g x0 H H0; generalize H H0; unfold D_in in |- *;
    unfold Cdiv in |- *; intros;
      generalize
        (limit_comp f (fun x:C => (g x - g (f x0)) * / (x - f x0)) (
          D_x Df x0) (D_x Dg (f x0)) (f x0) (dg (f x0)) x0); 
        intro; generalize (cont_deriv f df Df x0 H); intro; 
          unfold continue_in in H4; generalize (H3 H4 H2); clear H3; 
            intro;
              generalize
                (limit_mul (fun x:C => (g (f x) - g (f x0)) * / (f x - f x0))
                  (fun x:C => (f x - f x0) * / (x - x0))
                  (Dgf (D_x Df x0) (D_x Dg (f x0)) f) (dg (f x0)) (
                    df x0) x0 H3); intro;
                cut
                  (limit1_in (fun x:C => (f x - f x0) * / (x - x0))
                    (Dgf (D_x Df x0) (D_x Dg (f x0)) f) (df x0) x0).
  intro; generalize (H5 H6); clear H5; intro;
    generalize
      (limit_mul (fun x:C => (f x - f x0) * / (x - x0)) (
        fun x:C => dg (f x0)) (D_x Df x0) (df x0) (dg (f x0)) x0 H1
      (limit_free (fun x:C => dg (f x0)) (D_x Df x0) x0 x0)); 
      intro; unfold limit1_in in |- *; unfold limit_in in |- *; 
        simpl in |- *; unfold limit1_in in H5, H7; unfold limit_in in H5, H7;
          simpl in H5, H7; intros; elim (H5 eps H8); elim (H7 eps H8); 
            clear H5 H7; intros; elim H5; elim H7; clear H5 H7; 
              intros; split with (Rmin x x1); split.
  elim (Rmin_Rgt x x1 0); intros a b; apply (b (conj H9 H5)); clear a b.
  intros; elim H11; clear H11; intros; elim (Rmin_Rgt x x1 (C_dist x2 x0));
    intros a b; clear b; unfold Rgt in a; elim (a H12); 
      clear H5 a; intros; unfold D_x, Dgf in H11, H7, H10; 
        clear H12; elim (classic (f x2 = f x0)); intro.
  elim H11; clear H11; intros; elim H11; clear H11; intros;
    generalize (H10 x2 (conj (conj H11 H14) H5)); intro;
      rewrite (Cminus_diag_eq (f x2) (f x0) H12) in H16;
        rewrite (Cmult_0_l (/ (x2 - x0))) in H16;
          rewrite (Cmult_0_l (dg (f x0))) in H16; rewrite H12;
            rewrite (Cminus_diag_eq (g (f x0)) (g (f x0)) (refl_equal (g (f x0))));
            rewrite (Cmult_0_l (/ (x2 - x0))); assumption.
  clear H10 H5; elim H11; clear H11; intros; elim H5; clear H5; intros;
    cut
      (((Df x2 /\ x0 <> x2) /\ Dg (f x2) /\ f x0 <> f x2) /\ C_dist x2 x0 < x1);
      auto; intro; generalize (H7 x2 H14); intro;
        generalize (Cminus_eq_contra (f x2) (f x0) H12); intro;
          rewrite
            (Cmult_assoc (g (f x2) - g (f x0)) (/ (f x2 - f x0))
              ((f x2 - f x0) * / (x2 - x0))) in H15;
            rewrite <- (Cmult_assoc (/ (f x2 - f x0)) (f x2 - f x0) (/ (x2 - x0)))
              in H15; rewrite (Cinv_l (f x2 - f x0) H16) in H15.
                  rewrite (Cmult_comm (df x0) (dg (f x0))) ;
                  rewrite Cmult_1_l in H15 ; assumption.
  clear H5 H3 H4 H2; unfold limit1_in in |- *; unfold limit_in in |- *;
    simpl in |- *; unfold limit1_in in H1; unfold limit_in in H1; 
      simpl in H1; intros; elim (H1 eps H2); clear H1; intros; 
        elim H1; clear H1; intros; split with x; split; auto; 
          intros; unfold D_x, Dgf in H4, H3; elim H4; clear H4; 
            intros; elim H4; clear H4; intros; exact (H3 x1 (conj H4 H5)).
Qed.
