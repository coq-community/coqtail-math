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

Require Import Ranalysis_def.
Require Import MyRIneq.
Require Import Canalysis_def.
Require Import Canalysis_deriv.
Require Import CFsequence.
Require Import Cnorm.
Require Import Cprop_base.
Require Import Ctacfield.
Require Import Fourier.
Require Import Max.

Open Scope C_scope.

Lemma CFseq_cvu_derivable : forall (fn fn' : nat -> C -> C) (f g : C -> C) (z c : C) (r : posreal)
      (z_in : Boule c r z),
      (forall (x:C) (n:nat), Boule c r x -> derivable_pt_lim (fn n) x (fn' n x)) ->
      (CFseq_cv_boule fn f c r) ->
      (CFseq_cvu fn' g c r) ->
      (forall (x:C), Boule c r x -> continuity_pt g x) ->
      derivable_pt_lim f z (g z).
Proof.
intros fn fn' f g z c r z_in Dfn_eq_fn' fn_cv_f fn'_cvu_g g_cont eps eps_pos.
 assert (eps_8_pos : 0 < eps / 8) by fourier.
 destruct (g_cont z z_in (eps/8)%R eps_8_pos) as [delta1 H] ; clear g_cont ; destruct H as [delta1_pos g_cont].
 assert (delta_pos : 0 < Rmin ((r - (Cnorm (z - c))) / 2) delta1).
  apply Rmin_pos ; [| assumption].
  unfold middle, Rdiv ; apply Rlt_mult_inv_pos ; [| fourier].
  apply Rlt_Rminus ; rewrite Cnorm_minus_sym ; apply z_in.

 pose (delta := mkposreal (Rmin ((r - (Cnorm (z - c))) / 2) delta1) (delta_pos)).
 exists delta ; intros h h_neq h_ub.
 pose (eps' :=  ((Cnorm h) * eps / 4)%R).
 assert (eps'_pos : 0 < eps').
  unfold eps', Rdiv ; rewrite Rmult_assoc ; apply Rmult_lt_0_compat ;
  [apply Cnorm_pos_lt ; assumption | fourier].
 destruct (fn_cv_f z z_in eps' eps'_pos) as [Nz fnz_cv_fz].

assert (zh_in : Boule c r (z + h)).
 unfold Boule ; simpl ; unfold C_dist.
  unfold Cminus ; rewrite Copp_add_distr ; unfold Cminus ; rewrite <- Cadd_assoc ;
  apply Rle_lt_trans with (Cnorm (c - z) + Cnorm (-h))%R.
  apply Cnorm_triang.
  rewrite Cnorm_opp, Cnorm_minus_sym.
  apply Rlt_le_trans with (Cnorm (z - c) + delta)%R.
  apply Rplus_lt_compat_l ; assumption.
  apply Rle_trans with (Cnorm (z - c) + ((r - (Cnorm (z - c))) / 2))%R.
  apply Rplus_le_compat_l ; unfold delta ; apply Rmin_l.
  apply Rle_trans with ((Cnorm (z - c) + r) / 2)%R.
  right ; field.
  apply Rle_trans with ((r + r) / 2)%R.
  unfold Rdiv ; apply Rmult_le_compat_r ; [fourier |] ; apply Rplus_le_compat_r ;
  rewrite Cnorm_minus_sym ; left ; apply z_in.
  right ; field.

 destruct (fn_cv_f (z + h) zh_in eps' eps'_pos) as [Nzh fnzh_cv_fzh] ; clear fn_cv_f.

 destruct (fn'_cvu_g (eps/8)%R eps_8_pos) as [Ng fn'c_cvu_gc] ; clear fn'_cvu_g.

 pose (N := max (max Nz Nzh) Ng).
 assert (Main : Cnorm ((f (z+h) - fn N (z+h)) - (f z - fn N z) + (fn N (z+h) - fn N z - h * (g z))) < (Cnorm h)*eps).
 apply Rle_lt_trans with (Rplus (Cnorm (f (z + h) - fn N (z + h) - (f z - fn N z))) (Cnorm ((fn N (z + h) - fn N z - h * g z)))).
 apply Cnorm_triang.
 apply Rle_lt_trans with (Rplus (Rplus (Cnorm (f (z + h) - fn N (z + h))) (Cnorm (- (f z - fn N z))))
                                                            (Cnorm (fn N (z + h) - fn N z - h * g z))).
 apply Rplus_le_compat_r ; apply Cnorm_triang.
 rewrite Cnorm_opp.

apply Rlt_le_trans with (Rplus (Rplus eps' (Cnorm (f z - fn N z)))  (Cnorm (fn N (z + h) - fn N z - h * g z))).
 do 2 apply Rplus_lt_compat_r ; rewrite Cnorm_minus_sym ; apply fnzh_cv_fzh.
 unfold ge ; apply le_trans with (max Nz Nzh)%nat ; [apply le_max_r | apply le_max_l].

apply Rle_trans with (Rplus (Rplus eps' eps') (Cnorm (fn N (z + h) - fn N z - h * g z))).
 apply Rplus_le_compat_r ; apply Rplus_le_compat_l ; left ; rewrite Cnorm_minus_sym ;
 apply fnz_cv_fz ; unfold ge ; apply le_trans with (max Nz Nzh)%nat ; apply le_max_l.

apply Rle_trans with (Cnorm h * eps / 2 + Cnorm h * eps / 2)%R.
 apply Rle_trans with (Cnorm h * eps / 4 + Cnorm h * eps / 4 + Cnorm h * eps / 2)%R.
 apply Rplus_le_compat_l.

 assert (Interval_to_boule : forall (t: R), interval 0 1 t -> Boule c r (z + t * h)).
  intros t t_in ; unfold Boule ; simpl ; unfold C_dist.
  replace (c - (z + t * h)) with ((c - z) + - (t*h)).
  apply Rle_lt_trans with (Rplus (Cnorm (c - z)) (Cnorm (- (t*h)))) ;
  [apply Cnorm_triang | rewrite Cnorm_opp, Cnorm_Cmult].
  apply Rle_lt_trans with (Rplus (Cnorm (c - z)) (Cnorm h)).
  apply Rplus_le_compat_l ; rewrite <- Rmult_1_l ; apply Rmult_le_compat_r ;
  [apply Cnorm_pos | rewrite Cnorm_IRC_Rabs].
  clear -t_in ; destruct t_in as [t_lb [t_eq | t_ub]].
  left ; apply Rabs_def1 ; [| apply Rlt_le_trans with R0] ; fourier.
  subst ; rewrite Rabs_R1 ; right ; reflexivity.
  apply Rlt_le_trans with (Rplus (Cnorm (c - z)) delta) ;
  [apply Rplus_lt_compat_l ; assumption |].
  apply Rle_trans with (Rplus (Cnorm (c - z)) ((r - Cnorm (z - c)) / 2)) ;
  [apply Rplus_le_compat_l ; unfold delta ; apply Rmin_l |].
  rewrite Cnorm_minus_sym.
  field_simplify ; unfold Rdiv ; rewrite Rinv_1, Rmult_1_r.
  unfold Boule in z_in ; simpl in z_in ; unfold C_dist in z_in ;
  left ; rewrite Cnorm_minus_sym ;
 apply (proj2 (middle_is_in_the_middle _ _ z_in)).
 unfold Cminus ; rewrite Copp_add_distr ;
 rewrite Cadd_assoc ; reflexivity.


 assert (fn_deriv : forall t : R, interval 0 1 t -> derivable_pt (fn N) (z + t * h)).
  intros ; exists (fn' N (z + t * h)) ; apply Dfn_eq_fn'.
  apply Interval_to_boule ; assumption.

 destruct (MVT_Cre (fn N) z h fn_deriv h_neq) as [u [u_in_I Hu_bd]].
 destruct (MVT_Cim (fn N) z h fn_deriv h_neq) as [v [v_in_I Hv_bd]].

 apply Rle_trans with (Rmult (Cnorm h) (Rmult (Cnorm (fn N (z + h) - fn N z - h * g z)) (/ Cnorm h))).
 right ; field ; apply Cnorm_no_R0 ; assumption.

 unfold Rdiv ; rewrite Rmult_assoc ; apply Rmult_le_compat_l ;
 [apply Cnorm_pos |] ; rewrite <- Cnorm_inv, <- Cnorm_Cmult ; [| assumption].
 rewrite Cmult_minus_distr_r ; replace (h * g z * / h) with (g z) ; [| field ; assumption].
 rewrite <- Cproj_right with ((fn N (z + h) - fn N z) * / h), <- Cproj_right with (g z).
 apply Rle_trans with (Cnorm (Rminus (Cre ((fn N (z + h) - fn N z) * / h))  (Cre (g z)),
                                                    Rminus (Cim ((fn N (z + h) - fn N z) * / h)) (Cim (g z)))).
  right ; apply Cnorm_eq_compat ; CusingR.

apply Rle_trans with (Rplus (Cnorm ((Cre ((fn N (z + h)%C - fn N z) * / h) - Cre (g z))%R, R0))
        (Cnorm ((R0 , (Cim ((fn N (z + h)%C - fn N z) * / h) - Cim (g z))%R)))).
 apply Rle_trans with (Cnorm (((Cre ((fn N (z + h)%C - fn N z) * / h) - Cre (g z))%R, R0)
   + (R0, (Cim ((fn N (z + h)%C - fn N z) * / h) - Cim (g z))%R))).
  right ; apply Cnorm_eq_compat ; CusingR.
  apply Cnorm_triang.
 rewrite Cnorm_Cre_simpl, Cnorm_Cim_simpl.
 unfold Cdiv in Hu_bd, Hv_bd ; rewrite Hu_bd, Hv_bd.

apply Rle_trans with (eps/4 + Rabs (Cim (derive_pt (fn N) (z + v * h) (fn_deriv v v_in_I)) - Cim (g z)))%R.
apply Rplus_le_compat_r.
apply Rle_trans with (Rabs ((Cre (derive_pt (fn N) (z + u * h) (fn_deriv u u_in_I)) - Cre (g (z + u * h)))
                                                      +  (Cre (g (z + u * h)) - Cre (g z)))).
 right ; apply Rabs_eq_compat ; ring.
 apply Rle_trans with (Rplus (Rabs (Cre (derive_pt (fn N) (z + u * h) (fn_deriv u u_in_I)) - Cre (g (z + u * h))))
                                (Rabs (Cre (g (z + u * h)) - Cre (g z)))) ; [apply Rabs_triang |].
 do 2 rewrite Cre_minus_compat.
 apply Rle_trans with (Rplus (Cnorm (derive_pt (fn N) (z + u * h) (fn_deriv u u_in_I) - g (z + u * h)))
                                (Rabs (Cre (g (z + u * h) - g z)))).
 apply Rplus_le_compat_r ; apply Cre_le_Cnorm.
 apply Rle_trans with (Rplus (Cnorm (derive_pt (fn N) (z + u * h) (fn_deriv u u_in_I) - g (z + u * h)))
                                (Cnorm (g (z + u * h) - g z))).
 apply Rplus_le_compat_l ; apply Cre_le_Cnorm.

apply Rle_trans with (Rplus (eps / 8) (Cnorm (g (z + u * h) - g z))).
apply Rplus_le_compat_r.

assert (zuh_in : Boule c r (z + u *h)).
 apply Interval_to_boule ; assumption.
 rewrite (derive_pt_eq_0 _ _ _ (fn_deriv u u_in_I) (Dfn_eq_fn' _ N zuh_in)).
 unfold C_dist in fn'c_cvu_gc ; left ; apply fn'c_cvu_gc ;
 [unfold N ; apply le_max_r |] ; assumption.

apply Rle_trans with (eps / 8 + eps / 8)%R ; [apply Rplus_le_compat_l | right ; field].

destruct (proj1 u_in_I) as [u_neq | u_eq].

left ; simpl in g_cont ; unfold C_dist in g_cont ; apply g_cont ; split.
unfold Cderiv.D_x, no_cond ; split ; [trivial |].
 clear - u_neq h_neq.
 intro Hf ; symmetry in Hf ; generalize Hf ; clear Hf ; apply Cadd_neq_compat_l.
 apply  Cmult_integral_contrapositive_currified ;
 [apply IRC_neq_compat ; apply Rgt_not_eq |] ; assumption.

 replace (z + u * h - z) with (u * h).
 rewrite Cnorm_Cmult ; apply Rlt_le_trans with (1 * delta)%R.
 apply Rlt_le_trans with (Cnorm u * delta)%R.
 apply Rmult_lt_compat_l ; [apply Cnorm_pos_lt ; apply IRC_neq_compat ;
 apply Rgt_not_eq |] ; assumption.
 apply Rmult_le_compat_r ; [left ; assumption |].
 rewrite Cnorm_IRC_Rabs.
  clear -u_in_I ; destruct u_in_I as [u_lb [u_eq | u_ub]].
  left ; apply Rabs_def1 ; [| apply Rlt_le_trans with R0] ; fourier.
  subst ; rewrite Rabs_R1 ; right ; reflexivity.
  rewrite Rmult_1_l ; unfold delta ; apply Rmin_r.

 ring.

subst ; rewrite Cmult_0_l, Cadd_0_r ; unfold Cminus ; rewrite Cadd_opp_r, Cnorm_C0 ;
 left ; assumption.



apply Rle_trans with (eps / 4 +  eps/4)%R ; [apply Rplus_le_compat_l | right ; field].

apply Rle_trans with (Rabs ((Cim (derive_pt (fn N) (z + v * h) (fn_deriv v v_in_I)) - Cim (g (z + v * h)))
                                                      +  (Cim (g (z + v * h)) - Cim (g z)))).
 right ; apply Rabs_eq_compat ; ring.
 apply Rle_trans with (Rplus (Rabs (Cim (derive_pt (fn N) (z + v * h) (fn_deriv v v_in_I)) - Cim (g (z + v * h))))
                                (Rabs (Cim (g (z + v * h)) - Cim (g z)))) ; [apply Rabs_triang |].
 do 2 rewrite Cim_minus_compat.
 apply Rle_trans with (Rplus (Cnorm (derive_pt (fn N) (z + v * h) (fn_deriv v v_in_I) - g (z + v * h)))
                                (Rabs (Cim (g (z + v * h) - g z)))).
 apply Rplus_le_compat_r ; apply Cim_le_Cnorm.
 apply Rle_trans with (Rplus (Cnorm (derive_pt (fn N) (z + v * h) (fn_deriv v v_in_I) - g (z + v * h)))
                                (Cnorm (g (z + v * h) - g z))).
 apply Rplus_le_compat_l ; apply Cim_le_Cnorm.

apply Rle_trans with (Rplus (eps / 8) (Cnorm (g (z + v * h) - g z))).
apply Rplus_le_compat_r.

assert (zvh_in : Boule c r (z + v *h)).
 apply Interval_to_boule ; assumption.
 rewrite (derive_pt_eq_0 _ _ _ (fn_deriv v v_in_I) (Dfn_eq_fn' _ N zvh_in)).
 unfold C_dist in fn'c_cvu_gc ; left ; apply fn'c_cvu_gc ;
 [unfold N ; apply le_max_r |] ; assumption.

apply Rle_trans with (eps / 8 + eps / 8)%R ; [apply Rplus_le_compat_l | right ; field].

destruct (proj1 v_in_I) as [v_neq | v_eq].

left ; simpl in g_cont ; unfold C_dist in g_cont ; apply g_cont ; split.
unfold Cderiv.D_x, no_cond ; split ; [trivial |].
 clear - v_neq h_neq.
 intro Hf ; symmetry in Hf ; generalize Hf ; clear Hf ; apply Cadd_neq_compat_l.
 apply  Cmult_integral_contrapositive_currified ;
 [apply IRC_neq_compat ; apply Rgt_not_eq |] ; assumption.

 replace (z + v * h - z) with (v * h).
 rewrite Cnorm_Cmult ; apply Rlt_le_trans with (1 * delta)%R.
 apply Rlt_le_trans with (Cnorm v * delta)%R.
 apply Rmult_lt_compat_l ; [apply Cnorm_pos_lt ; apply IRC_neq_compat ;
 apply Rgt_not_eq |] ; assumption.
 apply Rmult_le_compat_r ; [left ; assumption |].
 rewrite Cnorm_IRC_Rabs.
  clear -v_in_I ; destruct v_in_I as [v_lb [v_eq | v_ub]].
  left ; apply Rabs_def1 ; [| apply Rlt_le_trans with R0] ; fourier.
  subst ; rewrite Rabs_R1 ; right ; reflexivity.
  rewrite Rmult_1_l ; unfold delta ; apply Rmin_r.

 ring.

subst ; rewrite Cmult_0_l, Cadd_0_r ; unfold Cminus ; rewrite Cadd_opp_r, Cnorm_C0 ;
 left ; assumption.

right ; field.
right ; field.

apply Rle_lt_trans with (Rmult (Cnorm ((f (z + h)  - f z) - h * g z)) (/ Cnorm h)).
rewrite <- Cnorm_inv, <- Cnorm_Cmult ; [| assumption] ; right ; apply Cnorm_eq_compat ;
 field ; assumption.

apply Rle_lt_trans with (Rmult (Cnorm (f (z + h) - fn N (z + h) - (f z - fn N z) +
          (fn N (z + h) - fn N z - h * g z))) (/ Cnorm h)).
right ; apply Rmult_eq_compat_r ; apply Cnorm_eq_compat ; ring.

apply Rlt_le_trans with ((Cnorm h * eps) * / Cnorm h)%R.
apply Rmult_lt_compat_r ; [rewrite <- Cnorm_inv ; [apply Cnorm_pos_lt ;
 apply Cinv_neq_0_compat |] |] ; assumption.

 right ; field ; apply Cnorm_no_R0 ; assumption.
Qed.