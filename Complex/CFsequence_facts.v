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

Require Import Rsequence_def.
Require Import Rinterval Ranalysis_def.
Require Import Rsequence_cv_facts.
Require Import Rsequence_tactics.
Require Import MyRIneq.
Require Import Cfunctions.
Require Import Csequence.
Require Import Csequence_facts.
Require Import CFsequence.
Require Import Cnorm.
Require Import Cprop_base.
Require Import Ctacfield.
Require Import Lia.
Require Import Lra.
Require Import Max.
Require Import Cmet.
Require Import Canalysis_def.
Require Import Canalysis_deriv.

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
 assert (eps_8_pos : 0 < eps / 8) by lra.
 destruct (g_cont z z_in (eps/8)%R eps_8_pos) as [delta1 H] ; clear g_cont ; destruct H as [delta1_pos g_cont].
 assert (delta_pos : 0 < Rmin ((r - (Cnorm (z - c))) / 2) delta1).
  apply Rmin_pos_lt ; [| assumption].
  unfold middle, Rdiv ; apply Rlt_mult_inv_pos ; [| lra].
  apply Rlt_Rminus ; rewrite Cnorm_minus_sym ; apply z_in.

 pose (delta := mkposreal (Rmin ((r - (Cnorm (z - c))) / 2) delta1) (delta_pos)).
 exists delta ; intros h h_neq h_ub.
 pose (eps' :=  ((Cnorm h) * eps / 4)%R).
 assert (eps'_pos : 0 < eps').
  unfold eps', Rdiv ; rewrite Rmult_assoc ; apply Rmult_lt_0_compat ;
  [apply Cnorm_pos_lt ; assumption | lra].
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
  unfold Rdiv ; apply Rmult_le_compat_r ; [lra |] ; apply Rplus_le_compat_r ;
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
  left ; apply Rabs_def1 ; [| apply Rlt_le_trans with R0] ; lra.
  subst ; rewrite Rabs_R1 ; right ; reflexivity.
  apply Rlt_le_trans with (Rplus (Cnorm (c - z)) delta) ;
  [apply Rplus_lt_compat_l ; assumption |].
  apply Rle_trans with (Rplus (Cnorm (c - z)) ((r - Cnorm (z - c)) / 2)) ;
  [apply Rplus_le_compat_l ; unfold delta ; apply Rmin_l |].
  rewrite Cnorm_minus_sym.
  field_simplify ; unfold Rdiv; try rewrite Rinv_1, Rmult_1_r.
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
  left ; apply Rabs_def1 ; [| apply Rlt_le_trans with R0] ; lra.
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
  left ; apply Rabs_def1 ; [| apply Rlt_le_trans with R0] ; lra.
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


Definition SFL_interv : forall (fn:nat -> C -> C) (r:posreal)
  (cv : forall z : C, Boule 0 r z -> {l:C | Cseq_cv (fun N:nat => CFpartial_sum (fun n => fn n z) N) l }) (y:C), C.
Proof.
intros fn r cv z.
 destruct (Rlt_le_dec (Cnorm (0 - z)) r) as [z_bd | z_lb].
 unfold Boule in cv ; simpl in cv ; unfold C_dist in cv ;
 destruct (cv _ z_bd) as (l, _) ; apply l.
 exact 0.
Defined.

Lemma SFL_interv_right : forall fn r cv y, Boule 0 r y ->
     Cseq_cv (fun N:nat => CFpartial_sum (fun n => fn n y) N) (SFL_interv fn r cv y).
Proof.
intros fn r cv z z_bd ; unfold SFL_interv ;
 destruct (Rlt_le_dec (Cnorm (0 - z)) r) as [z_bd2 | z_lb].
 destruct (cv z z_bd2) as [l Hl] ; assumption.
 assert (Hf : Cnorm (0 - z) < Cnorm (0 - z)).
  apply Rlt_le_trans with r ; unfold Boule in * ; assumption.
 elim (Rlt_irrefl _ Hf).
Qed.

Lemma Rlt_minus_exchange : forall a b c, a - b < c -> a - c < b.
Proof.
intros a b c H ; lra.
Qed.

Lemma Rlt_plus_exchange : forall a b c,  a - b < c  -> a < b + c.
Proof.
intros a b c H ; lra.
Qed.

Lemma sum_cv_maj : forall (An : nat -> R) (fn : nat -> C -> C) (z l1 : C) (l2 : R),
       Cseq_cv (fun n : nat => CFpartial_sum (fun n => fn n z) n) l1 ->
       Rseq_cv (fun n : nat => sum_f_R0 An n) l2 ->
       (forall n : nat, Cnorm (fn n z) <= An n) -> Cnorm l1 <= l2.
Proof.
intros An fn z l1 l2 fn_cv An_cv fn_bd.
 destruct (Rle_lt_dec (Cnorm l1) l2) as [H | Hf].
  assumption.
  pose (eps := ((Cnorm l1 - l2) / 4)%R) ;
  assert (eps_pos : 0 < eps).
   unfold eps, Rdiv ; apply Rlt_mult_inv_pos ; lra.
  destruct (fn_cv _ eps_pos) as [Nfn Hfn] ;
  destruct (An_cv _ eps_pos) as [NAn HAn].
  pose (N := max Nfn NAn).
  assert (Main : Cnorm l1 - eps < l2 + eps).
   apply Rlt_trans with (Cnorm (CFpartial_sum (fun n : nat => fn n z) N)).
   apply Rlt_minus_exchange ; apply Rle_lt_trans with (Cnorm (CFpartial_sum (fun n : nat => fn n z) N - l1)) ;
   [apply Cnorm_triang_rev_r | apply Hfn ;  apply le_max_l].
   apply Rle_lt_trans with (Rabs (sum_f_R0 An N)).
   apply Rle_trans with (sum_f_R0 (fun n => Cnorm (fn n z)) N).
   unfold CFpartial_sum ; apply sum_f_C0_triang.
   clear - fn_bd ; induction N.
   simpl ; rewrite Rabs_right ; [| apply Rle_ge ; apply Rle_trans with (Cnorm (fn O z)) ;
   [apply Cnorm_pos |] ] ; apply fn_bd.
   simpl ; rewrite Rabs_right.
   apply Rle_trans with (Rplus (sum_f_R0 An N) (Cnorm (fn (S N) z))) ;
   [apply Rplus_le_compat_r ; rewrite <- Rabs_right ; [apply IHN |] |
   apply Rplus_le_compat_l ; apply fn_bd].
   apply Rle_ge ; apply cond_pos_sum.
   intro n ; apply Rle_trans with (Cnorm (fn n z)) ; [apply Cnorm_pos | apply fn_bd].
   rewrite <- tech5 ; apply Rle_ge ; apply cond_pos_sum.
   intro n ; apply Rle_trans with (Cnorm (fn n z)) ; [apply Cnorm_pos | apply fn_bd].
   apply Rlt_plus_exchange.
   apply Rle_lt_trans with (R_dist (sum_f_R0 An N) l2).
   apply Rle_trans with (Rminus (Rabs (sum_f_R0 An N)) (Rabs l2)).
   replace (Rabs l2) with l2.
   right ; reflexivity.
   symmetry ; apply Rabs_right.
   apply Rle_ge ; apply Rseq_limit_comparison with (fun _ => R0)  (fun n : nat => sum_f_R0 An n).
   intros n ; apply cond_pos_sum ; intro n' ; apply Rle_trans with (Cnorm (fn n' z)) ;
   [apply Cnorm_pos | apply fn_bd].
   intros ; exists O ; intros ; simpl ; unfold R_dist . rewrite Rminus_0_r.
   change R0 with (IZR 0). rewrite Rabs_R0 ; assumption.
   assumption.
   unfold R_dist ; apply Rabs_triang_inv.
   apply HAn ; apply le_max_r.
   assert (Cnorm l1 < Cnorm l1).
   apply Rlt_trans with (l2 + 2 * eps)%R.
   lra.
   unfold eps.
   apply Rle_lt_trans with ((Cnorm l1 + l2) / 2)%R.
   right ; field.
   rewrite Rplus_comm ; apply (middle_is_in_the_middle _ _ Hf).
   elim (Rlt_irrefl _ H).
Qed.

Definition Csigma f low high := sum_f_C0 (fun n : nat => f (low + n)%nat) (high - low).

Lemma   Csigma_split : forall (f : nat -> C) (low high k : nat),
       (low <= k)%nat ->  (k < high)%nat ->
       Csigma f low high = (Csigma f low k + Csigma f (S k) high).
Proof.
intros f low high k l_le_k k_lt_h.
 unfold Csigma.
 apply (proj1 (Ceq _ _)) ; split.
 rewrite <- Cre_add_compat ; do 3 rewrite <- sum_f_C0_Cre_compat.
 assert (H := sigma_split (fun n => Cre (f n))  l_le_k k_lt_h) ;
 unfold sigma in H ; assumption.
 rewrite <- Cim_add_compat ; do 3 rewrite <- sum_f_C0_Cim_compat.
 assert (H := sigma_split (fun n => Cim (f n))  l_le_k k_lt_h) ;
 unfold sigma in H ; assumption.
Qed.

Lemma sum_maj1 : forall (fn : nat -> C -> C) (An : nat -> R) (x l1: C) (l2 : R) (N : nat),
       Cseq_cv (fun n : nat => CFpartial_sum (fun n => fn n x) n) l1 ->
       Rseq_cv (fun n : nat => sum_f_R0 An n) l2 ->
       (forall n : nat, Cnorm (fn n x) <= An n) ->
       Cnorm (l1 - CFpartial_sum (fun n => fn n x) N) <= l2 - sum_f_R0 An N.
Proof.
  intros fn An x l1 l2 N fn_cv An_cv fn_bd ;
    cut { l:C | Cseq_cv (fun n => sum_f_C0 (fun l => fn (S N + l)%nat x) n) l }.
  intro X;
    cut { l:R | Rseq_cv (fun n => sum_f_R0 (fun l => An (S N + l)%nat) n) l }.
  intro X0; elim X; intros l1N H2.
  elim X0; intros l2N H3.
  cut (l1 - CFpartial_sum (fun n => fn n x) N = l1N).
  intro Temp; cut (Rminus l2 (sum_f_R0 An N) = l2N).
  intro Temp2; rewrite Temp, Temp2.
  apply sum_cv_maj with (fun n => An (S N + n)%nat) (fun I => fn (S N + I)%nat) x.
  assumption.
  assumption.
  intro n ; apply fn_bd.
  symmetry ; eapply Rseq_cv_unique.
  apply H3.
  unfold Rseq_cv in An_cv |-* ; intros eps eps_pos ; destruct (An_cv _ eps_pos)
  as [N' HN'] ; exists N' ; intros n n_lb.
  unfold R_dist ; 
    replace (sum_f_R0 (fun l:nat => An (S N + l)%nat) n - (l2 - sum_f_R0 An N))%R
    with (sum_f_R0 An N + sum_f_R0 (fun l:nat => An (S N + l)%nat) n - l2)%R;
      [| ring ].
  replace (sum_f_R0 An N + sum_f_R0 (fun l:nat => An (S N + l)%nat) n)%R with
  (sum_f_R0 An (S (N + n)))%R.
  apply HN' ; intuition lia.
  assert (N_pos : (0 <= N)%nat) by intuition.
  assert (N_ub : (N < S (N + n))%nat) by intuition.
  intros; assert (H := sigma_split An N_pos N_ub) ; unfold sigma in H.
  do 2 rewrite <- minus_n_O in H.
  replace (sum_f_R0 An (S (N + n))) with
  (sum_f_R0 (fun k:nat => An (0 + k)%nat) (S (N + n))).
  replace (sum_f_R0 An N) with (sum_f_R0 (fun k:nat => An (0 + k)%nat) N).
  assert (Hrew : (S (N + n) - S N)%nat = n) by intuition lia.
  rewrite Hrew in H.
  apply H.
  apply sum_eq; intros ;  reflexivity.
  apply sum_eq; intros ;  reflexivity.
  symmetry ; eapply Cseq_cv_unique.
  apply H2.
  unfold Rseq_cv in fn_cv |-* ; intros eps eps_pos ; destruct (fn_cv _ eps_pos)
  as [N' HN'] ; exists N' ; intros n n_lb.
  unfold R_dist ; 
    replace (sum_f_C0 (fun l:nat => fn (S N + l)%nat x) n - (l1 -  CFpartial_sum (fun n0 : nat => fn n0 x) N))
    with ((CFpartial_sum (fun n0 : nat => fn n0 x) N + sum_f_C0 (fun l:nat => fn (S N + l)%nat x) n) - l1);
      [| ring ].
      replace ((CFpartial_sum (fun n0 : nat => fn n0 x) N + sum_f_C0 (fun l:nat => fn (S N + l)%nat x) n))
      with (CFpartial_sum (fun n0 : nat => fn n0 x) (S N + n)%nat).
  apply HN' ; intuition lia.
  assert (N_pos : (0 <= N)%nat) by intuition.
  assert (N_ub : (N < S (N + n))%nat) by intuition.
  intros; assert (H := Csigma_split (fun n => fn n x) O (S (N + n)) N N_pos N_ub) ; unfold Csigma in H.
  do 2 rewrite <- minus_n_O in H.
  replace (CFpartial_sum (fun n0 : nat => fn n0 x) (S N + n)) with
  (sum_f_C0 (fun n : nat => fn (0 + n)%nat x) (S (N + n))).
  replace (CFpartial_sum (fun n0 : nat => fn n0 x) N) with (sum_f_C0 (fun n : nat => fn (0 + n)%nat x) N).
  assert (Hrew : (S (N + n) - S N)%nat = n) by intuition lia.
  rewrite Hrew in H.
  apply H.
  unfold CFpartial_sum ; apply sum_f_C0_eq_seq ; intros ;  reflexivity.
  unfold CFpartial_sum ; apply sum_f_C0_eq_seq ; intros ;  reflexivity.

  exists (l2 - sum_f_R0 An N)%R.
   unfold Rseq_cv in An_cv |-* ; intros eps eps_pos ; destruct (An_cv _ eps_pos)
  as [N' HN'] ; exists N' ; intros n n_lb.
  unfold R_dist ; 
    replace (sum_f_R0 (fun l:nat => An (S N + l)%nat) n - (l2 - sum_f_R0 An N))%R
    with (sum_f_R0 An N + sum_f_R0 (fun l:nat => An (S N + l)%nat) n - l2)%R;
      [| ring ].
  replace (sum_f_R0 An N + sum_f_R0 (fun l:nat => An (S N + l)%nat) n)%R with
  (sum_f_R0 An (S (N + n)))%R.
  apply HN' ; intuition lia.
  assert (N_pos : (0 <= N)%nat) by intuition.
  assert (N_ub : (N < S (N + n))%nat) by intuition.
  intros; assert (H := sigma_split An N_pos N_ub) ; unfold sigma in H.
  do 2 rewrite <- minus_n_O in H.
  replace (sum_f_R0 An (S (N + n))) with
  (sum_f_R0 (fun k:nat => An (0 + k)%nat) (S (N + n))).
  replace (sum_f_R0 An N) with (sum_f_R0 (fun k:nat => An (0 + k)%nat) N).
  assert (Hrew : (S (N + n) - S N)%nat = n) by intuition lia.
  rewrite Hrew in H.
  apply H.
  apply sum_eq; intros ;  reflexivity.
  apply sum_eq; intros ;  reflexivity.

  exists (l1 - CFpartial_sum (fun n => fn n x) N).

 intros eps eps_pos ; destruct (fn_cv _ eps_pos) as [N' HN'] ; exists N' ; intros n n_lb.

    replace (sum_f_C0 (fun l:nat => fn (S N + l)%nat x) n - (l1 -  CFpartial_sum (fun n0 : nat => fn n0 x) N))
    with ((CFpartial_sum (fun n0 : nat => fn n0 x) N + sum_f_C0 (fun l:nat => fn (S N + l)%nat x) n) - l1);
      [| ring ].
      replace ((CFpartial_sum (fun n0 : nat => fn n0 x) N + sum_f_C0 (fun l:nat => fn (S N + l)%nat x) n))
      with (CFpartial_sum (fun n0 : nat => fn n0 x) (S N + n)%nat).
  apply HN' ; intuition lia.
  assert (N_pos : (0 <= N)%nat) by intuition.
  assert (N_ub : (N < S (N + n))%nat) by intuition.
  intros; assert (H := Csigma_split (fun n => fn n x) O (S (N + n)) N N_pos N_ub) ; unfold Csigma in H.
  do 2 rewrite <- minus_n_O in H.
  replace (CFpartial_sum (fun n0 : nat => fn n0 x) (S N + n)) with
  (sum_f_C0 (fun n : nat => fn (0 + n)%nat x) (S (N + n))).
  replace (CFpartial_sum (fun n0 : nat => fn n0 x) N) with (sum_f_C0 (fun n : nat => fn (0 + n)%nat x) N).
  assert (Hrew : (S (N + n) - S N)%nat = n) by intuition lia.
  rewrite Hrew in H.
  apply H.
  unfold CFpartial_sum ; apply sum_f_C0_eq_seq ; intros ;  reflexivity.
  unfold CFpartial_sum ; apply sum_f_C0_eq_seq ; intros ;  reflexivity.
Qed.

Lemma CVN_CVU_boule :forall (fn : nat -> C -> C) (r : posreal)
       (cv : forall z : C,  Boule 0 r z -> {l : C | Cseq_cv (fun N : nat => CFpartial_sum (fun n => fn n z) N) l}),
       CVN_r fn r ->
       CFseq_cvu (fun N  z => CFpartial_sum (fun n => fn n z) N) (SFL_interv fn r cv) 0 r.
Proof.
intros fn r cv cvn eps eps_pos.

 destruct cvn as [An [l [sum_cv fn_bd]]] ;
 destruct (sum_cv eps eps_pos) as [N HN] ;
 exists N ; intros n y n_lb y_bd.
 unfold SFL_interv.
 destruct (Rlt_le_dec (Cnorm (0 - y)) r) as [y_bd2 | y_lb].

  destruct (cv y y_bd2) as [l2 Hl2] ; unfold C_dist.

 apply Rle_lt_trans with (Rabs (sum_f_R0 (fun k => Cnorm (An k)) n - l)).
  rewrite <- (Rabs_Ropp (sum_f_R0 (fun k:nat => Cnorm (An k)) n - l));
    rewrite Ropp_minus_distr';
      rewrite (Rabs_right (l - sum_f_R0 (fun k:nat => Cnorm (An k)) n)).
  rewrite Cnorm_minus_sym ; eapply sum_maj1.
  apply Hl2.
  apply sum_cv.
  intros ; apply fn_bd ; assumption.
  apply Rge_minus ; apply Rle_ge ; apply sum_incr.
  assumption.
  intros ; apply Cnorm_pos.
  unfold R_dist in HN ; apply HN ; assumption.

unfold Boule in y_bd ; simpl in y_bd ; unfold C_dist in y_bd.
 assert (Hf : Cnorm (0 - y) < Cnorm (0 - y)).
  apply Rlt_le_trans with r ; assumption.
 destruct (Rlt_irrefl _ Hf).
Qed.

Lemma CVU_continuity_boule :forall (fn : nat -> C -> C) (f : C -> C) (c : C) (r : posreal),
       CFseq_cvu fn f c r ->
       (forall n z, Boule c r z -> continuity_pt (fn n) z) ->
       forall z, Boule c r z -> continuity_pt f z.
Proof.
intros fn f c r fn_cvu fn_cont z z_in.
 intros eps eps_pos ; assert (eps_3_pos : 0 < (eps / 3)%R) by lra ;
 destruct (fn_cvu _ eps_3_pos) as [N HN] ;
 destruct (fn_cont N z z_in _ eps_3_pos) as [delta1 [delta1_pos Hdelta]].
 pose (delta := Rmin delta1 ((r - Cnorm (c - z))/2)) ;
 assert (delta_pos : 0 < delta).
  unfold delta ; apply Rmin_pos_lt.
  assumption.
  unfold Rdiv ; apply Rlt_mult_inv_pos ; [apply Rlt_Rminus ; apply z_in | lra].
  exists delta ; split ; [assumption | intros x [_  Hx]].
  simpl ; unfold C_dist.
  apply Rle_lt_trans with (Cnorm (f x - fn N x) + Cnorm (fn N x - fn N z) + Cnorm (fn N z  - f z))%R.
  replace (f x - f z)%C with ((f x - fn N x) + (fn N x - fn N z) + (fn N z - f z))%C by ring.
  apply Rle_trans with (Cnorm ((f x - fn N x) + (fn N x - fn N z)) + Cnorm (fn N z - f z))%R ;
  [| apply Rplus_le_compat_r] ;  apply Cnorm_triang.
  apply Rlt_trans with (Cnorm (f x - fn N x) + Cnorm (fn N x - fn N z) + (eps/3))%R.
  apply Rplus_lt_compat_l ; apply HN ; trivial.
  apply Rlt_trans with (eps/3 + Cnorm (fn N x - fn N z) + eps / 3)%R.
  do 2 apply Rplus_lt_compat_r ; rewrite Cnorm_minus_sym ; apply HN ; trivial.
 unfold Boule in * ; simpl in * ; unfold C_dist in *.
 replace (c - x)%C with ((c - z) + - (x - z))%C by ring.
 apply Rle_lt_trans with (Cnorm (c - z) + Cnorm (- (x - z)))%R ;
 [apply Cnorm_triang | rewrite Cnorm_opp].
 apply Rlt_trans with (Cnorm (c - z) + delta)%R ;
 [apply Rplus_lt_compat_l ; assumption |].
 apply Rle_lt_trans with (Cnorm (c - z) +  (r - Cnorm (c - z))/2)%R ;
 [apply Rplus_le_compat_l ; apply Rmin_r |].
 field_simplify ; unfold Rdiv ; try rewrite Rinv_1, Rmult_1_r.
 apply (middle_is_in_the_middle _ _ z_in).
 destruct (Ceq_dec x z) as [eq | neq].
 subst ; unfold Cminus ; rewrite Cadd_opp_r, Cnorm_C0 ; lra.
 apply Rlt_le_trans with (eps/3 + eps/3 + eps/3)%R ; [| right ; field].
 apply Rplus_lt_compat_r ; apply Rplus_lt_compat_l ; simpl in Hdelta ; apply Hdelta ; split.
 unfold Cderiv.D_x, no_cond ; split ; auto.
 apply Rlt_le_trans with delta ; [apply Hx | unfold delta ; apply Rmin_l].
Qed.
