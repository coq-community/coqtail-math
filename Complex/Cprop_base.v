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
Require Import Cbase.
Require Import Cpow.
Require Import Lia.

(** * Decidability lemmas *)

Lemma Ceq_dec : forall z1 z2 : C, {z1 = z2} + {z1 <> z2}.
Proof.
intros z1 z2 ; destruct z1 as (r1, r2) ; destruct z2 as (r3, r4).
destruct Req_or_neq with (r1- r3)%R; destruct Req_or_neq with (r2 - r4)%R.
   left; CusingR.
  right ; intro Habs ; apply Ceq in Habs ; destruct Habs ; auto with real.
 right ; intro Habs ; apply Ceq in Habs ; destruct Habs ; auto with real.
right ; intro Habs ; apply Ceq in Habs ; destruct Habs ; auto with real.
Qed.

Lemma Ceq_or_neq_C0 : forall z : C, {z = C0} + {z <> C0}.
Proof.
intro z ; apply Ceq_dec.
Qed.

(** * Good relations on Cre Cim*)

Lemma Cre_mult_compat_l : forall (a:R) (b:C), (Cre (a * b) = a * Cre b)%R.
Proof.
intros a b.
 CusingR_rec.
 simpl ; field.
Qed.

Lemma Cre_mult_compat_r : forall (a:C) (b:R), (Cre (a * b) = (Cre a) * b)%R.
Proof.
intros a b.
 CusingR_rec.
 simpl ; field.
Qed.

Lemma Cim_mult_compat_l : forall (a:R) (b:C), (Cim (a * b) = a * Cim b)%R.
Proof.
intros a b.
 CusingR_rec.
 simpl ; field.
Qed.

Lemma Cim_mult_compat_r : forall (a:C) (b:R), (Cim (a * b) = (Cim a) * b)%R.
Proof.
intros a b.
 CusingR_rec.
 simpl ; field.
Qed.

Lemma  Cre_add_distr : forall a b : C, Cre (a + b) = (Cre a + Cre b)%R .
Proof.
intros a b.
CusingR_rec; simpl.
reflexivity.
Qed.

Lemma Cim_add_distr : forall a b : C, Cim (a + b) = (Cim a + Cim b)%R .
Proof.
intros a b.
CusingR_rec; simpl.
reflexivity.
Qed.

(** *** Compatibility of functions with equalities (Hint database) *)

Lemma Ceq_dec_prop : forall z1 z2 : C, z1 = z2 \/ z1 <> z2.
Proof.
intros z1 z2 ; case (Ceq_dec z1 z2) ; intro H ; [left | right] ; assumption.
Qed.
Hint Resolve Ceq_dec_prop: complex.

(** * IRC *)

Lemma eq_IRC_compat : forall (r r' : R), IRC r = IRC r' -> (r = r')%R.
Proof.
intros r r' T ; destruct (proj2 (Ceq _ _) T) as [H _] ; assumption.
Qed.

Lemma IRC_eq_compat : forall (r r' : R), (r = r')%R -> r = r'.
Proof.
intros ; subst ; reflexivity.
Qed.
Hint Resolve IRC_eq_compat: complex.

(** * Addition *)

Lemma Cadd_ne : forall z, z + C0 = z /\ C0 + z = z.
Proof.
intros.
rewrite Cadd_0_r.
rewrite Cadd_0_l.
split ; reflexivity.  
Qed.
Hint Resolve Cadd_ne: complex.

Definition f_equal_C := f_equal (A:=C).
Hint Resolve f_equal_C: complex.

Lemma Cadd_eq_compat_l : forall z z1 z2, z1 = z2 -> z + z1 = z + z2.
Proof.
intros; subst; trivial.
Qed.
Hint Resolve Cadd_eq_compat_l: complex.

Lemma Cadd_eq_compat_r : forall z z1 z2, z1 = z2 -> z1 + z = z2 + z.
Proof.
intros; subst; trivial.
Qed.
Hint Resolve Cadd_eq_compat_r: complex.

Lemma Cadd_eq_compat a b c d : a = c -> b = d -> a + b = c + d.
Proof.
intros; subst; trivial.
Qed.
Hint Resolve Cadd_eq_compat: complex.

Lemma Cadd_eq_reg_l : forall z z1 z2, z + z1 = z + z2 -> z1 = z2.
Proof.
intros z z1 z2 H.
destruct z as (r, r0) ; destruct z1 as (r1, r2) ; destruct z2 as (r3, r4).
simpl in *.
apply ( (Ceq _ _)) in H. destruct H. simpl in *.
apply Rplus_eq_reg_l in H. apply Rplus_eq_reg_l in H0. 
rewrite H; rewrite H0.
reflexivity.
Qed.
Hint Resolve Cadd_eq_reg_l: complex.

Lemma Cadd_eq_reg_r : forall z z1 z2, z1 + z = z2 + z -> z1 = z2.
Proof.
intros z z1 z2 H.
apply Cadd_eq_reg_l with z.
rewrite Cadd_comm.
rewrite H.
apply Cadd_comm.
Qed.
Hint Resolve Cadd_eq_reg_r : complex.

(** * Multiplication *)

Lemma Cmult_0_r : forall z, z * C0 = C0.
Proof.
CusingR_f.
Qed.
Hint Resolve Cmult_0_r: complex.

Lemma Cmult_0_l : forall z, C0 * z = C0.
Proof.
intro.
rewrite Cmult_comm; apply Cmult_0_r.
Qed.
Hint Resolve Cmult_0_l: complex.

Lemma Cmult_eq_compat_l : forall z z1 z2 : C, z1 = z2 -> z * z1 = z * z2.
Proof.
intros z z1 z2 H.
rewrite H ; reflexivity.
Qed.
Hint Resolve Cmult_eq_compat_l : complex.

Lemma Cmult_eq_compat_r : forall z z1 z2 : C, z1 = z2 -> z1 * z = z2 * z.
Proof.
intros z z1 z2 H.
rewrite H ; reflexivity.
Qed.
Hint Resolve Cmult_eq_compat_r : complex.

Lemma Cmult_eq_reg_l : forall z z1 z2 : C, z <> C0 -> z * z1 = z * z2 -> z1 = z2.
Proof.
intros z z1 z2 H0 H.
assert (H1 : (/ z * z * z1 = z1)).
 rewrite Cinv_l . apply Cmult_1_l . exact H0.
assert (H2 : (/ z * z * z2 = z2)).
 rewrite Cinv_l . apply Cmult_1_l . exact H0.
rewrite <- H1.
rewrite Cmult_assoc. rewrite H.
rewrite <- Cmult_assoc; apply H2.
Qed.

Lemma Cmult_eq_reg_r : forall z z1 z2 : C, z <> C0 -> z1 * z = z2 * z -> z1 = z2.
Proof.
intros z z1 z2 H H1.
apply Cmult_eq_reg_l with z.
exact H.
rewrite Cmult_comm ; rewrite H1 ; apply Cmult_comm.
Qed.

Lemma Cmult_integral : forall z1 z2, z1 * z2 = C0 -> z1 = C0 \/ z2 = C0.
Proof.
intros z1 z2 H.
elim (Ceq_dec z1 C0) ; elim (Ceq_dec z2 C0) ; intros H2 H1.
    left ; exact H1.
   left ; exact H1.
  right ; exact H2.
 rewrite <- (Cmult_0_r z1) in H ; apply Cmult_eq_reg_l in H.
  right ; assumption.
 assumption.
Qed.

Lemma Cmult_eq_0_compat : forall z1 z2 : C, z1 = C0 \/ z2 = C0 -> z1 * z2 = C0.
Proof.
intros z1 z2 H; elim H ; intros H1.
 rewrite H1 ; rewrite Cmult_0_l ; reflexivity.
rewrite H1 ; rewrite Cmult_0_r ; reflexivity.
Qed.
Hint Resolve Cmult_eq_0_compat: complex.

Lemma Cmult_eq_0_compat_r : forall z1 z2 : C, z1 = C0 -> z1 * z2 = C0.
Proof.
auto with complex.
Qed.

Lemma Cmult_eq_0_compat_l : forall z1 z2 : C, z2 = C0 -> z1 * z2 = C0.
Proof.
auto with complex.
Qed.

Lemma Cmult_neq_0_reg : forall z1 z2 : C, z1 * z2 <> C0 -> z1 <> C0 /\ z2 <> C0.
Proof.
auto 6 with complex.
Qed.

Lemma Cmult_integral_contrapositive : 
   forall z1 z2 : C, z1 <> C0 /\ z2 <> C0 -> z1 *  z2 <> C0.
Proof.
intros z1 z2 H.
destruct H as (H1, H2).
intro H ; apply H1 ; apply Cmult_integral in H ; elim H ; intro Hdet.
 exact Hdet.
rewrite Hdet in H2 ; destruct H2 ; reflexivity.
Qed.
Hint Resolve Cmult_integral_contrapositive: complex.

Lemma Cmult_integral_contrapositive_currified : 
  forall z1 z2 : C, z1 <> C0 -> z2 <> C0 -> z1 * z2 <> C0.
Proof.
auto with complex.
Qed.

(** * Opposite *)

Lemma Copp_eq_compat : forall z1 z2 : C, z1 = z2 -> - z1 = - z2.
Proof.
auto with complex.
Qed.
Hint Resolve Copp_eq_compat: complex.

Lemma Copp_0 : -C0 = C0.
Proof.
rewrite <- Ceq ; simpl ; rewrite Ropp_0 ; split ; trivial.
Qed.
Hint Resolve Copp_0: complex.

Lemma Copp_eq_0_compat : forall z : C, z = C0 -> - z = C0.
Proof.
intros z H; rewrite H ; apply Copp_0.
Qed.
Hint Resolve Copp_eq_0_compat: complex.

Lemma Copp_involutive : forall z : C, - - z = z.
Proof.
CusingR.
Qed.
Hint Resolve Copp_involutive: complex.

Lemma Copp_neq_0_compat : forall z : C, z <> C0 -> - z <> C0.
Proof.
intros z H Habs.
apply Copp_eq_0_compat in Habs.
rewrite Copp_involutive in Habs.
apply H ; assumption.
Qed.
Hint Resolve Copp_neq_0_compat: complex.

Lemma Copp_add_distr : forall z1 z2 : C, - (z1 + z2) = - z1 + - z2.
Proof.
CusingR.
Qed.
Hint Resolve Copp_add_distr: complex.

(** * Opposite and multiplication*)

Lemma Cmult_opp_1_opp : forall z, -1 * z = -z.
Proof.
intro z ; CusingR_f.
Qed.
Hint Resolve Cmult_opp_1_opp: complex.

Lemma Copp_mult_distr_l_reverse : forall z1 z2 : C, - z1 * z2 = - (z1 * z2).
Proof.
CusingR_f.
Qed.
Hint Resolve Copp_mult_distr_l_reverse: complex.

Lemma Cmult_opp_opp : forall z1 z2 : C, - z1 * - z2 = z1 * z2.
Proof.
CusingR_f.
Qed.
Hint Resolve Cmult_opp_opp: complex.

Lemma Copp_mult_distr_r_reverse : forall z1 z2 : C, z1 * - z2 = - (z1 * z2).
Proof.
CusingR_f.
Qed.

(** * Minus *)

Lemma Cminus_0_r : forall z : C, z - C0 = z.
Proof.
CusingR_f.
Qed.
Hint Resolve Cminus_0_r: complex.

Lemma Cminus_0_l : forall z : C, C0 - z = - z.
Proof.
CusingR.
Qed.
Hint Resolve Cminus_0_l : complex.

Lemma Copp_minus_distr : forall z1 z2 : C, - (z1 - z2) = z2 - z1.
Proof.
CusingR_f.
Qed.
Hint Resolve Copp_minus_distr: complex.

Lemma Copp_minus_distr' : forall z1 z2 : C, - (z2 - z1) = z1 - z2.
Proof.
CusingR_f.
Qed.

Lemma Cminus_diag_eq : forall z1 z2 : C, z1 = z2 -> z1 - z2 = C0.
Proof.
intros z1 z2 H ; destruct H ; CusingR.
Qed.
Hint Resolve Cminus_diag_eq: complex.

Lemma Cminus_diag_uniq : forall z1 z2 : C, z1 - z2 = C0 -> z1 = z2.
Proof.
intros z1 z2 H.
destruct z1 as (r, r0) ; destruct z2 as (r1, r2) ; rewrite <-Ceq in H ; rewrite <-Ceq ; simpl in *.
elim H ; intro H1 ; split ; apply Rminus_diag_uniq ; assumption.
Qed.
Hint Immediate Cminus_diag_uniq: complex.

Lemma Cminus_diag_uniq_sym : forall z1 z2 : C, z2 - z1 = C0 -> z1 = z2.
Proof.
intros ; apply Cminus_diag_uniq.
apply Cminus_diag_uniq in H.
rewrite H ; auto with complex.
Qed.
Hint Immediate Cminus_diag_uniq_sym: complex.

Lemma Cadd_minus : forall z1 z2 : C, z1 + (z2 - z1) = z2.
Proof.
CusingR_f.
Qed.
Hint Resolve Cadd_minus: complex.

Lemma Cminus_eq_contra : forall z1 z2 : C, z1 <> z2 -> z1 - z2 <> C0.
Proof.
intros z1 z2 H Habs.
apply Cminus_diag_uniq in Habs.
rewrite Habs in H.
apply H ; reflexivity.
Qed.
Hint Resolve Cminus_eq_contra: complex.

Lemma Cminus_not_eq : forall z1 z2 : C, z1 - z2 <> C0 -> z1 <> z2.
Proof.
intros z1 z2 H Habs.
rewrite Habs in H ; apply H ; auto with complex.
Qed.
Hint Resolve Cminus_not_eq: complex.

Lemma Cminus_not_eq_right : forall z1 z2 : C, z2 - z1 <> C0 -> z1 <> z2.
Proof.
auto with complex.
Qed.
Hint Resolve Cminus_not_eq_right: complex. 

Lemma Cmult_minus_distr_l : forall z1 z2 z3 : C, z1 * (z2 - z3) = z1 * z2 - z1 * z3.
Proof.
CusingR_f.
Qed.

Lemma Cmult_minus_distr_r : forall z1 z2 z3 : C, (z2 - z3) * z1 = z2 * z1 - z3 * z1.
Proof.
intros ; rewrite Cmult_comm, Cmult_minus_distr_l ; ring.
Qed.

(** * Inversion *)

Lemma Cinv_1 : /C1 = C1.
Proof.
field.
auto with complex.
Qed.

Lemma Cinv_R1 : /R1 = C1.
Proof.
CusingR_f.
Qed.

Lemma Cinv_neq_0_compat : forall z : C, z <> C0 -> / z <> C0.
Proof.
intros z H.
intro H0.
apply (Cmult_eq_0_compat_l z) in H0.
apply Cinv_r in H.
rewrite H in H0.
apply C1_neq_C0 ; exact H0.
Qed.
Hint Resolve Cinv_neq_0_compat: complex.

Lemma Cinv_involutive : forall z : C, z <> C0 -> / / z = z.
Proof.
intros z H ; field ; auto with complex.
Qed.
Hint Resolve Cinv_involutive: complex.

Lemma Cinv_mult_distr :
  forall z1 z2 : C, z1 <> C0 -> z2 <> C0 -> / (z1 * z2) = / z1 * / z2.
Proof.
intros z1 z2 H1 H2 ; field ; split ; assumption.
Qed.

Lemma Copp_inv_permute : forall z : C, z <> C0 -> - / z = / - z.
Proof.
intros z H ; field ; auto with complex.
Qed.

Lemma Cinv_r_simpl_r : forall z1 z2 : C, z1 <> C0 -> z1 * / z1 * z2 = z2.
Proof.
intros z1 z2 H ; field ; assumption.
Qed.
Hint Resolve Cinv_r_simpl_r : complex.

Lemma Cinv_r_simpl_l : forall z1 z2 : C, z1 <> C0 -> z2 * z1 * / z1 = z2.
Proof.
intros z1 z2 H ; field ; assumption.
Qed.
Hint Resolve Cinv_r_simpl_l : complex.

Lemma Cinv_r_simpl_m : forall z1 z2 : C, z1 <> C0 -> z1 * z2 * / z1 = z2.
Proof.
intros z1 z2 H ; field ; assumption.
Qed.
Hint Resolve Cinv_r_simpl_m: complex.

Lemma Cinv_mult_simpl :
  forall z1 z2 z3 : C, z1 <> C0 -> z1 * / z2 * (z3 * / z1) = z3 * / z2.
Proof.
intros z1 z2 z3 H.
rewrite Cmult_assoc ; rewrite Cmult_comm ; rewrite Cmult_assoc.
replace (z3 * /z1 * z1) with z3 by (field ; assumption).
apply Cmult_comm.
Qed.

Lemma Cpow_inv : forall (z : C) n, z <> C0 -> /(z ^ n) = (/z) ^ n.
Proof.
intros z n z_neq ; induction n.
 repeat (rewrite Cpow_0) ; CusingR_f.
 simpl ; rewrite Cinv_mult_distr ; [| assumption |].
 rewrite <- IHn ; reflexivity.
 clear -z_neq ; induction n.
 simpl ; intuition.
 simpl ; apply Cmult_integral_contrapositive ; split ; assumption.
Qed.

(** * Power *)

Lemma Cpow_neq_compat : forall (z : C) n, z <> C0 -> z ^ n <> C0.
Proof.
intros z n z_neq ; induction n.
 simpl ; auto with complex.
 simpl ; apply Cmult_integral_contrapositive_currified ; assumption.
Qed.

(** * Injection from [R] to [C]*)

Lemma IRC_minus_compat : forall lb ub, IRC lb - IRC ub = IRC (lb - ub).
Proof.
intros ; CusingR.
Qed.

Lemma IRC_neq_compat : forall r s, r <> s -> IRC r <> IRC s.
Proof.
intros r s r_neq_s Hf.
 destruct (proj2 (Ceq _ _) Hf) as [Hf' _].
 simpl in Hf' ; intuition.
Qed.

Lemma IRC_neq_0_compat : forall r:R, r <> 0%R -> IRC r <> C0.
Proof.
intros r r_neq_0 ; replace C0 with (IRC 0%R) by intuition ;
 apply IRC_neq_compat ; assumption.
Qed.

(** * Injection from [N] to [C]*)

Lemma S_INC : forall n:nat, INC (S n) = INC n + C1.
Proof.
intro n . simpl. destruct n ; auto with complex. 
Qed.

Lemma IRC_INR_INC : forall x, IRC (INR x) = INC x.
Proof.
intros x.
induction x. reflexivity.
rewrite S_INC. rewrite <- IHx.
rewrite S_INR. CusingR. 
Qed.

Lemma S_O_add_INC : forall n:nat, INC (1 + n) = INC 1 + INC n.
Proof.
destruct n . auto with complex.
replace (1 + S n)%nat with (S (S n))%nat by (simpl ; reflexivity).
do 3 (rewrite S_INC) ; replace (INC 0%nat) with C0 by (simpl ; reflexivity).
rewrite Cadd_0_l.
ring.
Qed.

Lemma add_INC : forall n m:nat, INC (n + m) = INC n + INC m. 
Proof.
intros n m.
induction n ; auto with complex.
rewrite S_INC ; rewrite Cadd_assoc ; rewrite Cadd_comm ; rewrite Cadd_assoc.
rewrite Cadd_comm in IHn ;  rewrite <- IHn.
replace (S n + m)%nat with (S (n + m)) by (simpl ; reflexivity).
rewrite S_INC ; auto with complex.
Qed.
Hint Resolve add_INC : complex.

Lemma minus_INC : forall n m:nat, (m <= n)%nat -> INC (n - m) = INC n - INC m.
Proof.
intros n m H1.
induction m.
simpl.
replace (n-0)%nat with n by intuition ; auto with complex.
destruct n.
 inversion H1.
replace (S n - S m)%nat with (n - m)%nat by intuition.
do 2 rewrite S_INC. replace (INC n + C1 - (INC m + C1)) with (INC n - INC m) by ring.
replace (INC (S n) - INC m) with (C1 + INC n - INC m) in IHm.
 replace (INC (S n - m)) with (C1 + INC (n - m)) in IHm.
  assert ( H :( C1 + INC (n - m) = C1 + INC n - INC m) -> (INC (n - m) = INC n - INC m)).
   unfold Cminus ; rewrite Cadd_assoc ; apply (Cadd_eq_reg_l C1).
  apply H. apply IHm. intuition.
 replace (S n - m)%nat with (S (n - m))%nat.
  rewrite S_INC. auto with complex.
 intuition.
rewrite S_INC. ring.
Qed.
Hint Resolve minus_INC : complex.

Lemma mult_INC : forall n m:nat, INC (n * m) = INC n * INC m.
Proof.
intros n m; induction n.
intuition.
rewrite S_INC. simpl (S n * m)%nat. rewrite add_INC.
rewrite IHn.
ring.
Qed.
Hint Resolve mult_INC: complex.

Lemma Cre_INC_pos : forall n : nat, 0 <= Cre (INC n).
Proof.
induction n.
intuition.
rewrite S_INC.
destruct (INC n); simpl in *.
intuition.
Qed.

Lemma Cim_INC_0 : forall n : nat, R0 = Cim (INC n).
Proof.
induction n. intuition.
rewrite S_INC.
rewrite Cim_add_distr.
rewrite <- IHn.
intuition.
Qed.

(** * Cnorm *)

Lemma Cnorm_eq_compat : forall z z', z = z' -> Cnorm z = Cnorm z'.
Proof.
intros ; subst ; reflexivity.
Qed.
Hint Resolve Cnorm_eq_compat: complex.

Lemma Cnorm_sqr_pos : forall r r1 : R, 0 <= r * r + r1 * r1.
Proof.
intros. apply Rplus_le_le_0_compat ; apply Rle_0_sqr. 
Qed.

Lemma Cnorm_sqr_pos_lt : forall r r1 : R, (r,r1) <> C0 -> 0 < r * r + r1 * r1.
Proof.
intros r r1 z_neq_0.
 case (proj1 (C0_neq_R0_neq _) z_neq_0) ; simpl ; intro H.
  apply Rplus_lt_le_0_compat.
  apply Rsqr_pos_lt ; assumption.
  apply Rle_0_sqr.
  apply Rplus_le_lt_0_compat.
  apply Rle_0_sqr.
  apply Rsqr_pos_lt ; assumption.
Qed.

Lemma Cnorm_lt_INC : forall n m:nat, (n < m)%nat -> Cnorm (INC n) < Cnorm (INC m).
Proof.
intros n m H. induction H.
generalize (Cre_INC_pos n). generalize (Cim_INC_0 n).
intros H1 H2.
rewrite S_INC.
destruct (INC n).
simpl in *.
apply sqrt_lt_1.
   apply Cnorm_sqr_pos. apply Cnorm_sqr_pos.
 unfold Cnorm_sqr. simpl. ring_simplify. do 2 rewrite Rplus_assoc. apply (Rplus_lt_compat_l (r^2)).
 rewrite <- H1. ring_simplify. apply Rplus_le_lt_0_compat.
 replace (IZR 0) with (2*0)%R by ring.
 apply Rmult_le_compat_l. lra. assumption. lra.
rewrite S_INC. 
apply Rlt_trans with (Cnorm (INC m)). exact IHle.
generalize (Cre_INC_pos m). generalize (Cim_INC_0 m).
intros H1 H2.
destruct (INC m). simpl in *.
apply sqrt_lt_1.
   apply Cnorm_sqr_pos. apply Cnorm_sqr_pos. 
unfold Cnorm_sqr. simpl. ring_simplify. do 2 rewrite Rplus_assoc. apply (Rplus_lt_compat_l (r^2)).
rewrite <- H1. ring_simplify. apply Rplus_le_lt_0_compat.
replace (IZR 0) with (2*0)%R by ring.
apply Rmult_le_compat_l. lra. assumption. lra.
Qed.
Hint Resolve Cnorm_lt_INC: complex.

Lemma Cnorm_lt_1_INC : forall n:nat, (1 < n)%nat -> 1 < Cnorm (INC n).
Proof.
intros n H.
induction n.
inversion H.
rewrite S_INC. 
destruct n. inversion H. inversion H1.
rewrite S_INC in IHn.
rewrite S_INC.
generalize (Cre_INC_pos n). generalize (Cim_INC_0 n).
intros H2 H3.
destruct (INC n); simpl in *.
rewrite <- sqrt_1. apply sqrt_lt_1. lra. apply Cnorm_sqr_pos.
unfold Cnorm_sqr ; simpl.
rewrite <- H2.
apply Rminus_gt. unfold Cnorm_sqr. ring_simplify.
unfold Rminus ; rewrite Rplus_assoc ; apply Rplus_le_lt_0_compat.
apply Rmult_le_pos ; [| rewrite Rmult_1_r] ; assumption.
 replace R0 with  (4*0)%R by ring.  lra.
Qed.
Hint Resolve Cnorm_lt_1_INC : complex.

Lemma Cnorm_INC_lt : forall n m:nat, Cnorm (INC n) < Cnorm (INC m) -> (n < m)%nat.
Proof.
induction n; induction m.
- simpl. intro Habs. lra.
- revert m IHm.
  intros n1 H1 H2. destruct n1. intuition. constructor. assert (Hind : (0<S n1 -> 1 <= S n1)%nat). intuition.
  apply Hind. apply H1. rewrite S_INC. 
  generalize (Cre_INC_pos n1). generalize (Cim_INC_0 n1). intros Hu Hs.
  destruct (INC n1). simpl in *. apply sqrt_lt_1. unfold Cnorm_sqr. simpl. apply Cnorm_sqr_pos.
   unfold Cnorm_sqr. apply Cnorm_sqr_pos.
   unfold Cnorm_sqr. simpl. rewrite <- Hu. ring_simplify. apply Rplus_le_lt_0_compat. apply Rplus_le_le_0_compat.
    replace (r^2)%R with (Rsqr r) by (compute; ring). apply Rle_0_sqr.
   replace (IZR 0) with (2*0)%R by ring.
   apply Rmult_le_compat_l. lra. assumption. lra.
- revert n IHn.
  intros n0 H1 H2. rewrite S_INC in H2.
 generalize (Cre_INC_pos n0). generalize (Cim_INC_0 n0). intros Hu Hs.
 destruct (INC n0). simpl in *. apply sqrt_lt_0 in H2. unfold Cnorm_sqr in *. simpl in *. rewrite <- Hu in H2. 
   ring_simplify in H2. assert (H : 0<= (Rsqr (r+1))%R). apply Rle_0_sqr. destruct H. compute in H. ring_simplify in H.
    assert (H0 : (forall x: R, x > 0 -> x < 0 -> False)). intros. lra. assert (Habs : ((0 < r ^ 2 + 2 * r + 1) ->  (r ^ 2 + 2 * r + 1 < 0)->False)%R).
     apply H0. destruct Habs ; assumption.
   rewrite H in H2. compute in H2. ring_simplify in H2. lra.
   apply Cnorm_sqr_pos. unfold Cnorm_sqr. simpl. apply Cnorm_sqr_pos.
- revert n IHn m IHm.
  intros n1 H3 n0 H1 H4.
assert (H : (n1<n0 -> S n1 < S n0)%nat). intuition.
apply H.
apply H3.
do 2 rewrite S_INC in H4.
generalize (Cre_INC_pos n0). generalize (Cim_INC_0 n0). intros Hu Hs.
generalize (Cre_INC_pos n1). generalize (Cim_INC_0 n1). intros Hu1 Hs1.
destruct (INC n0) ; destruct (INC n1). simpl in *. apply sqrt_lt_1. apply sqrt_lt_0 in H4.
    apply Cnorm_sqr_pos.
   apply Cnorm_sqr_pos.
  apply Cnorm_sqr_pos.
 apply Cnorm_sqr_pos.
rewrite <- Hu in *. rewrite <- Hu1 in *. apply sqrt_lt_0 in H4. ring_simplify in H4.
  unfold Cnorm_sqr in *. simpl in *. ring_simplify in H4. ring_simplify.
  generalize H4.
  replace (r1 ^ 2 + 2 * r1 + 1)%R with (Rsqr (r1 + 1))%R by (compute; ring).
  replace (r ^ 2 + 2 * r + 1)%R with (Rsqr (r + 1))%R by (compute; ring).
  replace ( r1 ^ 2)%R with (Rsqr r1) by (compute ; ring).
  replace ( r ^ 2)%R with (Rsqr r) by (compute ; ring).
intro H5. apply Rsqr_incrst_0 in H5. apply Rsqr_incrst_1. lra.
exact Hs1. exact Hs. lra. lra. apply Cnorm_sqr_pos. apply Cnorm_sqr_pos.
Qed.
Hint Resolve Cnorm_INC_lt: complex.

Lemma Cnorm_le_INC : forall n m:nat, (n <= m)%nat -> 
     Cnorm (INC n) <= Cnorm (INC m).
Proof.
intros n m H.
induction H. right. reflexivity.
apply Rle_trans with (Cnorm (INC m)). exact IHle.
left. apply Cnorm_lt_INC. intuition.
Qed.
Hint Resolve Cnorm_le_INC : complex.

(** * INC/Cre/Cim *)

Lemma INC_not_0 : forall n:nat, INC n <> 0 -> n <> 0%nat.
Proof.
induction n ; intuition lia.
Qed.
Hint Immediate INC_not_0 : complex.

Lemma not_0_INC : forall n:nat, n <> 0%nat -> INC n <> 0.
Proof.
induction n. intuition.
intro H.
rewrite S_INC.
generalize (Cre_INC_pos n).
intro H1.
destruct (INC n). simpl in *. rewrite <- Ceq. 
simpl. intuition. lra.
Qed.
Hint Resolve not_0_INC : complex.

Lemma not_INC : forall n m:nat, n <> m -> INC n <> INC m.
Proof.
induction n; induction m. intuition.
revert m IHm.
intros n1 H1 H2. intro H. apply H2. rewrite S_INC in H.
generalize (Cre_INC_pos n1). intro H3. destruct (INC n1). simpl in *.
apply Ceq in H. elim H. intros H5 H6. simpl in *. lra.
revert n IHn.
intros n1 H1 H2. intro H. apply H2. rewrite S_INC in H.
generalize (Cre_INC_pos n1). intro H3. destruct (INC n1). simpl in *.
apply Ceq in H. elim H. intros H5 H6. simpl in *. lra.
revert n IHn m IHm.
intros n1 H3 n0 H1 H4.
do 2 rewrite S_INC. assert ( H : (INC n1 <> INC n0 -> INC n1 + C1 <> INC n0 + C1)).
intros temp1 temp2. 
apply Cadd_eq_reg_r in temp2.
apply temp1.
exact temp2.
apply H.
apply H3.
intuition.
Qed.
Hint Resolve not_INC: complex.

Lemma Cre_let_1 : forall  (f g : R -> R) (c : R * R), 
  Cre (let (a, b) := c in (f a +i g b)) = f (Cre c).
Proof.
intros.
destruct c. simpl. reflexivity.
Qed.

Lemma Cim_let_1 : forall  (f g : R -> R) (c : R * R), 
  Cim (let (a, b) := c in (f a +i g b)) = g (Cim c).
Proof.
intros.
destruct c. simpl. reflexivity.
Qed.

Lemma Cre_let_2 : forall  (f g : R -> R -> R) (c : R * R), 
  Cre (let (a, b) := c in (f a b +i g a b)) = f (Cre c) (Cim c).
Proof.
intros.
destruct c. simpl. reflexivity.
Qed.

Lemma Cim_let_2 : forall  (f g : R -> R -> R) (c : R * R), 
  Cim (let (a, b) := c in (f a b +i g a b)) = g (Cre c) (Cim c).
Proof.
intros.
destruct c. simpl. reflexivity.
Qed.

Lemma Cim_mul : forall z1 z2, Cim (z1 * z2) = ((Cre z1) * (Cim z2) + (Cre z2) * (Cim z1))%R.
Proof.
intros z z' ; destruct z ; destruct z'.
 compute ; field.
Qed.

Lemma Cre_mul : forall z1 z2, Cre (z1 * z2) = (Cre z1 * Cre z2 - Cim z1 * Cim z2)%R.
Proof.
intros z z' ; destruct z ; destruct z'.
 compute ; field.
Qed.

Lemma Cim_inv_compat_0 : forall z, Cim z = 0%R -> Cim (/z) = 0%R.
Proof.
intuition.
destruct z.
unfold Cinv.
simpl in *.
rewrite H. replace (- 0 / (r * r + 0 * 0))%R with (0%R). 
intuition. rewrite Ropp_0. unfold Rdiv. rewrite Rmult_0_l.
reflexivity.
Qed.

Lemma Cre_inv_compat_0 : forall z, Cre z = 0%R -> Cre (/z) = 0%R.
Proof.
intuition.
destruct z.
unfold Cinv.
simpl in H.
rewrite H. unfold Rdiv. rewrite Rmult_0_l.
reflexivity.
Qed.

Lemma Cim_INC : forall n, Cim (INC n) = 0%R.
Proof.
intros n.
induction n.
intuition.
rewrite S_INC.
rewrite <- Cim_add_compat.
rewrite IHn. simpl. intuition.
Qed.

Lemma Cre_INC_INR : forall n, Cre (INC n) = INR n.
Proof.
induction n.
reflexivity.
rewrite S_INC. rewrite <- Cre_add_compat.
rewrite IHn. rewrite S_INR. reflexivity. 
Qed.

Lemma Cim_inv_INC : forall n, Cim (/ INC n) = 0%R.
Proof.
intros.
apply Cim_inv_compat_0.
apply Cim_INC.
Qed.

Lemma INC_inv_Cre_INR : forall n : nat, n <> 0%nat -> Cre (/INC n) = (/(INR n))%R.
Proof.
intros n Hn.
unfold Cinv.
simpl. repeat rewrite <- Cim_INC_0.
repeat rewrite Cre_INC_INR.
field. apply not_0_INR. exact Hn.
Qed.

Lemma INC_inv_Cim_INR : forall n : nat, n <> 0%nat -> Cim (/INC n) = 0%R.
Proof.
intros n Hn.
unfold Cinv.
simpl. repeat rewrite <- Cim_INC_0.
repeat rewrite Cre_INC_INR.
field. apply not_0_INR. exact Hn.
Qed.

(** * Cneq results*)

Lemma Cadd_neq_compat_l : forall z z' : C, z' <> C0 -> z + z' <> z.
Proof.
intros z z' z'_neq Hf ; apply z'_neq.
 assert (H := Cadd_eq_compat_l (- z) _ _ Hf).
 rewrite <- Cadd_assoc, Cadd_opp_l, Cadd_0_l in H ;
 assumption.
Qed.

Lemma Cadd_neq_compat_r : forall z z' : C, z' <> C0 -> z' + z <> z.
Proof.
intros z z' z'_neq ; rewrite Cadd_comm ;
 apply Cadd_neq_compat_l ; assumption.
Qed.

(** * Compatibility of IRC and real/complex lemma *)

Lemma Cadd_IRC_compat_l : forall (r a b : R), r + (a +i b) = ((r + a)%R +i b).
Proof.
CusingR.
Qed.
Hint Resolve Cadd_IRC_compat_l : complex.

Lemma Cadd_IRC_compat_r : forall (r a b : R), (a +i b) + r = ((a + r)%R +i b).
Proof.
CusingR.
Qed.
Hint Resolve Cadd_IRC_compat_r : complex.

Lemma Cminus_IRC_compat_l : forall (r a b : R), r - (a +i b) = ((r - a)%R +i -b).
Proof.
CusingR.
Qed.
Hint Resolve Cminus_IRC_compat_l : complex.

Lemma Cminus_IRC_compat_r : forall (r a b : R), (a +i b) - r = ((a - r)%R +i b).
Proof.
CusingR_f.
Qed.
Hint Resolve Cminus_IRC_compat_r : complex.

Lemma Cmult_IRC_compat_l : forall r a b, (r * a +i r * b) = r * (a +i b).
Proof.
intros.
CusingR_f.
Qed.
Hint Resolve Cmult_IRC_compat_l : complex.

Lemma Cmult_IRC_compat_r : forall r a b, ( a * r +i b * r) = (a +i b) * r.
Proof.
intros.
CusingR_f.
Qed.
Hint Resolve Cmult_IRC_compat_r : complex.

Lemma Cadd_IRC_Rplus : forall (a b : R), IRC (Rplus a b) = Cadd a b.
Proof.
CusingR.
Qed.
Hint Resolve Cadd_IRC_Rplus : complex.

Lemma Cminus_IRC_Rminus : forall (a b : R), IRC (a - b) = a - b.
Proof.
CusingR.
Qed.
Hint Resolve Cminus_IRC_Rminus : complex.

Lemma Cmult_IRC_Rmult : forall (a b : R), IRC (a * b) = a * b.
Proof.
intros.
CusingR_f ; assumption.
Qed.
Hint Resolve Cmult_IRC_Rmult : complex.

Lemma Cdiv_IRC_Rdiv : forall (a b : R), b <> 0%R -> IRC (a / b) = a / b.
Proof.
intros.
CusingR_f ; assumption.
Qed.
Hint Resolve Cdiv_IRC_Rdiv : complex.

Lemma Cinv_IRC_Rinv : forall (b : R), b <> 0%R -> IRC (/ b) = / b.
Proof.
intros.
CusingR_f ; assumption.
Qed.
Hint Resolve Cinv_IRC_Rinv : complex.

Lemma Cre_div_compat : forall (z : C) (r : R), r <> R0 -> Cre (z / r) = (Cre z / r)%R.
Proof.
intros z r r_neq ; unfold Rdiv, Cdiv ; rewrite <- Cinv_IRC_Rinv ;
 [apply Cre_mult_compat_r | assumption].
Qed.

Lemma Cim_div_compat : forall (z : C) (r : R), r <> R0 -> Cim (z / r) = (Cim z / r)%R.
Proof.
intros z r r_neq ; unfold Rdiv, Cdiv ; rewrite <- Cinv_IRC_Rinv ;
 [apply Cim_mult_compat_r | assumption].
Qed.

(** * Compatibility of Cconj with Cnorm_sqr*)

Lemma Cmod_conj_compat : forall z, Cre (z * Cconj z) = ((Cnorm z) ^ 2)%R
                                                           /\ Cim ( z * Cconj z) = 0%R.
Proof.
intros z.
 split ; CusingR1.
unfold Cnorm. rewrite Rmult_1_r. rewrite <- sqrt_mult.
rewrite sqrt_square.
unfold Cnorm_sqr. simpl. ring.
apply Cnorm_sqr_pos.
apply Cnorm_sqr_pos.
apply Cnorm_sqr_pos.
Qed.

(** * Compatibility of pow and Cpow*)

Lemma Cpow_Cre_Cim_0 : forall r n, Cre ((r +i 0%R) ^ n) = (r ^ n)%R /\ Cim ((r +i 0%R) ^ n) = 0%R.
Proof.
induction n.
 compute ; split ; reflexivity.
 replace ((r +i 0%R) ^ S n) with ((r +i 0%R) ^ n * (r +i 0%R)) by (rewrite Cpow_S ; intuition).
 simpl. destruct IHn as (IHn1, IHn2). 
 split ; simpl ; rewrite IHn1 ; rewrite IHn2 ; field.
Qed.

Lemma Cpow_Cre_0 : forall r n, Cre ((r +i 0%R) ^ n) = (r ^ n)%R.
Proof.
intros.
destruct (Cpow_Cre_Cim_0 r n).
assumption.
Qed.

Lemma Cpow_Cim_0 : forall r n, Cim ((r +i 0%R) ^ n) = 0%R.
Proof.
intros.
destruct (Cpow_Cre_Cim_0 r n).
assumption.
Qed.

Lemma nat_4_dec : forall n, exists k, (4 * k = n \/ 4 * k + 1= n \/ 4 * k + 2 = n \/ 4 * k + 3 = n )%nat.
Proof.
induction n.
exists 0%nat. left. intuition.
destruct IHn as [k [H | [H| [H|H]]]].
exists k. right. left. intuition lia.
exists k. right. right. left. intuition lia.
exists k. right. right. right. intuition lia.
exists (S k). left. intuition lia.
Qed.

Lemma Cpow_Cre_4_0 : forall n r, Cre ((0%R +i r) ^ (4 * n)) = (r ^ (4 * n))%R.
Proof.
intros.
induction n.
intuition. replace (4 * S n)%nat with (4 + 4 * n)%nat by ring.
rewrite Cpow_add. 
rewrite Cpow_mul in *. replace ((0%R +i r) ^ 4) with (r ^ 4 +i 0)%R in *.
rewrite Cre_mul in *. simpl (Cim (r ^ 4 +i  0))%R. ring_simplify.
rewrite IHn. simpl. field. CusingR_f. 
Qed.

Lemma Cpow_Cim_4_0 : forall n r, Cim ((0%R +i r) ^ (4 * n)) = 0%R.
Proof.
intros ; induction n.
intuition. replace (4 * S n)%nat with (4 + 4 * n)%nat by ring.
rewrite Cpow_add. 
rewrite Cpow_mul in *. replace ((0%R +i r) ^ 4) with (r ^ 4 +i 0)%R in *.
rewrite Cim_mul in *. simpl (Cim (r ^ 4 +i  0))%R. ring_simplify.
rewrite IHn. simpl. ring. CusingR_f. 
Qed.

Lemma Cpow_Cre_4_1 : forall n r, Cre ((0%R +i r) ^ (4 * n + 1)) = 0%R.
Proof.
intros.
rewrite Cpow_add. rewrite Cre_mul. 
rewrite Cpow_Cre_4_0. rewrite Cpow_Cim_4_0.
simpl ; field.
Qed.

Lemma Cpow_Cim_4_1 : forall n r, Cim ((0%R +i r) ^ (4 * n + 1)) = (r ^ (4 * n + 1))%R.
Proof.
intros. rewrite Cpow_add.
rewrite Cim_mul. rewrite Cpow_Cre_4_0. rewrite Cpow_Cim_4_0.
rewrite Rdef_pow_add. simpl. ring.
Qed.

Lemma Cpow_Cre_4_2 : forall n r, Cre ((0%R +i r) ^ (4 * n + 2)) = (- r ^ (4 * n + 2))%R.
Proof.
intros.
rewrite Cpow_add. rewrite Cre_mul. 
rewrite Cpow_Cre_4_0. rewrite Cpow_Cim_4_0. ring_simplify.
simpl ( Cre ((0%R +i r) ^ 2)). ring_simplify. rewrite Rdef_pow_add.
ring.
Qed.

Lemma Cpow_Cim_4_2 : forall n r, Cim ((0%R +i r) ^ (4 * n + 2)) = 0%R.
Proof.
intros. rewrite Cpow_add.
rewrite Cim_mul. rewrite Cpow_Cre_4_0. rewrite Cpow_Cim_4_0.
simpl. ring.
Qed.

Lemma Cpow_Cre_4_3 : forall n r, Cre ((0%R +i r) ^ (4 * n + 3)) = 0%R.
Proof.
intros.
rewrite Cpow_add. rewrite Cre_mul. 
rewrite Cpow_Cre_4_0. rewrite Cpow_Cim_4_0. ring_simplify.
simpl. ring.
Qed.

Lemma Cpow_Cim_4_3 : forall n r, Cim ((0%R +i r) ^ (4 * n + 3)) = (- r ^ (4 * n + 3))%R.
Proof.
intros.
rewrite Cpow_add. rewrite Cim_mul. 
rewrite Cpow_Cre_4_0. rewrite Cpow_Cim_4_0. ring_simplify.
rewrite Rdef_pow_add.
simpl. ring.
Qed.

(** Tactic CpowR which destructs a nat into 4 nat (4*k + 1 etc). Then, it rewrites the power
that can be simpler *)

Ltac CpowR a := 
let H := fresh "H" in let n := fresh "n" in
(destruct (nat_4_dec a) as (n, H);  
destruct H as [H|[H| [H|H]]] ; rewrite <- H ;
[repeat (rewrite Cpow_Cre_4_0||rewrite Cpow_Cim_4_0)
| repeat (rewrite Cpow_Cre_4_1||rewrite Cpow_Cim_4_1) 
| repeat (rewrite Cpow_Cre_4_2||rewrite Cpow_Cim_4_2)
| repeat (rewrite Cpow_Cre_4_3||rewrite Cpow_Cim_4_3)]).

(* begin hide *)
(* Tactic RpowR destroy minus with pow *)
(* Move these lemmas *)

Lemma Rpow_2_0 : forall x n,  ((-x) ^ (2 * n) = x ^ (2 * n))%R.
Proof.
intros.
induction n. intuition.
replace (2 * S n)%nat with (2 + 2 * n)%nat by ring.
rewrite Rdef_pow_add. replace ((-x) ^ 2)%R with (x ^ 2)%R by ring.
rewrite IHn. intuition. 
Qed.

Lemma Rpow_2_1 : forall x n, ((-x) ^ (S (2 * n)) = - (x ^ (S (2 * n))))%R.
Proof.
intros.
simpl.
replace (n + (n + 0))%nat with (2 * n)%nat by (simpl ; reflexivity).
rewrite Rpow_2_0.
ring.
Qed.

Ltac RpowR a :=
 let H := fresh "H" in let n := fresh "n" in
  destruct (even_odd_cor a) as (n, H); 
  destruct H as [H|H] ; rewrite H ; 
  [repeat rewrite Rpow_2_0|repeat rewrite Rpow_2_1].

(* end hide *)
