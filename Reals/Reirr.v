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

Require Import Max.

Require Import Rseries_facts.
Require Import Rsequence_facts.
Require Import Rsequence_subsequence.
Require Import Rpser_usual.
Require Import Reals.
Require Import Rsequence_tactics.
Require Import Rtactic.

Require Import Lra.

Open Scope R_scope.

Definition e := exp 1.

Definition partial_e n := sum_f_R0 (fun n => /INR (fact n)) n.

(* begin hide *)
Lemma Rabs_div : forall x y, y <> 0 -> Rabs (x / y) = Rabs x / Rabs y.
Proof.
intros x y H.
unfold Rdiv.
rewrite Rabs_mult.
rewrite Rabs_Rinv. field.
apply Rabs_no_R0.
assumption.
intuition.
Qed.

Lemma integer_INR_div : forall b, b <> O -> / INR b * INR (fact b) = INR (fact (b - 1)).
Proof.
intros b Hb0.
destruct b.
 destruct Hb0. reflexivity.
 
 rewrite fact_simpl. rewrite mult_INR. 
 field_simplify.
  simpl. rewrite <- minus_n_O. reflexivity.
 
 INR_solve.
Qed.
(* end hide *)

Lemma sum_integer_INR_div : forall n, {m | 
   sum_f_R0 (fun i : nat => / INR (fact i) * INR (fact n)) n = INR m}.
Proof.
induction n.
 exists 1%nat. simpl. field.
 
 destruct IHn as (m1, Hm1).
 rewrite tech5. rewrite fact_simpl. rewrite mult_INR.
 exists (S n * m1 + 1)%nat.
 rewrite <- scal_sum.
 rewrite <- scal_sum in Hm1. rewrite Rmult_assoc. rewrite Hm1.
 rewrite plus_INR. rewrite mult_INR. do 2 rewrite S_INR. simpl.
 field.
 
 split. 
  apply INR_fact_neq_0.
  assert (INR n >= 0) by intuition ; intro H1 ; lra.
Qed.

Lemma integer_exp_minus_sum : forall a b : nat, 
  b <> O -> e = INR a / INR b ->
  {n | INR (fact b) * (e - partial_e b) = IZR n}.
Proof.
intros a b Hb0 Habs.
rewrite Habs.
rewrite Rmult_minus_distr_l.
unfold partial_e.
rewrite scal_sum.
unfold Rdiv. rewrite Rmult_comm. rewrite Rmult_assoc.
rewrite (integer_INR_div b Hb0).
destruct (sum_integer_INR_div b) as (m1, Hm1).
rewrite Hm1.
exists (Z_of_nat a * Z_of_nat (fact (b-1)) - Z_of_nat m1)%Z.
unfold Zminus. rewrite plus_IZR. rewrite mult_IZR.
rewrite Ropp_Ropp_IZR. repeat rewrite <- INR_IZR_INZ.
ring.
Qed.

Lemma sum_max : forall b N f, 
  (forall n, f n > 0) -> (sum_f_R0 f b < 
    sum_f_R0 f (max N (S b))).
Proof.
intros b N f Hpos.
assert (b < max N (S b))%nat by intuition.
induction H.
 replace (sum_f_R0 f b) with (sum_f_R0 f b + 0) by ring.
 simpl. apply Rplus_le_lt_compat. 
  right. reflexivity. 
  
  apply Hpos.
 simpl.
 replace (sum_f_R0 f b) with (sum_f_R0 f b + 0) by ring.
 apply Rplus_le_lt_compat.
  left. apply IHle.
  
  apply Hpos.
Qed.

Lemma inv_INR_fact_pos : forall n, (/INR (fact n)) > 0.
Proof.
intros n.
assert (INR (fact n) > 0).
 induction n.
  simpl. lra.
  
  simpl. rewrite plus_INR. replace 0 with (0 + 0) by intuition.
  apply Rplus_gt_ge_compat. apply IHn. intuition.
 apply Rinv_0_lt_compat. intuition.
Qed.

Lemma Rminus_lt_plus : forall a b c, a - b < c -> a < b + c.
Proof.
intros.
lra.
Qed.

Lemma Rplus_lt_minus : forall a b c, a < b + c -> a - b < c.
Proof.
intros.
lra.
Qed.

Lemma sum_max1 : forall N b f, 
  (forall n, f n >= 0) ->
    sum_f_R0 f (max N (S b)) >=
    sum_f_R0 f (S b).
Proof.
intros N b f Hpos.
assert (H : (S b <= max N (S b))%nat) by intuition.
induction H.
 intuition.
 
 rewrite tech5.
 replace (sum_f_R0 f (S b)) with (sum_f_R0 f (S b) + 0) by ring.
 apply Rplus_ge_compat. apply IHle. apply Hpos.
Qed.

Lemma minus_exp_sum_pos : forall a b : nat, 
  b <> O ->
  INR (fact b) * (e - partial_e b) > 0.
Proof.
intros a b Hb0.
unfold e, partial_e, exp.
destruct (exist_exp 1) as (y, Hexp). unfold exp_in in *. simpl.
apply Rmult_gt_0_compat ; [apply INR_fact_lt_0|].
unfold infinite_sum in Hexp.
(* Absurd reasoning *)
assert (H : y <= sum_f_R0 (fun n : nat => / INR (fact n)) b -> False).
 intro Habs.
 assert (H1 : /INR (fact (S b)) > 0) by (apply inv_INR_fact_pos).
 generalize (Hexp (/INR (fact (S b))) H1) ; clear Hexp ; intro Hexp.
 destruct Hexp as (N, Hexp).
 assert (Hmax : ((max N (S b)) >= N)%nat). intuition.
 generalize (Hexp (max N (S b)) Hmax). clear Hexp. intros Hexp.
 unfold R_dist in *. unfold Rabs in *.
 replace (sum_f_R0 (fun i : nat => / INR (fact i) * 1 ^ i) (max N (S b)))
 with (sum_f_R0 (fun n : nat => / INR (fact n)) (max N (S b))) in * by
 (apply Rseq_sum_ext ; intros n; rewrite pow1; ring).
 destruct (Rcase_abs (sum_f_R0 (fun i : nat => / INR (fact i)) (max N (S b)) - y)) as [H|H].
  apply Rle_minus in Habs. 
  assert (sum_f_R0 (fun n : nat => / INR (fact n)) b - y < 
  sum_f_R0 (fun i : nat => / INR (fact i)) (max N (S b)) - y).
   unfold Rminus. apply Rplus_lt_compat_r.
   apply sum_max. intuition. apply inv_INR_fact_pos.
  
  lra.
  
  apply Rminus_lt_plus in Hexp.
  apply (Rplus_le_compat_r (/ INR (fact (S b)))) in Habs.
  assert (sum_f_R0 (fun i : nat => / INR (fact i)) (max N (S b)) >=
  sum_f_R0 (fun n : nat => / INR (fact n)) b + / INR (fact (S b))).
   rewrite <- tech5. apply sum_max1. intros. left. apply inv_INR_fact_pos.
  assert (H2 : (sum_f_R0 (fun i : nat => / INR (fact i)) (max N (S b)) <
  sum_f_R0 (fun n : nat => / INR (fact n)) b + / INR (fact (S b)))).
   eapply Rlt_le_trans. apply Hexp. apply Habs.
  apply Rlt_not_ge in H2. apply H2.
  assumption.
 
 apply Rgt_minus. apply Rlt_gt. 
 apply Rnot_le_gt. assumption.
Qed.

Lemma geometric_sum : forall (k:R),
  Rabs k < 1 -> infinite_sum (fun i:nat => k ^ i) (1 / (1 - k)).
Proof.
intros k H0k1.
intros eps Heps.
assert (Hpos : 0 < eps * (1 - k)).
 apply Rmult_lt_0_compat ; [apply Heps |].
 unfold Rabs in *. destruct (Rcase_abs k) ; lra.
destruct (pow_lt_1_zero k H0k1 (eps * (1 - k)) Hpos) as (N, HN).
exists N.
intros n Hn.
rewrite tech3.
 unfold R_dist, Rdiv.
 field_simplify ((1 - k ^ S n) * / (1 - k) - 1 * / (1 - k)).
  rewrite Rabs_div. rewrite Rabs_Ropp. unfold Rabs. destruct (Rcase_abs (-k + 1)) as [H|[H|H]].
(* environnement -> False beginning*)   
   assert (H1 : (N >= N)%nat) by intuition. generalize (HN N H1). intros. 
   assert (eps * (1 - k) < 0). replace 0 with (eps * 0) by intuition.
   apply Rmult_lt_compat_l. apply Heps. lra. lra.
(*end *)
   replace eps with (eps * (1 - k) * / (-k + 1)).
    unfold Rdiv. apply Rmult_lt_compat_r.
     apply Rinv_0_lt_compat. lra.
     
     apply HN. intuition. field. intros H3. lra. 
    
   unfold Rabs in H0k1 ; destruct (Rcase_abs k) ; lra. 
  intro H2. unfold Rabs in H0k1 ; destruct (Rcase_abs k) ; lra.
 intro H2. unfold Rabs in H0k1 ; destruct (Rcase_abs k) ; lra.
intro H2. unfold Rabs in H0k1 ; destruct (Rcase_abs k) ; lra.
Qed.

(* begin hide *)
Lemma identite : forall k b : nat, (k > b)%nat ->
  INR (fact b) * / INR (fact k) 
    <= / INR (S b) * (/ INR (S b)) ^ (k - S b).
Proof.
intros k n Hnb.
induction Hnb.
 rewrite fact_simpl. rewrite mult_INR.
 replace (S n - S n)%nat with O by intuition.
 simpl pow.
 field_simplify. 
  right. reflexivity.
  
  apply not_0_INR. intuition.
  
  split. 
   apply INR_fact_neq_0.
   
   apply not_0_INR. intuition.
   
   rewrite fact_simpl. rewrite mult_INR.
   rewrite <- minus_Sn_m ; [|intuition].
   assert (/INR (S m) <= /INR (S n)) by (apply Rle_Rinv ; intuition) .
   rewrite <- tech_pow_Rmult.
   rewrite Rinv_mult_distr.
    rewrite Rmult_comm. rewrite Rmult_assoc.
    apply Rmult_le_compat.
     left. apply Rinv_0_lt_compat. intuition.
     
     left. rewrite Rmult_comm. apply Rlt_mult_inv_pos ; apply INR_fact_lt_0.
     
     apply Rle_Rinv ; [apply lt_0_INR ; intuition|apply lt_0_INR ; intuition|intuition].
     
     rewrite Rmult_comm. apply IHHnb.
    
    apply not_0_INR. intuition.
    
    apply INR_fact_neq_0.
Qed.

Lemma identite1 : forall b, INR (fact b) * / INR (fact (S (S b))) <
  / INR (S b) * (/ INR (S b)) ^ (S (S b) - S b).
Proof.
intros b.
do 2 rewrite fact_simpl.
rewrite <- minus_Sn_m ; [|intuition].
rewrite <- minus_diag_reverse.
rewrite <- tech_pow_Rmult. simpl pow.
do 2 rewrite mult_INR. field_simplify.
 unfold Rdiv. rewrite Rinv_mult_distr.
  unfold pow. rewrite Rinv_mult_distr.
   do 2 rewrite Rmult_1_l. rewrite Rmult_1_r. apply Rmult_lt_compat_r.
    apply Rinv_0_lt_compat. intuition.
    
    apply Rinv_lt_contravar. apply Rmult_lt_0_compat ; intuition.
    intuition.
    
   apply not_0_INR. intuition.
   
   rewrite Rmult_1_r.  apply not_0_INR. intuition.
   
  apply not_0_INR. intuition.
  
  apply not_0_INR. intuition.
  
 apply not_0_INR. intuition.
 
 split.
  apply INR_fact_neq_0.
  
  split.
   apply not_0_INR. intuition.
   
   apply not_0_INR. intuition.
Qed.
(* end hide *)

Lemma exp_remain_sum : forall n, 
  n <> O -> INR (fact n) * (e - partial_e n) < 1 / INR n.
Proof.
intros b Hb0.
unfold partial_e, e, exp.
destruct (exist_exp 1) as (x, Hexp). simpl.
unfold exp_in in *.
(* geometric summation equal to 1 / b *)
assert (Hgeom : (infinite_sum (fun i => (/INR (S b)) ^ i) (1 / (1 - /INR (S b))))).
 apply (geometric_sum (/INR (S b))).
 unfold Rabs. destruct (Rcase_abs (/INR (S b))) as [H1|[H1|H1]].
  assert (H : (- /INR (S b) < 0 )) by intuition. 
  eapply (Rlt_trans) ; [apply H|intuition].
  
  replace 1 with (/1) by intuition. 
  apply Rinv_lt_contravar. 
   rewrite Rmult_1_l. intuition.
   
   destruct b. 
    destruct Hb0. reflexivity. 
    
    rewrite S_INR. assert (INR (S b) > 0) by intuition. lra.
  
  rewrite H1. lra.
(* end of geometric summation *)

(* rewriting of Hexp *)
assert (He : (infinite_sum (fun i : nat => / INR (fact i)) x)).
 intros eps Heps. destruct (Hexp eps Heps) as (N, Hexp1).
 exists N. intros n Hn. generalize (Hexp1 n Hn). intros H1.
 assert (Hrew : (sum_f_R0 (fun i : nat => / INR (fact i) * 1 ^ i) n = 
 sum_f_R0 (fun i : nat => / INR (fact i)) n)).
  apply sum_eq. intros. rewrite pow1. intuition.
  
 rewrite <- Hrew. apply H1. clear Hexp.
(* end of rewriting : He *)

pose (Un := fun n : nat => / INR (fact (n))).
pose (UUn := fun n : nat => Un (S b + n)%nat).
assert (Hluu : Rser_cv UUn (x - sum_f_R0 Un b)). 
 apply (Rser_cv_shifts b Un). assumption.

assert (Hlu : Rser_cv Un x). apply He.

assert (HRser : Rser_cv (fun k => Un (S b+ k)%nat) (Rser_rem Un x Hlu b)).
 apply (Rser_rem_cv Un).

assert (Rser_cv Un (Rser_rem Un x Hlu b + sum_f_R0 Un b)).
 apply Rser_cv_shifts_rev. assumption.

assert (H1 : (x = Rser_rem Un x Hlu b + sum_f_R0 Un b)).
 apply Rser_cv_unique with Un ; assumption.

rewrite H1. unfold Un. ring_simplify.
assert (Hlmachin : Rser_cv Un x). intuition.

apply Rser_cv_scal_compat_l with Un x (INR (fact b)) in Hlmachin.
fold Un. apply Rle_lt_trans with ((INR (fact b) * Rser_rem Un x Hlu)%Rseq b).
reflexivity. rewrite <- (Rser_rem_scal_compat_l Un x (INR (fact b)) Hlmachin).

pose (Vn := (fun n0 : nat => INR (fact b) * / INR (fact n0) )).
assert (Hlv : (Rser_cv Vn (INR (fact b) * x))).
 unfold Vn. apply Rser_cv_scal_compat_l. assumption.

unfold Un. fold Vn.
pose (Wn := (fun i : nat => /(INR (S b)) * (/ INR (S b)) ^ i)).
assert (Hlw : Rser_cv Wn (( /INR (S b) *(1/ (1 - / INR (S b)))))).
 unfold Wn. apply Rser_cv_scal_compat_l.
 apply Rser_cv_ext with (fun i : nat => (/ INR (S b)) ^ i).
 intro ; reflexivity.
  
  apply Hgeom.

eapply Rlt_le_trans with (/ INR (S b) * (1 / (1 - / INR (S b)))).
 apply (Rser_Rser_rem_lt_le Wn Vn _ _ _ _).
  intros k Hkn.
  unfold Vn, Wn. apply identite. assumption.
  
  exists (S (S b)). intuition. unfold Vn, Wn. apply identite1.
  
  apply Hlw.
 
 field_simplify.
  replace (INR (S b) - 1) with (INR b). right. reflexivity.
  
  rewrite S_INR. ring.
  
  INR_solve.

split. 
 apply not_0_INR. 
  intuition.
  
  rewrite S_INR. unfold Rminus. rewrite Rplus_assoc.
  intro H2. ring_simplify in H2. revert H2. change (INR b <> 0). INR_solve.
Qed.

Lemma inv_inf_1 : forall x, x <> 0%nat -> /INR x <= 1.
Proof.
intros x Hx0.
assert (H : (INR x > 0)) by intuition.
assert (H1 : (INR x >= 1)).
 induction x.
  destruct Hx0. reflexivity.
  
  replace 1 with (0 + 1) by intuition. rewrite S_INR.
  apply Rplus_ge_compat. intuition. intuition.
  
 rewrite <- Rinv_1.
 apply Rle_Rinv. lra. assumption.
intuition.
Qed.

Lemma minus_exp_sum_one : forall a b : nat, 
b <> 0%nat -> e = INR a / INR b ->
INR (fact b) * (e - partial_e b) < 1.
Proof.
intros a b Hb0 Habs.
eapply Rlt_le_trans.
 apply exp_remain_sum. assumption.
 
 unfold Rdiv. rewrite Rmult_1_l. apply inv_inf_1. assumption.
Qed.

Lemma integer_0_1 : forall x, 0 < IZR x < 1 -> False.
Proof.
  intros x [H0 H1].
  apply lt_IZR in H0; apply lt_IZR in H1.
  lia.
Qed.

Lemma eirr : forall a b, b <> 0%nat -> e = (INR a) / (INR b) -> False.
Proof.
intros a b Hb0 Habs.
pose (x := INR (fact b) * (e - partial_e b)).
assert (0 < x < 1).
 split.
  unfold x. apply (minus_exp_sum_pos a) ; intuition.
  
  unfold x. apply (minus_exp_sum_one a) ; intuition.
  
 destruct (integer_exp_minus_sum a b Hb0 Habs) as (m, Hm).
 unfold x in *.
 rewrite Hm in H.
 apply (integer_0_1 m). assumption.
Qed.

(** * Final result: e is irrational *)
Lemma e_is_irrational : forall (a : Z) (b : nat),
  b <> O -> e = (IZR a) / (INR b) -> False.
Proof.
intros [|a|a] b Hb He.
 refine (eirr O b Hb _).
 simpl in He; assumption.
 
 refine (eirr (nat_of_P a) b Hb _).
 rewrite INR_IPR. assumption.
 
 unfold IZR, e in *.
 assert (0 < IPR a / INR b).
 { rewrite <-INR_IPR. apply Rlt_mult_inv_pos. apply pos_INR_nat_of_P. INR_solve. }
 pose proof exp_pos 1 as Hpos.
 rewrite He in Hpos.
 lra.
Qed.
