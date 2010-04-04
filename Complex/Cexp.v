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

Require Import Cpser_def.
Require Import Cpser_facts.
Require Import Rseries.
Require Import Rsequence.
Require Import Rsequence_facts.
Require Import Rseries_facts.
Require Import Csequence.
Require Import Exp_prop.
Require Import Csequence_facts.
Require Import Cseries.
Require Import Cseries_facts.
Require Export Complex.
Open Scope C_scope.

(* TODO : à replacer *)
(* begin hide *)
Lemma sum_f_R0_multnat_compat : forall n1 f, (forall n, f (S (2 * n)) = 0) ->
sum_f_R0 (fun n2 : nat => f n2) (2 * n1)
=
sum_f_R0 (fun n2 : nat => f (2 * n2)%nat) (n1).
Proof.
intros n1 f H.
induction n1. simpl. reflexivity.
replace (2 * S n1)%nat with (S (S (2 * n1))) by ring.
do 3 rewrite tech5.
rewrite IHn1.
rewrite (H n1). 
replace (2 * S n1)%nat with (S (S (2 * n1))) by ring.
ring.
Qed.

Lemma sum_f_R0_Smultnat_compat : forall n1 f, (forall n, f ((2 * n)%nat) = 0) ->
sum_f_R0 (fun n2 : nat => f n2) (S (2 * n1))
=
sum_f_R0 (fun n2 : nat => f (S (2 * n2))%nat) (n1).
Proof.
intros n1 f H.
induction n1. simpl. replace 0%nat with (2*0)%nat by ring. rewrite H. simpl. ring.
replace (S (2 * S n1))%nat with (S (S (S (2 * n1)))) by ring.
do 2 rewrite tech5. symmetry. rewrite tech5.
rewrite IHn1.
replace (S (S (2 * n1))) with (2 * (S n1))%nat by ring.
rewrite H.
ring.
Qed.
(* end hide *)

(** ** Definition of Complex exponential as an infinite sum*)
Definition expc_in (z l:C) : Prop :=
  infinite_sum (fun j:nat => / INR (fact j) * z ^ j) l.

Lemma exist_expc : forall z:C, { l:C | expc_in z l }.
Proof.
intros z.
unfold expc_in.
unfold infinite_sum.
unfold Cmet.C_met. simpl.
unfold Cmet.C_dist.
generalize Cseq_norm_Rseq.
intros H1.
destruct (exist_exp (Cnorm z)) as (l, H).
unfold Cseq_cv in H1.
apply H1.
unfold Rseq_cv. unfold Rtrigo_def.exp_in in H.
unfold Rfunctions.infinite_sum in H.
exists l. 
intros eps Heps. generalize (H eps Heps). clear H. intros H.
destruct H as (N, H). exists N. intros n Hn. generalize (H n Hn). clear H. intros H.
unfold R_dist in *.
assert ( H4 :( forall n,
 (sum_f_R0 (fun j : nat => (/ INR (fact j) * Cnorm z ^ j)%R) n)
=(sum_f_R0 (fun n0 : nat => Cnorm (/ INR (fact n0) * z ^ n0)) n))).
induction n0. simpl. unfold Cnorm. unfold Cnorm_sqr.
repeat rewrite Cinv_l. simpl.
repeat rewrite Rinv_l. replace (sqrt(1 * 1 + 0 * 0)) with 1.
reflexivity.
rewrite Rmult_0_l. rewrite Rplus_0_r.
rewrite Rmult_1_l.
rewrite sqrt_1. reflexivity.
intro. fourier. intro. intuition.
simpl. 
rewrite IHn0. rewrite Cnorm_Cmult.
rewrite Cnorm_Cmult. rewrite Cnorm_pow.
rewrite Cnorm_inv. rewrite Cnorm_IRC_Rabs.
unfold Rabs. case (Rcase_abs (INR (fact n0 + n0 * fact n0))).
intros H2. destruct (pos_INR (fact n0 + n0 * fact n0)).
fourier. rewrite H0 in H2. fourier.
intros H2. field.
rewrite plus_INR. 
assert (H5 : INR (fact n0) + INR (n0 * fact n0) > 0).
replace 0%R with (0 + 0)%R by intuition. apply Rplus_gt_ge_compat.
apply lt_0_INR. apply lt_O_fact. destruct (pos_INR (n0 * fact n0)) .
fourier. fourier.
intro H11. rewrite H11 in H5. fourier.
rewrite plus_INR. 
assert (H5 : INR (fact n0) + INR (n0 * fact n0) > 0).
replace 0%R with (0 + 0)%R by intuition. apply Rplus_gt_ge_compat.
apply lt_0_INR. apply lt_O_fact. destruct (pos_INR (n0 * fact n0)) .
fourier. fourier.
intro H11. unfold IRC in *.
rewrite <- Ceq in H11. destruct H11 as (H11, H12). simpl in *.
rewrite H11 in H5. fourier.
rewrite <- H4. intuition.
Qed.

Open Scope C_scope.

Definition expc (z:C) : C := proj1_sig (exist_expc z).


(* TODO : RHAAAA mais c'est moche !!!! *)

(** ** Euler's Formula*)

Lemma expc_R_compat : forall a : R, exp (a) = Cre (expc (a +i 0))
/\ Cim (expc (a +i 0)) = 0%R.
Proof.
intros a.
unfold exp, expc. destruct (exist_exp a) as (l, H).
destruct (exist_expc (a +i 0)) as (l1, H1).
simpl.
unfold exp_in in H.
unfold expc_in in H1.
assert (H8 : forall n, Cim (sum_f_C0 (fun j : nat => / INR (fact j) * (a +i  0) ^ j) n) = 0).
induction n. simpl. field.
rewrite sum_f_C0_simpl. rewrite <- Cim_add_compat.
rewrite IHn. rewrite Cim_mul. rewrite Cpow_Cim_0.
rewrite Cpow_Cre_0.
rewrite IRC_INR_INC. rewrite INC_inv_Cim_INR.
ring. apply fact_neq_0.
assert (H6 : Cim l1 = 0).
apply (Rseq_cv_unique (fun n => Cim (sum_f_C0 (fun j : nat => / INR (fact j) * (a +i  0) ^ j) n))).
apply (Cseq_Rseq_Rseq_equiv (fun n => sum_f_C0 (fun j : nat => / INR (fact j) * (a +i  0) ^ j) n) l1).
unfold Cseq_cv. apply H1.
apply (Rseq_cv_eq_compat (fun n0 : nat => 0)).
unfold "==". induction n. simpl. field.
rewrite sum_f_C0_simpl. rewrite <- Cim_add_compat.
rewrite <- IHn. rewrite Cim_mul. rewrite Cpow_Cim_0.
rewrite Cpow_Cre_0. 
rewrite IRC_INR_INC. rewrite INC_inv_Cim_INR.
ring. apply fact_neq_0.
unfold Rseq_cv. intros. exists 0%nat. intros. unfold R_dist.
unfold Rminus. rewrite Ropp_0. rewrite Rplus_0_l.
unfold Rabs. destruct (Rcase_abs 0). fourier. intuition.
unfold infinite_sum in *. unfold infinit_sum in *. split.
apply (Rseq_cv_unique (sum_f_R0 (fun j : nat => (/ INR (fact j) * a ^ j)%R))).
unfold Rseq_cv. assumption.
unfold Rseq_cv.
unfold dist in *. simpl in *.
intros eps Heps.
generalize (H1 eps Heps). intros H2.
destruct H2 as (N, H2).
exists N. intros n HN. generalize (H2 n HN). intros H3.
unfold Cmet.C_dist in *.
unfold R_dist.
assert (H4 : Rabs (Cnorm (sum_f_C0 (fun j : nat => / INR (fact j) * (a +i  0) ^ j) n) - 
Cnorm (l1)) <=
Cnorm (sum_f_C0 (fun j : nat => / INR (fact j) * (a +i  0) ^ j) n - l1) ).
apply Cnorm_triang_rev.
eapply Rle_lt_trans. Focus 2. apply H3. 
unfold Cnorm. unfold Cnorm_sqr.
rewrite <- Cre_minus_compat.
rewrite <- Cim_minus_compat.
rewrite H6. 
rewrite H8. rewrite <- sum_f_C0_Cre_compat.
assert (H10 : forall n, 
((sum_f_R0 (fun n0 : nat => Cre (/ INR (fact n0) * (a +i  0) ^ n0)) n)) = 
((sum_f_R0 (fun j : nat => (/ INR (fact j) * a ^ j)%R) n))).
induction n0. simpl. field.
rewrite tech5. rewrite tech5.
rewrite IHn0. rewrite Cre_mul. rewrite Cpow_Cre_0.
rewrite Cpow_Cim_0. 
rewrite IRC_INR_INC. rewrite INC_inv_Cim_INR. rewrite INC_inv_Cre_INR.
ring. apply fact_neq_0. apply fact_neq_0.
rewrite H10.
unfold Rminus. rewrite Ropp_0. rewrite Rplus_0_l. rewrite Rmult_0_l. rewrite Rplus_0_r. 
rewrite <- sqrt_Rsqr_abs. unfold Rsqr. right. reflexivity.
apply H6.
Qed.

(* TODO c'est encore tres moche *)
Lemma expc_trigo_compat : forall a, cos a +i sin a = expc (0 +i a).
Proof.
intros a.
CusingR_simpl.
unfold expc.
destruct (exist_expc (0 +i  a)) as (l, H).
simpl. unfold expc_in in H.
unfold cos. destruct (exist_cos (Rsqr a)) as (l1, H1).
unfold cos_in in H1.
unfold cos_n in H1.
unfold infinit_sum in H1. unfold infinite_sum in H.
unfold dist in H. simpl in *.
apply (Rseq_cv_unique (sum_f_R0 (fun j :nat => ((-1) ^ j / INR (fact (j + (j + 0))) * a² ^ j)%R))).
unfold Rseq_cv. apply H1.
unfold Rseq_cv. intros eps Heps. assert (Heps1 : sqrt eps > 0).
apply sqrt_lt_R0. assumption.
generalize (H eps Heps). intros H2.
destruct H2 as (N, H2). exists N. intros n Hn. assert (H2n: (2* n >= N)%nat) by omega.
generalize (H2 (2*n)%nat H2n).
intros H3.
unfold Cmet.C_dist in H3. unfold R_dist.
unfold Cnorm in H3. unfold Cnorm_sqr in H3.
rewrite <- Cre_minus_compat in H3.
rewrite <- sum_f_C0_Cre_compat in H3.
assert (H6 : forall n, (sum_f_R0 (fun n : nat => Cre (/ INR (fact n) * (0 +i  a) ^ n)) (2* n)
=
(sum_f_R0 (fun n : nat => Cre (/ INR (fact (2*n)) * (0 +i  a) ^ (2*n))) n))).
intros n0.
apply sum_f_R0_multnat_compat.
intros. rewrite Cre_mul. 
rewrite IRC_INR_INC. rewrite INC_inv_Cim_INR.
ring_simplify. CpowR (S (2 * n1)). 
assert ((4 * n2)%nat = S (2 * n1) -> False)%nat. omega. intuition.
ring. assert ((4 * n2 + 2)%nat = S (2 * n1) -> False)%nat. omega. intuition.
ring. apply fact_neq_0.
assert (H4 : forall n, sum_f_R0 (fun n : nat => Cre (/ INR (fact n) * (0 +i  a) ^ n)) (2 * n) =
(sum_f_R0 (fun j : nat => ((-1) ^ j / INR (fact (j + (j + 0))) * a² ^ j)%R)
     n)).
intros n0.
rewrite H6.
induction n0. simpl. field.
do 2 rewrite tech5. rewrite Cre_mul.
rewrite IRC_INR_INC. rewrite INC_inv_Cre_INR.
rewrite INC_inv_Cim_INR.
rewrite IHn0. rewrite Rmult_0_l.
unfold Rminus. rewrite Ropp_0. rewrite Rplus_0_r.
replace (S n0 + (S n0 + 0))%nat with (2 * S n0)%nat by ring.
rewrite Cpow_mul. replace ((0 +i a) ^ 2 ) with (- Rsqr a +i 0).
rewrite Cpow_Cre_0. RpowR (S n0).
rewrite pow1. unfold Rdiv. ring.
rewrite pow1. unfold Rdiv. ring.
simpl. unfold Rsqr. CusingR_f.
apply fact_neq_0. apply fact_neq_0.
rewrite <- H4. 
apply Rsqr_incrst_1 in H3.
rewrite Rsqr_sqrt in H3.
apply Rplus_lt_reg_pos_r in H3.
replace ((sum_f_R0 (fun n : nat => Cre (/ INR (fact n) * (0 +i  a) ^ n)) (2 * n) -
      Cre l) *
     (sum_f_R0 (fun n : nat => Cre (/ INR (fact n) * (0 +i  a) ^ n)) (2 * n) -
      Cre l))%R
with
(Rsqr ((sum_f_R0 (fun n : nat => Cre (/ INR (fact n) * (0 +i  a) ^ n)) (2 * n) -
      Cre l))) in H3 by (unfold Rsqr ; ring).
apply Rsqr_lt_abs_0 in H3.
rewrite (Rabs_right eps) in H3.
assumption.
intuition.
destruct (Rle_0_sqr (Cim (sum_f_C0 (fun j : nat => / INR (fact j) * (0 +i  a) ^ j) (2 * n) - l))).
unfold Rsqr in *. fourier. intuition.
apply Cnorm_sqr_pos. apply sqrt_positivity. apply Cnorm_sqr_pos.
intuition.
unfold expc.
destruct (exist_expc (0 +i  a)) as (l, H).
simpl. unfold expc_in in H.
unfold sin. destruct (exist_sin (Rsqr a)) as (l1, H1).
unfold sin_in in H1.
unfold sin_n in H1.
unfold infinit_sum in H1. unfold infinite_sum in H.
unfold dist in H. simpl in *.
destruct (Req_or_neq a) as [H11|H11].
Focus 2.
apply (Rmult_eq_reg_l (/a)%R).
rewrite <- Rmult_assoc. rewrite Rinv_l.
rewrite Rmult_1_l.
apply (Rseq_cv_unique (sum_f_R0 (fun j :nat => ((-1) ^ j / INR (fact (j + (j + 0) + 1 )) * a² ^ j)%R))).
unfold Rseq_cv. apply H1.
unfold Rseq_cv. intros eps Heps. assert (Heps1 : sqrt eps > 0).
apply sqrt_lt_R0. assumption.
assert (Hepsa : Rabs a * eps > 0). apply Rmult_gt_0_compat.
unfold Rabs. destruct (Rcase_abs a) as [H20|H20]. fourier. destruct H20. fourier. intuition.
assumption.
generalize (H (Rabs a * eps)%R Hepsa). intros H2.
destruct H2 as (N, H2). exists N. intros n Hn. assert (HS2n: (S (2* n) >= N)%nat) by omega.
generalize (H2 (S (2*n))%nat HS2n).
intros H3.
unfold Cmet.C_dist in H3. unfold R_dist.
unfold Cnorm in H3. unfold Cnorm_sqr in H3.
rewrite <- Cim_minus_compat in H3.
rewrite <- sum_f_C0_Cim_compat in H3.
assert (H6 : forall n, (sum_f_R0 (fun n : nat => Cim (/ INR (fact n) * (0 +i  a) ^ n)) (S (2* n))
=
(sum_f_R0 (fun n : nat => Cim (/ INR (fact (S (2*n))) * (0 +i  a) ^ (S (2*n)))) n))).
intros n0.
apply sum_f_R0_Smultnat_compat.
intros. rewrite Cim_mul. 
rewrite IRC_INR_INC. rewrite INC_inv_Cim_INR.
ring_simplify. CpowR ((2 * n1)%nat). ring. 
assert ((4 * n2 + 1)%nat = (2 * n1) -> False)%nat. omega. intuition.
ring. assert ((4 * n2 + 3)%nat = (2 * n1) -> False)%nat. omega. intuition.
apply fact_neq_0.
assert (H4 : forall n, (/a * sum_f_R0 (fun n : nat => Cim (/ INR (fact n) * (0 +i  a) ^ n)) (S (2 * n)))%R =
(sum_f_R0 (fun j : nat => ((-1) ^ j / INR (fact (j + (j + 0) + 1)) * a² ^ j)%R)
     n)).
intros n0.
rewrite H6.
induction n0. simpl. field. assumption.
do 2 rewrite tech5. rewrite Cim_mul.
rewrite IRC_INR_INC. rewrite INC_inv_Cre_INR.
rewrite INC_inv_Cim_INR. rewrite Rmult_plus_distr_l.
rewrite IHn0. rewrite Rmult_0_r. rewrite Rplus_0_r.
replace (S n0 + (S n0 + 0) + 1)%nat with (S (2 * S n0))%nat by ring.
rewrite Cpow_S. rewrite Cpow_mul. replace ((0 +i a) ^ 2 ) with (- Rsqr a +i 0).
rewrite Cim_mul. rewrite Cpow_Cim_0. ring_simplify.
rewrite Cpow_Cre_0. simpl Cim.
replace (-Rsqr a)%R with (-1 * Rsqr a)%R by (unfold Rsqr ; ring).
rewrite MyRfunctions.Rpow_mult_distr. unfold Rdiv. field.
split. apply not_0_INR. apply fact_neq_0. assumption.
unfold Rsqr. CusingR_f. apply fact_neq_0. apply fact_neq_0.
rewrite <- H4. 
apply Rsqr_incrst_1 in H3.
rewrite Rsqr_sqrt in H3.
rewrite Rplus_comm in H3.
apply Rplus_lt_reg_pos_r in H3.
replace ((sum_f_R0 (fun n : nat => Cim (/ INR (fact n) * (0 +i  a) ^ n)) (S (2 * n)) -
      Cim l) *
     (sum_f_R0 (fun n : nat => Cim (/ INR (fact n) * (0 +i  a) ^ n)) (S (2 * n)) -
      Cim l))%R
with
(Rsqr ((sum_f_R0 (fun n : nat => Cim (/ INR (fact n) * (0 +i  a) ^ n)) (S (2 * n)) -
      Cim l))) in H3 by (unfold Rsqr ; ring).
apply Rsqr_lt_abs_0 in H3.
rewrite <- Rmult_minus_distr_l.
rewrite Rabs_mult. rewrite Rabs_Rinv. 
apply (Rmult_lt_reg_l (Rabs a)). unfold Rabs.
destruct (Rcase_abs a) as  [H20|H20]. fourier. destruct H20. assumption. intuition.
field_simplify. unfold Rdiv. rewrite Rinv_1. do 2 rewrite Rmult_1_r.
replace ( Rabs (Rabs a * eps))%R with (Rabs a * eps)%R in H3.
assumption.
unfold Rabs at 2. destruct (Rcase_abs (Rabs a * eps)) as [H20|H20 H20].
fourier. intuition. apply Rabs_no_R0. assumption.
assumption. 
generalize (Rle_0_sqr (Cre
  (sum_f_C0 (fun j : nat => / INR (fact j) * (0 +i  a) ^ j) (S (2 * n)) - l))).
intuition.
apply Cnorm_sqr_pos. apply sqrt_positivity. apply Cnorm_sqr_pos.
apply Rmult_le_pos. apply Rabs_pos. left. assumption.
assumption. apply Rinv_neq_0_compat. assumption.
rewrite H11 in *.
ring_simplify. 
apply (Rseq_cv_unique (sum_f_R0 (fun j :nat => 0)%R)).
assert (H20 : forall n, (sum_f_R0 (fun _ : nat => 0)) n = 0).
induction n. simpl. reflexivity. simpl. rewrite IHn. ring.
unfold Rseq_cv. intros eps Heps. exists 0%nat. intros n Hn.
unfold R_dist. unfold Rabs. induction n. simpl.
ring_simplify (0-0)%R. rewrite Ropp_0.
destruct (Rcase_abs 0). fourier. intuition. rewrite H20.
destruct (Rcase_abs (0-0)%R). fourier. fourier.
unfold Rseq_cv. intros eps Heps.
generalize (H eps Heps). intros H2.
destruct H2 as (N, H2). exists N. intros n Hn.
generalize (H2 n Hn). intros H3.
unfold Cmet.C_dist in H3. unfold R_dist.
unfold Cnorm in H3. unfold Cnorm_sqr in H3.
rewrite <- Cim_minus_compat in H3.
rewrite <- sum_f_C0_Cim_compat in H3.
apply Rsqr_incrst_1 in H3. 
rewrite Rsqr_sqrt in H3.
rewrite Rplus_comm in H3.
apply Rplus_lt_reg_pos_r in H3.
replace ((sum_f_R0 (fun n : nat => Cim (/ INR (fact n) * (0 +i  0) ^ n)) n -
      Cim l) *
     (sum_f_R0 (fun n : nat => Cim (/ INR (fact n) * (0 +i  0) ^ n)) n -
      Cim l))%R
with
(Rsqr (sum_f_R0 (fun n : nat => Cim (/ INR (fact n) * (0 +i  0) ^ n)) n -
      Cim l))%R in H3 by (unfold Rsqr ; ring).
apply Rsqr_lt_abs_0 in H3.
assert (H42 : forall n, sum_f_R0 (fun n : nat => Cim (/ INR (fact n) * (0 +i  0) ^ n)) n =
(sum_f_R0 (fun _ : nat => 0) n)).
induction n0. simpl. field.
do 2 rewrite tech5. rewrite Cim_mul.
rewrite Cpow_Cim_0. rewrite Cpow_Cre_0.
rewrite IRC_INR_INC. rewrite INC_inv_Cre_INR. rewrite INC_inv_Cim_INR.
rewrite IHn0. ring. apply fact_neq_0. apply fact_neq_0.
rewrite <- H42. unfold Rabs at 2 in H3. destruct (Rcase_abs eps) as [H20|[H20|H20]].
fourier. intuition. fourier.
generalize (Rle_0_sqr (Cre (sum_f_C0 (fun j : nat => / INR (fact j) * (0 +i  0) ^ j) n - l))).
intuition. apply Cnorm_sqr_pos.
apply sqrt_positivity. apply Cnorm_sqr_pos.
intuition.
Qed.

(* TODO pour les conventions de nommage *)
Lemma euler_formula : forall a, cos a +i sin a = expc (0 +i a).
Proof.
apply expc_trigo_compat.
Qed.

(** ** Properties of the exponential *)

Lemma expc_abs_cv x : {l | Cser_abs_cv (fun n => (/ INR (fact n) * x ^ n)%C) l}.
Proof.
intros x.
destruct (exist_exp (Cnorm x)) as [ex Hex].
exists ex.
eapply Rser_cv_eq_compat.
 2:apply Hex.
 
 intro n.
 rewrite Cnorm_Cmult.
 rewrite Cnorm_pow.
 rewrite Cnorm_inv; [|apply IRC_neq_compat; apply INR_fact_neq_0].
 rewrite Cnorm_IRC_Rabs.
 rewrite Rabs_right; [|apply Rgt_ge; apply INR_fact_lt_0].
 trivial.
Qed.

Lemma binomial_diag n : Binomial.C n n = 1.
Proof.
intros n.
unfold Binomial.C.
rewrite minus_diag.
simpl.
field.
INR_solve; apply fact_neq_0.
Qed.

Lemma binomial_zero n : Binomial.C n 0 = 1.
Proof.
intros n.
unfold Binomial.C.
simpl.
rewrite <- minus_n_O.
field.
INR_solve; apply fact_neq_0.
Qed.

Open Scope C_scope.

Lemma binomial_sum (x y:C) n :
  (x + y) ^ n = sum_f_C0 (fun p => IRC (Binomial.C n p) * x ^ p * y ^ (n - p)) n.
Proof.
intros x y n.
induction n.
 unfold Binomial.C; simpl.
 rewrite <- Ceq; simpl; split; field.
 
 destruct n.
  unfold Binomial.C; simpl.
  rewrite <- Ceq; simpl; split; field.
  
  rewrite sum_f_C0_simpl.
  rewrite <- sum_f_C0_reindex.
  
  rewrite Csum_eq_compat with _ (fun k => 
    Binomial.C (S n)    k  * x ^ S k * y ^ (S (S n) - S k) +
    Binomial.C (S n) (S k) * x ^ S k * y ^ (S (S n) - S k)) _.
   rewrite sum_f_C0_add_compat.
   rewrite Cpow_S.
   rewrite IHn.
   rewrite Cmult_add_distr_l.
   do 2 (rewrite Cmult_comm; rewrite sum_f_C0_mult).
   assert (AP:forall a b c d e f, a = d + f -> b = c + e -> a + b = c + (d + e) + f)
     by (intros; subst; ring); apply AP; clear AP.
    rewrite sum_f_C0_simpl.
    repeat rewrite binomial_diag.
    repeat rewrite minus_diag.
    apply Cadd_eq_compat.
     apply Csum_eq_compat_weak; intro; simpl; ring.
     simpl; ring.
    
    rewrite <- sum_f_C0_reindex.
    apply Cadd_eq_compat.
     simpl; repeat rewrite binomial_zero; ring.
     apply Csum_eq_compat; intros j Hj.
     rewrite <- minus_Sn_m with (S n) _; [|omega].
     simpl; ring.
   
   intros j Hj.
   repeat rewrite <- Cmult_add_distr_r.
   rewrite <- Binomial.pascal; [|omega].
   rewrite Cadd_IRC_Rplus; trivial.
Qed.

Lemma expc_plus : forall a b, expc (a + b) = (expc a * expc b)%C.
Proof.
intros a b.
unfold expc.
destruct (exist_expc (a + b)) as [eab Hab].
destruct (exist_expc a) as [ea Ha].
destruct (exist_expc b) as [eb Hb].
destruct (expc_abs_cv a) as [lna Hlna].
simpl.
pose (fun x n => (/ INR (fact n) * x ^ n)%C) as tg.
apply Cser_cv_unique with (tg (a + b)%C).
 apply Hab.
 
 eapply Cser_cv_eq_compat.
  2:apply (Ccauchy_product (tg a) (tg b) ea eb lna Ha Hb Hlna).
  
  intro n; simpl.
  unfold tg.
  rewrite binomial_sum.
  rewrite sum_f_C0_mult.
  apply Csum_eq_compat_weak; intros p.
  unfold Binomial.C.
  rewrite Cdiv_IRC_Rdiv.
   repeat rewrite Cmult_IRC_Rmult.
   repeat rewrite IRC_INR_INC.
   field; repeat split; replace C0 with (INC O)%C by trivial;
     apply not_INC; apply fact_neq_0.
  apply Rmult_integral_contrapositive.
   INR_solve; apply fact_neq_0.
Qed.

Lemma expc_0 : expc C0 = C1.
Proof.
destruct (expc_R_compat 0) as (H1, H2).
CusingR_simpl.
unfold C0. rewrite <- H1. apply exp_0.
unfold C0. apply H2.
Qed.

Lemma expc_mult : forall a n, expc (INC n * a) = (expc a) ^ n.
Proof.
intros a n.
induction n.
simpl. rewrite Cmult_0_l. apply expc_0.
rewrite S_INC. rewrite Cpow_S.
rewrite Cmult_add_distr_r. rewrite Cmult_1_l.
rewrite expc_plus. rewrite IHn. ring. 
Qed.
