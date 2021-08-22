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
Require Import Cprop_base.
Require Import Cfunctions.
Require Import Cpow.
Require Import Lia.

Open Scope C_scope.

Lemma binom_add_INC : forall n k : nat, (n>= k)%nat -> - INC (fact n) / INC (fact (n-k) * fact k)
 + INC (fact (S n)) / INC (fact k * fact (S (n - k)))
= INC (k * fact n) / INC ( fact k * fact (S (n-k))).
Proof.
intros n k H.
do 2 rewrite fact_simpl.
replace (INC (fact k * (S (n - k) * fact (n - k)))) with (INC (S (n-k)) * INC (fact k * fact (n-k))) by
(rewrite mult_comm ; symmetry ; rewrite mult_comm ; rewrite <- mult_INC ; 
rewrite mult_assoc ; reflexivity).

replace (INC (S n * fact n)) with (INC (S n) * INC (fact n)) 
by (rewrite mult_INC ; reflexivity).

unfold Cdiv. rewrite Cinv_mult_distr.
  apply (Cmult_eq_reg_l (INC (S (n - k)))). apply not_0_INC. intuition lia.
  rewrite Cmult_add_distr_l. repeat rewrite mult_INC.
  field_simplify.
    rewrite Cmult_comm. rewrite <- Cmult_add_distr_l.
    unfold Cdiv. repeat rewrite Cmult_assoc. apply Cmult_eq_compat_l.
    rewrite Cadd_comm. 
    replace (INC (S n) + - INC (S (n - k))) with (INC (S n) - INC (S (n - k))) by intuition. 
    rewrite <- minus_INC. simpl. rewrite minus_INC. rewrite minus_INC. ring. lia. lia. lia.
  split. apply not_0_INC. apply fact_neq_0. split. apply not_0_INC. apply fact_neq_0.
   apply not_0_INC. intuition lia.
   split. apply not_0_INC. apply fact_neq_0. split. apply not_0_INC. apply fact_neq_0.
   apply not_0_INC. intuition lia.
 apply not_0_INC. intuition lia.
apply not_0_INC. intro Habs. apply mult_is_O in Habs. elim Habs; apply fact_neq_0.
Qed.

(* begin hide *)
Lemma equi_binom_add : 
forall zR zI : R, forall n n0 : nat, (n0 <= n)%nat -> 
   ((zR +i 0%R) + (0%R +i zI)) *
   ((zR +i 0%R) ^ n0 * (0%R +i zI) ^ (n - n0) * INC (fact n) *
    / INC (fact n0 * fact (n - n0))) -
   (zR +i 0%R) ^ n0 * (0%R +i zI) ^ (S n - n0) * INC (fact (S n)) *
   / INC (fact n0 * fact (S n - n0)) = 
   (zR +i 0%R) ^ (S n0) * (0%R  +i zI) ^ (n - n0) *  INC (fact n) *
    / INC (fact n0 * fact (n - n0)) - (zR +i 0%R) ^ n0 * (0%R +i zI) ^ (S n - n0) *
INC (n0 * fact n)/ INC ( (fact n0) * fact (n-n0+1)).
Proof.
intros zR zI n k Hinf.
apply Cminus_diag_uniq.
rewrite Cmult_add_distr_r.
repeat rewrite <- Cmult_assoc.
assert (H : ( forall a b c d : C, a + b - c - d = a + (b - c) - d)). intros ; ring.
rewrite H.
(*replace*)
replace ((0%R +i  zI) * (zR +i 0%R) ^ k * (0%R +i zI) ^ (n - k) ) with
 ( (zR +i 0%R) ^ k * (0%R +i zI) ^ (S n - k)) by 
(symmetry ; rewrite Cmult_comm ; rewrite <- Cmult_assoc ; rewrite Cmult_comm ; 
rewrite <- Cpow_S ; rewrite minus_Sn_m ; intuition ;apply Hinf).
(*end replace*)
replace ((zR +i 0%R) ^ k * (0%R +i zI) ^ (S n - k) * INC (fact n) *
 / INC (fact k * fact (n - k)) -
 (zR +i 0%R) ^ k * (0%R +i zI) ^ (S n - k) * INC (fact (S n)) *
 / INC (fact k * fact (S n - k))) with
((zR +i 0%R) ^ k * (0%R +i zI) ^ (S n - k) * (INC (fact n) *
 / INC (fact k * fact (n - k)) - INC (fact (S n)) *
 / INC (fact k * fact (S n - k)))) by ring.
(* replace *)
replace (INC (fact n) * / INC (fact k * fact (n - k)) -
 INC (fact (S n)) * / INC (fact k * fact (S n - k))) with
(-(INC (k * fact n) / INC ( fact k * fact (S (n-k))))).
2: { rewrite <- binom_add_INC.
rewrite minus_Sn_m. unfold Cdiv. rewrite Copp_add_distr. rewrite Copp_mult_distr_l_reverse.
rewrite Copp_invol.
replace (fact k * fact (n-k))%nat with (fact (n-k) * fact k)%nat by ring.
reflexivity. apply Hinf. apply Hinf. }
(* end replace*)
assert (H1 : (forall a b c d : C, a + b - (c - d) = (a -c) + (b + d))). intros. ring.
rewrite H1.
rewrite Cpow_S. ring_simplify.
replace ((n- k +1)%nat) with (S(n-k))%nat by ring.
field_simplify. unfold Cdiv. repeat rewrite Cmult_0_l. reflexivity.
apply not_0_INC. intro Habs.  apply mult_is_O in Habs. elim Habs.
apply fact_neq_0. apply fact_neq_0.
Qed.

Lemma fun_prop_bin_add_INC : forall (n : nat) (zR zI : R), (sum_f_C0
  (fun n0 : nat =>
   (zR +i zI) * ((zR +i 0%R) ^ n0 * (0%R +i zI) ^ (n - n0) * INC (fact n) /
    INC (fact n0 * fact (n - n0))) -
   (zR +i 0%R) ^ n0 * (0%R +i zI) ^ (S n - n0) * INC (fact (S n)) /
   INC (fact n0 * fact (S n - n0))) n) = (sum_f_C0 
     (fun n0 : nat => (zR +i0%R)^ S n0 * (0%R +i zI) ^ (n-n0) * INC (fact n)
     /INC (fact n0 * fact (n - n0)) - (zR +i 0%R) ^ n0 * (0%R +i zI)^ (S n-n0) * INC (n0*fact n)
     / INC (fact n0 * fact (n-n0 + 1))) n ).
Proof.
intros n zR zI.
apply sum_f_C0_eq_seq.
intros n0 H.
replace (zR +i zI) with ((zR, 0%R) + (0%R, zI)) by (rewrite <- Ceq ; simpl ; intuition).
generalize equi_binom_add. intro Hn1. unfold Cdiv in *. apply Hn1. exact H. 
Qed.
(* end hide *)

Lemma Cpow_add_dev : forall z : C, forall n : nat,
((z ^ n)%C = (sum_f_C0 (fun k => (Cre z +i 0%R)^k * (0%R +i Cim z) ^ (n-k) * INC (fact n)/INC ((fact k) * fact (n-k))) n))%C.
Proof.
intros z.
induction n.
simpl. CusingR_f.
destruct z as (zR, zI).
replace ((zR, zI) ^ S n) with ((zR, zI) * (zR, zI) ^ n) by (simpl; reflexivity).
rewrite IHn.
replace (Cre (zR, zI)) with zR by (simpl; reflexivity).
replace (Cim (zR, zI)) with zI by (simpl; reflexivity).
rewrite sum_f_C0_mult.
rewrite sum_f_C0_simpl.
apply Cminus_diag_uniq.
assert (H4 : ( forall a b c : C, a - (b + c) = (a - b) - c)). intros; ring.
rewrite H4.
rewrite <- sum_f_C0_minus_compat.
replace (zR, zI) with (zR +i zI) by reflexivity.
replace (sum_f_C0
  (fun n0 : nat =>
   (zR +i zI) * ((zR +i 0%R) ^ n0 * (0%R +i zI) ^ (n - n0) * INC (fact n) /
    INC (fact n0 * fact (n - n0))) -
   (zR +i 0%R) ^ n0 * (0%R +i zI) ^ (S n - n0) * INC (fact (S n)) /
   INC (fact n0 * fact (S n - n0))) n)
with (sum_f_C0 
     (fun n0 : nat => (zR +i0%R)^ S n0 * (0%R +i zI) ^ (n-n0) * INC (fact n)
     /INC (fact n0 * fact (n - n0)) - (zR +i 0%R) ^ n0 * (0%R +i zI)^ (S n-n0) * INC (n0 * fact n) / INC (fact n0 * fact (n-n0 + 1))) n )
by (rewrite fun_prop_bin_add_INC ; reflexivity).
rewrite sum_f_C0_minus_compat.
destruct n. CusingR_f.
rewrite sum_f_C0_simpl. rewrite <- sum_f_C0_reindex.
(* begin replace *)
replace (sum_f_C0
  (fun n0 : nat =>
   (zR +i 0%R) ^ S n0 * (0%R +i zI) ^ (S n - n0) * INC (fact (S n)) /
   INC (fact n0 * fact (S n - n0))) n) with
(sum_f_C0
   (fun k : nat =>
    (zR +i 0%R) ^ S k * (0%R +i zI) ^ (S (S n) - S k) *
    INC (S k * fact (S n)) / INC (fact (S k) * fact (S n - S k + 1))) n).
2: { apply sum_f_C0_eq_seq. intros m H.
repeat rewrite fact_simpl. repeat rewrite mult_INC.
replace (S n - S m + 1)%nat with (S n - m)%nat by intuition lia.
replace (S (S n) - S m)%nat with (S n - m)%nat by intuition.
field. 
split ; try split ; apply not_0_INC ; try apply fact_neq_0 ; intuition lia.
}
ring_simplify.
replace (S n - S n)%nat with O by intuition.
replace (S (S n) - S (S n))%nat with O by intuition.
repeat rewrite fact_simpl.
repeat rewrite mult_INC. simpl (INC 0).
field_simplify. unfold Cdiv. repeat rewrite Cmult_0_r. rewrite Cmult_0_l. reflexivity.
split ; try split ; try split ; try split ; try apply not_0_INC ; try apply fact_neq_0 ; intuition lia.
Qed.
