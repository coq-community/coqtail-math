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

From Coq Require Import Arith Lia.
From Coqtail Require Export Nnewton Ndiv.
Open Scope nat_scope.

Lemma minus_L0: forall p q x, p>=q -> p+x-q=p-q+x.
Proof.
  intros.
  apply Nle_plus in H.
  destruct H.
  rewrite H.
  rewrite minus_plus.
  rewrite <- plus_assoc.
  rewrite minus_plus.
  auto.
Qed.

Lemma minus_L1 : forall p q x, p>=q -> x+(p-q)=x+p-q.
Proof.
  intros.
  apply Nle_plus in H.
  destruct H.
  rewrite H.
  rewrite minus_plus.
  rewrite plus_assoc.
  replace (x+q+x0) with (q+(x+x0)).
  rewrite minus_plus.
  auto.
  ring.
Qed.
Lemma minus_L2 : forall n p q, n>=p+q -> n-p-q=n-(p+q).
Proof.
  intros.
  apply Nle_plus in H.
  destruct H.
  rewrite H.
  rewrite minus_plus.
  replace (p+q+x-p) with (q+x).
  rewrite minus_plus.
  auto.
  rewrite <- plus_assoc.
  rewrite minus_plus.
  auto.
Qed.

Lemma plus_minus : forall n m r, r<=m -> (n+m)-r=n+(m-r).
Proof.
  induction n.
  intros.
  simpl.
  reflexivity.
  intros.
  assert (S n+m=S(n+m)).
  auto with arith.
  rewrite H0.
  rewrite <- minus_Sn_m.
  rewrite IHn.
  auto with arith.
  exact H.
  assert (m<=n+m).
  auto with arith.
  apply le_trans with m.
  exact H. exact H1.
Qed.

Lemma pow : forall (a p:nat), 
    Nprime p -> (p | (a+1)^p - a^p -1).
Proof.
  intros.
  rewrite Nnewton.
  assert (exists p', p=S(S p')).
  destruct p.
  apply Nnot_prime_0 in H. contradiction.
  destruct p.
  apply Nnot_prime_1 in H. contradiction.
  exists p.
  reflexivity.
  destruct H0.
  rewrite H0.
  unfold Nnewton_sum.
  rewrite Nfinite_sum_split_lower.
  rewrite Nfinite_sum_split_upper.
  rewrite Nbinomial_0.
  rewrite Nbinomial_diag.
  rewrite mult_1_l.
  rewrite mult_1_l.
  rewrite Npower_1_n.
  rewrite Npower_1_n.
  rewrite mult_1_r.
  assert (1 +
  (Nfinite_sum_0_n x
     (fun k : nat =>
      Nbinomial (S (S x)) (S k) * a ^ S k * 1 ^ (S (S x) - S k)) +
   a ^ S (S x)) - a ^ S (S x) - 1 =
  (Nfinite_sum_0_n x
     (fun k : nat =>
      Nbinomial (S (S x)) (S k) * a ^ S k * 1 ^ (S (S x) - S k)) + 1 +
   a ^ S (S x)) - a ^ S (S x) - 1).
  rewrite plus_assoc.
  auto with arith.
  rewrite H1. clear H1.
  

  rewrite plus_minus.
  rewrite minus_diag.
  rewrite plus_0_r.
  rewrite plus_minus.
  rewrite minus_diag.
  rewrite plus_0_r.

  rewrite <- H0.
  apply Nfinite_sum_div_compat.
  intros.
  apply Ndiv_mult_compat.
  apply Ndiv_mult_compat.
  apply Nbinomial_div.
  split.
  auto with arith.
  rewrite H0.
  auto with arith.
  auto.
  auto.
  auto.
Qed.


(** * Fermat's little theorem over [nat] *)
Theorem Nlittle_fermat : 
  forall a p, Nprime p -> (p | a ^ p - a).
(* begin hide *)

induction a.
intros.
rewrite Npower_0_n.
simpl.
apply Ndiv_0.
destruct p.
apply Nnot_prime_0 in H. contradiction.
destruct p.
apply Nnot_prime_1 in H. contradiction.
auto with arith.

intros.
destruct p.
apply Nnot_prime_0 in H. contradiction.
destruct p.
apply Nnot_prime_1 in H. contradiction.
simpl.
replace (S a) with (a+1).
replace ((a+1)^(S(S p))-(a+1)) with ((a+1)^(S(S p))-a-1).
assert((S(S p))|(a+1)^(S(S p)) - a^(S (S p))-1).
apply pow. auto.
assert((S(S p))|((a+1)^(S(S p))-a^(S(S p))-1)+(a^(S(S p))-a)).
apply Ndiv_plus_compat.
auto.
apply IHa. auto.
clear H0.
assert((a + 1) ^ S (S p) - a ^ S (S p) - 1 + (a ^ S (S p) - a)
          =(a + 1) ^ S (S p) - a - 1).
assert((a+1)^(S(S p))>=a^(S(S p))+1).
assert((a+1)^(S(S p))>=a^(S(S p))+1^(S (S p))).
apply Npower_plus_le_compat. auto with arith.
rewrite Npower_1_n in H0. auto.
apply Nle_plus in H0.
destruct H0.
rewrite H0.
clear H0.

rewrite minus_L0.
rewrite minus_plus.
rewrite minus_plus.
replace (a ^ S (S p) + 1 + x - a - 1) with (1+(a ^ S (S p) + x - a) - 1).
rewrite minus_plus.
rewrite minus_L1.
auto with arith.
destruct a.
rewrite Npower_0_n. auto. auto with arith.
apply le_trans with ((S a)^1).
rewrite Npower_n_1.
auto.
apply Npower_le_compat_r.
auto with arith.
auto with arith.
rewrite minus_L1.
rewrite plus_assoc.
auto with arith.
destruct a.
rewrite Npower_0_n.
simpl. auto with arith.
auto with arith.
apply le_trans with ((S a)^(S(S p))).
apply le_trans with ((S a)^1).
rewrite Npower_n_1. auto.
apply Npower_le_compat_r.
auto with arith.
auto with arith.
auto with arith.
auto with arith.
rewrite H0 in H1.
revert H1; match goal with |- (?a | ?b) -> (?a | ?c) => cut (b = c) end. now intros ->.
replace (a + 1) with (1 + a) by ring; simpl. repeat rewrite <-plus_assoc. lia.
lia.
lia.
Qed.

(* end hide *)
(** * Alternative formulation of Fermat's little theorem *)
Theorem Nlittle_fermat_alt :
  forall a p, Nprime p -> Nrel_prime a p ->
  (p | a ^ (pred p) - 1).
Proof.
intros.
destruct p.
apply Nnot_prime_0 in H. contradiction.
destruct p.
apply Nnot_prime_1 in H. contradiction.
assert(S(S p)|a^(S(S p))-a).
apply Nlittle_fermat.
auto.
simpl.
rewrite Npower_succ in H1.
replace (a * a ^ S p - a) with (a * a ^ S p - a*1) in H1.
rewrite <- mult_minus_distr_l in H1.
apply Ngauss in H1.
auto.
apply Nrel_prime_sym. auto.
rewrite mult_1_r.
auto.
Qed.

Theorem Nlittle_fermat_alt2 :
  forall a p, Nprime p -> ~(p | a) ->
  (p | a ^ (pred p) - 1).
Proof.
  intros a p Pp pa.
  apply Nlittle_fermat_alt; auto.
  now apply Nrel_prime_prime.
Qed.
