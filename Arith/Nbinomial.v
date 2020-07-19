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

Require Import Arith.
Require Import Compare.
Require Export Nfinite_prod.
Require Export Ndiv.
Open Scope nat_scope.

(** * Definition of a binomial coefficient using Pascal relation*)
(** Simple definition *)
Fixpoint Nsimple_binomial (n k : nat) : nat :=
match n with
| 0 =>
  match k with
  | 0 => 1
  | S _ => 0
  end
| S n' =>
  match k with
  | 0 => 1
  | S k' => (Nsimple_binomial n' k') + (Nsimple_binomial n' k)
  end
end.

(** Alternative definition *)
Definition Nbinomial (n k : nat) : nat :=
match leb k n with
| true => Nsimple_binomial n k
| false => 0
end.

(** * Properties of binomial coefficients *)

(** n choose k is zero if k is greater than n (simple version) *)
Lemma Nsimple_binomial_outside : forall n m,
  n < m -> Nsimple_binomial n m = 0.
Proof.
induction n.
intros.
compute.
destruct m.
apply lt_irrefl in H.
contradiction.
reflexivity.
intros.
unfold Nsimple_binomial. fold Nsimple_binomial.
destruct m.
apply lt_n_O in H.
contradiction.
assert (n<m).
auto with arith.
rewrite IHn.
simpl.
assert (n<S m).
auto with arith.
apply IHn.
auto.
auto.
Qed.

(** n choose k is zero if k is greater than n (alternative definition) *)
Lemma Nbinomial_outside : forall n m,
  n < m -> Nbinomial n m = 0.
Proof.
intros.
apply leb_correct_conv in H.
unfold Nbinomial.
rewrite H.
reflexivity.
Qed.

(** Special values of binomial coefficients *)
Lemma Nbinomial_0 : forall n, Nbinomial n 0 = 1.
Proof.
destruct n.
compute. reflexivity.
unfold Nbinomial.
assert (leb 0 (S n)=true).
apply leb_correct.
auto with arith.
rewrite H. clear H.
unfold Nsimple_binomial.
reflexivity.
Qed.

Lemma Nbinomial_diag : forall n, Nbinomial n n = 1.
Proof.
induction n.
compute. reflexivity.
unfold Nbinomial.
assert (leb (S n) (S n)=true).
apply leb_correct.
auto with arith.
rewrite H. clear H.
unfold Nsimple_binomial. fold Nsimple_binomial.
unfold Nbinomial in IHn.
assert (leb n n=true).
apply leb_correct.
auto with arith.
rewrite H in IHn.
rewrite IHn.
rewrite Nsimple_binomial_outside.
auto with arith.
auto with arith.
Qed.

Theorem Nbinomial_n_1 : forall n, 1 <= n -> Nbinomial n 1 = n.
induction n.
compute. reflexivity.
intros.
unfold Nbinomial.
assert (leb 1 (S n)=true).
apply leb_correct.
exact H.
rewrite H0.
unfold Nsimple_binomial.
fold Nsimple_binomial.
destruct n.
compute. reflexivity.
assert (Nbinomial (S n) 1=S n).
apply IHn.
auto with arith.
clear IHn.
unfold Nbinomial in H1.
clear H0.
assert (leb 1 (S n)=true).
apply leb_correct.
auto with arith.
rewrite H0 in H1. clear H0.
rewrite H1.
compute. reflexivity.
Qed.

(** Pascal relation and a generalization for alternative definition *)
Lemma Nbinomial_pascal': forall n k,
  S k <= n -> Nbinomial n k + Nbinomial n (S k) = Nbinomial (S n) (S k).
Proof.
intros.
unfold Nbinomial.
assert (leb k n=true).
apply leb_correct. auto with arith.
assert (leb (S k) (S n)=true).
apply leb_correct. auto with arith.
assert (leb (S k) n=true).
apply leb_correct. auto with arith.
rewrite H0. clear H0.
rewrite H1. clear H1.
rewrite H2. clear H2.
unfold Nsimple_binomial. fold Nsimple_binomial.
reflexivity.
Qed.

Lemma Nbinomial_pascal: forall n k,
  k <= n -> Nbinomial n k + Nbinomial n (S k) = Nbinomial (S n) (S k).
Proof.
intros.
assert (S k<=n -> Nbinomial n k + Nbinomial n (S k) = Nbinomial (S n) (S k)).
intro.
apply Nbinomial_pascal'.
exact H0.
assert (k=n -> Nbinomial n k + Nbinomial n (S k) = Nbinomial (S n) (S k)).
intro.
rewrite H1.
assert (Nbinomial n (S n)=0).
apply Nbinomial_outside.
auto with arith.
rewrite H2. clear H2.
rewrite Nbinomial_diag.
rewrite Nbinomial_diag.
auto with arith.
apply le_le_S_eq in H.
elim H.
exact H0.
exact H1.
Qed.

(** Expression of binomial coefficients using factorial and partial factorial *)
Theorem Nbinomial_factorial : forall n k, 
  1 <= k -> k <= n -> (fact k) * Nbinomial n k = Nfinite_prod_0_n (pred k) (fun x => n - x).
Proof.
induction n.
intros.
destruct k.
apply le_Sn_O in H.
contradiction.
rewrite Nbinomial_outside.
rewrite mult_0_r.
assert (Nfinite_prod_0_n (pred (S k)) (fun x : nat => 0 - x) =
  Nfinite_prod_0_n (pred (S k)) (fun x : nat => 0)).
apply Nfinite_prod_eq_compat.
auto with arith.
rewrite H1. clear H1.
symmetry.
apply Nfinite_prod_0_absord with k.
auto with arith.
reflexivity.
auto with arith.
intros.
apply le_le_S_eq in H0.
destruct H0.
assert (Q: S k<=S n).
exact H0.
apply (le_trans k) in H0.

destruct k.
apply le_Sn_O in H.
contradiction.

rewrite <- Nbinomial_pascal.
rewrite mult_plus_distr_l.
apply le_le_S_eq in H.
destruct H.
apply le_le_S_eq in H0.
destruct H0.

rewrite IHn.
unfold fact. fold fact.
rewrite <- mult_assoc.
rewrite IHn.
assert (exists k', k=S k').
destruct k.
apply le_Sn_n in H. contradiction.
exists k. reflexivity.
destruct H1.
rewrite H1.

assert (pred (S(S x))=S(pred (S x))).
rewrite pred_of_minus.
rewrite <- minus_Sn_m.
rewrite pred_of_minus.
reflexivity.
auto with arith.
rewrite H2.
rewrite Nfinite_prod_split_upper.
rewrite Nfinite_prod_split_lower.
assert (Nfinite_prod_0_n (pred (S x)) (fun k0 : nat => S n - S k0) =
  Nfinite_prod_0_n (pred (S x)) (fun k0 : nat => n - k0)).
apply Nfinite_prod_subtle_eq_compat.
intros.
auto with arith.
rewrite H3. clear H3.
assert (Nfinite_prod_0_n (pred (S x)) (fun x0 : nat => n - x0) * (n - S (pred (S x))) =
  (n - S (pred (S x))) * Nfinite_prod_0_n (pred (S x)) (fun x0 : nat => n - x0)).
auto with arith.
rewrite H3. clear H3.
rewrite <- mult_plus_distr_r.
rewrite <- minus_n_O.
assert (S (S x) + (n - S (pred (S x))) = S n).
rewrite <- pred_Sn.
assert (n-S x=S n-S(S x)).
auto with arith.
rewrite H3.
symmetry.
apply le_plus_minus.
rewrite <- H1.
auto with arith.
auto with arith.
auto with arith.
apply le_trans with (S k).
auto with arith.
auto with arith.
auto with arith.
auto with arith.
assert (k=n).
auto with arith.
rewrite H1.
rewrite Nbinomial_diag.
rewrite Nbinomial_outside.
rewrite mult_0_r.
rewrite plus_0_r.
rewrite mult_1_r.
rewrite Nfinite_prod_index_reversal.
rewrite <- H1.
rewrite Nfactorial_is_finite_prod.
rewrite <- pred_Sn.
apply Nfinite_prod_subtle_eq_compat.
intros.
assert (exists p, k=k0+p).
apply Nle_plus.
exact H2.
destruct H3.
rewrite plus_comm in H3. 
rewrite H3.
rewrite plus_comm.
assert (x-0=k0+x-(k0+0)).
apply minus_plus_simpl_l_reverse.
rewrite <- minus_n_O in H4.
rewrite plus_0_r in H4.
rewrite <- H4.
assert (S(k0+x)=S k0+x).
auto with arith.
rewrite H5. clear H4. clear H5.
assert (S k0-0=x+S k0-(x+0)).
apply minus_plus_simpl_l_reverse.
rewrite plus_0_r in H4.
rewrite <- minus_n_O in H4.
rewrite plus_comm in H4.
exact H4.
auto with arith.
assert (0=k).
auto with arith.
rewrite <- H1.
unfold fact. unfold iter_nat. unfold pred.
unfold Nfinite_prod_0_n.
unfold Nbinomial.
assert (leb 0 n=true).
apply leb_correct.
auto with arith.
rewrite H2. clear H2.
assert (leb 1 n=true).
apply leb_correct.
rewrite <- H1 in Q.
auto with arith.
rewrite H2.
assert (Nbinomial n 0=1).
apply Nbinomial_0.
assert (Nbinomial n 1=n).
apply Nbinomial_n_1.
rewrite <- H1 in Q.
auto with arith.
unfold Nbinomial in H3.
unfold Nbinomial in H4.
rewrite H2 in H4.
assert (leb 0 n=true).
auto.
rewrite H5 in H3.
rewrite H3.
rewrite H4.
simpl.
auto with arith.
auto with arith.
auto with arith.
rewrite H0.
rewrite Nbinomial_diag.
rewrite <- pred_Sn.
rewrite Nfactorial_is_finite_prod.
rewrite Nfinite_prod_index_reversal.
rewrite mult_1_r.
apply Nfinite_prod_subtle_eq_compat.
intros.
apply minus_Sn_m.
exact H1.
Qed.

(** Divisibility of binomial coefficients in prime case *)
Theorem Nbinomial_div : forall p k,
  0 < k < p -> Nprime p -> (p | Nbinomial p k).
intros.
assert((p|(fact k)*Nbinomial p k)).
rewrite Nbinomial_factorial.
apply Nfinite_prod_div with 0.
destruct H.
destruct k.
inversion H.
simpl. auto with arith.
rewrite <- minus_n_O. apply Ndiv_n_n.
destruct H.
destruct k.
inversion H.
auto with arith.
destruct H.
auto with arith.
apply Ngauss with (fact k).
auto.
clear H1.
generalize k H.
clear H k.
induction k.
intros.
inversion H. inversion H1.
intros.
destruct H.
unfold fact. fold fact.
destruct k.
simpl.
apply Nrel_prime_1.

apply Nrel_prime_mult_compat.
apply Nrel_prime_sym.
apply Nprime_le_rel_prime.
auto.
split.
auto with arith.
auto.
apply IHk.
split.
auto with arith.
auto with arith.
Qed.
