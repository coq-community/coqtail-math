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

From Coq Require Import Arith Euclid Compare Lia.
From Coqtail Require Export Nle Nk_ind.
Open Scope nat_scope.

(** * Definitions *)
(** Definition of divisibility *)
Inductive Ndivide a b : Prop :=
| Ndivide_intro : forall q, b = q * a -> Ndivide a b.

(** Definition of a quotient *)
Inductive Nquotient a b : nat -> Prop :=
| Nquotient_intro : forall q, b = q * a -> Nquotient a b q.

(** Definition of modulus/remainder *)
Inductive Nmod a b : nat -> Prop :=
| Nmod_intro : forall q r, b = q * a + r -> r < a -> Nmod a b r.

(** Notation *)
Notation "( a | b )" := (Ndivide a b) (at level 0) : nat_scope.

(** Definition of coprimality *)
Definition Nrel_prime p q := forall n, (n | p) -> (n | q) -> n = 1.

(** Definition of primality *)
Definition Nprime p := 1<p /\ (forall n, 1 < n < p -> ~ (n | p)).

(* begin hide *)
Lemma Nprime_intro : forall p, 1 < p -> (forall n, 1 < n < p -> ~(n | p)) -> Nprime p.
intros.
split; auto.
Qed.
(* end hide *)

(** * Basic results on prime numbers *)
(** [0] is not prime *)
Lemma Nnot_prime_0 : ~(Nprime 0).
Proof.
unfold Nprime.
intro.
destruct H.
apply le_Sn_O in H.
exact H.
Qed.

(** [1] is not prime *)
Lemma Nnot_prime_1 : ~(Nprime 1).
Proof.
unfold Nprime.
intro.
destruct H.
apply lt_irrefl in H.
exact H.
Qed.

(** A prime number is greater than or equal to [2] *)
Lemma Nprime_ge_2 : forall (p:nat), Nprime p -> 2<=p.
Proof.
intros.
destruct p.
apply Nnot_prime_0 in H.
contradiction.
destruct p.
apply Nnot_prime_1 in H.
contradiction.
unfold Nprime in H.
destruct H.
auto with arith.
Qed.

(** A composed number is not prime *)
Lemma Ncomposed_not_prime : forall n m, 1 < n -> 1 < m -> ~(Nprime (n * m)).
Proof.
intros.
intro.
destruct H1.
apply H2 with n.
split.
auto with arith.
replace n with (n*1).
destruct n.
apply le_Sn_O in H.
contradiction.
rewrite <- mult_assoc.
apply mult_S_lt_compat_l.
rewrite mult_1_l.
trivial.
auto with arith.
exists m.
ring.
Qed.

(** * Basic properties of divisibility *)
(** Compatibility with addition *)
Lemma Ndiv_plus_compat : forall p a b, (p | a) -> (p | b) -> (p | a + b).
Proof.
intros.
destruct H.
destruct H0.
apply Ndivide_intro with (q+q0).
rewrite H. rewrite H0.
ring.
Qed.

(** Product divisiblity weakening *)
Lemma Nab_div_c : forall a b c, (a * b | c) -> (a | c).
Proof.
intros.
destruct H.
apply Ndivide_intro with (q*b).
rewrite H.
ring.
Qed.

(** A divisor is usually nonzero *)
Lemma Ndiv_non_0 : forall a b, (a | b) -> 1 <= b -> 1 <= a.
Proof.
intros.
destruct a.
destruct H.
rewrite mult_0_r in H.
rewrite H in H0.
exact H0.
auto with arith.
Qed.

(** Any number divides [0] *)
Lemma Ndiv_0 : forall a, (a | 0).
intros.
apply Ndivide_intro with 0.
ring.
Qed.

(** [1] divides any number *)
Lemma Ndiv_1 : forall a, (1 | a).
intros.
apply Ndivide_intro with a.
ring.
Qed.

(** Not divisor implies nonzero *)
Lemma Nnon_div_non_zero : forall a b, ~( a | b) -> b > 0.
intros.
destruct b.
destruct H.
apply Ndiv_0.
auto with arith.
Qed.

(** [n] divides [n] *)
Lemma Ndiv_n_n : forall n, (n|n).
Proof.
intro.
apply Ndivide_intro with 1.
ring.
Qed.

(** * Basic properties of quotient *)
(** Quotient implies divisibility *)
Lemma Nquotient_div : forall a b q, Nquotient a b q -> (a | b).
Proof.
intros.
destruct H.
apply Ndivide_intro with q.
auto.
Qed.

(** Compatibility with order *)
Lemma Nquotient_le_compat : forall a b c q p, 
  Nquotient a b q -> Nquotient a c p -> 1 <= b <= c -> q <= p.
Proof.
intros.
assert (1<=a).
apply Ndiv_non_0 with b.
apply Nquotient_div with q.
exact H.
destruct H1.
exact H1.
assert (exists a',a=S a').
destruct a.
apply le_Sn_O in H2.
contradiction.
exists a.
reflexivity.
destruct H3.
destruct H.
destruct H0.
destruct H1.
rewrite H in H4.
rewrite H0 in H4.
rewrite H3 in H4.
apply mult_S_le_reg_l with x.
assert (S x*q=q*S x).
ring.
assert (S x*q0=q0*S x).
ring.
rewrite H5.
rewrite H6.
exact H4.
Qed.

(** * Properties of divisibility *)

(** Transitivity *)
Lemma Ndiv_trans : forall a b c, (a | b) -> (b | c) -> (a | c).
Proof.
intros.
destruct H.
destruct H0.
exists (q*q0).
rewrite H0.
rewrite H.
ring.
Qed.

(** Simplification of addition *)
Lemma Ndiv_plus_simpl : forall a b c, (a | b + c) -> (a | b) -> (a | c).
Proof.
intros.
destruct b.
destruct H.
apply Ndivide_intro with q.
auto with arith.

destruct H.
destruct H0.
apply Ndivide_intro with (q-q0).
assert (q0<=q).
apply Nquotient_le_compat with a (S b) (S b+c).
apply Nquotient_intro. exact H0.
apply Nquotient_intro. exact H.
split.
auto with arith.
auto with arith.
apply Nle_plus in H1.
destruct H1.
rewrite H1.
assert (q0+x-q0=x).
apply minus_plus.
rewrite H2.
rewrite H1 in H.
rewrite H0 in H.
rewrite mult_plus_distr_r in H.
rewrite plus_comm in H.
apply plus_reg_l with (q0*a).
rewrite plus_comm.
rewrite H.
auto with arith.
Qed.

(** Right implification of subtraction *)
Lemma Ndiv_minus_simpl_r : forall a b c, b >= c -> (a | b - c) -> (a | c) -> (a | b).
Proof.
intros.
apply Nle_plus in H.
destruct H.
rewrite H in * |- *.
rewrite minus_plus in H0.
apply Ndiv_plus_compat; auto.
Qed.

(** Left implification of subtraction *)
Lemma Ndiv_minus_simpl_l : forall a b c, b >= c -> (a | b - c) -> (a | b) -> (a | c).
Proof.
intros.
apply Nle_plus in H.
destruct H.
rewrite H in * |- *.
rewrite minus_plus in H0.
rewrite plus_comm in H1.
apply Ndiv_plus_simpl with x; auto.
Qed.

(** Weak compatibility with multiplication *)
Lemma Ndiv_mult_compat : forall a b q, (a | b) -> (a | b * q).
Proof.
intros.
destruct H.
apply Ndivide_intro with (q0*q).
rewrite H.
ring.
Qed.

(** Strong compatibility with multiplication *)
Lemma Ndiv_strong_mult_compat : forall a b q, (a|b) -> (a * q | b * q).
Proof.
intros.
destruct H.
apply Ndivide_intro with (q0).
rewrite H.
ring.
Qed.

(* begin hide *)
Lemma toto : forall a b q, S q * a = S q * b -> a = b.
  induction a.
  intros.
  rewrite mult_0_r in H.
  symmetry in H.
  apply mult_is_O in H.
  destruct H.
  discriminate H.
  auto.
  intros.
  destruct b.
  rewrite mult_0_r in H.
  discriminate H.
  assert (a=b).
  rewrite mult_succ_r in H.
  rewrite mult_succ_r in H.
  assert (S q  + S q * a= S q + S q * b).
  rewrite plus_comm.
  rewrite H.
  ring.
  apply plus_reg_l in H0.
  apply IHa with q.
  auto.
  rewrite H0.
  auto.
Qed.
(* end hide *)

(** Simplification of common factor *)
Lemma Ndiv_mult_simpl : forall a b q, q <> 0 -> (a * q | b * q) -> (a | b).
Proof.
intros.
destruct H0.
destruct q.
contradiction H.
reflexivity.
rewrite mult_assoc in H0.
assert (S q*b=S q*(q0*a)).
rewrite mult_comm.
rewrite H0.
ring.
assert (b=q0*a).
apply toto with q.
rewrite mult_comm.
rewrite H0.
ring.
apply Ndivide_intro with q0.
auto.
Qed.

(** Divisibility implies order *)
Lemma Ndiv_le : forall n p, 0 < p -> (n | p) -> n <= p.
Proof.
intros.
destruct H0.
destruct p.
apply lt_irrefl in H. contradiction.
destruct n.
auto with arith.
destruct q.
simpl in H0.
discriminate H0.
replace (S n) with (1*S n).
rewrite H0.
apply mult_le_compat.
auto with arith.
auto with arith.
rewrite mult_1_l.
trivial.
Qed.

(** Dividable by [0] implies zero *)
Lemma Ndiv_0_n : forall n, (0 | n) -> n = 0.
Proof.
destruct n.
trivial.
intro.
destruct H.
rewrite mult_0_r in H.
discriminate H.
Qed.

(** * Properties of coprimes *)

(** [n] and [n] are usually not coprime *)
Lemma Nnon_rel_prime_n_n : forall n, n <> 1 -> ~(Nrel_prime n n).
Proof.
intro.
intro.
intro.
unfold Nrel_prime in H0.
assert (n=1).
apply H0.
apply Ndiv_n_n.
apply Ndiv_n_n.
contradiction.
Qed.

(** Compatibility with modulus *)
Theorem Nrel_prime_mod : forall a b r, Nrel_prime a b -> Nmod a b r -> Nrel_prime a r.
Proof.
intros.
destruct H0.
unfold Nrel_prime in H.
unfold Nrel_prime.
intros.
assert (n|b).
rewrite H0.
apply Ndiv_plus_compat.
rewrite mult_comm.
apply Ndiv_mult_compat.
auto.
auto.
apply H.
auto.
auto.
Qed.

(** Symmetry *)
Lemma Nrel_prime_sym : forall a b, Nrel_prime a b -> Nrel_prime b a.
Proof.
intros.
intro.
intros.
apply H.
auto.
auto.
Qed.

(** Weakening from primality to coprimality *)
Lemma Nprime_le_rel_prime : forall n p, Nprime p -> 0 < n < p -> Nrel_prime n p.
Proof.
intros.
destruct H0.
destruct H.
intro.
intros.
assert (0<n0).
apply Ndiv_non_0 with n.
auto.
auto with arith.
assert (n0<p).
apply le_trans with (S n).
apply le_n_S.
apply Ndiv_le.
auto with arith.
trivial.
auto.
destruct n0.
apply Ndiv_0_n in H3.
rewrite H3 in H0.
inversion H0.
destruct n0.
trivial.
apply H2 in H4.
contradiction.
split.
auto with arith.
auto.
Qed.

(** A coprime of [0] is [1] *)
Lemma Nrel_prime_0 : forall n, Nrel_prime n 0 -> n = 1.
Proof.
intros.
apply H.
apply Ndiv_n_n.
apply Ndiv_0.
Qed.

(** Any number is coprime with [1] *)
Lemma Nrel_prime_1 : forall n, Nrel_prime n 1.
Proof.
intros.
intro.
intros.
destruct n0.
destruct H0.
rewrite mult_0_r in H0. auto.
apply Ndiv_le in H0.
destruct n0.
auto.
inversion H0.
inversion H2.
auto.
Qed.

(** * Gauss theorem *)
Theorem Ngauss : forall a b c, (a | b * c) -> Nrel_prime a b -> (a | c).
Proof.
apply (nat_strong_ind (fun a =>  forall b c, (a|b*c) -> Nrel_prime a b -> (a|c))).
intros.
destruct H.
rewrite mult_0_r in H.
apply mult_is_O in H.
destruct H.
rewrite H in H0.
apply Nnon_rel_prime_n_n in H0.
contradiction.
auto with arith.
rewrite H.
apply Ndiv_0.

intros.
destruct n.
apply Ndiv_1.

destruct H0.
assert (diveucl b (S (S n))).
apply eucl_dev.
auto with arith.
destruct H2.
assert (diveucl c (S(S n))).
apply eucl_dev.
auto with arith.
destruct H2.
rewrite e in H0.
rewrite e0 in H0.
rewrite mult_plus_distr_l in H0.
rewrite mult_plus_distr_r in H0.
rewrite mult_plus_distr_r in H0.
assert (S (S n)|r*r0).
apply Ndiv_plus_simpl with (q0 *S( S n) * r0).
apply Ndiv_plus_simpl with (r * (q1 * S(S n))).
apply Ndiv_plus_simpl with (q0 * S(S n) * (q1 * S(S n))).
apply Ndivide_intro with q.
rewrite <- H0.
ring.
apply Ndivide_intro with (q0*S(S n)*q1).
ring.
apply Ndivide_intro with (r*q1).
ring.
apply Ndivide_intro with (r0*q0).
ring.
destruct H2.
assert (Nrel_prime (S(S n)) r).
apply Nrel_prime_mod with b.
auto.
apply Nmod_intro with q0.
auto.
auto.
assert (r|q2).
apply H with (S(S n)).
auto with arith.
apply Ndivide_intro with r0.
rewrite mult_comm.
rewrite <- H2.
ring.
apply Nrel_prime_sym.
auto.
assert (S(S n)*r | r*r0).
rewrite H2.
rewrite mult_comm.
apply Ndiv_strong_mult_compat.
auto.
assert (S(S n)|r0).
apply Ndiv_mult_simpl with r.
destruct r.
rewrite plus_0_r in e.
assert (S(S n)|b).
apply Ndivide_intro with q0.
auto.
assert (S(S n)=1).
apply H1.
apply Ndiv_n_n.
auto.
discriminate H7.
auto with arith.
destruct H5.
apply Ndivide_intro with q3.
rewrite mult_comm.
rewrite H5.
ring.
rewrite e0.
apply Ndiv_plus_compat.
rewrite mult_comm.
apply Ndiv_mult_compat.
apply Ndiv_n_n.
auto.
Qed.

(** * Decidability of divisibility *)

(** Algorithm to compute a remainder modulus a number *)
Fixpoint Ndiv_mod_algo (n m:nat) {struct m} : nat :=
match n with
| 0 => 0
| S n' =>
  match m with
  | 0 => 0
  | S m' =>
    let tmp:=S (Ndiv_mod_algo n m') in
    match beq_nat n tmp with
    | true => 0
    | false => tmp
    end
  end
end.

(** Algorithm to decide divisibility *)
Definition Ndiv_algo (n m:nat) : bool :=
  beq_nat (Ndiv_mod_algo n m) 0.

  (* begin hide *)
  Lemma eq_nat_correct : forall n m, n<>m -> false=beq_nat n m.
  Proof.
  intros n.
  induction n.
  destruct m.
  intros.
  contradiction H. reflexivity.
  intros.
  compute. reflexivity.
  induction m.
  compute. reflexivity.
  simpl.
  intros.
  apply IHn.
  auto with arith.
  Qed.
(* end hide *)
(** [m] mod [n] equals [m] if [n] is greater than [m] *)
Lemma Ndiv_mod_l0 : forall n m, m < n -> Ndiv_mod_algo n m = m.
Proof.
induction m.
intros. destruct n. inversion H. compute. trivial.
intros.
destruct n.
inversion H.
simpl.
replace (Ndiv_mod_algo (S n) m) with m.
replace (beq_nat n m) with false.
reflexivity.
apply eq_nat_correct.
intro.
rewrite H0 in H.
apply lt_irrefl in H. contradiction.
symmetry.
apply IHm.
auto with arith.
Qed.

(** Simplification of addition *)
Lemma Ndiv_mod_l1 : forall n m, n > 0 -> Ndiv_mod_algo n (m + n) = Ndiv_mod_algo n m.
Proof.
intros n m. pattern m. apply nat_strong_ind.
intros. simpl.
induction n.
reflexivity.
simpl.
replace (Ndiv_mod_algo (S n) n) with n.
replace (beq_nat n n) with true.
reflexivity. apply beq_nat_refl.
symmetry.
apply Ndiv_mod_l0.
auto with arith.
intros.
induction n.
simpl. reflexivity.
simpl.
replace (Ndiv_mod_algo (S n) (n0+S n)) with (Ndiv_mod_algo (S n) n0); auto.
symmetry.
apply H.
auto with arith.
auto with arith.
Qed.

(** Correctness of divisibility algorithm *)
Theorem Ndiv_algo_correct : forall n m, n > 0 -> (n | m) -> Ndiv_algo n m=true.
Proof.
destruct n.
intros.
inversion H.
intro. pattern m.
apply nat_strong_ind.
intros.
compute. trivial.
intros.
unfold Ndiv_algo.
destruct H1.
destruct q.
simpl in H1.
inversion H1.
rewrite mult_succ_l in H1.
rewrite H1.
rewrite Ndiv_mod_l1.
apply H.
apply le_trans with (q*S n+n).
auto with arith.
rewrite plus_comm in H1.
simpl in H1.
apply eq_add_S in H1.
rewrite H1.
rewrite plus_comm.
auto with arith.
auto with arith.
exists q.
auto.
auto.
Qed.

(* The remainder is a remainder (strong condition) *)
Lemma Ndiv_mod_algo_rem : forall n m r, n > 0 -> Ndiv_mod_algo n m = r -> r < n.
Proof.
induction m.
intros.
destruct n. inversion H. compute in H0. rewrite <- H0. auto with arith.
intros.
destruct n. inversion H.
simpl in H0.
assert (Ndiv_mod_algo (S n) m<(S n)).
apply IHm. auto with arith. auto.
apply le_le_S_eq in H1.
destruct H1.
apply le_S_n in H1.
apply le_lt_n_Sm in H1.
apply lt_S_n in H1.
destruct (beq_nat n (Ndiv_mod_algo (S n) m)).
rewrite <- H0. auto with arith.
rewrite <- H0.
apply lt_n_S. auto.
apply eq_add_S in H1.
rewrite H1 in H0.
rewrite <- beq_nat_refl in H0.
rewrite <- H0.
auto with arith.
Qed.

(* The remainder is lower than or equal to number itself *)
Lemma Ndiv_mod_algo_rem2 : forall n m r, n > 0 -> Ndiv_mod_algo n m = r -> r <= m.
Proof.
induction m.
intros.
destruct n; compute in H0; rewrite <- H0; auto with arith.
intros.
simpl in H0.
destruct n. inversion H.
destruct (beq_nat (S n) (S (Ndiv_mod_algo (S n) m))).
rewrite <- H0. auto with arith.
destruct r.
inversion H0.
apply eq_add_S in H0.
apply le_n_S.
apply IHm.
auto.
auto.
Qed.

(** Completeness of modulus algorithm *)
Theorem Ndiv_mod_algo_complete : forall n m r, n > 0 -> Ndiv_mod_algo n m = r ->
(n | m - r).
Proof.
destruct n.
+ intros; inversion H.
+ intro m; pattern m; apply nat_strong_ind.
  - intros; compute in H0; rewrite <- H0.
    simpl; apply Ndiv_0.
  - intros; simpl in H1; case (lt_eq_lt_dec (S n) n0).
    intros; destruct s.

{ assert (exists d, n0=S n+d) by (apply Nle_plus; auto with arith).
  destruct H2; rewrite H2 in H1.
  assert (Ndiv_mod_algo (S n) (S n+x)=Ndiv_mod_algo (S n) (x+S n)) by (rewrite plus_comm; auto).
rewrite H3 in H1.
clear H3.
rewrite Ndiv_mod_l1 in H1.
rewrite H2.
replace (S (S n+x)) with (S n+S x) by auto with arith.
replace (S n+S x-r) with (S n+(S x-r)).
2: {
apply plus_minus.
replace (r+(S n+(S x-r))) with (S n+r+(S x-r)).
2: {
rewrite plus_assoc.
now auto with arith.
}
assert (S x=r+(S x-r)).
symmetry.
apply le_plus_minus_r.
destruct (beq_nat n (Ndiv_mod_algo (S n) x)).
rewrite <- H1. auto with arith.
destruct r. inversion H1.
apply eq_add_S in H1.
apply le_n_S.
apply Ndiv_mod_algo_rem2 with (S n).
auto with arith.
auto.
rewrite H3.
rewrite plus_assoc.
rewrite minus_plus.
auto.
}
apply Ndiv_plus_compat.
apply Ndiv_n_n.
apply H.
rewrite plus_Snm_nSm in H2.
apply le_trans with (S x+n).
auto with arith.
rewrite plus_comm.
rewrite <- H2.
auto with arith.
auto with arith.
auto.
auto with arith. }


    {
    rewrite <- e in H1.
    replace (Ndiv_mod_algo (S n) (S n)) with (Ndiv_mod_algo (S n) (0+S n)) in H1.
    rewrite Ndiv_mod_l1 in H1.
    simpl in H1; destruct n.
    { simpl in H1; rewrite <- H1; rewrite <- e; simpl; exists 2; ring. }
    { simpl in H1; rewrite <- H1; rewrite e; simpl; rewrite <- minus_n_O; apply Ndiv_n_n. }
    { auto with arith. }
    { simpl. auto. }
    }

    {
    intro;
    replace (Ndiv_mod_algo (S n) n0) with n0 in H1.
    apply le_le_S_eq in l.
    destruct l.
    assert (n<>n0).
    intro. rewrite H3 in H2. apply lt_irrefl in H2. auto.
    apply eq_nat_correct in H3.
    rewrite <- H3 in H1.
    rewrite <- H1.
    rewrite <- minus_diag_reverse.
    apply Ndiv_0.
    apply eq_add_S in H2.
    rewrite H2 in H1.
    rewrite <- beq_nat_refl in H1.
    rewrite <- H1.
    rewrite <- minus_n_O.
    rewrite H2.
    apply Ndiv_n_n.
    symmetry.
    apply Ndiv_mod_l0.
    auto. }
Qed.

(** Completeness of the divisibility algorith *)
Theorem Ndiv_algo_complete : forall n m, n>0 -> Ndiv_algo n m=true -> (n | m).
Proof.
intros.
unfold Ndiv_algo in H0.
symmetry in H0.
apply beq_nat_eq in H0.
replace m with (m-0).
apply Ndiv_mod_algo_complete.
auto.
auto.
auto with arith.
Qed.

(** * Greatest strict divisor *)
(** Algorithm to compute the greatest divisor lower than a number *)
Fixpoint Ngreatest_div_le (n:nat) (p:nat) {struct n}: nat :=
match n with
| 0 | 1 => 1
| S n => 
    if Ndiv_algo (S n) p then (S n)
    else Ngreatest_div_le n p
end.

(** Algorithm to compute the greatest strict divisor of a number *)
Definition Ngreatest_div (p:nat) : nat :=
  Ngreatest_div_le (pred p) p.

(** The greatest divisor is a divisor *)
Lemma Ngreatest_div_le_div : forall p n, p>1 -> (Ngreatest_div_le n p | p).
Proof.
induction n.
intros.
compute. apply Ndiv_1.
intros.
simpl.
destruct n. apply Ndiv_1.
assert(Ndiv_algo (S(S n)) p=true -> (S(S n)|p)).
intros. apply Ndiv_algo_complete. auto with arith. auto.
destruct (Ndiv_algo (S(S n)) p).
apply H0. auto.
auto.
Qed.

(** The greatest strict divisor is a divisor *)
Theorem Ngreatest_div_div : forall p, p > 1 -> (Ngreatest_div p | p).
Proof.
intros.
apply Ngreatest_div_le_div.
auto.
Qed.

(** The greatest divisor lower than a number is a lower than that number *)
Theorem Ngreatest_div_le_le : forall n p, n > 0 -> Ngreatest_div_le n p <= n.
Proof.
intros.
induction n.
inversion H.
simpl.
destruct n.
auto.
destruct (Ndiv_algo (S (S n)) p).
auto.
eapply le_trans.
eapply IHn. auto with arith.
auto with arith.
Qed.

(** The greatest divisor is a monotonous function *)
Theorem Ngreatest_div_le_monotone : forall n n' p,
  n <= n' -> Ngreatest_div_le n p <= Ngreatest_div_le n' p.
Proof.
intros.
induction H.
auto.
eapply le_trans.
eexact IHle.
assert (Ndiv_algo (S m) p=true -> Ngreatest_div_le (S m) p=S m).
intros.
simpl.
destruct m. auto.
rewrite H0. auto.
assert (Ndiv_algo (S m) p=false -> Ngreatest_div_le (S m) p=Ngreatest_div_le m p).
intros.
simpl.
destruct m. compute. auto.
rewrite H1. auto.
destruct (Ndiv_algo (S m) p).
rewrite H0.
destruct m. compute. auto.
eapply le_trans.
eapply Ngreatest_div_le_le. auto with arith.
auto with arith. auto.
rewrite H1. auto. auto.
Qed.

(** The greatest divisor is a the greatest divisor *)
Theorem Ngreatest_div_le_greatest : forall n p q, 
  p>1 -> q>=1 -> q<p -> q<=n -> (q | p) -> q <= Ngreatest_div_le n p.
Proof.
intros.
replace q with (Ngreatest_div_le q p).
apply Ngreatest_div_le_monotone. auto.
destruct q.
inversion H0.
simpl.
destruct q.
auto.
apply Ndiv_algo_correct in H3.
rewrite H3. auto. auto with arith.
Qed.

(** The greatest strict divisor is a the greatest strict divisor *)
Theorem Ngreatest_div_greatest : forall p q, 
  p>1 -> q>=1 -> q<p -> (q | p) -> q <= Ngreatest_div p.
Proof.
intros.
apply Ngreatest_div_le_greatest; auto.
destruct p. inversion H.
simpl. auto with arith.
Qed.

(** The greatest strict divisor is strict *)
Theorem Ngreatest_div_lt_p : forall n, n > 1 -> Ngreatest_div n < n.
Proof.
intros.
destruct n.
inversion H.
destruct n.
inversion H. inversion H1.
unfold lt.
apply le_n_S.
unfold Ngreatest_div.
replace (pred(S(S n))) with (S n).
apply Ngreatest_div_le_le.
auto with arith.
auto with arith.
Qed.

(** The greatest strict divisor is nonzero *)
Theorem Ngreatest_div_le_1 : forall n, Ngreatest_div n>=1.
Proof.
intros.
destruct n.
compute. auto.
destruct n. compute. auto.
apply Ngreatest_div_greatest.
auto with arith.
auto.
auto with arith.
apply Ndiv_1.
Qed.

(** * Decidability of primality with greatest strict divisor *)
(** Implication of greatest strict divisor on primality *)
Theorem Ngreatest_div_1_prime : forall p, p > 1 -> Ngreatest_div p = 1 -> Nprime p.
Proof.
intro.
destruct p.
intros. inversion H.
destruct p.
intros. inversion H. inversion H2.

intros.
split.
auto.
intros.
intro.
apply Ngreatest_div_greatest in H2.
rewrite H0 in H2.
destruct H1.
assert(1<1).
eapply le_trans.
eapply H1. auto.
inversion H4. inversion H6.
auto with arith.
destruct H1.
auto with arith.
destruct H1.
auto with arith.
Qed.

(** Implication of primality greatest divisor *)
Theorem Nprime_greatest_div_le_1 : forall n p, n<p -> Nprime p -> Ngreatest_div_le n p=1.
Proof.
induction n.
intros.
compute. auto.
intros.
simpl.
destruct n.
auto.
assert(~(Ndiv_algo (S (S n)) p=true)).
intro.
destruct H0.
apply H2 with (S(S n)).
split.
auto with arith. auto.
apply Ndiv_algo_complete.
auto with arith. auto.
destruct (Ndiv_algo (S (S n)) p).
contradiction H1. auto.
apply IHn.
auto with arith.
auto.
Qed.

(** Implication of primality greatest strict divisor *)
Theorem Nprime_greatest_div_1 : forall p, Nprime p -> Ngreatest_div p=1.
Proof.
intros.
apply Nprime_greatest_div_le_1.
destruct H.
inversion H;
auto with arith. auto.
Qed.

(** * Lowest strict divisor *)
(** Algorithm to compute the lowest divisor greater than a number *)
Fixpoint Nleast_div_ge (n p:nat) {struct n} : nat :=
match n with
| 0 => p
| S n =>
    if Ndiv_algo (p-S n) p then p-S n
    else Nleast_div_ge n p
end.

(** Algorithm to compute lowest strict divisor *)
Definition Nleast_div p := Nleast_div_ge (p-2) p.

(** Lowest divisor is a divisor *)
Lemma Nleast_div_ge_div : forall p n, p>1 -> n < p -> (Nleast_div_ge n p | p).
Proof.
induction n.
intros.
compute. apply Ndiv_n_n.
intros.
simpl.
assert (Ndiv_algo (p-S n) p=true -> (p-S n|p)).
apply Ndiv_algo_complete.
unfold gt.
apply (minus_le_compat_r (S (S n)) p (S n)) in H0.
rewrite <- minus_Sn_m in H0.
rewrite <- minus_n_n in H0.
eapply le_trans.
eapply H0. auto. auto.
destruct (Ndiv_algo (p-S n) p).
apply H1. auto.
apply IHn. auto.
auto with arith.
Qed.

(** Lowest divisor is usually greater than [1] *)
Theorem Nleast_div_ge_gt_1 : forall n p, p > 1 -> S n < p -> 1 < Nleast_div_ge n p.
Proof.
induction n.
intros.
compute. auto.
intros.
simpl.
destruct (Ndiv_algo (p-S n) p).
apply (minus_le_compat_r (S(S(S n))) p (S n)) in H0.
rewrite <- minus_Sn_m in H0.
rewrite <- minus_Sn_m in H0.
rewrite <- minus_n_n in H0.
auto. auto. auto.
apply IHn.
auto. auto with arith.
Qed.

(** Lowest strict divisor is greater than [1] *)
Theorem Nleast_div_gt_1 : forall p, p > 1 -> 1 < Nleast_div p.
Proof.
intros.
apply Nleast_div_ge_gt_1.
auto.
unfold lt.
assert(p>=2).
auto with arith.
apply Nle_plus in H0.
destruct H0.
rewrite H0.
rewrite minus_plus.
auto with arith.
Qed.

(** Lowest strict divisor is a divisor *)
Theorem Nleast_div_div : forall p, p>1 -> (Nleast_div p | p).
Proof.
intros.
apply Nleast_div_ge_div.
auto.
auto with arith.
Qed.

(** Lowest divisor greater than a number is greater than that number *)
Theorem Nleast_div_ge_ge : forall n p, n < p -> Nleast_div_ge n p >= p - n.
Proof.
induction n.
intros.
simpl.
rewrite <- minus_n_O.
auto.
intros.
simpl.
destruct (Ndiv_algo (p-S n) p).
auto.
unfold ge.
apply le_trans with (p-n).
apply minus_le_compat_l.
auto.
apply IHn. auto with arith.
Qed.

(** Lowest divisor is a monotonous function *)
Theorem Nleast_div_ge_monotone : forall n n' p,
  n <= n' -> n' < p -> Nleast_div_ge n p >= Nleast_div_ge n' p.
Proof.
intros.
induction H.
auto.
simpl.
destruct (Ndiv_algo (p-S m) p).
apply le_trans with (p-m).
apply minus_le_compat_l.
auto.
apply le_trans with (p-n).
apply minus_le_compat_l.
auto.
apply Nleast_div_ge_ge.
apply le_trans with (S m).
auto with arith.
auto with arith.
apply IHle.
auto with arith.
Qed.

(** Lowest divisor is lowest divisor *)
Theorem Nleast_div_ge_least : forall n p q, 
  p > 1 -> q >= 1 -> q < p -> n < p -> q >= p-n -> (q | p) -> Nleast_div_ge n p <= q.
Proof.
intros.
replace q with (Nleast_div_ge (p-q) p).
apply Nleast_div_ge_monotone.
unfold ge in H3.
destruct (le_dec n p).
apply (plus_le_compat_l (p-n) q n) in H3.
rewrite le_plus_minus_r  in H3.
apply (minus_le_compat_r p (n+q) q) in H3.
rewrite plus_comm in H3.
rewrite minus_plus in H3.
auto.
auto.
apply le_trans with p.
apply le_minus.
auto.
auto.

destruct H1.
rewrite <- minus_Sn_m.
rewrite <- minus_n_n.
simpl. rewrite <- minus_n_O.
apply Ndiv_algo_correct in H4.
rewrite H4. auto. auto. auto.

rewrite <- minus_Sn_m.
simpl.
apply Ndiv_algo_correct in H4.
assert(q<=m).
auto with arith.
apply Nle_plus in H5.
destruct H5.
rewrite H5.
rewrite minus_plus.
rewrite plus_comm.
rewrite minus_plus.
rewrite H5 in H4.
rewrite plus_comm.
rewrite H4.
auto. auto. auto with arith.
Qed.

(** Lowest strict divisor is lowest divisor *)
Theorem Nleast_div_least : forall p q, 
  p > 1 -> q > 1 -> q < p -> (q | p) -> Nleast_div p <= q.
Proof.
intros.
apply Nleast_div_ge_least.
auto. auto with arith. auto. auto with arith.
apply Nle_plus in H.
destruct H.
rewrite H.
rewrite minus_plus.
rewrite plus_comm.
rewrite minus_plus.
auto.
auto.
Qed.

(** * Decidability of primality with lowest strict divisor *)
(** Implication of lowest strict divisor on primality *)
Theorem Nleast_div_p_prime : forall p, p > 1 -> Nleast_div p = p -> Nprime p.
Proof.
intros.
destruct p.
inversion H.
split.
auto.
intros.
destruct H1.
intro.
apply Nleast_div_least in H3.
rewrite H0 in H3.
assert(n<n).
apply le_trans with (S p).
auto. auto.
apply lt_irrefl in H4. auto.
auto.
auto.
auto.
Qed.

(** Implication of primality on lowest divisor *)
Theorem Nprime_least_div_ge_p : forall n p, S n < p -> Nprime p -> Nleast_div_ge n p = p.
(* fixme: cette preuve est foireuse *)
induction n.
intros.
compute. auto.
intros.
destruct H0.
apply le_le_S_eq in H.
destruct H.
simpl.
assert(~(p-S n|p)).
apply H1.
split.
apply (minus_le_compat_r (S(S(S(S n)))) p (S n)) in H.
rewrite <- minus_Sn_m in H.
rewrite <- minus_Sn_m in H.
rewrite <- minus_Sn_m in H.
rewrite <- minus_n_n in H.
auto with arith.
auto.
auto.
auto with arith.
apply lt_minus.
apply le_trans with (S(S(S n))).
auto with arith. auto.
auto with arith.
auto with arith.
assert (~Ndiv_algo (p-S n) p=true).
intro.
apply H1 with (p-S n).
split.
apply (minus_le_compat_r (S(S(S(S n)))) p (S n)) in H.
rewrite <- minus_Sn_m in H.
rewrite <- minus_Sn_m in H.
rewrite <- minus_Sn_m in H.
rewrite <- minus_n_n in H.
auto with arith.
auto.
auto.
auto.
apply lt_minus.
apply le_trans with (S(S(S(S n)))).
auto. auto. auto with arith.
apply Ndiv_algo_complete.
unfold gt.
apply (minus_le_compat_r (S(S(S(S n)))) p (S n)) in H.
rewrite <- minus_Sn_m in H.
rewrite <- minus_Sn_m in H.
rewrite <- minus_Sn_m in H.
rewrite <- minus_n_n in H.
apply le_trans with 3. auto. auto. auto. auto. auto. auto. auto with arith.

destruct (Ndiv_algo (p-S n) p).
contradiction H3. auto.
apply IHn.
apply le_trans with (S(S(S(S n)))).
auto. auto.
split. auto. auto.

destruct p. inversion H.
destruct p. inversion H.
destruct p. inversion H.
do 3 apply eq_add_S in H.
rewrite H.
unfold Nleast_div_ge.
rewrite <- minus_Sn_m.
rewrite <- minus_Sn_m.
rewrite <- minus_n_n.
assert(~(Ndiv_algo 2 (S(S(S p)))=true)).
intro.
apply H1 with 2.
split. auto. auto with arith.
apply Ndiv_algo_complete. auto. auto.
destruct (Ndiv_algo 2 (S(S(S p)))).
contradiction H2. auto.
fold Nleast_div_ge.
rewrite <- H.
apply IHn.
auto.
split. auto with arith.
rewrite H.
auto.
auto.
auto.
Qed. 

(** Implication of primality on lowest strict divisor *)
Theorem Nprime_least_div_p : forall p, Nprime p -> Nleast_div p = p.
Proof.
intros.
apply Nprime_least_div_ge_p.
destruct p.
apply Nnot_prime_0 in H. contradiction.
destruct p.
apply Nnot_prime_1 in H. contradiction.
rewrite minus_Sn_m.
apply le_trans with (S (S p)).
apply lt_n_S.
auto with arith. auto. auto with arith.
auto.
Qed.

(** Lowest strict divisor is prime *)
Theorem Nleast_div_prime : forall p, p>1 -> Nprime (Nleast_div p).
Proof.
intros.
split.
apply Nleast_div_gt_1.
auto.
intros.
intro.
destruct H0.
assert((n|p)).
apply Ndiv_trans with (Nleast_div p).
auto.
apply Nleast_div_div.
auto with arith.
apply Nleast_div_least in H3.
apply lt_irrefl with (Nleast_div p).
apply le_trans with (S n).
auto with arith.
auto.
auto with arith.
auto.
apply le_trans with (Nleast_div p).
auto.
apply Ndiv_le.
destruct p. inversion H.
auto with arith.
apply Nleast_div_div.
auto with arith.
Qed.

(** Lowest strict divisor is greater than [1] *)
Theorem Nleast_div_ge_2 : forall n, n > 1 -> Nleast_div n >= 2.
Proof.
intros.
assert(Nprime (Nleast_div n)).
apply Nleast_div_prime.
auto.
assert(0<=Nleast_div n).
auto with arith.
apply le_le_S_eq in H1.
destruct H1.
apply le_le_S_eq in H1.
destruct H1.
auto.
rewrite <- H1 in H0.
apply Nnot_prime_1 in H0. contradiction.
rewrite <- H1 in H0.
apply Nnot_prime_0 in H0. contradiction.
Qed.

(** Implication of lowest strict divisor on not primality *)
Theorem Nleast_div_lt_p_not_prime : forall n, n > 2 -> (Nleast_div n) < n -> ~(Nprime n).
Proof.
intros.
intro.
assert((Nleast_div n|n)).
apply Nleast_div_div.
auto with arith.
destruct H2.
destruct q.
rewrite mult_0_l in H2.
rewrite H2 in H.
inversion H.
destruct q.
rewrite mult_1_l in H2.
rewrite <- H2 in H0.
apply lt_irrefl in H0.
auto.
apply (Ncomposed_not_prime (S(S q)) (Nleast_div n)).
auto with arith.
apply Nleast_div_gt_1.
auto with arith.
rewrite H2 in H1. auto.
Qed.

(** Every number has a prime divisor *)
Theorem Nhas_prime_divisor : forall n, n > 1 -> exists p, Nprime p /\ (p | n).
Proof.
intros.
exists (Nleast_div n).
split.
apply Nleast_div_prime.
auto.
apply Nleast_div_div.
auto with arith.
Qed.

(** * Gauss theorem (prime formulation) *)
Theorem Ngauss_prime : forall a b c, (a | b * c) -> Nprime a -> (a | c) \/ (a | b).
Proof.
intros.
destruct a.
apply Nnot_prime_0 in H0. contradiction.

assert(Ndiv_algo (S(a)) b=true -> ((S(a))|b)).
intro. apply Ndiv_algo_complete. auto.
auto with arith. auto.
assert(Ndiv_algo (S a) b=false -> Nrel_prime (S a) b).
intro.
assert(~(S a|b)).
intro.
apply Ndiv_algo_correct in H3. rewrite H3 in H2. inversion H2.
auto with arith.
intro.
intros.
destruct n.
destruct H4. rewrite mult_0_r in H4. inversion H4.
destruct n.
auto.
destruct H0.
apply H6 in H4.
contradiction.
split.
auto with arith.
apply Ndiv_le in H4.
apply le_le_S_eq in H4.
destruct H4.
auto.
rewrite H4 in H5.
apply H3 in H5.
contradiction.
auto with arith.
destruct (Ndiv_algo (S a) b).
right.
apply H1.
auto.
left.
apply Ngauss with b.
apply H.
apply H2.
auto.
Qed.

(** * Compatibility of coprimality with multiplication *)
Theorem Nrel_prime_mult_compat : forall p n m,
  Nrel_prime p n -> Nrel_prime p m -> Nrel_prime p (n * m).
Proof.
intros.
intro.
intros.
destruct n0.
destruct H1.
rewrite mult_0_r in H1.
rewrite H1 in H.
destruct H2.
rewrite mult_0_r in H2.
apply mult_is_O in H2.
destruct H2.
rewrite H2 in H.
apply H.
apply Ndiv_n_n.
apply Ndiv_n_n.
rewrite H1 in H0.
rewrite H2 in H0.
apply H0.
apply Ndiv_n_n.
apply Ndiv_n_n.
destruct n0.
auto.

assert(exists pn0, Nprime pn0 /\ (pn0|(S(S n0)))).
apply Nhas_prime_divisor.
auto with arith.
destruct H3.
destruct H3.
assert((x|n*m)).
eapply Ndiv_trans.
eapply H4.
apply H2.
apply Ngauss_prime in H5.
assert(x=1).
destruct H5.
apply H0.
eapply Ndiv_trans. eapply H4. apply H1.
apply H5.
apply H.
eapply Ndiv_trans. eapply H4. apply H1.
apply H5.
rewrite H6 in H3.
apply Nnot_prime_1 in H3.
contradiction.
auto.
Qed.

(** * Primality results *)
(** Not prime implies composed *)
Theorem Nnot_prime_composed : forall n, 
  n > 2 -> ~(Nprime n) -> exists p, exists q, p > 1 /\ q > 1 /\ n = p * q.
Proof.
intros.
exists(Nleast_div n).
assert(Nleast_div n|n).
apply Nleast_div_div.
auto with arith.
destruct H1.
exists q.
split.
apply Nleast_div_gt_1. auto with arith.
split.
destruct q.
rewrite mult_0_l in H1.
rewrite H1 in H.
inversion H.
destruct q.
rewrite mult_1_l in H1.
symmetry in H1.
apply Nleast_div_p_prime in H1.
apply H0 in H1. contradiction.
auto with arith.
auto with arith.
rewrite mult_comm. auto.
Qed.

(** A number if either prime or not prime *)
Theorem Nprime_or_not_prime : forall n, (Nprime n) \/ (~(Nprime n)).
Proof.
intros.
destruct n.
right. apply Nnot_prime_0.
destruct n.
right. apply Nnot_prime_1.
destruct n.
left.
apply Nprime_intro.
auto with arith.
intros.
destruct H.
inversion H.
rewrite H1 in H0.
apply lt_irrefl in H0. contradiction.
rewrite <- H2 in H0.
assert(2<2).
apply le_trans with (S m).
auto with arith. auto with arith.
apply lt_irrefl in H3. contradiction.
assert(beq_nat (Nleast_div (S(S(S n)))) (S(S(S n)))=true -> Nprime (S(S(S n)))).
intros.
apply Nleast_div_p_prime.
auto with arith.
apply beq_nat_true.
auto.
assert(beq_nat (Nleast_div (S(S(S n)))) (S(S(S n)))=false -> ~Nprime (S(S(S n)))).
intros.
assert(Nleast_div (S(S(S n)))<>(S(S(S n)))).
apply beq_nat_false.
auto.
apply not_eq in H1.
destruct H1.
apply Nleast_div_lt_p_not_prime.
auto with arith.
auto.
assert(Nleast_div (S(S(S n)))<=S(S(S n))).
apply Ndiv_le.
auto with arith.
apply Nleast_div_div.
auto with arith.
assert(S(S(S n))<S(S(S n))).
eapply le_trans.
eapply H1.
apply H2.
apply lt_irrefl in H3.
intro. auto.

destruct (beq_nat (Nleast_div (S (S (S n)))) (S (S (S n)))).
left. auto.
right. auto.
Qed.

(** A number is either prime or composed *)
Theorem Nprime_or_composed : forall n, 
  n > 2 -> (Nprime n) \/ (exists p, exists q, p > 1 /\ q > 1 /\ n=p * q).
Proof.
intros.
assert(Nprime n \/ ~Nprime n).
apply Nprime_or_not_prime.
destruct H0.
left. auto.
right.
apply Nnot_prime_composed.
auto. auto.
Qed.

(** * Relation between lowest strict divisor and greatest strict divisor *)
Theorem Ngreatest_least_div_relation : forall n, n > 2 -> (Ngreatest_div n) * (Nleast_div n)=n.
Proof.
intros.
assert(Nprime n \/ ~Nprime n).
apply Nprime_or_not_prime.
destruct H0.
replace (Ngreatest_div n) with 1.
replace (Nleast_div n) with n.
ring.
symmetry.
apply Nprime_least_div_p. auto.
symmetry.
apply Nprime_greatest_div_1. auto.

assert(Q:~Nprime n).
auto. clear H0.
assert((Ngreatest_div n)*(Nleast_div n)<=n).
assert((Ngreatest_div n)|n).
apply Ngreatest_div_div. auto with arith.
destruct H0.
assert(q|n).
exists (Ngreatest_div n).
rewrite mult_comm. auto.
apply Nleast_div_least in H1.
rewrite H0 at 3.
rewrite mult_comm.
apply mult_le_compat_r.
auto.
auto with arith.
destruct q.
rewrite mult_0_l in H0. rewrite H0 in H. inversion H.
destruct q.
rewrite mult_1_l in H0.
assert(Ngreatest_div n<n).
apply Ngreatest_div_lt_p.
auto with arith.
rewrite <- H0 in H2 at 1.
apply lt_irrefl in H2.
contradiction.
auto with arith.
assert(q<=n).
apply Ndiv_le; auto. destruct n. inversion H. auto with arith.
apply le_le_S_eq in H2.
destruct H2.
auto.
rewrite H2 in H0.
destruct n.
inversion H.
assert(1<=Ngreatest_div (S n)).
apply Ngreatest_div_le_1.
apply le_le_S_eq in H3.
destruct H3.
replace q with (q*1).
rewrite H0.
rewrite H2.
apply mult_S_lt_compat_l.
auto. ring.
symmetry in H3.
apply Ngreatest_div_1_prime in H3.
apply Q in H3. contradiction.
auto with arith.

assert((Ngreatest_div n)*(Nleast_div n)>=n).
assert((Nleast_div n)|n).
apply Nleast_div_div. auto with arith.
destruct H1.
assert(q|n).
exists (Nleast_div n).
rewrite mult_comm. auto.
apply Ngreatest_div_greatest in H2.
unfold ge.
rewrite H1 at 1.
apply mult_le_compat_r.
auto.
auto with arith.
destruct q.
rewrite mult_0_l in H1.
rewrite H1 in H. inversion H.
auto with arith.
apply Ndiv_le in H2.
apply le_le_S_eq in H2.
destruct H2.
auto.
rewrite H2 in H1.
assert(Nleast_div n>=2).
apply Nleast_div_ge_2.
destruct n. inversion H.
auto with arith.
replace q with (q*1).
rewrite H1.
rewrite H2.
destruct n.
inversion H.
apply mult_S_lt_compat_l.
auto. ring.
destruct n.
inversion H.
auto with arith.

apply le_antisym; auto.
Qed.

Lemma div_mod a b : a <> 0 -> (a | b) <-> b mod a = 0.
Proof.
  intros az; split.
  - intros (k, ->). apply Nat.mod_mul, az.
  - intros e. exists (b / a).
    etransitivity. apply (Nat.div_mod _ a), az.
    lia.
Qed.

Lemma eqmod_div m a b : m <> 0 -> a <= b -> a mod m = b mod m <-> (m | b - a).
Proof.
  intros mz l; split.
  - intros e. exists ((b / m) - (a / m)).
    rewrite Nat.mul_comm, Nat.mul_sub_distr_l.
    rewrite (Nat.div_mod a m mz) at 1.
    rewrite (Nat.div_mod b m mz) at 1.
    lia.
  - intros (k, e).
    assert (b = a + k * m) by lia.
    assert (b mod m = (a + k * m) mod m) as -> by congruence.
    rewrite Nat.mod_add; auto.
Qed.

Lemma Nrel_prime_eqmod m a b :
  m <> 0 ->
  a mod m = b mod m ->
  Nrel_prime m a ->
  Nrel_prime m b.
Proof.
  intros mz ab ma x xm xb.
  apply (ma x xm); clear ma.
  destruct (le_lt_dec a b) as [le|lt].
  - rewrite eqmod_div in ab; auto.
    destruct xb as (k & ->).
    destruct xm as (l & ->).
    destruct ab as (m & em).
    exists (k - m * l).
    replace ((k - m * l) * x) with (k * x - m * (l * x)). lia.
    rewrite Nat.mul_sub_distr_r. lia.
  - symmetry in ab.
    rewrite eqmod_div in ab; auto. 2:lia.
    destruct xb as (k & ->).
    destruct xm as (l & ->).
    destruct ab as (m & em).
    exists (m * l + k).
    replace ((m * l + k) * x) with (k * x + m * (l * x)). lia.
    rewrite Nat.mul_add_distr_r. lia.
Qed.

Lemma Ndivide_eqmod m a b :
  m <> 0 ->
  a mod m = b mod m ->
  (m | a) <-> (m | b).
Proof.
  intros mz ab.
  rewrite 2 div_mod; auto.
  split; lia.
Qed.

Lemma Nrel_prime_prime (a p : nat) :
  Nprime p ->
  Nrel_prime a p <-> ~ (p | a).
Proof.
  intros Pp.
  pose proof Nprime_ge_2 _ Pp as p2.
  split; intros ap.
  - intros pa.
    specialize (ap p pa (Ndiv_n_n _)).
    lia.
  - apply Nrel_prime_sym.
    eapply Nrel_prime_eqmod with (a mod p).
    lia.
    now rewrite Nat.mod_mod; lia.
    apply Nrel_prime_sym, Nprime_le_rel_prime; auto.
    split.
    + rewrite (Ndivide_eqmod _ _ (a mod p)) in ap.
      2: lia.
      2: now rewrite Nat.mod_mod; lia.
      enough (0 <> a mod p) by lia.
      intros e. apply ap. rewrite <-e.
      apply Ndiv_0.
    + apply Nat.mod_upper_bound. lia.
Qed.
