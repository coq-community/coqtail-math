From Coq Require Import ZArith Znumtheory Lia Psatz.
From Coqtail Require Import Nlittle_fermat Ztools.

Open Scope Z_scope.

Lemma Ndivide_Zdivide (a b : nat) : (a | b)%nat <-> (Z.of_nat a | Z.of_nat b).
Proof.
  split; intros (k & e).
  - exists (Z.of_nat k). subst. lia.
  - destruct (Nat.eq_dec a 0).
    + assert (b = 0)%nat as -> by lia. apply Ndiv_0.
    + exists (Z.to_nat k). nia.
Qed.

Lemma Zdivide_Ndivide (a b : Z) :
  0 <= a -> 0 <= b ->
  (a | b) <-> (Z.to_nat a | Z.to_nat b)%nat.
Proof.
  intros pa pb. rewrite Ndivide_Zdivide.
  rewrite 2 Z2Nat.id; tauto.
Qed.

Lemma Nprime_prime (p : nat) : Nprime p <-> prime (Z.of_nat p).
Proof.
  rewrite <-prime_alt.
  split; intros (p1, Pp).
  - split. lia.
    intros n hn.
    specialize (Pp (Z.to_nat n) ltac:(lia)).
    rewrite Ndivide_Zdivide in Pp.
    rewrite Z2Nat.id in Pp. auto. lia.
  - split. lia.
    intros n hn.
    specialize (Pp (Z.of_nat n) ltac:(lia)).
    now rewrite Ndivide_Zdivide.
Qed.

Lemma prime_Nprime (p : Z) : prime p <-> Nprime (Z.to_nat p).
Proof.
  split; intros pp.
  - apply Nprime_prime. rewrite Z2Nat.id; auto.
    apply prime_ge_2 in pp; lia.
  - rewrite <-(Z2Nat.id p). now apply Nprime_prime.
    apply Nprime_ge_2 in pp. lia.
Qed.

Lemma Nat2Z_pow (a b : nat) : Z.of_nat (a ^ b) = Z.of_nat a ^ Z.of_nat b.
Proof.
  rewrite <-Zpower_nat_Z.
  induction b. easy.
  simpl. lia.
Qed.

(* Both hypotheses on a and b are necessary *)
Lemma Z2Nat_pow (a b : Z) :
  0 <= a -> 0 <= b ->
  Z.to_nat (a ^ b) = (Z.to_nat a ^ Z.to_nat b)%nat.
Proof.
  intros pa pb.
  rewrite <-(Z2Nat.id a) at 1; auto.
  rewrite <-(Z2Nat.id b) at 1; auto.
  rewrite <-Nat2Z_pow. lia.
Qed.

Lemma Fermat's_little_theorem_aux (p a : Z) :
  0 < a ->
  prime p ->
  ~(p | a) ->
  (p | a ^ (p - 1) - 1).
Proof.
  intros az pp pa.
  pose proof prime_ge_2 _ pp.
  pose proof Nlittle_fermat.Nlittle_fermat_alt2 (Z.to_nat a) (Z.to_nat p) as h.
  rewrite <-prime_Nprime in h.
  rewrite <-Zdivide_Ndivide in h; try lia.
  specialize (h pp pa).
  assert (0 <= a ^ (p - 1) - 1). {
    enough (1 <= a ^ (p - 1)) by lia.
    rewrite <-(Z.pow_1_l (p - 1)) at 1. 2:lia.
    apply Z.pow_le_mono_l. lia.
  }
  rewrite Zdivide_Ndivide; try lia.
  exact_eq h. f_equal.
  rewrite Z2Nat.inj_sub; try lia.
  rewrite Z2Nat_pow; try lia.
  do 2 f_equal.
  lia.
Qed.

Lemma primes_are_often_odd p : 3 <= p -> prime p -> Z.Odd p.
Proof.
  intros p3 pp.
  destruct (Z.Even_or_Odd p) as [[n ->] | ?]; auto. exfalso.
  apply prime_alt in pp.
  destruct pp as (_, pp).
  apply (pp 2). lia. exists n. lia.
Qed.

Theorem Fermat's_little_theorem (p a : Z) :
  prime p ->
  ~(p | a) ->
  (p | a ^ (p - 1) - 1).
Proof.
  assert (a = 0 \/ 0 < a \/ a < 0) as [ -> | [ pa | na ] ] by lia.
  - intros _ h; destruct h. apply Z.divide_0_r.
  - apply Fermat's_little_theorem_aux, pa.
  - intros pp pa.
    pose proof (Fermat's_little_theorem_aux p (- a) ltac:(lia) pp) as F.
    spec F.
    { intro h; apply pa. apply Zdivide_opp_r_rev in h. auto. }
    assert (p = 2 \/ p > 2) as [-> | p3]
        by now pose proof prime_ge_2 _ pp; lia.
    + rewrite <-Z.mod_divide in *; try lia.
      rewrite Zminus_mod, Zpow_mod.
      enough (a mod 2 = 1) as ->. reflexivity.
      pose proof Z.mod_pos_bound a 2. lia.
    + exact_eq F; do 2 f_equal.
      apply Z.pow_opp_even, Z.Odd_succ.
      enough (Z.Odd p) as h. exact_eq h. f_equal. lia.
      apply primes_are_often_odd. lia. auto.
Qed.

Theorem Fermat's_little_theorem_Z_pZ (p a : Z) :
  prime p ->
  0 < a < p ->
  (p | a ^ (p - 1) - 1).
Proof.
  intros pp [az ap].
  apply Fermat's_little_theorem_aux; auto.
  intros pa.
  pose proof rel_prime_le_prime a p pp ltac:(lia) as r.
  eapply Zrel_prime_neq_mod_0; eauto. lia.
  apply Z.mod_divide; auto.
  intros ->. apply not_prime_0, pp.
Qed.
