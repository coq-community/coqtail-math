From Coq Require Import ZArith Znumtheory Lia Psatz.
From Coqtail Require Import Ztools Zeqm Zlittle_fermat.

Theorem square_roots_of_unity (x p : Z) :
  prime p ->
  x ^ 2 ≡ 1 [p] ->
  x ≡ 1 [p] \/ x ≡ -1 [p].
Proof.
  intros pp.
  rewrite !eqm_divide.
  replace (x ^ 2 - 1) with ((x - 1) * (x + 1)) by lia.
  now intros H % prime_mult.
  all: apply prime_not_0, pp.
Qed.

Lemma miller_rabin_step (p a r d : Z) :
  prime p ->
  0 <= d ->
  0 <= r ->
  a ^ (2 ^ (r + 1) * d) ≡ 1 [p] ->
  a ^ (2 ^ r * d) ≡ 1 [p] \/
  a ^ (2 ^ r * d) ≡ - 1 [p].
Proof.
  intros pp Hd Hr H.
  apply square_roots_of_unity; auto.
  rewrite eqm_divide in *; try apply prime_not_0, pp.
  enough ((a ^ (2 ^ r * d)) ^ 2 = a ^ (2 ^ (r + 1) * d)) by congruence.
  assert (2 ^ (r + 1) * d = (2 ^ r * d) * 2) as ->
      by now rewrite Z.pow_add_r; lia || auto.
  rewrite (Z.pow_mul_r _ _ 2). easy.
  pose proof Z.pow_nonneg 2 r ltac:(lia). lia. lia.
Qed.

Lemma miller_rabin_step' (p a r d : Z) :
  prime p ->
  0 <= d ->
  1 <= r ->
  a ^ (2 ^ r * d) ≡ 1 [p] ->
  a ^ (2 ^ (r - 1) * d) ≡ 1 [p] \/
  a ^ (2 ^ (r - 1) * d) ≡ - 1 [p].
Proof.
  intros pp d0 r1 e.
  apply miller_rabin_step; auto; try lia.
  exact_eq e. do 4 f_equal. lia.
Qed.

Lemma factoring_out_prime p x :
  prime p -> 0 < x -> exists k y, x = p ^ k * y /\ ~(p | y) /\ 0 <= k.
Proof.
  intros pp xz. generalize xz.
  refine (Z_lt_induction
            (fun x => 0 < x -> exists k y : Z, x = p ^ k * y /\ ~ (p | y) /\ 0 <= k)
            _ x ltac:(lia)).
  clear x xz; intros x IHx xz.
  destruct (Zdivide_dec p x) as [ px | ? ].
  2:{ exists 0, x. split. rewrite Z.pow_0_r. lia. split. auto. lia. }
  pose proof prime_ge_2 p pp as p3.
  assert (0 < x / p). {
    apply Z.div_str_pos. split. lia.
    eapply Z.divide_pos_le; eauto.
  }
  destruct (IHx (x / p)) as (k & y & e & py & kz).
  - split. apply Z.div_pos; lia. apply Z.div_lt; lia.
  - auto.
  - exists (1 + k), y. split; auto.
    assert (k < 0 \/ 0 <= k) as [|] by lia.
    + rewrite Z.pow_neg_r in e; auto. lia.
    + rewrite Z.pow_add_r; try lia.
      rewrite <-Z.mul_assoc, <-e.
      replace (p ^ 1) with p by lia.
      apply Z_div_exact_2. lia.
      apply Zdivide_mod, px.
    + split; auto. lia.
Qed.

Lemma factoring_out_prime_at_least_once p x :
  prime p -> 0 < x -> (p | x) -> exists k y, x = p ^ k * y /\ ~(p | y) /\ 1 <= k.
Proof.
  intros pp xz px.
  destruct (factoring_out_prime p x pp xz) as (k & y & -> & py & kz).
  exists k, y; intuition.
  enough (k <> 0) by lia.
  intros ->.
  apply py. exact_eq px. f_equal.
  lia.
Qed.

Lemma Even_div x : Z.Even x <-> (2 | x).
Proof.
  split; intros [k]; exists k; lia.
Qed.

Lemma Odd_div x : Z.Odd x <-> ~(2 | x).
Proof.
  split.
  - intros [k ->] [l e]. lia.
  - intros d. destruct (Z.Even_or_Odd x) as [ [k ->] | ]; auto.
    destruct d. exists k; lia.
Qed.

Lemma Even_not_Odd x : Z.Even x <-> ~Z.Odd x.
Proof.
  rewrite Even_div, Odd_div.
  destruct (Zdivide_dec 2 x); tauto.
Qed.

Lemma Odd_not_Even x : Z.Odd x <-> ~Z.Even x.
Proof.
  rewrite Even_div, Odd_div.
  destruct (Zdivide_dec 2 x); tauto.
Qed.

Theorem miller_rabin_criterion (p : Z) :
  p > 2 ->
  prime p ->
  exists s d : Z,
    0 < s /\
    0 < d /\
    Z.Odd d /\
    p - 1 = 2 ^ s * d /\
    forall a,
      0 < a < p ->
      a ^ d ≡ 1 [p] \/
      exists r, 0 <= r < s /\ a ^ (2 ^ r * d) ≡ -1 [p].
Proof.
  intros p3 pp.
  pose proof primes_are_often_odd p ltac:(lia) pp as op.
  destruct (factoring_out_prime_at_least_once 2 (p - 1))
    as (s & d & psd & d2 & s1).
  - apply prime_2.
  - lia.
  - destruct op as (k & ->). exists k. lia.
  - assert (0 < d). {
      enough (~d = 0 /\ ~d < 0) by lia. split; intros d0.
      - apply d2. exists 0. lia.
      - enough (2 ^ s * d < 0) by lia. apply Z.mul_pos_neg. 2:lia.
        apply Z.pow_pos_nonneg; lia.
    }
    exists s, d. repeat split; try lia.
    + apply Odd_div, d2.
    + intros a zap.
      pose proof Fermat's_little_theorem_Z_pZ p a pp zap as f.
      rewrite psd in f. clear psd.
      apply eqm_divide in f; try now apply prime_not_0.
      change (a ^ (2 ^ s * d) ≡ 1 [p]) in f.
      (* main recurrence *)
      assert (s0 : 0 <= s) by lia.
      revert s s0 s1 f.
      match goal with
        |- forall s, 0 <= s -> ?G =>
        apply (Z.right_induction (fun s => G))
      end.
      intros ? ? ->; tauto.
      lia.
      intros s s0 IHs s0_ asp.
      apply miller_rabin_step in asp; lia || auto.
      destruct asp as [e | e].
      * destruct (Z.eq_dec s 0) as [-> | s1].
        -- left. exact_eq e. repeat f_equal. lia.
        -- destruct (IHs ltac:(lia) e) as [ ? | (r & lr & E)]; auto.
           right. exists r. split; lia || auto.
      * right. exists s. split; lia || auto.
Qed.

(* There will be pseudoprimes for many sets of [a]. The deterministic
 variant, of running time ~O(log^4), uses the bound 2ln(p) which
 relies on the generalized Riemann hypothesis. Maybe more useful would
 be to prove that the set {2,3,5,7,11} suffices for p<=10^14. Note
 that AKS is ~O(log^6). *)

(* First step to implement the primality test: remove 0 bits *)

Fixpoint remove_twos (x : positive) : (nat * positive) :=
  match x with
  | xO p => let (k, d) := remove_twos p in (S k, d)
  | _ => (O, x)
  end.

Lemma Odd_xI x : Z.Odd (Z.pos x~1).
Proof.
  exists (Z.pos x). auto.
Qed.

Lemma remove_twos_spec x k d :
  remove_twos x = (k, d) <->
  Zpos x = 2 ^ (Z.of_nat k) * Zpos d /\ Z.Odd (Zpos d).
Proof.
  revert k d; induction x; intros k d; split.
  - intros [=<-<-]. simpl; split; auto. apply Odd_xI.
  - intros [e _]. simpl.
    assert (k = O) as ->. {
      destruct k. easy. exfalso.
      eapply Odd_not_Even. eapply (Odd_xI x).
      rewrite e. rewrite <-Zpower_nat_Z. exists (Zpower_nat 2 k * Z.pos d).
      change (Zpower_nat 2 (S k)) with (2 * Zpower_nat 2 k).
      lia.
    }
    change (2 ^ Z.of_nat 0) with 1 in e.
    f_equal. lia.
  - simpl. destruct (remove_twos x) as (k_, d_).
    intros [=<-->]. rename k_ into k.
    specialize (IHx k d). apply proj1 in IHx. specialize IHx; auto.
    destruct IHx as [e od]. split; auto.
    rewrite <-Zpower_nat_Z in *.
    change (Zpower_nat 2 (S k)) with (2 * Zpower_nat 2 k).
    lia.
  - simpl. destruct (remove_twos x) as (k_, d_).
    specialize (IHx k_ d_). apply proj1 in IHx.
    destruct IHx as [ex hd_]; auto.
    change (Z.pos x~0) with (2 * Z.pos x).
    rewrite ex.
    intros [ex' hd].
    assert (k <= k_ \/ k > S k_ \/ k = S k_)%nat as [lk | [lk | ->]] by lia.
    + enough (Z.Even (Z.pos d)) by now apply Odd_not_Even in hd.
      exists (2 ^ Z.of_nat (k_ - k) * Z.pos d_).
      rewrite <-(Z.mul_cancel_l _ _ (2 ^ Z.of_nat k)). 2:lia.
      rewrite <-ex'. replace k_ with (k + (k_ - k))%nat at 1 by lia.
      rewrite <-!Zpower_nat_Z, Zpower_nat_is_exp. lia.
    + enough (Z.Even (Z.pos d_)) by now apply Odd_not_Even in hd_.
      exists (2 ^ Z.of_nat (k - k_ - 2) * Z.pos d).
      rewrite <-(Z.mul_cancel_l _ _ (2 * 2 ^ Z.of_nat k_)). 2:lia.
      rewrite <-!Zpower_nat_Z in *.
      transitivity (Zpower_nat 2 k_ * Zpower_nat 2 (k - k_ - 2) * 4 * Z.pos d).
      2: lia.
      change 4 with (Zpower_nat 2 2).
      rewrite Z.mul_assoc in ex'. rewrite ex'.
      rewrite <-2Zpower_nat_is_exp.
      repeat f_equal. lia.
    + enough (d_ = d) by congruence.
      rewrite <-!Zpower_nat_Z in *.
      change (Zpower_nat 2 (S k_)) with (2 * Zpower_nat 2 k_) in ex'.
      enough (Z.pos d_ = Z.pos d) by congruence.
      rewrite <-(Z.mul_cancel_l _ _ (2 * Zpower_nat 2 k_)). lia. lia.
  - simpl. intros [=<-<-]. intuition. exists 0; lia.
  - intros (ek, od).
    assert (k = O). {
      destruct k; auto.
      pose proof Z.pow_le_mono_r 2 1 (Z.of_nat (S k)) ltac:(lia) ltac:(lia).
      nia.
    }
    simpl. subst. f_equal.
    enough (Z.pos d = 1) by congruence.
    auto.
Qed.
