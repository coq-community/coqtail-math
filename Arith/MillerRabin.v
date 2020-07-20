From Coq Require Import ZArith Znumtheory Lia Psatz.
From Coqtail Require Import Zlittle_fermat.

Open Scope Z_scope.

Definition congruent_mod m a b := (m | a - b).

Notation "a ≡ b [ m ]" := (congruent_mod m a b) (at level 40).

Theorem square_roots_of_unity (x p : Z) :
  prime p ->
  x ^ 2 ≡ 1 [p] ->
  x ≡ 1 [p] \/ x ≡ -1 [p].
Proof.
  intros Pp.
  unfold congruent_mod.
  replace (x ^ 2 - 1) with ((x - 1) * (x + 1)) by lia.
  now intros H % prime_mult.
Qed.

Lemma miller_rabin_step (p a r d : Z) :
  prime p ->
  0 <= d ->
  0 <= r ->
  a ^ (2 ^ (r + 1) * d) ≡ 1 [p] ->
  a ^ (2 ^ r * d) ≡ 1 [p] \/
  a ^ (2 ^ r * d) ≡ - 1 [p].
Proof.
  intros Pp Hd Hr H.
  apply square_roots_of_unity; auto.
  unfold congruent_mod in *.
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

