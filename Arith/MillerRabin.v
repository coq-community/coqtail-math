From Coq Require Import ZArith Znumtheory Lia Psatz List Bool.
From Coqtail Require Import Ztools Zeqm Zlittle_fermat Zpow Zprime.

(** This file defines the Rabin Miller primality test, first as a
theorem, then as a boolean function.

We prove it is sound, in that it returns true when p is prime.

We prove it is complete below some bounds with sufficient sets of
witnesses:

- below 2048 for the set {2}
- below 10000 for the set {2,3}
- below 1373653 for the set {2,3}

The last item can be checked but it takes a lot of time. Without
parallelism, it is even worse, and enabling parallelism for all files
makes compiling most other files more slowly, so we removed this
exhaustive check.
*)

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
 be to prove that the set {2,3,5,7,11} suffices for p<=10^14. *)

(* First step to implement the primality test: remove the null bits *)

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
    specialize (IHx k d). apply proj1 in IHx. spec IHx by auto.
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

Definition eqmb (m a b : Z) : bool := a mod m =? b mod m.

Lemma eqmb_true_iff m a b : eqmb m a b = true <-> a ≡ b [m].
Proof.
  apply Z.eqb_eq.
Qed.

Import ListNotations.

Definition miller_rabin (l : list Z) (n : Z) : bool :=
  if n <? 2 then false else
    if n =? 2 then true else
      Z.odd n &&
      let (s, d) := remove_twos (Z.to_pos (n - 1)) in
      forallb
        (fun a =>
           implb
             ((0 <? a) && (a <? n))
             ((pow_mod n a (Zpos d) =? 1)
                  || existsb
                      (fun r => pow_mod n a (2 ^ r * Zpos d) =? n - 1)
                      (Zseq 0 s))) l.

Lemma pow_mod_help m a b : 1 < m -> (pow_mod m a b =? 1) = (eqmb m (a ^ b) 1).
Proof.
  intros hm.
  rewrite pow_mod_spec. unfold eqmb.
  f_equal.
  rewrite Zmod_1_l; auto.
Qed.

Lemma Zmod_m1_l a : 0 < a -> (-1) mod a = a - 1.
Proof.
  intros ha.
  destruct (Z.eq_dec a 1) as [-> | a1]. reflexivity.
  transitivity ((a - 1) mod a).
  - rewrite Zminus_mod, Z_mod_same, Zmod_1_l. reflexivity. lia. lia.
  - apply Z.mod_small. lia.
Qed.

Lemma pow_mod_help' m a b : 0 < m -> (pow_mod m a b =? m - 1) = (eqmb m (a ^ b) (- 1)).
Proof.
  intros hm.
  rewrite pow_mod_spec. unfold eqmb.
  f_equal.
  rewrite Zmod_m1_l; auto.
Qed.

Lemma miller_rabin_sound l n : miller_rabin l n = false -> ~prime n.
Proof.
  intros c pn.
  enough (miller_rabin l n = true) by congruence; clear c.
  unfold miller_rabin.

  destruct (n <? 2) eqn:n1.
  { apply Z.ltb_lt in n1. apply prime_ge_2 in pn. lia. }

  destruct (n =? 2) eqn:n2; auto.
  apply Z.eqb_neq in n2. apply Z.ltb_ge in n1.
  assert (bn : n > 2) by lia. clear n1 n2.

  rewrite andb_true_iff, Z.odd_spec.
  split. apply primes_are_often_odd; auto; lia.

  apply miller_rabin_criterion in pn; auto.
  destruct pn as (s & d & zs & zd & od & e & crit).

  destruct (remove_twos _) as (s_, d_) eqn:esd.
  assert (e' : remove_twos (Z.to_pos (n - 1)) = (Z.to_nat s, Z.to_pos d)).
  {
    apply remove_twos_spec; split.
    - exact_eq e; repeat f_equal.
      + rewrite Z2Pos.id; lia.
      + rewrite Z2Nat.id; lia.
      + rewrite Z2Pos.id; lia.
    - exact_eq od; f_equal.
      rewrite Z2Pos.id; lia.
  }
  rewrite esd in e'. injection e' as -> ->.
  rewrite Z2Pos.id; auto.

  rewrite forallb_forall.
  intros a al.
  destruct (_ <? _) eqn:za. apply Z.ltb_lt in za. 2:reflexivity.
  destruct (_ <? _) eqn:an. apply Z.ltb_lt in an. 2:reflexivity.
  specialize (crit a ltac:(lia)).
  change (implb (true && true) ?b) with b.
  rewrite pow_mod_help; try lia.
  rewrite orb_true_iff, existsb_exists, eqmb_true_iff.
  destruct crit as [?|(r & rs & er)]. now left.
  right. exists r.
  rewrite pow_mod_help'; try lia.
  rewrite eqmb_true_iff, in_Zseq.
  split. lia. exact_eq er; repeat f_equal.
Qed.

Lemma miller_rabin_more_tests l l' :
  (forall x, In x l -> In x l') -> forall n, implb (miller_rabin l' n) (miller_rabin l n) = true.
Proof.
  intros s n.
  unfold miller_rabin in *.
  destruct (_ <? _). reflexivity.
  destruct (_ =? _). reflexivity.
  destruct (Z.odd _). 2: reflexivity.
  destruct (remove_twos _).
  rewrite 2andb_true_l.
  assert (a : forall a b, (a = true -> b = true) -> implb a b = true)
    by now intros [|] [|]; try discriminate || tauto. apply a.
  rewrite 2forallb_forall. eauto.
Qed.

(* It is faster to just use "primeb", it seems:

Definition primes (n : Z) := filter primeb (Zseq 1 (Z.to_nat n)).
Definition primesmr l (n : Z) := filter (miller_rabin l) (Zseq 1 (Z.to_nat n)).

Time Eval vm_compute in primes 10000. (* 3s sec *)
Time Eval vm_compute in primesmr [2; 3] 10000. (* 6 sec *)
*)

(** Re-using work to try an accelerate the computation *)

Fixpoint mainloop n s x :=
  match s with
  | O => false
  | S s => (x =? n - 1) || mainloop n s ((x * x) mod n)
  end.

Lemma mainloop_spec n a d s x :
  x = pow_mod n a (Z.pos d) ->
  mainloop n s x =
  existsb
    (fun r => pow_mod n a (2 ^ r * Z.pos d) =? n - 1)
    (Zseq 0 s).
Proof.
  replace (Z.pos d) with (2 ^ 0 * Z.pos d) at 1 by lia.
  generalize (Z.le_refl 0).
  generalize 0 at 2 3 4 as offset.
  revert d x.
  induction s. reflexivity.
  intros d x offset oz ex.
  change (Zseq offset (S s)) with (offset :: Zseq (1 + offset) s).
  change (existsb ?f (?a :: ?l)) with (f a || existsb f l).
  simpl mainloop.
  f_equal. rewrite ex; auto.
  apply IHs. lia.
  replace (x * x) with (x ^ 2) by lia.
  rewrite ex.
  rewrite 2pow_mod_spec.
  rewrite <-Zpow_mod. f_equal.
  rewrite <-!Z.pow_mul_r.
  rewrite Z.pow_add_r.
  f_equal. lia.
  lia.
  lia.
  apply Z.mul_nonneg_nonneg; try lia; try (apply Z.pow_nonneg; lia).
  lia.
Qed.

Definition miller_rabin' (l : list Z) (n : Z) : bool :=
  if n <? 2 then false else
    if n =? 2 then true else
      Z.odd n &&
      let (s, d) := remove_twos (Z.to_pos (n - 1)) in
      forallb
        (fun a =>
           implb
             ((0 <? a) && (a <? n))
             (let x := pow_mod n a (Zpos d) in
              (x =? 1) ||
              mainloop n s x)) l.

Lemma forallb_ext {A} (f g : A -> bool) l :
  (forall a, f a = g a) -> forallb f l = forallb g l.
Proof.
  intros e; induction l; simpl; congruence.
Qed.

Lemma implb_true_l: forall b : bool, implb true b = b. now intros []. Qed.
Lemma implb_true_r: forall b : bool, implb b true = true. now intros []. Qed.
Lemma implb_false_l: forall b : bool, implb false b = true. now intros []. Qed.
Lemma implb_false_r: forall b : bool, implb b false = negb b. now intros []. Qed.

Definition miller_rabin'_spec l n : miller_rabin' l n = miller_rabin l n.
Proof.
  unfold miller_rabin.
  unfold miller_rabin'.
  destruct (n <? 2); auto.
  destruct (n =? 2); auto.
  destruct (Z.odd _); auto.
  rewrite 2 andb_true_l.
  destruct (remove_twos _) as (s, d).
  apply forallb_ext; intros a.
  destruct (_ && _); auto.
  rewrite 2 implb_true_l.
  f_equal.
  now apply mainloop_spec.
Qed.

(* Some benchmarking.

miller_rabin' is a bit faster, but not by much. If primeb (sqrt
algorithm) is still faster on small numbers, it does get surpassed by
the miller_rabin' above about 10000. miller_rabin also gets faster
than primeb only after about 80000.

Time Eval vm_compute in length (filter  primeb                (Zseq 1 (Z.to_nat 10000))). (* 3 secs *)
Time Eval vm_compute in length (filter (miller_rabin  [2; 3]) (Zseq 1 (Z.to_nat 10000))). (* 6 secs *)
Time Eval vm_compute in length (filter (miller_rabin' [2; 3]) (Zseq 1 (Z.to_nat 10000))). (* 4 secs *)

Time Eval vm_compute in length (filter  primeb                (Zseq 1 (Z.to_nat 20000))). (* 10.4 secs *)
Time Eval vm_compute in length (filter (miller_rabin  [2; 3]) (Zseq 1 (Z.to_nat 20000))). (* 21.1 secs *)
Time Eval vm_compute in length (filter (miller_rabin' [2; 3]) (Zseq 1 (Z.to_nat 20000))). (* 10.1 secs *)

Time Eval vm_compute in length (filter  primeb                (Zseq 1 (Z.to_nat 40000))). (* 41.3 secs *)
Time Eval vm_compute in length (filter (miller_rabin  [2; 3]) (Zseq 1 (Z.to_nat 40000))). (* 54.6 secs *)
Time Eval vm_compute in length (filter (miller_rabin' [2; 3]) (Zseq 1 (Z.to_nat 40000))). (* 26.6 secs *)

Time Eval vm_compute in length (filter  primeb                (Zseq 1 (Z.to_nat 80000))). (* 132 sec *)
Time Eval vm_compute in length (filter (miller_rabin  [2; 3]) (Zseq 1 (Z.to_nat 80000))). (* 125 sec *)
Time Eval vm_compute in length (filter (miller_rabin' [2; 3]) (Zseq 1 (Z.to_nat 80000))). (* 68 sec *)

other simple ideas for improvement:
- use positive instead of Z (maybe there is a lot of going back and forth)
- replace "x mod m" with "if x < m then x else x mod m" (seem unlikely)
- use 64 bits integers
*)


(** Checking that Miller-Rabin is sufficient below some bounds *)

Definition MR_at l n := if miller_rabin l n then primeb n else true.
Definition MR_range l a b := forallb (MR_at l) (Zseq a (Z.to_nat (b - a + 1))).

Lemma iff_intro {A} (P Q : A -> Prop) : (forall a, P a <-> Q a) -> (forall a, P a) <-> (forall a, Q a).
Proof.
  firstorder.
Qed.

Lemma iff_intro_Prop (P Q P' Q' : Prop) : (P <-> Q) -> (P -> Q -> (P' <-> Q')) -> ((P -> P') <-> (Q -> Q')).
Proof.
  firstorder.
Qed.

Lemma MR_range_spec l a b : MR_range l a b = true <-> (forall n : Z, a <= n <= b -> miller_rabin l n = primeb n).
Proof.
  unfold MR_range.
  rewrite forallb_forall.
  apply iff_intro; intros x.
  apply iff_intro_Prop. rewrite in_Zseq; lia.
  intros _ bx.
  unfold MR_at in *.
  destruct (miller_rabin l x) eqn:e. split; auto.
  destruct (primeb x) eqn:p; split; auto.
  apply miller_rabin_sound in e.
  now apply primeb_prime in p.
Qed.

Lemma MR_range_empty l a b : a > b -> MR_range l a b = true.
Proof.
  intros ab.
  unfold MR_range.
  replace (Z.to_nat _) with O by lia.
  easy.
Qed.

Lemma MR_range_spec_0 l b : MR_range l 0 b = true -> forall n : Z, n <= b -> miller_rabin l n = primeb n.
Proof.
  intros h n nb.
  pose proof proj1 (MR_range_spec _ _ _) h n as m.
  destruct (n <? 2) eqn:n2.
  - unfold miller_rabin in *. rewrite n2 in *.
    destruct (primeb n) eqn:pn; auto.
    apply Z.ltb_lt in n2. apply primeb_prime, prime_ge_2 in pn. lia.
  - apply Z.ltb_ge in n2. apply m. lia.
Qed.

Lemma MR_range_spec_2 l b : MR_range l 2 b = true -> forall n : Z, n <= b -> miller_rabin l n = primeb n.
Proof.
  intros h n nb.
  pose proof proj1 (MR_range_spec _ _ _) h n as m.
  destruct (n <? 2) eqn:n2.
  - unfold miller_rabin in *. rewrite n2 in *.
    destruct (primeb n) eqn:pn; auto.
    apply Z.ltb_lt in n2. apply primeb_prime, prime_ge_2 in pn. lia.
  - apply Z.ltb_ge in n2. tauto.
Qed.

(** Below 2047, it is enough to check a=2 *)

Lemma miller_rabin_2 n : n <= 2046 -> miller_rabin [2] n = primeb n.
Proof.
  apply MR_range_spec_2.
  vm_compute. (* 0.3 seconds *)
  reflexivity.
Qed.

Lemma first_miller_rabin_2_pseudo_prime :
  miller_rabin [2]    2047 = true /\
  miller_rabin [2; 3] 2047 = false /\
  primeb              2047 = false.
Proof.
  now native_compute.
Qed.

(** Below 1373653, it is enough to check a=3, but we check for <= 10000 *)

Lemma miller_rabin_2_3 n : n <= 10000 -> miller_rabin [2; 3] n = primeb n.
Proof.
  apply MR_range_spec_2.
  Time native_compute. (* 1.6 secs *)
  reflexivity.
Time Qed. (* 1.6 secs *)

Lemma first_miller_rabin_2_3_pseudo_prime :
  miller_rabin [2; 3]    1373653 = true /\
  miller_rabin [2; 3; 5] 1373653 = false /\
  primeb                 1373653 = false.
Proof.
  now native_compute.
Qed.
