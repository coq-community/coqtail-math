From Coq Require Import ZArith Znumtheory Lia List Bool.
From Coqtail Require Import Ztools Zpow.

(** Naive decision procedure for primality, checking up to sqrt(n) *)

Definition prime_sqrt (n : Z) : Prop := 1 < n /\ (forall x : Z, 1 < x <= Z.sqrt n -> ~ (x | n)).

Lemma prime_sqrt_spec n : prime_sqrt n <-> prime n.
Proof.
  rewrite <-prime_alt. symmetry.
  unfold prime', prime_sqrt.
  split; intros [bn h]; split; auto; intros x bx.
  - apply h. split. lia. pose proof Z.sqrt_lt_lin n; lia.
  - intros (y, e).
    destruct (Z_le_gt_dec x y) as [ xy | xy ].
    + apply (h x); [ | exists y; lia ].
      assert (1 < x). enough (x <> 0) by nia. intros ->. lia.
      split; auto.
      apply Z.sqrt_le_square; try lia.
      rewrite e. nia.
    + apply (h y); [ | exists x; lia ].
      assert (1 < y). enough (y <> 0) by nia. intros ->. lia.
      split; auto.
      apply Z.sqrt_le_square; try lia.
      rewrite e. nia.
Qed.

Fixpoint Zseq (start : Z) (len : nat) {struct len} : list Z :=
  match len with
  | 0%nat => nil
  | S len => start :: Zseq (1 + start) len
  end.

Lemma in_Zseq n a x : In x (Zseq a n) <-> (a <= x < a + Z.of_nat n).
Proof.
  revert a. induction n; intros a. simpl. lia.
  split.
  - intros [ -> | h ]. lia.
    rewrite IHn in h. lia.
  - intros h. destruct (Z.eq_dec a x). now left. right.
    apply IHn. lia.
Qed.

Definition primeb (p : Z) : bool :=
  ((1 <? p) &&
   forallb
     (fun n => negb (p mod n =? 0))
     (Zseq 2 (Z.to_nat (Z.sqrt p) - 1)))%bool.

Lemma primeb_prime (n : Z) : primeb n = true <-> prime n.
Proof.
  rewrite <-prime_sqrt_spec.
  unfold prime_sqrt, primeb.
  rewrite andb_true_iff, Z.ltb_lt, forallb_forall.
  split; intros [hn h]; split; auto.
  - intros x bx xn. specialize (h x). rewrite in_Zseq in h.
    spec h by lia. rewrite negb_true_iff, Z.eqb_neq in h.
    apply h, Zdivide_mod, xn.
  - intros x bx%in_Zseq. rewrite negb_true_iff, Z.eqb_neq, Z.mod_divide. 2:lia.
    apply h. lia.
Qed.

Import ListNotations.
Definition primes_up_to (n : Z) := filter primeb (Zseq 1 (Z.to_nat n)).

(*
Time Eval vm_compute in primes_up_to 1000. (* 0.1 sec *)
Time Eval vm_compute in primes_up_to 10000. (* 3 sec *)
*)
