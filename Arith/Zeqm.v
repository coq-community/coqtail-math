Require Import ZArith Znumtheory.
Require Import MyNat Ztools.

(** * Results about [eqm], congruence modulo some integer *)

Notation " a ≡ b [ p ] " := ( eqm p a b ) (at level 70).

Existing Instances eqm_setoid Zplus_eqm Zminus_eqm Zmult_eqm.

Lemma mod0_eqm : forall x m, x ≡ 0 [m] <-> x mod m = 0.
Proof.
  intros x m.
  rewrite <- Zmod_0_l with m.
  intuition.
Qed.

Lemma divide_eqm : forall x m, m <> 0 -> (x ≡ 0 [m] <-> (m | x)).
Proof.
  intros x m Nm; split; rewrite mod0_eqm; intros H.
    apply Zmod_divide; auto.
    apply Zdivide_mod; auto.
Qed.

Lemma eq_eqm : forall m a b, a = b -> a ≡ b [m].
Proof.
  intros; subst; reflexivity.
Qed.

Lemma eqm_diag : forall m, m ≡ 0 [m].
Proof.
  intros; red; rewrite Z_mod_same_full; reflexivity.
Qed.

Lemma eqm_minus_0 : forall a b m, a ≡ b [m] <-> a - b ≡ 0 [m].
Proof.
  intros a b m; split; intros E.
    rewrite E; red; f_equal; ring.
    rewrite <- (Zminus_0_r a), <- E; red; f_equal; ring.
Qed.

Lemma eqm_divide m a b : m <> 0 -> a ≡ b [ m ] <-> (m | a - b).
Proof.
  intros mz.
  rewrite eqm_minus_0.
  rewrite <-Z.mod_divide; tauto.
Qed.

Lemma eqm_mult_compat_l : forall k a b m, a ≡ b [m] -> k * a ≡ k * b [k * m].
Proof.
  intros k a b m E.
  red.
  repeat rewrite Zmult_mod_distr_l.
  rewrite E.
  auto.
Qed.

Lemma eqm_mult_compat_r : forall k a b m, a ≡ b [m] -> a * k ≡ b * k [k * m].
Proof.
  intros k a b m.
  repeat rewrite <- (Zmult_comm k).
  apply eqm_mult_compat_l.
Qed.


(** Modulo m if a≡m/2 then a²≡m²/4 *)

Lemma eqm_square_half : forall x m, 0 <> m ->
  x ≡ m [2 * m] -> x * x ≡ m * m [4 * (m * m)].
Proof.
  intros x m Nm D.
  rewrite eqm_minus_0 in D.
  rewrite divide_eqm in D; notzero.
  destruct (Zdivide_inf _ _ D) as (k, Ek).
  replace x with (x - m + m) by ring.
  rewrite Ek.
  apply eqm_minus_0.
  ring_simplify.
  apply divide_eqm; notzero.
  exists (k + k ^ 2).
  ring.
Qed.
