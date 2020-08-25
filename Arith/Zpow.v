From Coq Require Import PArith ZArith Lia Znumtheory.
From Coqtail Require Import Ztools.
Open Scope Z_scope.

(** Exponentiation via "square and multiply" *)

Fixpoint Zpow_pos (a : Z) (n : positive) :=
  match n with
  | xH => a
  | xO n => Zpow_pos (a * a) n
  | xI n => a * Zpow_pos (a * a) n
  end.

Lemma Zpow_pos_spec a n : Zpow_pos a n = a ^ Zpos n.
Proof.
  revert a.
  induction n; intros a; simpl Zpow_pos.
  - rewrite IHn. replace (Z.pos n~1) with (1 + 2 * Z.pos n) by lia.
    rewrite Z.pow_add_r; try lia.
    rewrite Z.pow_mul_r; try lia.
    replace (a ^ 2) with (a * a) by lia.
    lia.
  - rewrite IHn. change (Z.pos n~0) with (2 * Z.pos n).
    rewrite Z.pow_mul_r; try lia.
    replace (a ^ 2) with (a * a) by lia.
    lia.
  - lia.
Qed.

Definition Zpow_fast (a b : Z) :=
  match b with
  | 0 => 1
  | Z.pos p => Zpow_pos a p
  | Z.neg _ => 0
  end.

Lemma Zpow_fast_spec a b : Zpow_fast a b = a ^ b.
Proof.
  destruct b; auto.
  apply Zpow_pos_spec.
Qed.


(** Modular exponentiation *)

Fixpoint pow_mod_pos (m : Z) (a : Z) (n : positive) :=
  match n with
  | xH => a mod m
  | xO n => pow_mod_pos m ((a * a) mod m) n
  | xI n => (a * pow_mod_pos m ((a * a) mod m) n) mod m
  end.

Lemma pow_mod_pos_spec m a n : pow_mod_pos m a n = (a ^ Z.pos n) mod m.
Proof.
  revert a.
  induction n; intros a; simpl pow_mod_pos.
  - rewrite IHn. replace (Z.pos n~1) with (1 + 2 * Z.pos n) by lia.
    rewrite Z.pow_add_r; try lia.
    rewrite Z.pow_mul_r; try lia.
    replace (a ^ 2) with (a * a) by lia.
    replace (a ^ 1) with a by lia.
    rewrite <-Zpow_mod.
    rewrite Zmult_mod_idemp_r.
    reflexivity.
  - rewrite IHn. change (Z.pos n~0) with (2 * Z.pos n).
    rewrite Z.pow_mul_r; try lia.
    replace (a ^ 2) with (a * a) by lia.
    rewrite <-Zpow_mod.
    lia.
  - f_equal. lia.
Qed.

Definition pow_mod m (a b : Z) :=
  match b with
  | 0 => 1 mod m
  | Z.pos p => pow_mod_pos m a p
  | Z.neg _ => 0
  end.

Lemma pow_mod_spec m a b : pow_mod m a b = (a ^ b) mod m.
Proof.
  destruct b; auto.
  apply pow_mod_pos_spec.
Qed.
