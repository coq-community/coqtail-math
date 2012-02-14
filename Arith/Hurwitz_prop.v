Require Import ZArith Zpow_facts MyZ.
Require Import Hurwitz_def.

Section basic_lemmas.

Variable h1 h2 h3 : Hurwitz.

(* hopp *)

Lemma hopp_invol : h- (h- h1) = h1.
Proof.
destruct h1 ; simpl ; f_equal ; ring.
Qed.

Lemma hopp_hadd_distrib : h- (h1 h+ h2) = h- h1 h+ h- h2.
Proof.
destruct h1, h2, h3 ; simpl ; f_equal ; ring.
Qed.

Lemma hopp_hadd_hminus : h- h1 h+ h2 = h2 h- h1.
Proof.
destruct h1, h2 ; simpl ; f_equal ; ring.
Qed.

(* hadd *)

Lemma hadd_comm : h1 h+ h2 = h2 h+ h1.
Proof.
destruct h1, h2 ; simpl ; f_equal ; ring.
Qed.

Lemma hadd_assoc : h1 h+ h2 h+ h3 = h1 h+ (h2 h+ h3).
Proof.
destruct h1, h2, h3 ; simpl ; f_equal ; ring.
Qed.

(* hmul *)

Lemma hmul_assoc : forall a b c, hmul a (hmul b c) = hmul (hmul a b) c.
Proof.
intros () () (); intros.
 unfold hmul ; f_equal ; ring.
Qed.

Lemma hmul_1_l : hmul (IZH 1) h1 = h1.
Proof.
destruct h1 ; intros.
unfold hmul, IZH.
f_equal; ring.
Qed.

Lemma hmul_1_r : hmul h1 (IZH 1) = h1.
Proof.
destruct h1 ; intros.
unfold hmul, IZH.
f_equal; ring.
Qed.

(* conjugate *)

Lemma hconj_invol : hconj (hconj h1) = h1.
Proof.
destruct h1 ; intros ; unfold hconj ; f_equal ; ring.
Qed.

Lemma hconj_hopp : hconj (h- h1) = h- (hconj h1).
unfold hconj, hopp ; destruct h1 ; intros ; f_equal ; ring.
Qed.

Lemma hconj_hadd : hconj (h1 h+ h2) = hconj h1 h+ hconj h2.
Proof.
unfold hconj, hadd ; destruct h1, h2 ; intros ; f_equal ; ring.
Qed.

Lemma hconj_hminus : hconj (h1 h- h2) = (hconj h1) h- (hconj h2).
Proof.
unfold hminus, hadd, hopp, hconj ; destruct h1, h2 ; intros ; f_equal ; ring.
Qed.

Lemma hconj_hmul : hconj (h1 h* h2) = (hconj h2) h* (hconj h1).
Proof.
unfold hmul, hconj ; destruct h1, h2 ; f_equal ; ring.
Qed.

(* norm *)

Lemma real_norm2 : is_real (hmul h1 (hconj h1)).
Proof.
destruct h1 ; intros; unfold hmul, hconj.
repeat split;
  cbv delta [Hurwitz_def.h Hurwitz_def.i Hurwitz_def.j Hurwitz_def.k];
  cbv iota beta;
  ring.
Qed.

Lemma hnorm2_pos : 0 <= hnorm2 h1.
Proof.
destruct h1 ; intros ; unfold hnorm2, hmul, hconj.
 cbv delta [Hurwitz_def.h] ; cbv beta ; cbv iota ; cbv beta.
 ring_simplify.
 transitivity ((h + 2 * i) ^ 2 + (h + 2 * j) ^ 2 + (h + 2 * k) ^ 2 + h ^ 2).
 do 4 rewrite Zpower_2 ; repeat apply Zplus_le_0_compat ; apply Zge_le, sqr_pos.
 apply eq_Zle ; ring.
Qed.

Lemma H_unit_is_unit : forall x, H_unit x -> is_H_unit x.
Proof.
  intros x Ux.
  exists (hconj x).
  destruct Ux as [[]|[]|[]|[]|[] [] [] []]; auto.
Qed.

Lemma hnorm2_conj : forall x, hnorm2 (hconj x) = hnorm2 x.
Proof.
  intros [a b c d]; intros.
  unfold hnorm2, hconj, hmul, h.
  ring.
Qed.

Lemma H_unit_characterization : forall x, is_H_unit x -> H_unit x.
Proof.
  intros x Ux.
  (* destruction bourrine *)
Admitted.

End basic_lemmas.
