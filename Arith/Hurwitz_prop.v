Require Import Hurwitz_def.

Section basic_lemmas.

Variable h1 h2 h3 : Hurwitz.

(* hopp *)

Lemma hopp_invol : h- (h- h1) = h1.
Proof.
destruct h1 ; hastuce.
Qed.

Lemma hopp_hadd_distrib : h- (h1 h+ h2) = h- h1 h+ h- h2.
Proof.
destruct h1, h2, h3; hastuce.
Qed.

Lemma hadd_comm : h1 h+ h2 = h2 h+ h1.
Proof.
destruct h1, h2; hastuce.
Qed.

Lemma hadd_assoc : h1 h+ h2 h+ h3 = h1 h+ (h2 h+ h3).
Proof.
destruct h1, h2, h3; hastuce.
Qed.

Lemma hmul_assoc : forall a b c, hmul a (hmul b c) = hmul (hmul a b) c.
Proof.
intros () () (); intros.
unfold hmul.
(* ok maintenant on a un problème de scope *)
f_equal; ring.
Qed.

Lemma hmul_1_l : forall a, hmul (IZH 1) a = a.
Proof.
intros (); intros.
unfold hmul, IZH.
f_equal; ring.
Qed.

Lemma hmul_1_r : forall a, hmul a (IZH 1) = a.
Proof.
intros (); intros.
unfold hmul, IZH.
f_equal; ring.
Qed.

Lemma real_norm2 : forall a, is_real (hmul a (hconj a)).
Proof.
intros (); intros; unfold hmul, hconj.
repeat split;
  cbv delta [Hurwitz_def.h Hurwitz_def.i Hurwitz_def.j Hurwitz_def.k];
  cbv iota beta;
  ring.
Qed.

End basic_lemmas.
