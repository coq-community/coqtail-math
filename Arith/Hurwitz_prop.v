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
hastuce.
Qed.

Lemma hopp_hminus_distrib

Lemma hadd_comm : h1 h+ h2 = h2 h+ h1.
Proof.
hastuce.
Qed.

Lemma hadd_assoc : h1 h+ h2 h+ h3 = h1 h+ (h2 h+ h3).
Proof.
hastuce.
Qed.

End basic_lemmas.