Require Import Rsequence_def.

Local Open Scope Rseq_scope.

Lemma Rseq_fact_simpl : forall n,
  Rseq_fact (S n) = (INR (S n) * Rseq_fact n)%R.
Proof.
intro n ; unfold Rseq_fact ;
rewrite fact_simpl, mult_INR ;
reflexivity.
Qed.

Lemma Rseq_shifts_0 : forall Un,
  Rseq_shifts Un 0 == Un.
Proof.
intros Un n ; unfold Rseq_shifts ; rewrite plus_0_l ;
reflexivity.
Qed.

Lemma Rseq_shifts_O : forall Un k,
  Rseq_shifts Un k O = Un k.
Proof.
intros Un k ; unfold Rseq_shifts ; rewrite plus_0_r ;
reflexivity.
Qed.

Lemma Rseq_cv_Un_cv_equiv : forall Un l,
  Rseq_cv Un l <-> Un_cv Un l.
Proof.
intros Un l ; split ; trivial.
Qed.

Lemma Rseq_abs_proj : forall An,
  Rseq_abs (Rseq_abs An) == Rseq_abs An.
Proof.
intros An n ; unfold Rseq_abs ; apply Rabs_Rabsolu.
Qed.