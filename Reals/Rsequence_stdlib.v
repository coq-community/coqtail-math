Require Import Ranalysis.
Require Import Rsequence_def.

Lemma Rseq_cv_Un_cv: Rseq_cv = Un_cv.
Proof.
reflexivity.
Qed.

Lemma Rseq_bound_max_has_ub: forall Un M,
  Rseq_bound_max Un M -> has_ub Un.
Proof.
intros Un M HM ; exists M ; intros x [i Hi] ;
 subst ; apply HM.
Qed.