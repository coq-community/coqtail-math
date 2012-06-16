Require Import Rsequence_def.

Local Open Scope Rseq_scope.

Lemma Rseq_shift_shifts: forall Un n,
  Rseq_shifts Un (S n) == Rseq_shift (Rseq_shifts Un n).
Proof.
intros Un n k ; unfold Rseq_shift, Rseq_shifts ;
 f_equal ; apply plus_n_Sm.
Qed.

Lemma Rseq_shifts_shift: forall Un n,
  Rseq_shifts Un (S n) == Rseq_shifts (Rseq_shift Un) n.
Proof.
intros Un n k ; reflexivity.
Qed.

Lemma Rseq_shifts_fusion : forall An k m,
  (Rseq_shifts (Rseq_shifts An k) m == Rseq_shifts An (k + m))%Rseq.
Proof.
intros ; unfold Rseq_shifts ; intro ; rewrite plus_assoc ; reflexivity.
Qed.

Lemma Rseq_minus_simpl : forall Un Vn,
  Un - Vn == Un + - Vn.
Proof.
intros Un Vn n ; unfold Rseq_minus, Rminus ; reflexivity.
Qed.

Lemma Rseq_div_simpl : forall Un Vn,
  Un / Vn == Un * / Vn.
Proof.
intros Un Vn n ; unfold Rseq_div, Rdiv ; reflexivity.
Qed.

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

(** Shifts and common operations *)

Lemma Rseq_shifts_opp_compat : forall An k,
  Rseq_shifts (- An) k == - Rseq_shifts An k.
Proof.
intros ; unfold Rseq_shifts ; intro n ; reflexivity.
Qed.

Lemma Rseq_shifts_plus_compat : forall An Bn k,
  Rseq_shifts (An + Bn) k == Rseq_shifts An k + Rseq_shifts Bn k.
Proof.
intros ; unfold Rseq_shifts ; intro n ; reflexivity.
Qed.

Lemma Rseq_shifts_mult_compat : forall An Bn k,
  Rseq_shifts (An * Bn) k == Rseq_shifts An k * Rseq_shifts Bn k.
Proof.
intros ; unfold Rseq_shifts ; intro n ; reflexivity.
Qed.

Lemma Rseq_shifts_div_compat : forall An Bn k,
  Rseq_shifts (An / Bn) k == Rseq_shifts An k / Rseq_shifts Bn k.
Proof.
intros ; unfold Rseq_shifts ; intro n ; reflexivity.
Qed.

Lemma Rseq_shifts_inv_compat : forall An k,
  Rseq_shifts (/ An) k == / Rseq_shifts An k.
Proof.
intros ; unfold Rseq_shifts ; intro n ; reflexivity.
Qed.

Lemma Rseq_shifts_scal_compat : forall (c : R) An k,
  Rseq_shifts (c * An) k == c * Rseq_shifts An k.
Proof.
intros ; unfold Rseq_shifts ; intro n ; reflexivity.
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