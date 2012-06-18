Require Import MyRIneq.
Require Import Rsequence_def.

Local Open Scope Rseq_scope.

(** Unfolding Rseq_sum *)

Lemma Rseq_sum_simpl : forall Un n,
  (Rseq_sum Un (S n) = Rseq_sum Un n + Un (S n))%R.
Proof.
intros ; reflexivity.
Qed.

(** Rseq_shift(s) simplification rules *)

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

(** Unfolding definitions *)

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

(** Action of Rseq_abs on different operations *)

Lemma Rseq_abs_idempotent : forall An,
  Rseq_abs (Rseq_abs An) == Rseq_abs An.
Proof.
intros An n ; unfold Rseq_abs ; apply Rabs_Rabsolu.
Qed.

Lemma Rseq_abs_mult : forall An Bn,
  Rseq_abs (An * Bn) == Rseq_abs An * Rseq_abs Bn.
Proof.
intros An Bn n ; apply Rabs_mult.
Qed.

Lemma Rseq_abs_pow : forall r,
  Rseq_abs (Rseq_pow r) == Rseq_pow (Rabs r).
Proof.
intros r n ; symmetry ; apply RPow_abs.
Qed.

Lemma Rseq_abs_alt : forall An,
  Rseq_abs (Rseq_alt An) == Rseq_abs An.
Proof.
intros An n ; unfold Rseq_alt, Rseq_pow ;
 rewrite Rseq_abs_mult ; unfold Rseq_mult, Rseq_abs ;
 rewrite Rabs_opp1 ; apply Rmult_1_l.
Qed.

Lemma Rseq_abs_zip : forall An Bn,
  Rseq_abs (Rseq_zip An Bn) == Rseq_zip (Rseq_abs An) (Rseq_abs Bn).
Proof.
intros An Bn n ; unfold Rseq_abs, Rseq_zip ; case (n_modulo_2 n) ;
 intros [p Hp] ; reflexivity.
Qed.

(** Action of Rseq_alt on common operations *)

Lemma Rseq_alt_involutive : forall An,
  Rseq_alt (Rseq_alt An) == An.
Proof.
intros An n ; unfold Rseq_alt, Rseq_mult, Rseq_pow.
 rewrite <- Rmult_assoc, <- pow_add ;
 replace (n + n)%nat with (2 * n)%nat by ring ;
 rewrite pow_1_even ; apply Rmult_1_l.
Qed.

Lemma Rseq_alt_scal_l : forall An (l : R),
  Rseq_alt (l * An) == l * Rseq_alt An.
Proof.
intros An l n ; unfold Rseq_alt, Rseq_mult, Rseq_constant ; ring.
Qed.

Lemma Rseq_alt_scal_r : forall An (l : R),
  Rseq_alt (An * l) == Rseq_alt An * l.
Proof.
intros An l n ; unfold Rseq_alt, Rseq_mult, Rseq_constant ; ring.
Qed.

Lemma Rseq_alt_opp : forall An,
  Rseq_alt (- An) == - Rseq_alt An.
Proof.
intros An n ; unfold Rseq_alt, Rseq_mult, Rseq_opp ; ring.
Qed.

Lemma Rseq_alt_plus : forall An Bn,
  Rseq_alt (An + Bn) == Rseq_alt An + Rseq_alt Bn.
Proof.
intros An Bn n ; unfold Rseq_alt, Rseq_mult, Rseq_plus ; ring.
Qed.

Lemma Rseq_alt_minus : forall An Bn,
  Rseq_alt (An - Bn) == Rseq_alt An - Rseq_alt Bn.
Proof.
intros An Bn n ; unfold Rseq_alt, Rseq_mult, Rseq_minus ; ring.
Qed.

Lemma Rseq_alt_mult_l : forall An Bn,
  Rseq_alt (An * Bn) == Rseq_alt An * Bn.
Proof.
intros An Bn n ; unfold Rseq_alt, Rseq_mult ; ring.
Qed.

Lemma Rseq_alt_mult_r : forall An Bn,
  Rseq_alt (An * Bn) == An * Rseq_alt Bn.
Proof.
intros An Bn n ; unfold Rseq_alt, Rseq_mult ; ring.
Qed.

Lemma Rseq_alt_zip : forall An Bn,
  Rseq_alt (Rseq_zip An Bn) == Rseq_zip An (- Bn).
Proof.
intros An Bn n ; unfold Rseq_alt, Rseq_zip, Rseq_mult, Rseq_opp, Rseq_pow ;
 case (n_modulo_2 n) ; intros [p Hp] ; subst.
 rewrite pow_1_even ; apply Rmult_1_l.
 rewrite pow_1_odd ; ring.
Qed.

(* TODO: add Rseq_alt_inv, Rseq_alt_div, Rseq_alt_prod *)

(** Action of Rseq_zip over simple operations *)

Lemma Rseq_zip_opp : forall An Bn,
 - Rseq_zip An Bn == Rseq_zip (- An) (- Bn).
Proof.
intros An Bn n ; unfold Rseq_zip, Rseq_opp ;
 case (n_modulo_2 n) ; intros [p Hp] ; reflexivity.
Qed.

Lemma Rseq_zip_scal_l : forall An Bn (l : R),
  l * Rseq_zip An Bn == Rseq_zip (l * An) (l * Bn).
Proof.
intros An Bn l n ; unfold Rseq_mult, Rseq_constant, Rseq_zip ;
 case (n_modulo_2 n) ; intros [p Hp] ; reflexivity.
Qed.

(** Link with stdlib *)

Lemma Rseq_cv_Un_cv_equiv : forall Un l,
  Rseq_cv Un l <-> Un_cv Un l.
Proof.
intros Un l ; split ; trivial.
Qed.
