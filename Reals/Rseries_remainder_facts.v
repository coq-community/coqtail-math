Require Import Rsequence.
Require Import Rseries_def Rseries_base_facts Rseries_cv_facts.

Require Import MyRIneq.

Local Open Scope R_scope.
Local Open Scope Rseq_scope.

(** Remainder caracterization *)

Lemma Rser_rem_ext: forall An l Hl Bn l' Hl' n,
  An == Bn -> Rser_rem An l Hl n = Rser_rem Bn l' Hl' n.
Proof.
intros ; apply Rminus_eq_compat ;
 [eapply Rser_cv_unique | eapply Rseq_sum_ext] ;
 [ | erewrite Rser_cv_ext |] ; eassumption.
Qed.

Lemma Rser_rem_cv : forall An l (Hl : Rser_cv An l ) (n : nat), 
    Rser_cv (Rseq_shifts An (S n)) (Rser_rem An l Hl n).
Proof.
intros An l Hl n ; unfold Rser_cv ; eapply Rseq_cv_eq_compat.
 intro p ; eapply Rseq_sum_shifts_compat.
 unfold Rser_rem ; apply Rseq_cv_minus_compat.
  apply Rseq_cv_shifts_compat_reciprocal ; assumption.
  apply Rseq_constant_cv.
Qed.

(** Compatibility between remainder and usual operations *)

Lemma Rser_rem_scal_compat_l: forall An l (k : R) Hkl Hl,
  Rser_rem (k * An) (k * l) Hkl == k * Rser_rem An l Hl.
Proof.
intros An l k Hkl Hl n ; unfold Rser_rem ; rewrite Rseq_sum_scal_compat_l ;
 unfold Rseq_plus, Rseq_minus, Rseq_constant, Rseq_mult ;  ring.
Qed.

Lemma Rser_rem_scal_compat_r: forall An l (k : R) Hlk Hl,
  Rser_rem (An * k) (l * k) Hlk == Rser_rem An l Hl * k.
Proof.
intros An l k Hlk Hl n ; unfold Rser_rem ; rewrite Rseq_sum_scal_compat_r ;
 unfold Rseq_plus, Rseq_minus, Rseq_constant, Rseq_mult ;  ring.
Qed.

Lemma Rser_rem_opp_compat: forall An l Hl Hl2,
  Rser_rem (- An) (- l) Hl == - Rser_rem An l Hl2.
Proof.
intros An l Hl Hl2 n ; unfold Rser_rem ; rewrite Rseq_sum_opp_compat ;
 unfold Rseq_plus, Rseq_minus, Rseq_opp ; ring.
Qed.

Lemma Rser_rem_plus_compat: forall An Bn la lb Hla Hlb Hlab,
  Rser_rem An la Hla + Rser_rem Bn lb Hlb == Rser_rem (An + Bn) (la + lb) Hlab.
Proof.
intros An Bn la lb Hla Hlb Hlab n ; unfold Rser_rem ;
 rewrite Rseq_sum_plus_compat ; unfold Rseq_plus, Rseq_minus ; ring.
Qed.

Lemma Rser_rem_minus_compat: forall An Bn la lb Hla Hlb Hlab,
  Rser_rem An la Hla - Rser_rem Bn lb Hlb == Rser_rem (An - Bn) (la - lb) Hlab.
Proof.
intros An Bn la lb Hla Hlb Hlab n ; unfold Rser_rem ;
 rewrite Rseq_sum_minus_compat ; unfold Rseq_plus, Rseq_minus ; ring.
Qed.
