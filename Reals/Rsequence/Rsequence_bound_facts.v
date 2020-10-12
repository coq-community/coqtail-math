Require Import Lia.
Require Import Rsequence_def.
Require Import Rsequence_base_facts Rsequence_sums_facts.
Require Import Rsequence_rewrite_facts.
Require Import Lra.
Require Import MyRIneq.	

Open Scope R_scope.
Open Scope Rseq_scope.

(** * Boundedness compatibility. *)

Section Rseq_bound_compatibilities.

Variables (Un Vn : Rseq) (lu lv : R).
Hypothesis (Un_bd : Rseq_bound Un lu) (Vn_bd : Rseq_bound Vn lv).

Lemma Rseq_bound_eq : forall Wn, Un == Wn ->
  Rseq_bound Wn lu.
Proof.
intros Wn Heq n ; rewrite <- Heq ; apply Un_bd.
Qed.

Lemma Rseq_bound_opp : Rseq_bound (- Un) lu.
Proof.
intro n ; unfold Rseq_opp ; rewrite Rabs_Ropp ; apply Un_bd.
Qed.

Lemma Rseq_bound_plus : Rseq_bound (Un + Vn) (lu + lv).
Proof.
intro n ; unfold Rseq_plus ;
 apply Rle_trans with (Rabs (Un n) + Rabs (Vn n))%R ;
 [apply Rabs_triang | apply Rplus_le_compat ; auto].
Qed.

Lemma Rseq_bound_minus : Rseq_bound (Un - Vn) (lu + lv).
Proof.
intro n ; unfold Rseq_minus, Rminus ;
 apply Rle_trans with (Rabs (Un n) + Rabs (- Vn n))%R ;
 [apply Rabs_triang | rewrite Rabs_Ropp ; apply Rplus_le_compat ; auto].
Qed.

Lemma Rseq_bound_mult : Rseq_bound (Un * Vn) (lu * lv).
Proof.
intro n ; unfold Rseq_mult ; rewrite Rabs_mult ;
 apply Rmult_le_compat ; (apply Rabs_pos || auto).
Qed.

Lemma Rseq_bound_sum : Rseq_bound (Rseq_sum Un / Rseq_shift INR) lu.
Proof.
intro n ; induction n ; unfold Rseq_div, Rseq_shift, Rdiv.
 simpl ; rewrite Rinv_1, Rmult_1_r ; apply Un_bd.
 rewrite Rabs_mult, Rabs_Rinv ; [| apply not_0_INR ; lia].
 apply Rmult_Rinv_le_compat ; [apply Rabs_pos_lt ; apply not_0_INR ; lia |].
 rewrite (Rabs_pos_eq (INR (S (S n)))), Rseq_sum_simpl, S_INR,
 Rmult_plus_distr_r, Rmult_1_l ; [| apply pos_INR].
 eapply Rle_trans ; [eapply Rabs_triang |] ; apply Rplus_le_compat.
 rewrite <- (Rabs_pos_eq (INR (S n))) ; [| apply pos_INR].
 apply Rmult_Rinv_le_compat_contravar ; [apply Rabs_pos_lt ; apply not_0_INR ; lia |].
 rewrite <- Rabs_Rinv, <- Rabs_mult ; [apply IHn | apply not_0_INR ; lia].
 apply Un_bd.
Qed.

End Rseq_bound_compatibilities.

Lemma Rseq_bound_prod : forall (Un Vn : Rseq) (lu lv : R),
  Rseq_bound Un lu -> Rseq_bound Vn lv ->
  Rseq_bound ((Un # Vn) / Rseq_shift INR) (lu * lv).
Proof.
intros Un Vn lu lv Un_bd Vn_bd n ; unfold Rseq_prod, Rseq_div ;
 apply Rseq_bound_sum ; apply Rseq_bound_mult ;
 [apply Un_bd | intro p ; apply Vn_bd].
Qed.
