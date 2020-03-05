Require Import Rsequence.
Require Import Rseries_def Rseries_base_facts Rseries_pos_facts Rseries_cv_facts.

Require Import Lra Rtactic.

Local Open Scope R_scope.
Local Open Scope Rseq_scope.

Lemma Rser_cv_square_inv : {l | Rser_cv (fun i => / (Rseq_shift INR i) ^ 2)%R l}.
Proof.
apply Rser_cv_sig_shift_rev.
apply Rser_pos_maj_cv with (/ (Rseq_shift INR * Rseq_shifts INR 2)).
 intro n ; left ; apply Rinv_0_lt_compat, pow_lt, lt_0_INR, lt_O_Sn.
 intro n ; left ; apply Rinv_0_lt_compat, Rmult_lt_0_compat ; apply lt_0_INR, lt_O_Sn.
 intro p ; unfold Rseq_shift, Rseq_shifts, Rseq_mult, Rseq_inv, pow ;
 rewrite Rmult_1_r, Rinv_mult_distr, Rinv_mult_distr ;
 try (now (apply Rgt_not_eq, lt_0_INR, lt_0_Sn)).
 apply Rmult_le_compat ; try (now (left ; apply Rinv_0_lt_compat, lt_0_INR, lt_0_Sn)).
  apply Rle_Rinv ; try (now (apply lt_0_INR, lt_O_Sn)) ; apply le_INR ; apply le_n_Sn.
  reflexivity.
 exists 1 ; apply Rseq_cv_eq_compat with (1 - (/ Rseq_shifts INR 2)).
  intro p ; unfold Rseq_minus, Rseq_constant ; induction p.
  unfold Rseq_mult, Rseq_inv, Rseq_shift, Rseq_shifts ; simpl ; field.
  rewrite Rseq_sum_simpl, IHp ; unfold Rseq_constant, Rseq_mult, Rseq_inv,
  Rseq_shifts, Rseq_shift, Rminus ; rewrite Rplus_assoc ; apply Rplus_eq_compat_l.
  simpl ; field ; split ; apply Rgt_not_eq.
  destruct p ; [| assert (H := lt_0_INR _ (lt_0_Sn p))] ; lra.
  destruct p ; [| assert (H := lt_0_INR _ (lt_0_Sn p))] ; lra.
  rewrite <- Rminus_0_r ; apply Rseq_cv_minus_compat ; [apply Rseq_constant_cv |].
   apply Rseq_cv_pos_infty_inv_compat ; eapply Rseq_cv_pos_infty_eq_compat ;
   [| eapply Rseq_cv_finite_plus_pos_infty_l ; [eapply (Rseq_poly_cv 1) |
   eexact (Rseq_constant_cv 2)]].
  intro p ; unfold Rseq_shifts, Rseq_poly, Rseq_plus, Rseq_constant, pow ;
   rewrite plus_INR ; simpl ; ring.
  apply lt_O_Sn.
Qed.

Lemma Rser_cv_inv_poly : forall d, (2 <= d)%nat -> {l | Rser_abs_cv (Rseq_inv_poly d) l}.
Proof.
intros d Hd.
unfold Rser_abs_cv.
cut ({l | Rser_cv (Rseq_inv_poly d) l}).
 intros [l Hl]; exists l.
 eapply Rser_cv_eq_compat; [|apply Hl]; intro i.
 destruct i; unfold Rseq_abs; symmetry; apply Rabs_right.
  apply Rle_refl.
  
  unfold Rseq_inv_poly.
  apply Rle_ge; apply pow_le.
  apply Rlt_le; apply Rinv_0_lt_compat; INR_solve.

apply Rser_pos_maj_cv_shift with (fun (i : nat) => (/ (INR (S i) ^ 2))%R).
 unfold Rseq_inv_poly; intro n; rewrite <- Rinv_pow; [|INR_solve].
 split.
  apply Rlt_le; apply Rinv_0_lt_compat; apply pow_lt; INR_solve.
  apply Rle_Rinv.
   unfold pow; INR_solve; simpl mult; apply lt_O_Sn.
   apply pow_lt; INR_solve.
  apply Rle_pow; auto; INR_solve.
apply Rser_cv_square_inv.
Qed.