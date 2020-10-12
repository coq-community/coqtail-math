Require Import Reals.
Require Import Lra.

Require Import Rsequence.
Require Import Rpser_def Rpser_base_facts.
Require Import Rpser_cv_facts.
Require Import Rpser_sums Rpser_derivative.

Local Open Scope R_scope.

(** * Comparison of Taylor development *)

Section Taylor.

Variable Un : nat -> R.
Variable En : nat -> R.
Variable r : R.

(* begin hide *)
Lemma partial_sum_null : forall N x,
  Rseq_pps (fun n => if le_lt_dec n N then 0 else Un n) x N = 0.
Proof.
intros N x ; assert (Hrec : forall n, (n <= N)%nat ->
  Rseq_pps (fun n => if le_lt_dec n N then 0 else Un n) x n = 0).
  intros n Hn ; induction n.
   unfold Rseq_pps, gt_pser, Rseq_mult ; simpl ; apply Rmult_0_l.
   rewrite Rseq_pps_simpl, IHn, Rplus_0_l ;
   destruct (le_lt_dec (S n) N) as [H | Hf].
    apply Rmult_0_l.
    exfalso ; lia.
   lia.
   exfalso ; lia.
apply Hrec ; trivial.
Qed.

Lemma partial_sum : forall N x
  (Vn := fun n : nat => if le_lt_dec n N then 0 else Un n) n
  (Hle : (N<= n)%nat),
  Rseq_pps Un x n = Rseq_pps Un x N + Rseq_pps Vn x n.
Proof.
intros N x Vn n Hle ; induction Hle.
unfold Vn ; rewrite partial_sum_null ; ring.
do 2 rewrite Rseq_pps_simpl ; rewrite IHHle ; unfold Vn at 3.
destruct (le_lt_dec (S m ) N).
  exfalso ; lia.
  apply Rplus_assoc.
Qed.
(* end hide *)

Lemma Rpser_big_O_partial_sum :
  forall N (H : 0 < r) (Hcv : Rseq_cv En 0) (pr : Cv_radius_weak Un r),
    (fun p => weaksum_r Un r pr (En p) - Rseq_pps Un (En p) N)
    = O((fun p => (En p) ^ (S N))).
Proof.
intros N H Hcv pr.
pose (Vn := fun n => if le_lt_dec n N then 0 else Un n).
pose (Wn := fun n => Un (n + S N)%nat).
assert (prv : Cv_radius_weak Vn r).
  destruct pr as [M HM].
  exists M; intros m Hm.
  destruct Hm as [i Hi]; rewrite Hi.
  unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult.
  unfold Vn; destruct le_lt_dec.
  rewrite Rmult_0_l; rewrite Rabs_R0.
  eapply Rle_trans.
    apply Rabs_pos.
    apply HM.
    exists i; reflexivity.
  apply HM.
  unfold EUn, gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult.
  exists i; reflexivity.
assert (prw : Cv_radius_weak Wn r).
  destruct pr as [M HM].
  exists (M / r ^ (S N)); intros m Hm.
  destruct Hm as [i Hi]; rewrite Hi.
  unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult, Wn.
  apply (Rmult_le_reg_l (r ^ (S N))).
  apply pow_lt; assumption.
  replace (r ^ (S N) * (M / r ^ (S N)))
    with M by (field; apply Rgt_not_eq; apply pow_lt; assumption).
  rewrite <- (Rabs_right (r ^ (S N))); [|apply Rle_ge; apply pow_le; lra].
  rewrite <- Rabs_mult.
  rewrite Rmult_comm.
  rewrite Rmult_assoc.
  rewrite <- pow_add.
  apply HM.
  unfold EUn, gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult.
  exists (i + (S N))%nat; reflexivity.
pose (St := fun x => weaksum_r Un r pr x).
pose (Sr := fun x => weaksum_r Vn r prv x).
pose (Sp := fun x => sum_f_R0 (fun n => Un n * x ^ n) N).
pose (Ss := fun x => weaksum_r Wn r prw x).
assert (Hsum : forall x, Rabs x < r -> St x = Sp x + Sr x).
  intros x Hx.
  eapply Rseq_cv_unique.
    apply weaksum_r_sums; assumption.
    assert (Hcvv := weaksum_r_sums Vn r prv x Hx).
    intros eps Heps; destruct (Hcvv eps Heps) as [n0 Hn0].
    exists (Max.max N n0); intros n Hn.
    assert (Rseq_pps Un x n = Rseq_pps Un x N + Rseq_pps Vn x n) as ->; swap 1 2.
    assert (Hrw : exists p, n = (N + p)%nat).
      exists (n - N)%nat.
      assert (n >= N)%nat.
        eapply le_trans; [apply Max.le_max_l|eexact Hn].
      lia.
    destruct Hrw as [p Hp]; subst n.
    unfold R_dist.
    rewrite Rplus_comm.
    unfold Rminus.
    rewrite Rplus_assoc.
    rewrite Ropp_plus_distr.
    rewrite <- Rplus_assoc with (r2 := - Sp x).
    rewrite Rplus_opp_r.
    rewrite Rplus_0_l.
    apply Hn0; eapply le_trans; [apply Max.le_max_r|eexact Hn].
    assert (Hle : (N <= n)%nat).
      eapply le_trans; [apply Max.le_max_l|eexact Hn].
    clear - Un Hle.
    apply partial_sum; apply Hle.
assert (Hmul : forall x, Rabs x < r -> Sr x = x ^ (S N) * Ss x).
  intros x Hx.
  eapply Rseq_cv_unique.
    apply weaksum_r_sums; assumption.
    assert (Hcvw := weaksum_r_sums Wn r prw x Hx).
    destruct (Req_dec x 0) as [Hz|Hnz].
      rewrite Hz.
      intros eps Heps.
      exists 0%nat; intros n _.
      assert (Rseq_pps Vn 0 n = 0) as ->; swap 1 2.
      rewrite pow_ne_zero; [|lia].
      rewrite Rmult_0_l.
      rewrite R_dist_eq.
      assumption.
      induction n; simpl.
        rewrite Rseq_pps_0_simpl ; unfold Vn.
        destruct le_lt_dec; [field|apply False_ind; lia].
        rewrite Rseq_pps_simpl.
        rewrite pow_i, Rmult_0_r, Rplus_0_r.
        assumption.
        lia.
      intros eps Heps.
      destruct (Hcvw (eps / Rabs (x ^ (S N)))) as [n0 Hn0].
        unfold Rdiv; apply Rmult_gt_0_compat.
          assumption.
          apply Rinv_0_lt_compat.
          apply Rabs_pos_lt; apply pow_nonzero; assumption.
      exists (n0 + S N)%nat; intros n Hn.
      assert (Rseq_pps Vn x n = x ^ S N * Rseq_pps Wn x (n - (S N))) as ->; swap 1 2.
      unfold R_dist; rewrite <- Rmult_minus_distr_l.
      rewrite Rabs_mult.
      apply (Rmult_lt_reg_l (/ Rabs (x ^ S N))).
      apply Rinv_0_lt_compat.
      apply Rabs_pos_lt; apply pow_nonzero; assumption.
      rewrite <- Rmult_assoc.
      rewrite Rinv_l.
      rewrite Rmult_1_l.
      rewrite Rmult_comm.
      apply Hn0; lia.
      apply Rgt_not_eq.
      apply Rabs_pos_lt; apply pow_nonzero; assumption.
    assert (Hrw : exists p, (n = N + S p)%nat).
      exists (n - (S N))%nat; lia.
    destruct Hrw as [p Hp]; subst n.
    clear - p.
      induction p; simpl.
        replace (N + 1)%nat with (S N) by lia.
        replace (S N - S N)%nat with 0%nat by lia.
        unfold Vn, Wn.
        rewrite Rseq_pps_simpl, Rseq_pps_O_simpl, partial_sum_null.
        destruct le_lt_dec as [H|_]; [apply False_ind; lia|].
        simpl ; ring.
        rewrite <- plus_n_Sm.
        replace (S (N + S p) - S N)%nat with (S (N + S p - S N))%nat by lia.
        rewrite Rseq_pps_simpl, IHp.
        replace (S (N + S p)) with ((S N) + (S p))%nat by lia ;
        rewrite (pow_add _ (S N)).
        transitivity (x ^ S N * (Rseq_pps Wn x (N + S p - S N) +
         x ^ S p * Vn (S N + S p)%nat)).
        ring.
        simpl ; do 2 (repeat rewrite Rmult_assoc ; apply Rmult_eq_compat_l).
        rewrite Rseq_pps_simpl ; apply Rplus_eq_compat_l.
        unfold Vn, Wn.
        destruct le_lt_dec as [H|_]; [apply False_ind; lia|].
        replace (S (N + S p - S N) + S N)%nat with (S (N + S p))%nat by lia.
        replace (N + S p - S N)%nat with p by lia.
        simpl ; ring.
assert (Hct : continuity_pt Ss 0).
  apply continuity_pt_weaksum_r.
  rewrite Rabs_R0; assumption.
destruct (Hct 1) as [alp [Halp Hd]]; [lra|].
assert (Hradius : exists P, forall p, (p >= P)%nat -> Rabs (En p) < r /\ Rabs (En p) < alp).
  destruct (Hcv r H) as [P1 HP1].
  destruct (Hcv alp Halp) as [P2 HP2].
  exists (Max.max P1 P2); intros p Hp.
  rewrite <- (Rminus_0_r (En p)); split.
  apply HP1; eapply le_trans; [apply Max.le_max_l|apply Hp].
  apply HP2; eapply le_trans; [apply Max.le_max_r|apply Hp].
destruct Hradius as [P HP].
exists (Rabs (Ss 0) + 1); split.
  apply Rle_ge; apply Rplus_le_le_0_compat.
    apply Rabs_pos.
    lra.
  exists P; intros p Hp.
  assert (Hp1 : Rabs (En p) < r).
    apply (HP p); assumption.
  assert (Hp2 : Rabs (En p) < alp).
    apply (HP p); assumption.
  rewrite Hsum; [|assumption].
  rewrite Rplus_comm.
  unfold Rminus; rewrite Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  rewrite Hmul; [|assumption].
  rewrite Rabs_mult.
  rewrite Rmult_comm.
  apply Rmult_le_compat_r; [apply Rabs_pos|].
  rewrite <- (Rplus_0_l (Rabs (Ss (En p)))).
  pattern 0 at 1; erewrite <- Rplus_opp_r.
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  rewrite Rplus_comm.
  eapply Rle_trans.
    apply Rabs_triang_inv.
    destruct (Req_dec (En p) 0) as [He|He].
      rewrite He; unfold Rminus; rewrite Rplus_opp_r.
      rewrite Rabs_R0; lra.
    apply Rlt_le; apply (Hd (En p)); split.
      compute; auto.
      simpl; unfold R_dist; rewrite Rminus_0_r.
      apply Hp2.
Qed.

Lemma Rpser_little_O_partial_sum :
  forall N (H : 0 < r) (Hcv : Rseq_cv En 0) (pr : Cv_radius_weak Un r),
    (fun p => weaksum_r Un r pr (En p) - sum_f_R0 (fun n => Un n * (En p) ^ n) N) = o((fun p => (En p) ^ N)).
Proof.
intros N H Hcv pr.
eapply Rseq_big_O_little_O_trans; [apply Rpser_big_O_partial_sum; assumption|].
intros eps Heps.
destruct (Hcv eps Heps) as [M HM].
exists M; intros n Hn.
simpl pow; rewrite Rabs_mult.
apply Rmult_le_compat_r; [apply Rabs_pos|].
apply Rlt_le; replace (En n) with (En n - 0) by field.
apply HM; assumption.
Qed.

End Taylor.
