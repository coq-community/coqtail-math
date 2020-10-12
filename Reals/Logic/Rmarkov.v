(*
(C) Copyright 2010, COQTAIL team

Project Info: http://sourceforge.net/projects/coqtail/

This library is free software; you can redistribute it and/or modify it
under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation; either version 2.1 of the License, or
(at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301,
USA.
*)

Require Import Reals Lia Lra.

Open Scope R_scope.

Section Definitions.

Variable f : nat -> bool.

Definition fp (b : bool) n :=
  if b then pow (/ 2) (S n)
  else 0.

Fixpoint Bn n :=
match n with
| O => 0
| S n => Bn n + fp (f n) n
end.

Lemma Rlt_0_inv_2 : 0 < / 2.
Proof.
assert (H : 1 < 2).
  pattern 1 at 1; rewrite <- (Rplus_0_r 1).
  apply Rplus_lt_compat_l; apply Rlt_0_1.
apply Rmult_lt_reg_l with (r := 2).
  eapply Rlt_trans; [apply Rlt_0_1|apply H].
  rewrite Rmult_0_r.
  replace (2 * / 2) with 1; [apply Rlt_0_1|].
  rewrite Rmult_comm; symmetry; apply Rinv_l.
  intros Hneg.
  apply (Rlt_asym 1 0).
    rewrite <- Hneg; apply H.
    apply Rlt_0_1.
Qed.

Lemma Rle_0_inv_2 : 0 <= / 2.
Proof.
left; apply Rlt_0_inv_2.
Qed.

Lemma Bn_pos : forall n, 0 <= Bn n.
Proof.
intros n; induction n; simpl.
apply Rle_refl.
unfold fp; destruct f.
  apply Rplus_le_le_0_compat.
    assumption.
    apply pow_le; apply Rle_0_inv_2.
    rewrite Rplus_0_r; assumption.
Qed.

Lemma Bn_growing : forall n, (Bn n) <= (Bn (S n)).
Proof.
intros n; induction n; simpl.
unfold fp; destruct f.
  apply Rplus_le_le_0_compat.
    apply Rle_refl.
    apply pow_le; apply Rle_0_inv_2.
    rewrite Rplus_0_l; apply Rle_refl.
unfold fp.
assert (H : 0 <= (/2) ^ (S (S n))).
  apply pow_le; apply Rle_0_inv_2.
do 2 destruct f; repeat rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  pattern ((/ 2) ^ S n) at 1.
  rewrite <- (Rplus_0_r ((/ 2) ^ S n)).
  apply Rplus_le_compat_l.
  apply pow_le; apply Rle_0_inv_2.
  apply Rplus_le_compat_l.
  rewrite Rplus_0_r; apply Rle_refl.
  apply Rplus_le_compat_l.
  rewrite Rplus_0_l; apply pow_le; apply Rle_0_inv_2.
  repeat rewrite Rplus_0_r; apply Rle_refl.
Qed.

Lemma Bn_growing_trans : forall n N, (Bn n) <= (Bn (N + n)).
Proof.
intros n N.
induction N.
  simpl; apply Rle_refl.
  replace (S N + n)%nat with (S (N + n))%nat by lia.
  eapply Rle_trans.
    apply IHN.
    apply Bn_growing.
Qed.

Lemma Bn_dist : forall n, (Bn (S n)) - Bn n <= (/ 2) ^ (S n).
Proof.
intros n; simpl Bn.
replace (Bn n + fp (f n) n - Bn n)
  with (fp (f n) n) by ring.
  unfold fp; destruct f; simpl.
  apply Rle_refl.
  rewrite <- (Rmult_0_r 0).
  apply Rmult_le_compat.
    apply Rle_refl.
    apply Rle_refl.
    apply Rle_0_inv_2.
    apply pow_le; apply Rle_0_inv_2.
Qed.

Lemma Bn_dist_trans : forall n N, Bn (N + n) - Bn n <= (/ 2) ^ n * (1 - (/ 2) ^ N).
Proof.
intros n N.
induction N.
  simpl.
  unfold Rminus; repeat rewrite Rplus_opp_r.
  rewrite Rmult_0_r.
  apply Rle_refl.
  simpl plus.
  replace (Bn (S (N + n)) - Bn n)
    with (Bn (S (N + n)) - Bn (N + n) + (Bn (N + n) - Bn n))
    by ring.
  eapply Rle_trans.
    apply Rplus_le_compat.
      apply Bn_dist.
      apply IHN.
  repeat rewrite <- tech_pow_Rmult.
  rewrite pow_add.
  right.
  apply Rminus_diag_uniq; ring_simplify.
  replace (2 * / 2) with 1; [ring|].
  symmetry; rewrite Rmult_comm; apply Rinv_l.
  intros Hneg.
  apply (Rlt_asym 1 0).
    rewrite <- Hneg; pattern 1 at 1; rewrite <- (Rplus_0_r 1).
    apply Rplus_lt_compat_l; apply Rlt_0_1.
    apply Rlt_0_1.
Qed.

Lemma Bn_maj : forall n, Bn n <= 1.
Proof.
intros n.
pattern (Bn n) at 1.
replace (Bn n) with (Bn n - 0) by ring.
replace 0 with (Bn 0) by reflexivity.
replace n with (n + 0)%nat by ring.
eapply Rle_trans.
  apply Bn_dist_trans.
  simpl; rewrite <- Rmult_1_r.
  apply Rmult_le_compat_l; [apply Rle_0_1|].
  rewrite <- Rminus_0_r.
  apply Rplus_le_compat_l.
  apply Ropp_le_contravar.
  apply pow_le; apply Rle_0_inv_2.
Qed.

Let E r := exists n, Bn n = r.

Lemma Bn_lub : { l | is_lub E l }.
Proof.
destruct (completeness E) as [l Hl].
  exists 1.
  unfold is_upper_bound.
  intros r Hr.
  destruct Hr as [n Hn].
  rewrite <- Hn.
  apply Bn_maj.
  exists 0; exists 0%nat.
  reflexivity.
exists l; assumption.
Qed.

Definition l := proj1_sig Bn_lub.
Definition Hlub := proj2_sig Bn_lub.

Lemma l_maj : forall n, Bn n <= l.
Proof.
intros n.
destruct Hlub as [Hb _].
apply Hb.
exists n; reflexivity.
Qed.

Lemma l_lub : forall M, (forall n, Bn n <= M) -> l <= M.
Proof.
intros M HM.
destruct Hlub as [_ Hl].
apply Hl.
intros r Hr.
destruct Hr as [n Hn].
rewrite <- Hn.
apply HM.
Qed.

Lemma Rabs_le_maj : forall r1 r2 d, Rabs (r1 - r2) <= d -> r1 <= r2 + d.
Proof.
intros r1 r2 d H.
unfold Rabs in H;
repeat destruct Rcase_abs in H; lra.
Qed.

Lemma Bn_l_dist : forall n, l - Bn n <= (/2) ^ n.
Proof.
intros n.
apply (Rplus_le_reg_l (Bn n)); ring_simplify.
apply l_lub; intros m.
destruct (le_ge_dec m n) as [Hd|Hd].
  pattern (Bn m); rewrite <- Rplus_0_r.
  apply Rplus_le_compat.
    replace n with ((n - m) + m)%nat by lia.
    apply Bn_growing_trans.
    apply pow_le; apply Rle_0_inv_2.
  replace (Bn m) with (Bn n + (Bn m - Bn n)) by ring.
  apply Rplus_le_compat_l.
  replace m with ((m - n) + n)%nat by lia.
  eapply Rle_trans.
    apply Bn_dist_trans.
    rewrite <- Rmult_1_r.
    apply Rmult_le_compat_l.
      apply pow_le; apply Rle_0_inv_2.
      rewrite <- Rminus_0_r.
      apply Rplus_le_compat_l.
      apply Ropp_le_contravar.
      apply pow_le; apply Rle_0_inv_2.
Qed.

Lemma l_partial : forall N, (forall n, (n <= N)%nat -> f n = false) -> l <= (/2) ^ N.
Proof.
intros N HN.
assert (forall n, (n <= N)%nat -> Bn n = 0).
  intros n H; induction n.
    reflexivity.
    replace (Bn (S n))
      with (Bn n + fp (f n) n) by reflexivity.
    rewrite IHn; [|lia].
    unfold fp.
    destruct (Bool.bool_dec (f n) true) as [Hd|Hd].
      destruct (Bool.eq_true_false_abs (f n)).
      assumption.
      apply HN; lia.
    destruct (f n) as [|].
      elim Hd; reflexivity.
      ring.
assert (Hd : Bn N = 0); [apply H; constructor|].
  replace l with (l - Bn N) by (rewrite Hd; ring).
  apply Bn_l_dist.
Qed.

Section l_is_zero.

Hypothesis Hl : l = 0.

Lemma l_R0 : forall n, f n = false.
Proof.
assert (H : forall n, Bn n = 0).
  intros n.
  apply Rle_antisym.
    rewrite <- Hl; apply l_maj.
    apply Bn_pos.
intros n; induction n.
  assert (H1 : Bn 1 = 0); [exact (H 1%nat)|].
  unfold Bn, fp in H1.
  destruct (f 0).
    simpl in H1; rewrite Rplus_0_l in H1.
    rewrite Rmult_1_r in H1; symmetry in H1.
    eelim Rlt_not_eq; [apply Rlt_0_inv_2|assumption].
    reflexivity.
  assert (Hn : Bn (S (S n)) = 0); [exact (H (S (S n)))|].
  replace (Bn (S (S n)))
    with (Bn (S n) + fp (f (S n)) (S n)) in Hn by reflexivity. 
  unfold fp in Hn.
  destruct (f n).
    discriminate IHn.
    destruct (f (S n)).
    replace (Bn (S n)) with 0 in Hn by (symmetry; apply H).
    rewrite Rplus_0_l in Hn.
    assert (Hc : forall m, (/ 2) ^ m > 0).
      intros m; induction m; simpl.
        apply Rlt_0_1.
        apply Rmult_lt_0_compat.
        apply Rlt_0_inv_2.
        assumption.
    eelim Rgt_not_eq; [apply Hc|apply Hn].
    reflexivity.
Qed.

End l_is_zero.

Section f_is_false.

Hypothesis Hf : forall n, f n = false.

Lemma f_false : l = 0.
Proof.
apply Rle_antisym.
  apply l_lub.
  intros n.
  induction n; simpl.
    apply Rle_refl.
    assert (H : f n = false).
      apply Hf.
    unfold fp; destruct (f n).
      discriminate H.
    rewrite Rplus_0_r; assumption.
  apply Rle_trans with (Bn 0).
    apply Rle_refl.
    apply l_maj.
Qed.

End f_is_false.

Section l_not_zero.

Hypothesis Hl : l <> 0.

Lemma Hl_lt_0 : l > 0.
Proof.
assert (H : 0 <= l).
  eapply Rle_trans.
    apply (Bn_pos 0).
    apply l_maj.
destruct H.
  assumption.
  elim Hl; symmetry; assumption.
Qed.

Lemma l_not_R0_partial : exists N, ~(forall n, (n <= N)%nat -> f n = false).
Proof.
assert (Hlt : l > 0); [apply Hl_lt_0|].
assert (HN : exists N, forall n, (n >= N)%nat -> (/ 2) ^ n < l).
  destruct (pow_lt_1_zero (/2)) with l as [N HN].
  rewrite Rabs_right; lra.
  lra.
  exists N; intros n Hn.
  pattern ((/ 2) ^ n); rewrite <- Rabs_right.
    apply HN; assumption.
    apply Rle_ge; apply pow_le; lra.
destruct HN as [N HN].
exists N; intros Hneg.
assert (Hc : l <= (/2) ^ N).
  apply l_partial; assumption.
assert (Hk : l > (/2) ^ N).
  apply HN; constructor.
lra.
Qed.

Lemma l_not_R0 : exists n, f n <> false.
Proof.
destruct l_not_R0_partial as [N HN].
induction N.
  exists 0%nat; intro Hneg.
  destruct HN.
   intros n Hn; induction n.
     assumption.
     inversion Hn.
  destruct (Bool.bool_dec (f (S N)) true) as [H|H].
    exists (S N); intros Hneg.
      eapply Bool.eq_true_false_abs; eassumption.
    apply IHN; intros Hneg.
    apply Bool.not_true_is_false in H.
    apply HN; intros n Hn.
    destruct (eq_nat_dec n (S N)) as [Hd|Hd].
      rewrite Hd; assumption.
      apply Hneg; lia.
Qed.

End l_not_zero.

End Definitions.

Section Markov.

Variable P : nat -> Prop.
Hypothesis P_dec : forall n, {P n} + {~ P n}.

Let f n := if (P_dec n) then false else true.

Lemma Heq1 : forall n, f n <> false -> ~ P n.
Proof.
intros n; unfold f; intros H.
destruct (P_dec n) as [Hd|Hd].
  elim H; reflexivity.
  assumption.
Qed.

Lemma Heq2 : forall n, f n = false -> P n.
Proof.
intros n; unfold f; intros H.
  destruct (P_dec n) as [Hd|Hd].
    assumption.
    discriminate H.
Qed.

Theorem R_markov : ~ (forall n, P n) -> exists n, ~ P n.
Proof.
intros Hneg.
destruct (l_not_R0 f) as [N HN].
  intros Hf.
  apply Hneg.
  intros n; apply l_R0 with (n := n) in Hf.
  apply Heq2; assumption.
exists N; apply Heq1; assumption.
Qed.

Theorem R_sequence_dec : {forall n, P n} + {~ forall n, P n}.
Proof.
assert (H : {l f = 0} + {l f <> 0}).
  destruct (total_order_T (l f) 0) as [[Hlt|Heq]|Hgt].
  right; apply Rlt_not_eq; assumption.
  left; assumption.
  right; apply Rgt_not_eq; assumption.
destruct H as [H|H].
  left; intros n.
  destruct (P_dec n) as [Hd|Hd]; [assumption|].
  apply l_R0 with (n := n) in H.
  apply Heq2; assumption.
  right; intros Hneg; elim H.
  apply f_false; intros n.
  assert (Hd : {f n = false} + {f n <> false}).
    destruct (f n); [right|left].
      intros Hc; discriminate Hc.
      reflexivity.
  destruct Hd as [Hd|Hd]; [assumption|].
  apply Heq1 in Hd; elim Hd; apply Hneg.
Qed.

End Markov.
