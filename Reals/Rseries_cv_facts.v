Require Import Rsequence.
Require Import Rseries_def Rseries_base_facts Rseries_pos_facts.

(** * Convergence facts *)
(** For basic convergence lemmas (e.g. compatibility with common operations), see Rseries_base_facts *)


(** Even / odd partition *)

Lemma Rser_even_odd_split : forall An le lo, 
  Rser_cv (fun n => An (2*n)%nat) le ->
  Rser_cv (fun n => An (S(2*n))%nat) lo ->
  Rser_cv An (le + lo).
Proof.
intros An le lo Hle Hlo ; apply Rseq_cv_even_odd_compat.
 apply Rseq_cv_shift_compat ; unfold Rseq_shift ; apply Rseq_cv_eq_compat
  with (Rseq_plus (Rseq_shift (Rseq_sum (fun i => An (2 * i)%nat)))
       (Rseq_sum (fun i => An (S (2 * i))))).
  intro n ; rewrite <- Rseq_sum_even_odd_split' ; unfold Rseq_shift, Rseq_plus ;
  reflexivity.
  apply Rseq_cv_plus_compat ; [apply Rseq_cv_shift_compat_reciprocal |] ; assumption.
 apply Rseq_cv_eq_compat with (Rseq_plus (Rseq_sum (fun i => An (2 * i)%nat))
       (Rseq_sum (fun i => An (S (2 * i))))).
  intro n ; symmetry ; apply Rseq_sum_even_odd_split.
  apply Rseq_cv_plus_compat ; assumption.
Qed.

(** A gt-positive series bounded by a converging one is converging. *)

Lemma Rser_pos_maj_cv : forall (An Bn : nat -> R), 
  (forall n : nat, 0 <= An n) -> (forall n : nat, 0 <= Bn n) ->
  Rseq_le An Bn ->  {l | Rser_cv Bn l } -> {l | Rser_cv An l}.
Proof.
intros An Bn An_pos Bn_pos AnBn [lb Hlb] ; apply Rser_pos_bound_cv with lb.
 assumption.
 intro n ; transitivity (Rseq_sum Bn n).
  apply Rseq_sum_le_compat ; assumption.
  apply growing_ineq ; [apply Rser_pos_growing |] ; assumption.
Qed.

(** * Mertens' theorem *)

Lemma Rser_cv_prod_compat : forall An Bn la lb lna,
 Rser_cv An la -> 
 Rser_cv Bn lb -> 
 Rser_abs_cv An lna ->
 Rser_cv ((fun k:nat => sum_f_R0 (fun p:nat => An p * Bn (k - p)%nat) k)%R)
   (la * lb)%R.
Proof.
Admitted.

(* intros An Bn la lb lna HA HB HNA e epos.

pose (e * / 4 * / (lna + 1))%R as eN.
assert (lnapos : lna + 1 > 0).
 apply Rle_lt_0_plus_1.
 apply Rle_trans with (Rabs (An O)).
  apply Rabs_pos.
  apply (sum_incr (|An|) O lna HNA).
  intro; apply Rabs_pos.
assert (eNpos : eN > 0) by (apply Rlt_mult_inv_pos; auto; fourier).
destruct (HB eN eNpos) as [N HN].

destruct (maj_by_pos (sum_f_R0 Bn)) as [supBn[]]; [exists lb; apply HB|].
pose (supBn + Rabs lb)%R as supBnB.
assert (HsupBnB : forall n, (Rabs ((sum_f_R0 Bn n) - lb) <= supBnB)%R).
 intro n.
 replace ((sum_f_R0 Bn n) - lb)%R with (sum_f_R0 Bn n + - lb)%R by auto.
 eapply Rle_trans.
  apply Rabs_triang.
  apply Rplus_le_compat.
   apply H0.
   rewrite Rabs_Ropp; apply Rle_refl.
pose (e * / 8 * / (INR (S N)) * / (supBnB + 1))%R as eM.
assert (eMpos : eM > 0).
 repeat apply Rlt_mult_inv_pos; try fourier.
  replace 0 with (INR O) by trivial; apply lt_INR; omega.
  apply Rle_lt_0_plus_1; apply Rplus_le_le_0_compat; try fourier; apply Rabs_pos.
destruct (Rser_cv_zero An la HA eM eMpos) as [M' HM'].
pose (plus M' N) as M.

pose (e * / 2 * / (Rabs lb + 1))%R as eL.
assert (eLpos : eL > 0).
 repeat apply Rlt_mult_inv_pos; try fourier.
 apply Rle_lt_0_plus_1; try fourier; apply Rabs_pos.
destruct (HA eL eLpos) as [L HL].

clear H H0 eLpos epos.

pose (max (max (S N) M) L) as K.

pose (sum_f_R0 An) as SAn.
pose (sum_f_R0 Bn) as SBn.
pose (sum_f_R0 (fun i => sum_f_R0 (fun k => (An k * Bn (minus i k))%R) i)) as Cn.
fold Cn.

exists K; intros n Hn.
replace (Cn n) with (sum (fun i => SBn i * (An (n - i)%nat))%R n) by
  (unfold SBn, Cn; apply cauchy_product_subproof_rearrangement).

replace (sum (fun i => (SBn i * An (n - i)%nat)%R) n)
  with (sum (fun i => ((SBn i - lb) * An (n - i)%nat) + An (n - i)%nat * lb)%R n)
  by (apply Rsum_eq_compat; intro; ring).

rewrite sum_plus.
rewrite <- scal_sum.
rewrite Rseq_reverse.
fold SAn.

unfold R_dist.
assert (RE : forall x y z t, x + t * y - z * t = x + t * (y - z))
  by (intros; ring); rewrite RE; clear RE.

eapply Rle_lt_trans; [apply Rabs_triang|].
replace e with (e/4 + e/4 + e/2) by field.
apply Rplus_lt_compat.
 eapply Rle_lt_trans; [apply Rsum_abs |].
 pose (fun l => (fun l0 : nat => (SBn l0 - lb) * An (n - l0)%nat) l) as dab.
 fold dab.
 
 pose (minus n (S N)) as p.
 assert (HnN : (n >= S N)%nat).
  apply le_trans with K; auto.
  eapply le_trans; apply le_max_l.
 replace n with (S (N + p)) by (unfold p; omega).
 rewrite Rseq_decomp.
 
 apply Rplus_lt_compat.
  unfold dab.
  replace (e / 4) with (eM * 2 * INR (S N) * (supBnB + 1))
    by (unfold eM; field; split; replace 0 with (INR O) by auto; try (apply not_INR; omega);
    apply Rgt_not_eq; apply Rle_lt_0_plus_1; apply Rle_trans with (Rabs (SBn O - lb)); apply Rabs_pos || apply HsupBnB).
  apply Rle_lt_trans with (sum (fun l => Rabs (An (n - l)%nat) * supBnB) N).
   apply sum_Rle; intros.
   rewrite Rmult_comm.
   rewrite Rabs_mult.
   apply Rmult_le_compat_l.
    apply Rabs_pos.
    apply HsupBnB.
   
   rewrite <- scal_sum.
   rewrite Rmult_comm.
   apply Rmult_le_0_lt_compat; [
    apply cond_pos_sum; intro; apply Rabs_pos|
    apply Rle_trans with (Rabs (SBn O - lb)); apply Rabs_pos || apply HsupBnB | |
    auto with * ].
   apply Rle_lt_trans with (eM * INR (S N)); [|
    replace (eM * INR (S N)) with (eM * 1 * INR (S N)) by ring;
    apply Rmult_lt_compat_r; replace 0 with (INR O) by auto; try (apply lt_INR; omega);
    apply Rmult_lt_compat_l; auto; fourier].
   
   apply Rle_trans with (sum (fun i => eM) N); [|rewrite sum_cte; auto with *].
   apply sum_Rle; intros.
   unfold R_dist in HM'.
   rewrite <- Rminus_0_r with (An (n - n0)%nat).
   apply Rlt_le.
   apply HM'.
   replace n with (S p + N)%nat by (unfold p; omega).
   replace (S p + N - n0)%nat with (S p + (N - n0))%nat by omega.
   apply le_trans with (S p); [|omega].
   unfold p.
   apply le_trans with (K - N)%nat; [|omega].
   replace M' with (M - N)%nat by (unfold M; omega).
   apply minus_le_compat_r.
   unfold K; apply le_trans with (max (S N) M); auto with *.
  
  replace (e / 4) with (eN * (lna + 1)) by (unfold eN; field; auto with .
  unfold dab.
  apply Rle_lt_trans with (sum (fun i => Rabs (An (n - (i + S N))%nat) * eN) p).
   apply sum_Rle; intros.
   rewrite Rmult_comm.
   rewrite Rabs_mult.
   apply Rmult_le_compat_l; [apply Rabs_pos|].
   apply Rlt_le; apply HN; omega.
   
   rewrite <- scal_sum.
   apply (Rmult_lt_compat_l _ _ _ eNpos).
   eapply Rle_lt_trans; [|apply Rlt_plus_1].
   replace (sum (fun i => Rabs (An (n - (i + S N))%nat)) p)
     with (sum (fun i => Rseq_abs An (p - i)%nat) p)
     by (apply Rsum_eq_compat; intro; replace (n - (n0 + S N))%nat with (n - S N - n0)%nat by omega; trivial).
   rewrite Rseq_reverse.
   apply growing_ineq.
    intro i; simpl sum; apply Rplus_le_simpl_l; apply Rabs_pos.
    apply HNA.
 
 rewrite Rabs_mult.
 replace e with (eL * 2 * (Rabs lb + 1)) by (unfold eL; field;
   apply Rgt_not_eq; apply Rle_lt_0_plus_1; apply Rabs_pos).
 cut (Rabs (SAn n - la) < eL).
  intro.
  replace (eL * 2 * (Rabs lb + 1) / 2) with (eL * (Rabs lb + 1)) by field.
  rewrite Rmult_comm.
  apply Rmult_le_0_lt_compat; auto || apply Rabs_pos || apply Rlt_plus_1.
 apply HL.
 apply le_trans with K; auto.
 unfold K; auto with *.
Qed.
*)
