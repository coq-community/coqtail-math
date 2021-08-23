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

(** Properties of real sequences. *)

Require Export Lia.
Require Export Reals.
Require Export Rsequence_def.
Require Export Rsequence_base_facts.
Require Export Rsequence_cv_facts.
Require Export Rsequence_rel_facts.
Require Export Rsequence_usual_facts.
Require Import Lra.
Open Scope R_scope.
Open Scope Rseq_scope.

(** printing ~	~ *)
Lemma Rseq_growing_constructive_limit : forall (Un : nat -> R), Rseq_growing Un -> (exists l, Rseq_cv Un l) -> {l | Rseq_cv Un l}.
Proof.
intros Un Hg Hl.
assert (has_ub Un).
  destruct Hl as [l Hl]; exists l.
  intros x Hx; destruct Hx as [n Hn]; rewrite Hn.
  apply growing_ineq; assumption.
apply growing_cv; assumption.
Qed.

(** A sequence cannot both converge and diverge to infinity *)
Lemma Rseq_cv_not_infty : forall (Un : nat -> R), ~ ((exists l, Rseq_cv Un l) /\ Rseq_cv_pos_infty Un).
Proof.
intros Un Hf.
destruct Hf as [[l Hl] Hinf].
unfold Rseq_cv in Hl.
unfold Rseq_cv_pos_infty in Hinf.
destruct (Hinf (l+1)%R) as [ N HN].
destruct (Hl 1) as [N0 HN0].
auto with *.
apply Rlt_irrefl with (Un (Max.max N N0)).
apply Rlt_trans with (l+1)%R.
replace (Un (Max.max N N0)) with (l+(Un (Max.max N N0)-l))%R by ring.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (Rabs (Un (Max.max N N0) - l)).
apply RRle_abs.
apply HN0.
apply Max.le_max_r.
apply HN.
apply Max.le_max_l.
Qed.

(** Rseq monotonic definitions implies usual meaning *)
Lemma Rseq_growing_trans : forall an, Rseq_growing an -> forall y x:nat, 
  (x <= y)%nat -> (an x <= an y)%R.
Proof.
induction y.
 intros x Hxy; rewrite (le_n_O_eq x Hxy); intuition.
 
 intros x Hxy; destruct (Compare.le_decide _ _ Hxy) as [Hyx|Hyx].
  apply Rle_trans with (an y).
   apply IHy.
   apply gt_S_le.
   apply Hyx.
   
   apply H.
  
  subst; apply Rle_refl.
Qed.

Lemma Rseq_strictly_growing_trans : forall an, Rseq_strictly_growing an -> forall y x:nat, 
  (x < y)%nat -> (an x < an y)%R.
Proof.
induction y.
 intros x Hx0. inversion Hx0.
 
 intros x Hxy.
 destruct (Compare.le_decide _ _ Hxy) as [Hyx|Hyx].
  apply Rlt_trans with (an y).
   apply IHy.
   apply gt_S_le.
   apply Hyx.
   
   apply H.
  
  rewrite <- Hyx. apply H.
Qed.

(** Sequences convergence shifting compatibility *)

Lemma Rseq_cv_shift_compat : forall Un l, Rseq_cv (Rseq_shift Un) l -> Rseq_cv Un l.
Proof.
intros Un l H eps epspos.
destruct (H eps epspos) as [N Hu].
exists (S N); intros n nSN.
destruct n; [inversion nSN | ].
replace (Un (S n)) with (Rseq_shift Un n) by reflexivity.
intuition.
Qed.

Lemma Rseq_cv_pos_infty_shift_compat : forall Un, Rseq_cv_pos_infty (Rseq_shift Un) -> Rseq_cv_pos_infty Un.
Proof.
intros Un H M.
destruct (H M) as [N Hu].
exists (S N); intros n nSN.
destruct n; [inversion nSN | ].
replace (Un (S n)) with (Rseq_shift Un n) by reflexivity.
intuition.
Qed.

Lemma Rseq_cv_neg_infty_shift_compat : forall Un, Rseq_cv_neg_infty (Rseq_shift Un) -> Rseq_cv_neg_infty Un.
Proof.
intros Un H M.
destruct (H M) as [N Hu].
exists (S N); intros n nSN.
destruct n; [inversion nSN | ].
replace (Un (S n)) with (Rseq_shift Un n) by reflexivity.
intuition.
Qed.

Lemma Rseq_cv_shift_compat_reciprocal : forall Un l, Rseq_cv Un l -> Rseq_cv (Rseq_shift Un) l.
Proof.
intros Un l H eps epspos.
destruct (H eps epspos) as [N Hu].
exists N; intros n nSN.
unfold Rseq_shift.
apply Hu.
intuition.
Qed.

Lemma Rseq_cv_pos_infty_shift_compat_reciprocal : forall Un, Rseq_cv_pos_infty Un -> Rseq_cv_pos_infty (Rseq_shift Un).
Proof.
intros Un H M.
destruct (H M) as [N Hu].
exists N; intros n nSN.
unfold Rseq_shift.
apply Hu.
intuition.
Qed.

Lemma Rseq_cv_neg_infty_shift_compat_reciprocal : forall Un, Rseq_cv_neg_infty Un -> Rseq_cv_neg_infty (Rseq_shift Un).
Proof.
intros Un H M.
destruct (H M) as [N Hu].
exists N; intros n nSN.
unfold Rseq_shift.
apply Hu.
intuition.
Qed.

Lemma Rseq_cv_shifts_compat : forall N Un l, Rseq_cv (Rseq_shifts Un N) l -> Rseq_cv Un l.
Proof.
intros N Un l H eps eps_pos.
destruct (H eps eps_pos) as [M HM].
exists (N + M)%nat; intros n nSN.
assert (Hrew: (n = N + (n - N))%nat) by lia.
rewrite Hrew ; apply HM ; lia.
Qed.

Lemma Rseq_cv_shifts_compat_reciprocal : forall N Un l,
  Rseq_cv Un l -> Rseq_cv (Rseq_shifts Un N) l.
Proof.
intros N Un l H eps eps_pos.
destruct (H eps eps_pos) as [M HM].
exists (M - N)%nat; intros n nSN.
apply HM ; intuition lia.
Qed.

Lemma Rseq_cv_pos_infty_shifts_compat : forall Un N,
  Rseq_cv_pos_infty (Rseq_shifts Un N) -> Rseq_cv_pos_infty Un.
Proof.
intros Un N H M.
destruct (H M) as [P HP].
exists (N + P)%nat; intros n nSN.
assert (Hrew: (n = N + (n - N))%nat) by lia.
rewrite Hrew ; apply HP ; lia.
Qed.

(** * Results which need classical *)

Section Classical_facts.

Variables Un : nat -> R.
Hypothesis NNPP : forall p : Prop, ~ ~ p -> p.

(** An unbounded growing sequence goes to + infinity*)
Lemma Rseq_unbounded_growing  : 
    Rseq_growing Un -> (~ exists M, Rseq_bound_max Un M) -> Rseq_cv_pos_infty Un.
Proof.
intros Hgr Hnmaj m.
apply NNPP; intro Hf; apply Hnmaj.
exists m; intro n.
apply NNPP.
intro Hff.
apply Hf.
apply Rnot_le_lt in Hff.
exists n.
intros p Hp.
apply Rlt_le_trans with (Un n); [ apply Hff | apply Rge_le].
apply growing_prop.
apply Hgr.
apply Hp.
Qed.

(** An unbounded decreasing sequence goes to - infinity*)
Lemma Rseq_unbounded_decreasing : 
    Rseq_decreasing Un -> (~ exists M, Rseq_bound_min Un M) -> Rseq_cv_neg_infty Un.
Proof.
intros Hgr Hnmin m.
apply NNPP; intro Hf; apply Hnmin.
exists m; intro n.
apply NNPP.
intro Hff.
apply Hf.
apply Rnot_le_lt in Hff.
exists n.
intros p Hp.
apply Rle_lt_trans with (Un n).
apply decreasing_prop.
apply Hgr.
apply Hp.
apply Hff.
Qed.

End Classical_facts.

Close Scope Rseq_scope.
