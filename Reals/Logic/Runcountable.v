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

Require Import Reals.
Require Import Lra.

Open Scope R_scope.
(* begin hide *)

Lemma epsilon_2 : forall x, 0 < x -> x / 2 < x.
Proof.
intros x H; lra.
Qed.

Lemma Rabs_include :
  forall x y u v, x <= u <= y -> x <= v <= y -> Rabs (u - v) <= Rabs (x - y).
Proof.
intros x y u v [Hul Hur] [Hvl Hvr].
unfold Rabs.
repeat destruct Rcase_abs; lra.
Qed.

Lemma Rabs_max : forall x y d, Rabs (x - y) <= d -> x <= y + d.
Proof.
intros x y d H.
unfold Rabs in H; destruct Rcase_abs; lra.
Qed.

Lemma Rabs_min : forall x y d, Rabs (x - y) <= d -> x - d <= y.
intros x y d H.
unfold Rabs in H; destruct Rcase_abs; lra.
Qed.

Section middle_facts.

Definition middle (x y : R) := (x + y) / 2.

Variables x y x' y': R.

Lemma Rlt_middle_r : x < y -> (middle x y) < y.
Proof.
intros H.
unfold middle; unfold Rdiv; rewrite Rmult_plus_distr_r; lra.
Qed.

Lemma Rlt_middle_l : x < y -> x < middle x y.
intros H.
unfold middle; unfold Rdiv; rewrite Rmult_plus_distr_r; lra.
Qed.

Lemma middle_sym : middle x y = middle y x.
Proof.
unfold middle; field.
Qed.

Lemma middle_minus : x - (middle x y) = (x - y) / 2.
Proof.
unfold middle; field.
Qed.

Lemma middle_dist : R_dist x (middle x y) = (R_dist x y) / 2.
Proof.
unfold R_dist.
rewrite middle_minus.
unfold Rdiv.
rewrite Rabs_mult.
rewrite Rmult_eq_compat_l with (r2 := / 2).
reflexivity.
rewrite Rabs_Rinv.
rewrite Rabs_pos_eq.
reflexivity.
lra.
apply Rgt_not_eq; lra.
Qed.

End middle_facts.

Section succ_facts.

Definition succ x y k :=
  let m := middle x y in
  let loc := total_order_T m k in
  match loc with
  | inleft (left _) => (x, m)
  | inleft (right _) => (x, middle x m)
  | inright _ => (m, y)
  end
.

Variable x y k : R.
Hypothesis H : x < y.

Lemma succ_compat : fst (succ x y k) < snd (succ x y k).
Proof.
unfold succ.
destruct (total_order_T (middle x y) k) as [[_|_]|_]; simpl;
repeat (apply Rlt_middle_r || apply Rlt_middle_l); assumption.
Qed.

Lemma succ_not_in : ~ (fst (succ x y k) <= k <= snd (succ x y k)).
Proof.
unfold succ.
destruct (total_order_T (middle x y) k) as [[Ho|Ho]|Ho];
simpl; intro Hn.
destruct Hn as [_ Hn]; lra.
assert (Hm: middle x (middle x y) < middle x y).
apply Rlt_middle_r; apply Rlt_middle_l; assumption.
destruct Hn as [_ [Hn|Hn]]; lra.
destruct Hn as [Hn _]; lra.
Qed.

Lemma succ_included_l : x <= fst (succ x y k).
Proof.
unfold succ.
destruct (total_order_T (middle x y) k) as [[_|_]|_]; simpl; try lra.
left; apply Rlt_middle_l; assumption.
Qed.

Lemma succ_included_r : snd (succ x y k) <= y.
Proof.
unfold succ.
destruct (total_order_T (middle x y) k) as [[_|_]|_]; simpl.
left; apply Rlt_middle_r; assumption.
left; apply Rlt_trans with (r2 := (middle x y));
repeat (apply Rlt_middle_r || apply Rlt_middle_l); assumption.
right; reflexivity.
Qed.

Lemma succ_dist : R_dist (fst (succ x y k)) (snd (succ x y k)) <= (R_dist x y) / 2.
Proof.
unfold succ.
destruct (total_order_T (middle x y) k) as [[_|_]|_];
simpl; [right|left|right].
apply middle_dist.
repeat (rewrite middle_dist).
apply epsilon_2.
unfold Rdiv.
apply Rmult_lt_0_compat; [|lra].
destruct (R_dist_pos x y) as [Hp|Hp]; [lra|].
apply -> R_dist_refl in Hp; lra.
rewrite R_dist_sym; rewrite middle_sym.
rewrite middle_dist.
rewrite R_dist_sym; reflexivity.
Qed.

End succ_facts.

Section CantorDiagonal.

Variable lb ub : R.
Hypothesis not_empty : lb < ub. 
Variable f : nat -> R.

Definition Rn n := f n.

Fixpoint Dn n {struct n} :=
  match n with
  | O => succ lb ub (Rn O)
  | S m =>
    succ (fst (Dn m)) (snd (Dn m)) (Rn n)
  end
.

Lemma non_zero_dist : R_dist lb ub > 0.
Proof.
destruct (R_dist_pos lb ub) as [Ho|Ho].
assumption.
apply -> R_dist_refl in Ho; lra.
Qed.

Lemma diagonal_compat : forall n, fst (Dn n) < snd (Dn n).
Proof.
intros n.
induction n; simpl; apply succ_compat; assumption.
Qed.

Lemma diagonal_included_l : forall n p, (n <= p)%nat -> fst (Dn n) <= fst (Dn p).
Proof.
intros n p H.
induction H; simpl.
right; reflexivity.
apply Rle_trans with (r2 := fst (Dn m)).
assumption.
apply succ_included_l; apply diagonal_compat.
Qed.

Lemma diagonal_included_r : forall n p, (n <= p)%nat -> snd (Dn p) <= snd (Dn n).
Proof.
intros n p H.
induction H; simpl.
right; reflexivity.
apply Rle_trans with (r2 := snd (Dn m)).
apply succ_included_r; apply diagonal_compat.
assumption.
Qed.

Lemma diagonal_dist : forall n, R_dist (fst (Dn n)) (snd (Dn n)) <= (R_dist lb ub) * ((/2) ^ (S n)).
Proof.
intros n.
induction n; simpl.
replace ((R_dist lb ub) * (/2 * 1))
  with ((R_dist lb ub) / 2) by field.
apply succ_dist; exact not_empty.
eapply Rle_trans.
apply succ_dist; apply diagonal_compat.
rewrite tech_pow_Rmult;
replace (R_dist lb ub * (/2 * (/2) ^ (S n)))
  with (R_dist lb ub * (/ 2) ^ (S n) /2) by field;
lra.
Qed.

Lemma diagonal_not_in : forall n p, (n <= p)%nat -> ~ (fst (Dn p) <= Rn n <= snd (Dn p)).
Proof.
intros n p H.
induction H; simpl.
destruct n; simpl; apply succ_not_in;
[assumption|apply diagonal_compat].
intros Hn; destruct Hn as [Hl Hr].
apply IHle; split.
eapply Rle_trans; [|apply Hl].
apply succ_included_l; apply diagonal_compat.
eapply Rle_trans; [apply Hr|].
apply succ_included_r; apply diagonal_compat.
Qed.

Definition Ln n := middle (fst (Dn n)) (snd (Dn n)).

Lemma sequence_bound : forall n p, (n <= p)%nat -> (fst (Dn n)) <= Ln p <= (snd (Dn n)).
Proof.
intros n p H; split.
left; eapply Rle_lt_trans with (r2 := fst (Dn p)).
apply diagonal_included_l; apply H.
apply Rlt_middle_l; apply diagonal_compat.
left; apply Rlt_le_trans with (r2 := snd (Dn p)).
apply Rlt_middle_r; apply diagonal_compat.
apply diagonal_included_r; apply H.
Qed.

Lemma sequence_cauchy : forall n p q, (p >= n)%nat -> (q >= n)%nat -> R_dist (Ln p) (Ln q) < (R_dist lb ub) * (/2) ^ n.
Proof.
intros n p q Hnp Hpq.
assert (R_dist (Ln p) (Ln q) <= R_dist (fst (Dn n)) (snd (Dn n))).
unfold R_dist; apply Rabs_include; apply sequence_bound; assumption.
eapply Rle_lt_trans; [apply H|].
eapply Rle_lt_trans; [apply diagonal_dist|].
rewrite <- tech_pow_Rmult.
replace (R_dist lb ub * (/2 * (/2) ^ n))
  with ((R_dist lb ub * (/2) ^ n)/2) by field.
apply epsilon_2; apply Rmult_lt_0_compat.
apply non_zero_dist.
apply pow_lt; lra.
Qed.

Lemma sequence_cauchy_crit : Cauchy_crit Ln.
Proof.
intros eps H.
assert (Hinf: (Rabs (/ 2)) < 1).
rewrite Rabs_right; lra.
destruct (pow_lt_1_zero (/2) Hinf (eps / (R_dist lb ub))) as [n M].
apply Rmult_lt_0_compat.
assumption.
apply Rinv_0_lt_compat; apply non_zero_dist.
exists n.
intros p q Hp Hq.
eapply Rlt_trans.
apply sequence_cauchy; [apply Hp|apply Hq].
let t := type of (M n (le_refl n)) in assert (Hr: t).
apply M; apply le_refl.
rewrite Rabs_right in Hr.
unfold Rdiv in Hr.
apply Rmult_lt_reg_l with (r := / R_dist lb ub).
apply Rinv_0_lt_compat; apply non_zero_dist.
rewrite <- Rmult_assoc;
rewrite <- Rinv_l_sym.
rewrite Rmult_1_l;
rewrite Rmult_comm;
exact Hr.
apply Rgt_not_eq; apply non_zero_dist.
apply Rle_ge; apply pow_le; lra.
Qed.

Lemma sequence_cv : { l : R | Un_cv Ln l }.
Proof.
apply R_complete.
apply sequence_cauchy_crit.
Qed.

Definition l := proj1_sig sequence_cv.
Definition l_is_limit := proj2_sig sequence_cv.

Lemma l_in_Dn : forall n, fst (Dn n) <= l <= snd (Dn n).
Proof.
intros n; split;
apply le_epsilon;
intros eps Heps;
destruct (l_is_limit (eps / 2)) as [N H].
lra.
destruct (sequence_bound n (Max.max N n)) as [Hb _].
apply Max.le_max_r.
eapply Rle_trans; [apply Hb|].
apply Rabs_max.
apply Rle_trans with (r2 := eps / 2); [|lra].
left; apply H; apply Max.le_max_l.
lra.
destruct (sequence_bound n (Max.max N n)) as [_ Hb].
apply Max.le_max_r.
assert (l - eps <= snd (Dn n)); [|lra].
eapply Rle_trans; [|apply Hb].
apply Rabs_min.
apply Rle_trans with (r2 := eps / 2); [|lra].
left; rewrite Rabs_minus_sym; apply H.
apply Max.le_max_l.
Qed.

Lemma l_not_in_Rn : forall n, ~(Rn n = l).
Proof.
intros n Hn.
apply (diagonal_not_in n n).
apply le_refl.
rewrite Hn; apply l_in_Dn.
Qed.

Lemma l_in_segment : lb <= l <= ub.
Proof.
destruct (l_in_Dn 0) as [Hl Hr]; split.
eapply Rle_trans; [|apply Hl].
simpl; unfold succ.
destruct (total_order_T (middle lb ub) (Rn 0)) as [[_|_]|_];
simpl; try apply Rle_refl.
left; apply Rlt_middle_l; apply not_empty.
eapply Rle_trans; [apply Hr|].
simpl; unfold succ.
destruct (total_order_T (middle lb ub) (Rn 0)) as [[_|_]|_];
simpl; try apply Rle_refl.
left; apply Rlt_middle_r; apply not_empty.
left; eapply Rlt_trans; apply Rlt_middle_r.
apply Rlt_middle_l; apply not_empty.
apply not_empty.
Qed.

Lemma segment_uncountable : { l | forall n, l <> Rn n }.
Proof.
exists l; intros n H.
symmetry in H; apply (l_not_in_Rn n); assumption.
Qed.

End CantorDiagonal.
(* end hide *)

(** * R is uncountable. *)

Theorem R_uncountable_strong :
  forall (f : nat -> R) (x y : R), x < y -> {l : R | forall n, l <> f n & x <= l <= y}.
Proof.
intros f x y H.
pose (lf := l x y H f).
exists lf.
  intros n Hc; destruct (l_not_in_Rn x y H f n); unfold Rn; auto.
  apply l_in_segment.
Qed.

Theorem R_uncountable : forall (f : nat -> R), {l : R | forall n, l <> f n}.
Proof.
apply (segment_uncountable 0 1); lra.
Qed.
