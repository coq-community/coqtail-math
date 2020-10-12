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

Require Import Lia.
Require Import Rsequence_def.
Require Import Morphisms Setoid.
Require Import Lra.

Open Scope R_scope.
Open Scope Rseq_scope.
(** printing ~	~ *)
(** ** Extensionnal equality. *)

(** * Extensional equality is an equivalence relation. *)

(**********)
Lemma Rseq_eq_refl : forall Un, Un == Un.
Proof.
intros Un n; reflexivity.
Qed.

(**********)
Lemma Rseq_eq_sym : forall Un Vn, Un == Vn -> Vn == Un.
Proof.
intros Un Vn Heq n.
symmetry; apply Heq.
Qed.

(**********)
Lemma Rseq_eq_trans : forall Un Vn Wn, Un == Vn -> Vn == Wn -> Un == Wn.
Proof.
intros Un Vn Wn Heq1 Heq2 n.
transitivity (Vn n); [apply Heq1|apply Heq2].
Qed.

(**********)
Instance Rseq_eq_Equivalence : Equivalence Rseq_eq.
Proof.
split.
  exact Rseq_eq_refl.
  exact Rseq_eq_sym.
  exact Rseq_eq_trans.
Qed.

(** * Rseq_opp is involutive. *)

Lemma Rseq_opp_invol : forall Un, - - Un == Un.
Proof.
intros Un n ; unfold Rseq_opp ; rewrite Ropp_involutive ;
 reflexivity.
Qed.

(** * Compatibility of extensional equality with convergence. *)

(**********)
Lemma Rseq_cv_eq_compat :
  forall Un Vn l, Un == Vn ->
  (Rseq_cv Un l <-> Rseq_cv Vn l).
Proof.
intros Un Vn l Heq ; split ; intros Hcv eps Heps ;
destruct (Hcv eps Heps) as [N HN] ;
exists N; intros n Hn ;
[rewrite <- Heq | rewrite Heq] ;
apply HN; assumption.
Qed.

(**********)
Lemma Rseq_cv_pos_infty_eq_compat :
  forall Un Vn, Un == Vn -> Rseq_cv_pos_infty Un -> Rseq_cv_pos_infty Vn.
Proof.
intros Un Vn Heq Hdiv.
intros m.
destruct (Hdiv m) as [N HN].
exists N; intros n Hn.
rewrite <- (Heq n).
apply HN; assumption.
Qed.

(**********)
Lemma Rseq_cv_neg_infty_eq_compat :
  forall Un Vn, Un == Vn -> Rseq_cv_neg_infty Un -> Rseq_cv_neg_infty Vn.
Proof.
intros Un Vn Heq Hdiv.
intros m.
destruct (Hdiv m) as [N HN].
exists N; intros n Hn.
rewrite <- (Heq n).
apply HN; assumption.
Qed.

(** * Compatibility of extensional equality with Laudau relations. *)

(**********)
Lemma Rseq_big_O_eq_compat :
  forall Un Vn Wn Xn, Un == Wn -> Vn == Xn ->
    Un = O(Vn) -> Wn = O(Xn).
Proof.
intros Un Vn Wn Xn Huw Hvx Huv.
destruct Huv as [M [HM [N HN]]].
exists M; split.
  assumption.
  exists N; intros n Hn.
  rewrite <- Huw; rewrite <- Hvx.
  apply HN; assumption.
Qed.

(**********)
Lemma Rseq_little_O_eq_compat :
  forall Un Vn Wn Xn, Un == Wn -> Vn == Xn ->
    Un = o(Vn) -> Wn = o(Xn).
Proof.
intros Un Vn Wn Xn Huw Hvx Huv.
intros eps Heps.
destruct (Huv eps Heps) as [N HN].
exists N; intros n Hn.
rewrite <- Huw; rewrite <- Hvx.
apply HN; assumption.
Qed.

(**********)
Lemma Rseq_equiv_eq_compat : 
  forall Un Vn Wn Xn, Un == Wn -> Vn == Xn ->
    Un ~ Vn -> Wn ~ Xn.
Proof.
intros Un Vn Wn Xn Huw Hvx Huv.
intros eps Heps.
destruct(Huv eps Heps) as [N HN].
exists N; intros n Hn.
unfold Rseq_minus.
rewrite <- Huw; rewrite <- Hvx.
apply HN; apply Hn.
Qed.

(** ** Boundedness and subsequences *)

Lemma even_odd_boundedness : forall (An : nat -> R) (M1 M2 : R),
     Rseq_bound (fun n => An (2 * n)%nat) M1 ->
     Rseq_bound (fun n => An (S (2 * n))) M2 ->
     Rseq_bound An (Rmax M1 M2).
Proof.
intros An M1 M2 HM1 HM2 n ; destruct (n_modulo_2 n) as [n_even | n_odd].
 destruct n_even as [p Hp] ; rewrite Hp ; apply Rle_trans with M1 ; [apply HM1 | apply RmaxLess1].
 destruct n_odd as [p Hp] ; rewrite Hp ; apply Rle_trans with M2 ; [apply HM2 | apply RmaxLess2].
Qed.

(** ** Partial sequences. *)

Section Rseq_partial.

Variable Un : nat -> R.

(**********)
Lemma Rseq_partial_bound_max : forall N, exists M, forall n, (n <= N)%nat -> Un n <= M.
Proof.
induction N.
exists (Un 0).
intros n Hn; inversion Hn as [H|H]; apply Rle_refl.
destruct IHN as [M IHN].
exists (Rmax M (Un (S N))).
intros n Hn.
destruct (le_lt_eq_dec n (S N)) as [He|He]; try assumption.
eapply Rle_trans; [apply IHN|apply RmaxLess1].
apply lt_n_Sm_le; assumption.
rewrite He; apply RmaxLess2.
Qed.

(**********)
Lemma Rseq_partial_bound_min : forall N, exists m, forall n, (n <= N)%nat -> m <= Un n.
Proof.
induction N.
exists (Un 0).
intros n Hn; inversion Hn as [H|H]; apply Rle_refl.
destruct IHN as [m IHN].
exists (Rmin m (Un (S N))).
intros n Hn.
destruct (le_lt_eq_dec n (S N)) as [He|He]; try assumption.
eapply Rle_trans; [apply Rmin_l|apply IHN].
apply lt_n_Sm_le; assumption.
rewrite He; apply Rmin_r.
Qed.

(**********)
Lemma Rseq_partial_bound : forall N, exists M, forall n, (n <= N)%nat -> Rabs (Un n) <= M.
Proof.
intros N.
destruct (Rseq_partial_bound_max N) as [M HM].
destruct (Rseq_partial_bound_min N) as [m Hm].
exists (Rmax (Rabs m) (Rabs M)).
intros n Hn.
apply RmaxAbs; [apply Hm|apply HM]; assumption.
Qed.

End Rseq_partial.

(** ** Asymptotic properties. *)

(**********)
Definition Rseq_asymptotic P :=
  forall (Q : Rseq -> Prop) Un,
    (forall Vn, Q Vn -> P Vn) -> Rseq_eventually Q Un -> P Un.

(**********)
Definition Rseq_asymptotic2 P :=
  forall (Q : Rseq -> Rseq -> Prop) Un Vn,
    (forall Wn Xn, Q Wn Xn -> P Wn Xn) -> Rseq_eventually2 Q Un Vn -> P Un Vn.

(** * Convergence is asymptotic. *)

(**********)
Lemma Rseq_cv_asymptotic : forall l, Rseq_asymptotic (fun Un => Rseq_cv Un l).
Proof.
intros l Q Un HQ He eps Heps.
destruct He as [Ne HNe].
edestruct HQ as [N HN]; [eexact HNe|eexact Heps|].
exists (Ne + N)%nat; intros n Hn.
assert (Hn0 : exists n0, (n = Ne + n0)%nat).
induction Hn.
exists N; reflexivity.
destruct IHHn as [n0 H]; exists (S n0).
rewrite <- plus_Snm_nSm; simpl; rewrite H; reflexivity.
destruct Hn0 as [n0 Hn0].
rewrite Hn0; apply HN; lia.
Qed.

(**********)
Lemma Rseq_cv_asymptotic_eq_compat : forall Un Vn l, 
    (exists N, forall n : nat, (N <= n)%nat -> Un n = Vn n) -> Rseq_cv Un l -> Rseq_cv Vn l.
Proof.
intros Un Vn l [N HN] Hu eps Heps.
destruct (Hu eps Heps) as [N' HN'].
exists (N+N')%nat.
intros n Hn; unfold R_dist.
replace (Vn n -l)%R with ((Vn n - Un n) + (Un n -l))%R by ring.
apply Rle_lt_trans with (Rabs (Vn n - Un n)+ Rabs(Un n -l))%R.
apply Rabs_triang.
rewrite HN at 1.
unfold Rminus at 1.
rewrite Rplus_opp_r, Rabs_R0, Rplus_0_l.
apply HN'.
lia.
lia.
Qed.

(**********)
Lemma Rseq_cv_pos_infty_asymptotic : Rseq_asymptotic Rseq_cv_pos_infty.
Proof.
intros Q Un HQ He M.
destruct He as [Ne HNe].
edestruct HQ as [N HN]; [eexact HNe|].
exists (Ne + N)%nat; intros n Hn.
assert (Hn0 : exists n0, (n = Ne + n0)%nat).
induction Hn.
exists N; reflexivity.
destruct IHHn as [n0 H]; exists (S n0).
rewrite <- plus_Snm_nSm; simpl; rewrite H; reflexivity.
destruct Hn0 as [n0 Hn0].
rewrite Hn0; apply HN; lia.
Qed.

(**********)
Lemma Rseq_cv_neg_infty_asymptotic : Rseq_asymptotic Rseq_cv_neg_infty.
Proof.
intros Q Un HQ He M.
destruct He as [Ne HNe].
edestruct HQ as [N HN]; [eexact HNe|].
exists (Ne + N)%nat; intros n Hn.
assert (Hn0 : exists n0, (n = Ne + n0)%nat).
induction Hn.
exists N; reflexivity.
destruct IHHn as [n0 H]; exists (S n0).
rewrite <- plus_Snm_nSm; simpl; rewrite H; reflexivity.
destruct Hn0 as [n0 Hn0].
rewrite Hn0; apply HN; lia.
Qed.

(** * Landau relations are asymptotic. *)

(**********)
Lemma Rseq_big_O_asymptotic : Rseq_asymptotic2 Rseq_big_O.
Proof.
intros Q Un Vn HQ He.
destruct He as [Ne HNe].
edestruct HQ as [M [HM [N HN]]]; [eexact HNe|].
exists M; split.
assumption.
exists (Ne + N)%nat; intros n Hn.
assert (Hn0 : exists n0, (n = Ne + n0)%nat).
induction Hn.
exists N; reflexivity.
destruct IHHn as [n0 H]; exists (S n0).
rewrite <- plus_Snm_nSm; simpl; rewrite H; reflexivity.
destruct Hn0 as [n0 Hn0].
rewrite Hn0; apply HN; lia.
Qed.

(**********)
Lemma Rseq_little_O_asymptotic : Rseq_asymptotic2 Rseq_little_O.
Proof.
intros Q Un Vn HQ He.
destruct He as [Ne HNe].
intros eps Heps.
edestruct HQ as [N HN]; [eexact HNe|apply Heps|].
exists (Ne + N)%nat; intros n Hn.
assert (Hn0 : exists n0, (n = Ne + n0)%nat).
induction Hn.
exists N; reflexivity.
destruct IHHn as [n0 H]; exists (S n0).
rewrite <- plus_Snm_nSm; simpl; rewrite H; reflexivity.
destruct Hn0 as [n0 Hn0].
rewrite Hn0; apply HN; lia.
Qed.

(**********)
Lemma Rseq_equiv_asymptotic : Rseq_asymptotic2 Rseq_equiv.
Proof.
intros Q Un Vn HQ He.
destruct He as [Ne HNe].
intros eps Heps.
edestruct HQ as [N HN]; [eexact HNe|apply Heps|].
exists (Ne + N)%nat; intros n Hn.
assert (Hn0 : exists n0, (n = Ne + n0)%nat).
induction Hn.
exists N; reflexivity.
destruct IHHn as [n0 H]; exists (S n0).
rewrite <- plus_Snm_nSm; simpl; rewrite H; reflexivity.
destruct Hn0 as [n0 Hn0].
unfold Rseq_minus in HN.
rewrite Hn0; apply HN; lia.
Qed.
