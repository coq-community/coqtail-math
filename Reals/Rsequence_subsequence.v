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
Require Import Rsequence.
Require Import Rsequence_facts.

Require Import Fourier.
Open Scope nat_scope.

Definition extractor (phi : nat -> nat) := forall n, phi n < phi (S n).

Definition subsequence X (un vn : nat -> X) :=
  {phi | extractor phi & forall n, un n = vn (phi n)}.

(** Properties on nat -> nat sequences *)

(* Growing sequence *)
Lemma nat_seq_growing_trans : forall an : nat -> nat, (forall x, an x <= an (S x)) ->
  forall y x, x <= y -> an x <= an y.
Proof.
induction y.
 intros x Hx0; rewrite (le_n_O_eq x Hx0).
 apply le_refl.
 
 intros x Hxy.
 destruct (Compare.le_decide _ _ Hxy) as [Hyx|Hyx].
  apply le_trans with (an y).
   apply IHy.
   apply gt_S_le.
   apply Hyx.
   
   apply H.
  
  subst; apply le_refl.
Qed.

(* Strictly growing sequence *)
Lemma nat_seq_strict_growing_trans : forall an, (forall x, an x < an (S x)) ->
  forall y x, x < y -> an x < an y.
Proof.
induction y.
 intros x Hx0. inversion Hx0.
 
 intros x Hxy.
 destruct (Compare.le_decide _ _ Hxy) as [Hyx|Hyx].
  apply le_trans with (an y).
   apply IHy.
   apply gt_S_le.
   apply Hyx.
   apply lt_le_weak.
   apply H.
  
  rewrite <- Hyx.
  apply H.
Qed.

(* Inverse of stricty growing is growing *)
Lemma nat_seq_growing_trans_converse : forall an, (forall x, an x < an (S x)) ->
  forall x y, an x <= an y -> x <= y.
Proof.
intros an H x y Hxy.
destruct (le_le_S_dec x y).
 assumption.
 
 pose proof (nat_seq_strict_growing_trans an H x y).
 intuition.
Qed.

(** Properties on extractors *)
Lemma Rsubseq_n_le_extractor_n : forall phi n, extractor phi -> n <= phi n.
Proof.
intros phi n ephi.
induction n.
 apply le_O_n.
 
 eapply le_trans with (S (phi n)).
 apply (le_n_S _ _ IHn).
 apply ephi.
Qed.

(** Convergence compatible with subsequence *)
Lemma Rseq_subseq_cv_compat : forall un vn l, subsequence _ un vn -> Rseq_cv vn l -> Rseq_cv un l.
Proof.
intros un vn l subuv vncv eps epspos.
destruct (vncv eps epspos) as [N H].
exists N.
intros n nN.
destruct subuv as [phi exphi phiun].
rewrite phiun.
apply H.
apply le_trans with n.
 apply nN.
 apply Rsubseq_n_le_extractor_n; assumption.
Qed.

(** Divergence compatible with subsequence *)
Lemma Rseq_subseq_cv_pos_infty_compat : forall un vn, subsequence _ un vn ->  
  Rseq_cv_pos_infty vn -> Rseq_cv_pos_infty un. 
Proof. 
intros un vn subuv vncv M. 
destruct (vncv M) as [N H]. 
exists N. 
intros n nN. 
destruct subuv as [phi exphi phiun]. 
rewrite phiun. 
apply H. 
apply le_trans with n. 
 apply nN. 
 apply Rsubseq_n_le_extractor_n; assumption. 
Qed.

(** An extractor defines a partition of N *)
Lemma Rseq_extractor_partition : forall phi, extractor phi -> 
  forall n, phi 0 <= n -> exists p, phi p <= n < phi (S p).
Proof.
intros phi ephi.
induction n.
 exists 0.
 split.
  assumption.
  apply (Rsubseq_n_le_extractor_n _ 1 ephi).
 
 destruct (le_le_S_dec (phi 0) n).
  intros _.
  destruct (IHn l) as [p [Hpn Hnsp]].
  destruct (Compare.le_decide _ _ Hnsp).
   exists p.
   split; [constructor|]; assumption.
   
   exists (S p).
   rewrite e.
   intuition.

  intro l'; rewrite (le_antisym _ _ l l').
  exists 0.
  split.
   constructor.
   apply ephi.
Qed.

(** Composition of extractors *)

Lemma extractor_comp phi1 phi2 :
  extractor phi1 -> extractor phi2 -> extractor (fun n => phi1 (phi2 n)).
Proof.
intros phi1 phi2 H1 H2 n.
apply nat_seq_strict_growing_trans; trivial.
Qed.

(** Common extractors *)
Definition Rseq_iter_S k := plus k.

Lemma extractor_S : extractor S.
Proof.
intro n.
constructor.
Qed.

Lemma extractor_Rseq_iter_S k : extractor (Rseq_iter_S k).
Proof.
intros k n. 
unfold Rseq_iter_S.
apply plus_lt_compat_l; constructor.
Qed.

Lemma extractor_mult_2 : extractor (mult 2).
Proof.
intros n; omega.
Qed.


(** Convergence of subsequence implies convergence of the growing sequence *)
Open Scope R_scope.

(* begin hide *)
Lemma R_dist_bounded_in_segment : forall a b c e, a <= b <= c -> R_dist a c < e -> 
  (*R_dist a b < e /\*) R_dist b c < e.
Proof.
intros a b c e [ab bc] ace.
unfold R_dist in *.
assert (forall x y, x <= y -> Rabs (x - y) = y - x).
 intros.
 rewrite Rabs_minus_sym.
 apply Rabs_right.
 fourier.
 
 pose proof (Rle_trans _ _ _ ab bc) as ac.
 
 (*split;*)
  repeat rewrite H; rewrite H in ace; intuition;
  apply Rle_lt_trans with (c - a);
   fourier.
Qed.
(* end hide *)

Lemma Rseq_subseq_growing_cv_compat : forall un vn l, subsequence _ un vn -> Rseq_cv un l ->
  Rseq_growing vn -> Rseq_cv vn l.
Proof.
intros un vn l [phi ephi phiun] uncv vngrow eps epspos.
assert (spliteps : (eps / 3 > 0)%R) by fourier.
destruct (uncv (eps / 3) spliteps) as [Nu Hu].
exists (phi Nu).
intros n nNu.
destruct (Rseq_extractor_partition phi ephi n) as [N Hpart].
 apply le_trans with (phi Nu).
  apply nat_seq_growing_trans.
   intros x.
   apply lt_le_weak.
   apply ephi.
   
   apply le_O_n.
  
  exact nNu.
 
 assert (HNuN : (Nu <= N)%nat).
  destruct (le_le_S_dec Nu N) as [goal|Hinv].
   exact goal.
   
   destruct Hpart as [HNn HnSN].
   pose proof (nat_seq_growing_trans phi (fun x => lt_le_weak _ _ (ephi _)) Nu (S N) Hinv).
   pose proof (le_trans _ _ _ H nNu).
   pose proof (lt_le_trans _ _ _ HnSN H).
   intuition.
 
 pose proof (Hu N HNuN) as Hun.
 pose proof (Hu (S N) (le_S _ _ HNuN)) as Husn.
 rewrite phiun in Hun.
 rewrite phiun in Husn.
 assert (vn (phi N) <= vn n <= vn (phi (S N)))%R.
  split; apply (Rseq_growing_trans _ vngrow); intuition.
 rewrite R_dist_sym in Husn.
 replace eps with (eps / 3 + eps / 3 + eps / 3) by field.
 eapply Rle_lt_trans.
  apply (R_dist_tri _ _ (vn (phi (S N)))).
  apply Rplus_lt_compat.
   eapply R_dist_bounded_in_segment.
    apply H.
    eapply Rle_lt_trans.
     apply (R_dist_tri _ _ l).
     apply Rplus_lt_compat.
      apply Hun.
      apply Husn.
   rewrite R_dist_sym .
   apply Husn.
Qed.

(** u(2n) → l and u growing implies u → l *)

Corollary Rseq_even_growing_compat : forall un l, Rseq_growing un ->
 Rseq_cv (fun i => un (2*i)%nat) l -> Rseq_cv un l.
Proof.
intros.
apply Rseq_subseq_growing_cv_compat with (fun i : nat => un (2 * i)%nat).
 exists (mult 2).
  intros n; omega.
  reflexivity.
 assumption.
 assumption.
Qed.

(** Link with Landau's relations *)
Section Landau.

Variables Un Vn : nat -> R.

(** Subsequence and big-O. *)

(**********)
Lemma Rseq_big_O_subseq_compat phi : 
  (Un = O (Vn)) -> extractor phi -> (fun n => Un (phi n)) = O(fun n => Vn (phi n)).
Proof.
intros phi Heq Hphi.
destruct Heq as [N [HN [N0 HN0]]].
exists N; split.
assumption.
exists N0; intros n Hn.
apply HN0.
apply le_trans with n.
assumption.
apply Rsubseq_n_le_extractor_n; assumption.
Qed.

(** Subsequence and little-O. *)

(**********)
Lemma Rseq_little_O_subseq_compat phi : 
  (Un = o (Vn)) -> extractor phi -> (fun n => Un (phi n)) = o(fun n => Vn (phi n)).
Proof.
intros phi Heq Hphi.
intros eps Heps.
destruct (Heq eps Heps) as [N HN].
exists N.
intros n Hn; unfold Rseq_minus.
apply HN.
apply le_trans with (phi N).
apply Rsubseq_n_le_extractor_n; assumption.
apply nat_seq_growing_trans;auto with *.
Qed.

(** Subsequence and equivalence. *)

(**********)
Lemma Rseq_equiv_subseq_compat phi : 
  (Un ~ Vn) -> extractor phi -> (fun n => Un (phi n)) ~ (fun n => Vn (phi n)).
Proof.
intros phi Heq Hphi.
intros eps Heps.
destruct (Heq eps Heps) as [N HN].
exists N.
intros n Hn; unfold Rseq_minus.
apply HN.
apply le_trans with (phi N).
apply Rsubseq_n_le_extractor_n; assumption.
apply nat_seq_growing_trans;auto with *.
Qed.

End Landau.