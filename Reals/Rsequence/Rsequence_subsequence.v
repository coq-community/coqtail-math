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
Require Import Rsequence_def.
Require Import Rsequence_facts.

Require Import Lia Lra.
Open Scope Rseq_scope.
Open Scope nat_scope.
(** printing ~	~ *)
Definition is_extractor (phi : nat -> nat) := forall n, phi n < phi (S n).

Definition extractor := {phi | is_extractor phi}.

Definition extracted {X : Type} (phi : extractor) (Un : nat -> X) n := Un ((proj1_sig phi) n).

(** printing ⋅ #&bull;# *)
Notation "Un ⋅ phi" := (extracted phi Un) (at level 40, left associativity) : Rseq_scope.


Definition subsequence {X : Type} (Un Vn : nat -> X) :=
  {phi | forall n, Un n = (Vn ⋅ phi) n}.

Lemma subsequence_helper {u v : Rseq} (f : nat -> nat) :
  (forall n, f n < f (1 + n))%nat ->
  (forall n, u n = v (f n)) ->
  subsequence u v.
Proof.
  intros Hf.
  hnf. unfold extractor.
  exists (exist is_extractor f Hf).
  eauto.
Qed.

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
 intuition lia.
Qed.

(** Properties on extractors *)
Lemma Rsubseq_n_le_extractor_n : forall phi n, is_extractor phi -> n <= phi n.
Proof.
intros phi n Hphi.
induction n.
 apply le_O_n.
 
 eapply le_trans with (S (phi n)).
 apply (le_n_S _ _ IHn).
 apply Hphi.
Qed.

(** Convergence compatible with subsequence *)
Lemma Rseq_subseq_cv_compat : forall Un Vn l, subsequence Un Vn -> Rseq_cv Vn l -> Rseq_cv Un l.
Proof.
intros Un Vn l Hsub Hcv eps Heps.
destruct (Hcv eps Heps) as [N HN].
exists N; intros n Hn.
destruct Hsub as [phi Hphi].
unfold extracted in *; simpl in Hphi.
rewrite Hphi.
apply HN.
apply le_trans with n.
 apply Hn.
 apply Rsubseq_n_le_extractor_n; destruct phi; auto.
Qed.

(** Divergence compatible with subsequence *)
Lemma Rseq_subseq_cv_pos_infty_compat :
  forall Un Vn, subsequence Un Vn ->  
    Rseq_cv_pos_infty Vn -> Rseq_cv_pos_infty Un. 
Proof. 
intros Un Vn Hsub Hdv M.
destruct (Hdv M) as [N HN].
exists N; intros n Hn.
destruct Hsub as [phi Hphi].
rewrite Hphi.
apply HN.
apply le_trans with n.
 apply Hn.
 apply Rsubseq_n_le_extractor_n; destruct phi; auto. 
Qed.

(** An extractor defines a partition of N *)
Lemma Rseq_extractor_partition : forall phi, is_extractor phi -> 
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

Lemma extractor_comp : forall phi1 phi2,
  is_extractor phi1 -> is_extractor phi2 -> is_extractor (fun n => phi1 (phi2 n)).
Proof.
intros phi1 phi2 H1 H2 n.
apply nat_seq_strict_growing_trans; trivial.
Qed.

(** Common extractors *)
Definition Rseq_iter_S k := plus k.

Lemma extractor_S : is_extractor S.
Proof.
intro n.
constructor.
Qed.

Lemma extractor_Rseq_iter_S : forall k, is_extractor (Rseq_iter_S k).
Proof.
intros k n. 
unfold Rseq_iter_S.
apply plus_lt_compat_l; constructor.
Qed.

Lemma is_extractor_mult_2 : is_extractor (mult 2).
Proof.
intros n; lia.
Qed.

Definition extractor_mult_2 := exist _ (mult 2) is_extractor_mult_2.

(** Rseq_zip can be inversed thanks to extractors *)

Lemma Rseq_zip_extract_evens : forall Un Vn,
  Rseq_zip Un Vn ⋅ extractor_mult_2 == Un.
Proof.
intros Un Vn n ; unfold Rseq_zip, extracted, extractor_mult_2 ;
 simpl ; case (n_modulo_2 (n + (n + 0))) ; intros [p Hp].
  f_equal ; lia.
  apply False_ind ; lia.
Qed.

(** Convergence of subsequence implies convergence of the growing sequence *)
Open Scope R_scope.

(* begin hide *)
Lemma R_dist_bounded_in_segment : forall a b c e, a <= b <= c -> R_dist a c < e -> 
  R_dist b c < e.
Proof.
intros a b c e [ab bc] ace.
unfold R_dist in *.
assert (forall x y, x <= y -> Rabs (x - y) = y - x).
 intros.
 rewrite Rabs_minus_sym.
 apply Rabs_right.
 lra.
 
 pose proof (Rle_trans _ _ _ ab bc) as ac.
 
  repeat rewrite H; rewrite H in ace; intuition;
  apply Rle_lt_trans with (c - a);
   lra.
Qed.
(* end hide *)

Lemma Rseq_subseq_growing_cv_compat :
  forall Un Vn l, subsequence Un Vn -> Rseq_cv Un l -> Rseq_growing Vn -> Rseq_cv Vn l.
Proof.
intros un vn l [phi ephi] uncv vngrow eps epspos.
destruct phi as [phi Hphi]; unfold extracted in *; simpl in *.
assert (spliteps : (eps / 3 > 0)%R) by lra.
destruct (uncv (eps / 3) spliteps) as [Nu Hu].
exists (phi Nu).
intros n nNu.
destruct (Rseq_extractor_partition phi Hphi n) as [N Hpart].
 apply le_trans with (phi Nu).
  apply nat_seq_growing_trans.
   intros x.
   apply lt_le_weak.
   apply Hphi.
   
   apply le_O_n.
  
  exact nNu.
 
 assert (HNuN : (Nu <= N)%nat).
  destruct (le_le_S_dec Nu N) as [goal|Hinv].
   exact goal.
   
   destruct Hpart as [HNn HnSN].
   pose proof (nat_seq_growing_trans phi (fun x => lt_le_weak _ _ (Hphi _)) Nu (S N) Hinv).
   pose proof (le_trans _ _ _ H nNu).
   pose proof (lt_le_trans _ _ _ HnSN H).
   intuition lia.
 
 pose proof (Hu N HNuN) as Hun.
 pose proof (Hu (S N) (le_S _ _ HNuN)) as Husn.
 rewrite ephi in Hun.
 rewrite ephi in Husn.
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
 assert (Hex : is_extractor (mult 2)).
   intros n; lia.
 pose (phi := exist _ (mult 2) Hex).
 exists phi; reflexivity.
 assumption.
 assumption.
Qed.

(** Link with Landau's relations *)
Section Landau.

Variables Un Vn : nat -> R.

(** Subsequence and big-O. *)

(**********)
Lemma Rseq_big_O_subseq_compat : 
  forall phi, Un = O (Vn) -> (Un ⋅ phi) = O(Vn ⋅ phi).
Proof.
intros phi Heq.
destruct Heq as [N [HN [N0 HN0]]].
exists N; split.
assumption.
exists N0; intros n Hn.
apply HN0.
apply le_trans with n.
assumption.
apply Rsubseq_n_le_extractor_n; destruct phi; assumption.
Qed.

(** Subsequence and little-O. *)

(**********)
Lemma Rseq_little_O_subseq_compat : 
  forall phi, Un = o (Vn) -> (Un ⋅ phi) = o(Vn ⋅ phi).
Proof.
intros [phi Hphi] Heq.
intros eps Heps.
destruct (Heq eps Heps) as [N HN].
exists N.
intros n Hn; unfold Rseq_minus.
apply HN.
apply le_trans with (phi N).
apply Rsubseq_n_le_extractor_n; assumption.
apply nat_seq_growing_trans; auto with *.
Qed.

(** Subsequence and equivalence. *)

(**********)
Lemma Rseq_equiv_subseq_compat : 
  forall phi, Un ~ Vn -> (Un ⋅ phi) ~ (Vn ⋅ phi).
Proof.
intros [phi Hphi] Heq.
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
