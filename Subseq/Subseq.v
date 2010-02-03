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

Require Export Reals.
Require Export Max.
Open Local Scope R_scope.

Definition strictly_increasing (f : nat -> nat) := forall n: nat, (f n < f (S n)) %nat.

(** Definition of a sub-sequence*)
Definition sub_seq (An : nat -> R) (f : nat -> nat) (pr : strictly_increasing f) :=
    fun n => An (f n).

Lemma sincr_ge_id (f : nat -> nat) : strictly_increasing f -> forall n : nat, (n <= f n )%nat.
Proof.
induction n.
omega.
apply le_trans with (S (f n)).
apply le_n_S.
apply IHn.
apply lt_le_S.
apply (H n).
Qed.

(** A sub-sequence of a convergent sequence converges to the same limit*)
Lemma Rsubseq_cv (An : nat -> R) (f : nat -> nat) (pr : strictly_increasing f) (l : R):
    Un_cv An l -> Un_cv (sub_seq An f pr) l.
Proof.
unfold Un_cv.
intros An f pr l Hcv eps Heps.
destruct (Hcv eps Heps) as (N, HN).
exists N.
intros n Hn.
apply HN.
apply le_trans  with n.
apply Hn.
apply sincr_ge_id.
apply pr.
Qed.

Lemma odd_or_even : forall n : nat, exists p : nat, (n = 2*p \/  n = S (2*p)) %nat.
Proof.
intros.
induction n.
exists 0%nat.
left.
trivial.
destruct IHn.
case H; intro.
exists x.
right.
rewrite H0.
reflexivity.
exists (S x).
left.
rewrite H0.
omega.
Qed.

(** a seqence converges if its odd and even subsequences converges to the same limit*)
Lemma even_odd_cv (An : nat -> R) (l : R): 
    Un_cv (fun n => An ((2*n) %nat)) l ->  Un_cv (fun n => An (S (2*n) %nat)) l ->
        Un_cv An l.
Proof.
unfold Un_cv.
intros An l Hcve Hcvo eps Heps.
destruct (Hcve eps Heps) as (Ne, He).
destruct (Hcvo eps Heps) as (No, Ho).
SearchPattern (?a <= ?b )%nat.
exists (max (2*Ne) (S (2*No))).
intros n Hn.
destruct (odd_or_even n) as (p, Hp).
destruct Hp.
rewrite H.
apply He.
apply le_double.
rewrite <- H.
apply le_trans with (max (2 * Ne) (S (2 * No) )).
apply le_max_l.
apply Hn.
rewrite H.
apply Ho.
apply le_double.
apply le_S_n.
rewrite <- H.
apply le_trans with (max (2 * Ne) (S (2 * No))).
apply le_max_r.
apply Hn.
Qed.

Lemma sub_seq_ub_compat (An : nat -> R) (f : nat -> nat) (pr : strictly_increasing f) : 
    has_ub An -> has_ub (sub_seq An f pr).
Proof.
intros An f pr Hub.
destruct Hub as (m, Hm).
exists m.
intros x Hx.
destruct Hx as (n, Hn).
rewrite Hn.
apply Hm.
exists (f n).
reflexivity.
Qed.

(*?*)
Lemma sub_seq_lb_compat (An : nat -> R) (f : nat -> nat) (pr : strictly_increasing f) : 
    has_lb An -> has_lb (sub_seq An f pr).
Proof.
intros An f pr Hlb.
destruct Hlb as (m, Hm).
exists m.
intros x Hx.
destruct Hx as (n, Hn).
rewrite Hn.
apply Hm.
exists (f n).
reflexivity.
Qed.
