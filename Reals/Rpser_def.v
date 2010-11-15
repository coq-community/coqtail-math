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

Require Export MyReals.
Require Import Rsequence.
Require Import Rsequence_cv_facts.
Require Import Rsequence_base_facts.

Require Import Max.
Require Import Fourier.


Open Local Scope R_scope.


(** * Definitions *)

(** General term of a Power Serie and its absolute value *)
Definition gt_Pser (An : nat -> R) (x : R) := fun (n:nat) => (An n) * (x ^ n).

Definition gt_abs_Pser (An : nat -> R) (x : R) := fun (n:nat) => Rabs(An n * x ^ n).

Definition An_deriv (An:nat -> R) := fun n => INR (S n) * An (S n).

Definition gt_deriv_Pser (An : nat -> R) (x : R) := gt_Pser (An_deriv An) x.

Definition Pser_abs (An : nat -> R) (x l: R) := 
    Pser (fun n : nat => Rabs (An n)) (Rabs x) l.

(** Lower bound on the cv radius *)

Definition Cv_radius_weak (An : nat -> R) (r:R) := has_ub (gt_abs_Pser An r).

(** Cv radius definition *)

Definition finite_cv_radius (An : nat -> R) (r:R) := 
    (forall r', 0 <= r' < r -> Cv_radius_weak An r') /\
    (forall r', r < r' -> ~ (Cv_radius_weak An r')).

Definition infinite_cv_radius (An : nat -> R) := forall (r : R), Cv_radius_weak An r.

(** * Some lemmas manipulating the definitions *)

Lemma Cv_radius_weak_0 : forall An, Cv_radius_weak An 0.
Proof.
intro An.
exists (Rabs(An O)).
intros x Hx.
destruct Hx as [n Hn].
rewrite Hn.
unfold gt_abs_Pser.
destruct n.
 rewrite pow_O.
  ring_simplify(An 0%nat * 1); apply Rle_refl.
  
 rewrite pow_i.
 ring_simplify(An(S n)%nat * 0).
 rewrite Rabs_R0; apply Rabs_pos.
omega.
Qed.

Lemma finite_cv_radius_pos : forall An r, finite_cv_radius An r -> 0 <= r.
Proof.
intros An r [_ Hf].
 destruct(Rle_lt_dec 0 r).
  trivial.
destruct (Hf 0).
trivial.
apply Cv_radius_weak_0.
Qed.

Lemma Rle_cv_radius_compat : forall (An Bn : nat -> R) (r : R),
      (forall n, Rabs (Bn n) <= Rabs (An n)) ->
      Cv_radius_weak An r ->
      Cv_radius_weak Bn r.
Proof.
intros An Bn r Bn_le_An [M HM] ; exists M ; intros x [n Hn] ;
 rewrite Hn ; apply Rle_trans with (gt_abs_Pser An r n) ;
 [| apply HM ; exists n ; reflexivity].
 unfold gt_abs_Pser ; do 2 rewrite Rabs_mult ;
 apply Rmult_le_compat_r ; [apply Rabs_pos | apply Bn_le_An].
Qed.

Lemma Cv_radius_weak_Rabs_compat_rev : forall (An : nat -> R) (r : R), 
       Cv_radius_weak (fun n => Rabs (An n)) r -> Cv_radius_weak An r.
Proof.
intros An r [M HM] ; exists M.
 intros x [n Hn] ; rewrite Hn.
 unfold gt_abs_Pser ; rewrite Rabs_mult, <- Rabs_Rabsolu, <- Rabs_mult ;
 apply HM ; exists n ; reflexivity.
Qed.

Lemma Cv_radius_weak_Rabs_compat : forall (An : nat -> R) (r : R), 
       Cv_radius_weak An r -> Cv_radius_weak (fun n => Rabs (An n)) r.
Proof.
intros An r Rho.
elim Rho ; intros m Hm ; exists m ; unfold gt_abs_Pser ; intros a Ha ;
 unfold EUn in Ha ; elim Ha ; intros i Hi ; rewrite Hi ; rewrite Rabs_mult ;
 rewrite Rabs_Rabsolu ; rewrite <- Rabs_mult ; apply Hm ; exists i ; unfold gt_abs_Pser ;
 reflexivity.
Qed.

Lemma pow_lt_compat : forall x y, 0 < x -> x < y ->
  forall n, (1 <= n)%nat -> x ^ n < y ^ n.
Proof.
intros x y x_pos x_lt_y n n_lb.
 induction n.
 apply False_ind ; intuition.
 destruct n.
 simpl ; repeat (rewrite Rmult_1_r) ; assumption.
 assert (Hrew : forall a n, a ^ S (S n) = a * a ^ S n).
  intros a m ; simpl ; reflexivity.
 repeat (rewrite Hrew) ; apply Rmult_gt_0_lt_compat ; [apply pow_lt | | | apply IHn] ; intuition.
 apply Rlt_trans with x ; assumption.
Qed.

Lemma pow_le_compat : forall x y, 0 <= x -> x <= y ->
  forall n, x ^ n <= y ^ n.
Proof.
intros x y x_pos x_lt_y n.
 induction n.
 simpl ; apply Req_le ; reflexivity.
 simpl ; apply Rmult_le_compat ; [| apply pow_le | |] ; assumption.
Qed.

Lemma Cv_radius_weak_le_compat : forall (An : nat -> R) (r r' : R),
       Rabs r' <= Rabs r -> Cv_radius_weak An r -> Cv_radius_weak An r'.
Proof.
intros An r r' r'_bd Rho.
 case (Req_or_neq r') ; intro r_eq.
  rewrite r_eq ; exists (Rabs (An 0%nat)) ; intros x Hx ; destruct Hx as (i, Hi) ;
  rewrite Hi ; unfold gt_abs_Pser ; clear ; induction i ; [apply Req_le ;
  apply Rabs_eq_compat ; field | rewrite pow_i ; intuition ; rewrite Rmult_0_r ;
  rewrite Rabs_R0 ; apply Rabs_pos].
  assert (r_pos : 0 < Rabs r).
   apply Rlt_le_trans with (Rabs r') ; [apply Rabs_pos_lt |] ; assumption.
  assert (r_neq : r <> 0).
   case (Req_or_neq r) ; intro s ; [| assumption] ;
  apply False_ind ; rewrite s in r_pos ; rewrite Rabs_R0 in r_pos ; fourier.
  destruct Rho as (C, HC) ; exists C ; intros x Hx ; destruct Hx as (i,Hi) ; rewrite Hi ;
  unfold gt_abs_Pser.
  replace (r' ^ i) with ((r' ^ i * /r ^ i) * (r ^ i)).
  repeat (rewrite Rabs_mult) ; rewrite Rmult_comm ; rewrite <- Rabs_mult at 1 ;
  rewrite Rmult_assoc ; rewrite <- Rabs_mult.
  apply Rle_trans with (1 * Rabs (r ^ i * An i)).
  apply Rmult_le_compat_r ; [apply Rabs_pos | rewrite Rinv_pow] ;
  [|assumption].
  rewrite <- Rpow_mult_distr ; rewrite <- RPow_abs ; replace 1 with (1 ^ i) ;
  [|apply pow1] ; apply pow_le_compat ; [apply Rabs_pos | rewrite Rabs_mult].
  replace 1 with ((Rabs r) * /(Rabs r)) ; [rewrite Rabs_Rinv ; [apply Rmult_le_compat_r ;
  [apply Rlt_le ; apply Rinv_0_lt_compat |] |] | apply Rinv_r ; apply Rgt_not_eq] ;
  assumption.
  rewrite Rmult_1_l ; rewrite Rmult_comm ; apply HC ; exists i ; reflexivity.
  field ; apply pow_nonzero ; assumption.
Qed.


Lemma finite_cv_radius_weakening : forall An r, finite_cv_radius An r ->
      forall x, Rabs x < r -> Cv_radius_weak An x.
Proof.
intros An r [H_sup _] x Hx.
 apply Cv_radius_weak_le_compat with (Rabs x).
  rewrite Rabs_Rabsolu ; right ; reflexivity.
  apply H_sup ; split ; [apply Rabs_pos | assumption].
Qed.

Lemma Cv_radius_weak_padding_pos_compat : forall (An : nat -> R) (r : R),
     Cv_radius_weak An r -> forall N, Cv_radius_weak (fun n => An (n + N)%nat) r.
Proof.
intros An r Rho N.
 destruct (Req_dec r 0) as [r_eq | r_neq].
  rewrite r_eq ; exists (Rabs (An N)).
  intros u Hu ; destruct Hu as [n Hn] ; rewrite Hn ; unfold gt_abs_Pser ; destruct n.
  simpl ; rewrite Rmult_1_r ; right ; reflexivity.
  rewrite Rabs_mult, pow_i,
  Rabs_R0, Rmult_0_r ; [apply Rabs_pos | intuition].
 destruct Rho as [M HM].
 exists (M * (/ Rabs r) ^ N)%R.
 intros u Hu ; destruct Hu as [n Hn] ; rewrite Hn.
 unfold gt_abs_Pser ; simpl.
 rewrite Rabs_mult ; apply Rle_trans with (Rabs (An (n + N)%nat) * Rabs (r ^ n) *
 (Rabs r ^ N) * ((/Rabs r) ^ N))%R.
 right ; repeat rewrite Rmult_assoc ; repeat apply Rmult_eq_compat_l.
 rewrite <- Rpow_mult_distr, Rinv_r, pow1, Rmult_1_r ; [reflexivity |
 apply Rabs_no_R0 ; assumption].
 apply Rmult_le_compat_r.
 apply pow_le ; left ; apply Rinv_0_lt_compat ; apply Rabs_pos_lt ; assumption.
 rewrite Rmult_assoc, RPow_abs ; apply HM.
 exists (n + N)%nat ; unfold gt_abs_Pser.
 repeat rewrite Rabs_mult ; apply Rmult_eq_compat_l ;
 rewrite <- Rabs_mult ; apply Rabs_eq_compat.
 symmetry ; apply pow_add.
Qed.

Lemma Cv_radius_weak_padding_neg_compat : forall (An : nat -> R) (r : R) (N : nat),
     Cv_radius_weak (fun n => An (n + N)%nat) r -> Cv_radius_weak An r.
Proof.
intros An r N Rho.
 destruct Rho as [M HM].
 destruct (Rseq_partial_bound (fun n => (An n) * r ^ n) N) as [M' HM'].
 destruct (Req_dec r 0) as [r_eq | r_neq].
 exists (Rabs (An 0%nat)) ; intros u Hu ; destruct Hu as [n Hn] ; rewrite Hn.
  unfold gt_abs_Pser ; destruct n.
   simpl ; rewrite Rmult_1_r ; right ; reflexivity.
   rewrite Rabs_mult, r_eq, pow_i, Rabs_R0,  Rmult_0_r ; [apply Rabs_pos | intuition].
 exists (Rmax (M * Rabs (r ^ N)) M') ; intros u Hu ; destruct Hu as [n Hn] ; rewrite Hn.
 destruct (le_lt_dec n N) as [n_lb | n_ub].
 apply Rle_trans with M' ; [apply HM' | apply RmaxLess2] ; assumption.
 apply Rle_trans with (M * Rabs (r ^ N))%R ; [| apply RmaxLess1] ; unfold gt_abs_Pser.
 apply Rle_trans with (Rabs (An n * r ^ n) * (/ Rabs (r ^ N)) * Rabs (r ^ N))%R.
 right ; field ; apply Rabs_no_R0.
 apply pow_nonzero ; assumption.
  apply Rmult_le_compat_r ; [apply Rabs_pos |].
  apply HM ; exists (n - N)%nat.
  unfold gt_abs_Pser.
  rewrite <- RPow_abs, Rinv_pow, <- Rabs_Rinv, RPow_abs, <- Rabs_mult,
  <- Rinv_pow.
  assert (Hrew : (n = n - N + N)%nat).
   intuition.
   repeat rewrite Rabs_mult ; rewrite Hrew at 1 ; rewrite Rmult_assoc ;
   apply Rmult_eq_compat_l ; rewrite <- Rabs_mult ; apply Rabs_eq_compat.
   rewrite Hrew at 1 ; rewrite pow_add, Rmult_assoc, Rinv_r, Rmult_1_r ;
   [reflexivity | apply pow_nonzero ; assumption].
   assumption.
   assumption.
   apply Rabs_no_R0 ; assumption.
Qed.

Lemma Cv_radius_weak_plus : forall (An Bn : nat -> R) (r1 r2 : R),
       Cv_radius_weak An r1 -> Cv_radius_weak Bn r2 ->
       Cv_radius_weak (fun n => An n + Bn n) (Rmin (Rabs r1) (Rabs r2)).
Proof.
intros An Bn r1 r2 RhoA RhoB.
assert (r''_bd1 : Rabs (Rmin (Rabs r1) (Rabs r2)) <= Rabs r1).
 unfold Rmin ; case (Rle_dec (Rabs r1) (Rabs r2)) ; intro H ;
 rewrite Rabs_Rabsolu ; intuition.
assert (r''_bd2 : Rabs (Rmin (Rabs r1) (Rabs r2)) <= Rabs r2).
 unfold Rmin ; case (Rle_dec (Rabs r1) (Rabs r2)) ; intro H ;
 rewrite Rabs_Rabsolu ; intuition.
assert (Rho'A := Cv_radius_weak_le_compat An _ _ r''_bd1 RhoA).
assert (Rho'B := Cv_radius_weak_le_compat Bn _ _ r''_bd2 RhoB).
 destruct Rho'A as (C, HC) ;
 destruct Rho'B as (C', HC') ;
 exists (C + C').
 intros x Hx ; destruct Hx as (i, Hi) ; rewrite Hi ; unfold gt_abs_Pser.
 rewrite Rmult_plus_distr_r ; apply Rle_trans with (Rabs (An i *  Rmin (Rabs r1)
         (Rabs r2) ^ i) + Rabs (Bn i * Rmin (Rabs r1) (Rabs r2) ^ i)) ; [apply Rabs_triang |].
 apply Rle_trans with (Rabs (An i * Rmin (Rabs r1) (Rabs r2) ^ i) + C') ;
 [apply Rplus_le_compat_l ; apply HC' | apply Rplus_le_compat_r ; apply HC] ;
 exists i ; intuition.
Qed.

Lemma Cv_radius_weak_opp : forall (An : nat -> R) (r : R),
       Cv_radius_weak An r ->
       Cv_radius_weak (fun n => - An n) r.
Proof.
intros An r Rho.
 destruct Rho as (C, HC) ; exists C ; intros x Hx ; destruct Hx as (i,Hi) ; rewrite Hi ;
 unfold gt_abs_Pser ; rewrite Ropp_mult_distr_l_reverse ; rewrite Rabs_Ropp ;
 apply HC ; exists i ; intuition.
Qed.

Lemma Cv_radius_weak_minus : forall (An Bn : nat -> R) (r1 r2 : R),
       Cv_radius_weak An r1 -> Cv_radius_weak Bn r2 ->
       Cv_radius_weak (fun n => An n - Bn n) (Rmin (Rabs r1) (Rabs r2)).
Proof.
intros An Bn r1 r2 RhoA RhoB.
 assert (Rho'B := Cv_radius_weak_opp Bn _ RhoB).
 unfold Rminus ; apply Cv_radius_weak_plus ; assumption.
Qed.

Lemma Rmin_ge_0 : forall x y, 0 <= x -> 0 <= y -> 0 <= Rmin x y.
Proof.
intros x y x_pos y_pos.
 unfold Rmin ; case (Rle_dec x y) ; intro h ; intuition.
Qed.

Lemma Pser_add : forall (An Bn : nat -> R) (x : R) (N : nat),
       sum_f_R0 (gt_Pser (fun n => An n + Bn n) x) N = sum_f_R0 (gt_Pser An x) N + sum_f_R0 (gt_Pser Bn x) N.
Proof.
intros An Bn x N ; induction N. 
 compute ; field.
 assert (Hrew : forall a b c d e, c = d + e -> a + b + c = a + d + (b + e)).
  intros ; repeat (rewrite Rplus_assoc) ; apply Rplus_eq_compat_l ;
  replace (d + (b + e)) with (b + (d + e)) by field ; apply Rplus_eq_compat_l ;
  assumption.
 simpl ; rewrite IHN ; apply Hrew.
 unfold gt_Pser ; field.
Qed.

Lemma Pser_minus : forall (An Bn : nat -> R) (x : R) (N : nat),
       sum_f_R0 (gt_Pser (fun n => An n - Bn n) x) N = sum_f_R0 (gt_Pser An x) N - sum_f_R0 (gt_Pser Bn x) N.
Proof.
intros An Bn x N ; induction N. 
 compute ; field.
 assert (Hrew : forall a b c d e, c = d - e -> a - b + c = a + d - (b + e)).
  intros ; unfold Rminus ; repeat (rewrite Rplus_assoc) ; apply Rplus_eq_compat_l ;
  replace (d + - (b + e)) with (- b + (d - e)) by field ; apply Rplus_eq_compat_l ;
  assumption.
 simpl ; rewrite IHN ; apply Hrew.
 unfold gt_Pser ; field.
Qed.

Lemma Pser_opp : forall (An : nat -> R) (x : R) (N : nat),
        sum_f_R0 (gt_Pser (- An)%Rseq x) N = - sum_f_R0 (gt_Pser An x) N.
Proof.
intros An x N ; induction N.
 unfold gt_Pser ; simpl ; unfold Rseq_opp ; ring.
 repeat rewrite tech5 ; rewrite IHN, Ropp_plus_distr ;
 unfold gt_Pser, Rseq_opp ; ring.
Qed.

(** Pser and Un_cv are linked. See "tech12" for the reciprocal lemma *)

Lemma Pser_Rseqcv_link : forall (An : nat -> R) (x l : R),
       Pser An x l ->
       Rseq_cv (fun N : nat => sum_f_R0 (gt_Pser An x) N) l.
Proof.
intros An x l Hyp.
 unfold gt_Pser.
 apply Hyp.
Qed.

Lemma Pser_opp_compat : forall (An : nat -> R) (x l : R),
	Pser An x l -> Pser (- An)%Rseq x (-l).
Proof.
intros An x l Hl eps eps_pos ; destruct (Hl _ eps_pos) as [N HN] ;
 exists N ; intros n n_lb ; unfold R_dist, Rminus in *.
 fold (gt_Pser (-An)%Rseq x).
 rewrite Pser_opp, <- Ropp_plus_distr, Rabs_Ropp ; apply HN ;
 assumption.
Qed.

Lemma Pser_unique : forall (An : nat -> R) (x l1 l2 : R),
          Pser An x l1 -> Pser An x l2 -> l1 = l2.
Proof.
intros An x l1 l2 Hl1 Hl2.
 assert (T1 := Pser_Rseqcv_link _ _ _ Hl1) ;
 assert (T2 := Pser_Rseqcv_link _ _ _ Hl2) ;
 eapply Rseq_cv_unique ; eassumption.
Qed.

Lemma Pser_unique_extentionality : forall (An Bn : nat -> R) (x l1 l2 : R),
	(forall n, An n = Bn n) ->
        Pser An x l1 -> Pser Bn x l2 -> l1 = l2.
Proof.
intros An Bn x l1 l2 An_eq_Bn Hl1 Hl2.
 assert (T1 := Pser_Rseqcv_link _ _ _ Hl1) ;
 assert (T2 := Pser_Rseqcv_link _ _ _ Hl2).
 assert (T3 : forall (n : nat), sum_f_R0 (fun n => (gt_Pser An x) n) n
                  = sum_f_R0 (fun n => (gt_Pser Bn x) n) n).
  intro n ; apply sum_eq ; intros ; unfold gt_Pser ; rewrite An_eq_Bn ; reflexivity.
 assert (T4 := Rseq_cv_eq_compat _ _ _ T3 T1).
 eapply Rseq_cv_unique ; eassumption.
Qed.

(** Link between the finite_cv_radius and the upper bound *)

Lemma finite_cv_radius_le : forall An r r', 
  finite_cv_radius An r -> Cv_radius_weak An r' -> r' <= r.
Proof.
intros An r r' [_ Hf] Hr'.
 destruct(Rle_lt_dec r' r).
  trivial.
  apply False_ind; apply (Hf r' r0 Hr').
Qed.

Lemma finite_cv_radius_lub : forall An r, 
  finite_cv_radius An r -> is_lub (fun r' => Cv_radius_weak An r') r.
Proof.
intros An r H.
split; intros r' Hr'.
 apply finite_cv_radius_le with An; trivial.

 destruct H as [H1 H2].
 destruct (Rle_lt_dec r r').
  trivial.

  pose ((r+r')/2) as r1.
  assert(r' < r1 < r).
   assert(H : forall a, a = (a+a)/2) by (intro; field).
   split; unfold r1; [rewrite (H r') at 1 | rewrite (H r) at 2];
    apply Rmult_lt_compat_r; auto with *.

destruct H as [H H'].
destruct (Hr' r1).
 apply H1; split.
  apply Rle_trans with r'.
   apply Hr', Cv_radius_weak_0; auto with *.
auto with *.
trivial.

 apply False_ind, (Rlt_irrefl r'), Rlt_trans with r1; trivial.

 apply False_ind, (Rlt_irrefl r').
 rewrite <- H0 in *; trivial.
Qed.

(*
Lemma finite_cv_radius_ex An r0 : 
 ~ Cv_radius_weak An r0 -> {r | finite_cv_radius An r}.
Proof.

needs classical *)