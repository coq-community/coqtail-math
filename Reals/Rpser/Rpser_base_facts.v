(*
(C) Copyright 2011, COQTAIL team

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
Require Import Rpser_def Rpser_def_simpl.

Require Import Rinterval.
Require Import Rsequence_def Rsequence_base_facts Rsequence_subsequence Rsequence_rewrite_facts.
Require Import Rsequence_cv_facts Rsequence_facts Rsequence_bound_facts Rsequence_sums_facts.
Require Import Rpow_facts.
Require Import Max.
Require Import Lra MyRIneq MyNat MyNNR.

Local Open Scope R_scope.

(** ** Some lemmas manipulating the definitions. *)


(** * Extensionality of radiuses. *)

Section Radius_extensionality.

Variables An Bn : Rseq.
Hypothesis AnBn_ext : (An == Bn)%Rseq.

Lemma An_deriv_ext : (An_deriv An == An_deriv Bn)%Rseq.
Proof.
intro n ; unfold An_deriv, Rseq_mult, Rseq_shift ; rewrite AnBn_ext ; reflexivity.
Qed.

Lemma An_nth_deriv_ext : forall k, (An_nth_deriv An k == An_nth_deriv Bn k)%Rseq.
Proof.
intros n k ; unfold An_nth_deriv, Rseq_mult, Rseq_div, Rseq_shifts ;
rewrite AnBn_ext ; reflexivity.
Qed.

Lemma Cv_radius_weak_ext : forall r, Cv_radius_weak An r <-> Cv_radius_weak Bn r.
Proof.
intro r ; split ; intros [B HB] ; exists B ; intros x [i Hi] ; subst ;
 [rewrite <- (gt_abs_pser_ext  _ _ _ AnBn_ext) |
 rewrite (gt_abs_pser_ext _ _ _ AnBn_ext)] ; apply HB ; exists i ; reflexivity.
Qed.

Lemma finite_cv_radius_ext : forall r, finite_cv_radius An r <->
  finite_cv_radius Bn r.
Proof.
intro r ; split ; intros [rho_lb rho_ub] ; split ; intros r' Hr' ;
 [rewrite <- Cv_radius_weak_ext | rewrite <- Cv_radius_weak_ext
 | rewrite Cv_radius_weak_ext | rewrite Cv_radius_weak_ext] ; auto.
Qed.

Lemma infinite_cv_radius_ext : infinite_cv_radius An <->
  infinite_cv_radius Bn.
Proof.
split ; intros rho r ; [rewrite <- Cv_radius_weak_ext |
 rewrite Cv_radius_weak_ext] ; trivial.
Qed.

End Radius_extensionality.

(** Compatibility of gt_pser with common operations. *)

Lemma gt_pser_expand_compat : forall Un l x,
  forall n, gt_pser (An_expand Un l) x n = gt_pser Un (l * x) n.
Proof.
intros ; unfold gt_pser, An_expand, Rseq_mult, Rseq_pow ;
rewrite Rpow_mult_distr ; ring.
Qed. 

Lemma gt_pser_scal_compat_l : forall Un (l : R) x,
  forall n, gt_pser (l * Un) x n = l * gt_pser Un x n.
Proof.
intros Un l x n ; unfold gt_pser, Rseq_mult, Rseq_constant ; ring.
Qed.

Lemma gt_pser_scal_compat_r : forall Un (l : R) x,
  forall n, gt_pser (Un * l) x n = gt_pser Un x n * l.
Proof.
intros Un l x n ; unfold gt_pser, Rseq_mult, Rseq_constant ; ring.
Qed.

Lemma gt_pser_opp_compat : forall Un x,
  gt_pser (- Un) x == - gt_pser Un x.
Proof.
intros Un x n ; unfold gt_pser, Rseq_opp, Rseq_mult ; ring.
Qed.

Lemma gt_pser_plus_compat : forall Un Vn x,
  gt_pser (Un + Vn) x == gt_pser Un x + gt_pser Vn x.
Proof.
intros Un Vn x n ; unfold gt_pser, Rseq_plus, Rseq_mult ; ring.
Qed.

Lemma gt_pser_minus_compat : forall Un Vn x,
  gt_pser (Un - Vn) x == gt_pser Un x - gt_pser Vn x.
Proof.
intros Un Vn x n ; unfold gt_pser, Rseq_minus, Rminus,
 Rseq_plus, Rseq_mult ; ring.
Qed.

Lemma gt_pser_mult_compat_l : forall Un Vn x,
  gt_pser (Un * Vn) x == Un * gt_pser Vn x.
Proof.
intros Un Vn x n ; unfold gt_pser, Rseq_mult ; ring.
Qed.

Lemma gt_pser_mult_compat_r : forall Un Vn x,
  gt_pser (Un * Vn) x == gt_pser Un x * Vn.
Proof.
intros Un Vn x n ; unfold gt_pser, Rseq_mult ; ring.
Qed.

Lemma gt_pser_prod_compat : forall Un Vn x,
  gt_pser (Un # Vn) x == (gt_pser Un x) # (gt_pser Vn x).
Proof.
intros Un Vn x n ; unfold gt_pser, Rseq_prod, Rseq_mult.
 assert (Hrew := Rseq_sum_scal_compat_r (pow x n)
 (fun n0 : nat => Un n0 * Vn (n - n0)%nat)%R n) ;
 unfold Rseq_mult, Rseq_constant in Hrew ;
 rewrite <- Hrew ; apply Rseq_sum_ext_strong.
 intros p p_bd ; replace (x ^ n) with (x ^ ((p + (n - p))%nat)).
 rewrite pow_add ; ring.
 replace (p + (n - p))%nat with n by lia ; reflexivity.
Qed.

(** Compatibility of gt_abs_pser with common operations. *)

Lemma gt_abs_pser_pos : forall An x n,
  0 <= gt_abs_pser An x n.
Proof.
intros ; unfold gt_abs_pser, Rseq_abs ; apply Rabs_pos.
Qed.

Lemma gt_abs_pser_scal_compat_l : forall Un (l : R) x,
  forall n, gt_abs_pser (l * Un) x n = Rabs l * gt_abs_pser Un x n.
Proof.
intros Un l x n ; unfold gt_abs_pser, Rseq_abs ;
 rewrite gt_pser_scal_compat_l ; apply Rabs_mult.
Qed.

Lemma gt_abs_pser_scal_compat_r : forall Un (l : R) x,
  forall n, gt_abs_pser (Un * l) x n = gt_abs_pser Un x n * Rabs l.
Proof.
intros Un l x n ; unfold gt_abs_pser, Rseq_abs ;
 rewrite gt_pser_scal_compat_r ; apply Rabs_mult.
Qed.

Lemma gt_abs_pser_opp_compat : forall Un x,
  gt_abs_pser (- Un) x == gt_abs_pser Un x.
Proof.
intros Un x n ; unfold gt_abs_pser, Rseq_abs ;
rewrite gt_pser_opp_compat ; unfold Rseq_opp ;
apply Rabs_Ropp.
Qed.

Lemma gt_abs_pser_mult_compat_l : forall Un Vn x,
  gt_abs_pser (Un * Vn) x == | Un | * gt_abs_pser Vn x.
Proof.
intros Un Vn x n ; unfold gt_abs_pser, Rseq_abs ;
rewrite gt_pser_mult_compat_l ; unfold Rseq_mult ;
apply Rabs_mult.
Qed.

Lemma gt_abs_pser_mult_compat_r : forall Un Vn x,
  gt_abs_pser (Un * Vn) x == gt_abs_pser Un x * | Vn |.
Proof.
intros Un Vn x n ; unfold gt_abs_pser, Rseq_abs ;
rewrite gt_pser_mult_compat_r ; unfold Rseq_mult ;
apply Rabs_mult.
Qed.

Lemma gt_abs_pser_prod_le_compat : forall Un Vn x n,
  gt_abs_pser (Un # Vn) x n <= ((gt_abs_pser Un x) # (gt_abs_pser Vn x)) n.
Proof.
intros Un Vn x n ; unfold gt_abs_pser, Rseq_abs ; rewrite gt_pser_prod_compat.
unfold Rseq_prod ; eapply Rle_trans ; [eapply Rseq_sum_triang |].
right ; apply Rseq_sum_ext ; intro p ; unfold gt_pser, Rseq_abs, Rseq_mult ;
apply Rabs_mult.
Qed.

(** Compatibility of An_deriv with the common operators. *)

Lemma An_deriv_opp_compat : forall An,
  An_deriv (- An) == - An_deriv An.
Proof.
intros An n ; unfold Rseq_opp, An_deriv, Rseq_mult,
Rseq_shift ; apply Ropp_mult_distr_r_reverse.
Qed.

Lemma An_deriv_plus_compat : forall An Bn,
  An_deriv (An + Bn) == (An_deriv An) + (An_deriv Bn).
Proof.
intros An Bn n ; unfold Rseq_opp, An_deriv, Rseq_mult,
 Rseq_shift, Rseq_plus ; apply Rmult_plus_distr_l.
Qed.

Lemma An_deriv_minus_compat : forall An Bn,
  An_deriv (An - Bn) == An_deriv An - An_deriv Bn.
Proof.
intros An Bn n ; unfold An_deriv, Rseq_shift,
Rseq_mult, Rseq_minus ; apply Rmult_minus_distr_l.
Qed.

Lemma An_deriv_abs_compat : forall An,
  An_deriv (| An |) == | An_deriv An |.
Proof.
intros An n ; unfold An_deriv, Rseq_shift, Rseq_mult, Rseq_abs ;
 rewrite Rabs_mult ; apply Rmult_eq_compat.
 symmetry ; apply Rabs_right, Rle_ge, pos_INR.
 reflexivity.
Qed.

Lemma An_deriv_alt_compat : forall An,
  An_deriv (Rseq_alt An) == - Rseq_alt (An_deriv An).
Proof.
intros An n ; unfold An_deriv, Rseq_shift, Rseq_alt, Rseq_mult, Rseq_opp ;
 simpl Rseq_pow ; ring.
Qed.

Lemma An_deriv_mult_compat_l : forall An Bn,
  An_deriv (An * Bn) == An_deriv An * Rseq_shift Bn.
Proof.
intros An Bn n ; unfold An_deriv, Rseq_mult, Rseq_shift ;
 ring.
Qed.

Lemma An_deriv_mult_compat_r : forall An Bn,
  An_deriv (An * Bn) == Rseq_shift An * An_deriv Bn.
Proof.
intros An Bn n ; unfold An_deriv, Rseq_mult, Rseq_shift ;
 ring.
Qed.

(** * Cv_radius_weak *)
(** There exists always a Cv_radius_weak. *)

Lemma Cv_radius_weak_0 : forall An, Cv_radius_weak An 0.
Proof.
intro An ; exists (Rabs(An O)) ; intros x [n Hn] ; subst ;
unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult.
destruct n.
 simpl ; rewrite Rmult_1_r ; reflexivity.
 rewrite pow_i ; [| lia] ; rewrite Rmult_0_r, Rabs_R0 ;
 apply Rabs_pos.
Qed.

Lemma Cv_radius_weak_subseq_compat :
  forall An Bn r, 1 <= Rabs r -> subsequence Bn An ->
  Cv_radius_weak An r -> Cv_radius_weak Bn r.
Proof.
intros An Bn r Hr [[phi Hphi] HAB] [ub Hub].
 exists ub ; intros B [i Hi] ; subst ; transitivity (gt_abs_pser An r (phi i)).
  unfold gt_abs_pser, Rseq_abs, gt_pser, Rseq_mult ; do 2 rewrite Rabs_mult.
  apply Rmult_le_compat ; try (apply Rabs_pos).
  right ; apply Rabs_eq_compat, HAB.
  do 2 rewrite <- RPow_abs ; apply Rle_pow, Rsubseq_n_le_extractor_n ; assumption.
  apply Hub ; exists (phi i) ; reflexivity.
Qed.

(** Compatibility of the Cv_radius_weak concept with common operations. *)

Lemma Cv_radius_weak_Rabs : forall (An : Rseq) (r : R),
  Cv_radius_weak An (Rabs r) <-> Cv_radius_weak An r.
Proof.
intros An r ; split ; intros [B HB] ; exists B ; intros y [i Hi] ; subst ;
 apply HB ; exists i ; rewrite gt_abs_pser_Rabs_compat ; reflexivity.
Qed.

Lemma Rle_Cv_radius_weak_compat : forall (An Bn : nat -> R) (r : R),
      (forall n, Rabs (Bn n) <= Rabs (An n)) ->
      Cv_radius_weak An r ->
      Cv_radius_weak Bn r.
Proof.
intros An Bn r Bn_le_An [M HM] ; exists M ; intros x [n Hn] ; subst ;
 apply Rle_trans with (gt_abs_pser An r n) ;
 [| apply HM ; exists n ; reflexivity].
 unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult ; do 2 rewrite Rabs_mult ;
 apply Rmult_le_compat_r ; [apply Rabs_pos | apply Bn_le_An].
Qed.

Lemma Cv_radius_weak_le_compat : forall (An : nat -> R) (r r' : R),
       Rabs r' <= Rabs r -> Cv_radius_weak An r -> Cv_radius_weak An r'.
Proof.
intros An r r' r'_bd [B HB].
  exists B ; intros x [i Hi] ; subst ; apply Rle_trans with (gt_abs_pser An r i).
  apply gt_abs_pser_le_compat ; assumption.
  apply HB ; exists i ; reflexivity.
Qed.

Lemma Cv_radius_weak_shifts_compat : forall An r k,
  Cv_radius_weak An r <-> Cv_radius_weak (Rseq_shifts An k) r.
Proof.
intros An r k ; split ; intros [B HB].
destruct (Req_dec r 0) as [r_eq | r_neq].
 rewrite r_eq ; exists (Rabs (An k)) ; intros x [i Hi] ; subst ;
 rewrite <- (Rseq_shifts_O An) ; apply gt_abs_pser_0_ub.
 assert (Rabs (r ^ k) <> 0) by (apply Rabs_no_R0 ; apply pow_nonzero ; assumption).
 exists (B * (/ Rabs (r ^ k))) ; intros x [i Hi] ; subst.
 apply Rle_trans with (Rseq_shifts (gt_abs_pser An r) k i * / Rabs (r ^ k)).
 unfold gt_abs_pser, gt_pser, Rseq_shifts, Rseq_abs, Rseq_mult ; simpl ;
 rewrite plus_comm, pow_add, <- Rmult_assoc, (Rabs_mult (An (i + k)%nat * r ^ i)) ;
 right ; field ; assumption.
 apply Rmult_le_compat_r ; [left ; apply Rinv_0_lt_compat ;
  assert (T := Rabs_pos (r ^k)) ; apply Rle_neq_lt ; auto|].
 apply HB ; exists (k + i)%nat ; unfold Rseq_shifts ; reflexivity.
destruct (Rseq_partial_bound (gt_pser An r) k) as [C HC] ;
 exists (Rmax (B * Rabs (r ^ k)) C) ; intros u [i Hi] ; subst.
 destruct (le_lt_dec i k) as [k_lb | k_ub].
 apply Rle_trans with C ; [apply HC | apply RmaxLess2] ; assumption.
 apply Rle_trans with (B * Rabs (r ^ k))%R ; [| apply RmaxLess1].
 destruct (lt_exist k i k_ub) as [p Hp] ; subst ; unfold gt_abs_pser, gt_pser,
 Rseq_abs, Rseq_mult ; rewrite plus_comm, pow_add, plus_comm, <- Rmult_assoc,
 Rabs_mult ; apply Rmult_le_compat_r ; [apply Rabs_pos |] ; apply HB ; exists p ;
 unfold Rseq_shifts, gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult ; reflexivity.
Qed.

Lemma Cv_radius_weak_shift_compat : forall An r,
  Cv_radius_weak An r <-> Cv_radius_weak (Rseq_shift An) r.
Proof.
intros An r ; replace (Rseq_shift An) with (Rseq_shifts An 1) by reflexivity ;
 apply Cv_radius_weak_shifts_compat.
Qed.

Lemma Cv_radius_weak_expand_compat : forall An r l,
  Cv_radius_weak An (l * r) <-> Cv_radius_weak (An_expand An l) r.
Proof.
intros An r l ; split ; intros [B HB] ; exists B ; intros x [i Hi] ; subst ;
apply HB ; exists i ; unfold An_expand, gt_abs_pser, gt_pser, Rseq_mult, Rseq_abs, Rseq_pow ;
apply Rabs_eq_compat ; rewrite Rpow_mult_distr ; ring.
Qed.

(** Compatibility of Cv_radius_weak with common operators. *)

Lemma Cv_radius_weak_scal : forall (An : Rseq) (lambda r : R), lambda <> 0 ->
  (Cv_radius_weak An r <-> Cv_radius_weak (lambda * An)%Rseq r).
Proof.
intros An lam r lam_neq ; split ; intros [B HB] ;
 [exists (Rabs lam * B) | exists (B * / (Rabs lam))] ;
 intros x [n Hn] ; subst ; unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult.

 do 2 rewrite Rabs_mult ; rewrite Rmult_assoc ;
  apply Rmult_le_compat_l ; [apply Rabs_pos |] ;
  rewrite <- Rabs_mult ; apply HB ; exists n ; reflexivity.

 apply Rle_trans with (Rabs lam * Rabs (An n * r ^ n) * / Rabs lam) ;
  [right ; field ; apply Rabs_no_R0 ; assumption |].
  rewrite <- Rabs_mult ; apply Rmult_le_compat_r ; [left ;
  apply Rinv_0_lt_compat ; apply Rabs_pos_lt ; assumption |].
  rewrite <- Rmult_assoc ; apply HB ; exists n ; reflexivity.
Qed.

Lemma Cv_radius_weak_abs : forall (An : Rseq) (r : R),
  Cv_radius_weak An r <-> Cv_radius_weak (| An |) r.
Proof.
intros An r ; split ; intros [B HB] ; exists B ; intros x [n Hn] ;
subst ; [rewrite gt_abs_pser_Rseq_abs_compat |
rewrite <- gt_abs_pser_Rseq_abs_compat] ; apply HB ; exists n ; reflexivity.
Qed.

Lemma Cv_radius_weak_plus : forall An Bn r1 r2,
  Cv_radius_weak An r1 -> Cv_radius_weak Bn r2 ->
  Cv_radius_weak (An + Bn)%Rseq (Rmin (Rabs r1) (Rabs r2)).
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
 intros x [i Hi] ; subst ; unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult, Rseq_plus.
 rewrite Rmult_plus_distr_r ; apply Rle_trans with (Rabs (An i *  Rmin (Rabs r1)
         (Rabs r2) ^ i) + Rabs (Bn i * Rmin (Rabs r1) (Rabs r2) ^ i)) ; [apply Rabs_triang |].
 apply Rle_trans with (Rabs (An i * Rmin (Rabs r1) (Rabs r2) ^ i) + C') ;
 [apply Rplus_le_compat_l ; apply HC' | apply Rplus_le_compat_r ; apply HC] ;
 exists i ; intuition.
Qed.

Lemma Cv_radius_weak_opp : forall (An : Rseq) (r : R),
  Cv_radius_weak An r <->
  Cv_radius_weak (- An)%Rseq r.
Proof.
intros An r ; split ; intros [B HB] ; exists B ; intros x [i Hi] ; subst ;
 unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult.
 unfold Rseq_opp ; rewrite Ropp_mult_distr_l_reverse, Rabs_Ropp ;
 apply HB ; exists i ; reflexivity.
 rewrite <- Rabs_Ropp, <- Ropp_mult_distr_l_reverse ; apply HB ;
 exists i ; reflexivity.
Qed.

Lemma Cv_radius_weak_minus : forall (An Bn : nat -> R) (r1 r2 : R),
  Cv_radius_weak An r1 -> Cv_radius_weak Bn r2 ->
  Cv_radius_weak (An - Bn)%Rseq (Rmin (Rabs r1) (Rabs r2)).
Proof.
intros An Bn r1 r2 RhoA RhoB.
 assert (Rho'B := proj1 (Cv_radius_weak_opp Bn _) RhoB).
 unfold Rminus ; apply Cv_radius_weak_plus ; assumption.
Qed.

Lemma Cv_radius_weak_alt : forall An r,
  Cv_radius_weak An r <-> Cv_radius_weak (Rseq_alt An) r.
Proof.
intros An r ; split ; intro rAn.
 eapply Cv_radius_weak_abs, Cv_radius_weak_ext.
  apply Rseq_abs_alt.
  rewrite <- Cv_radius_weak_abs ; assumption.
 rewrite Cv_radius_weak_abs, Cv_radius_weak_ext with (Bn := Rseq_abs (Rseq_alt An)).
  rewrite <- Cv_radius_weak_abs ; assumption.
  symmetry ; apply Rseq_abs_alt.
Qed.

(** This lemma will, together with the one about An_deriv, give us Cv_radius_weak_prod. *)

Lemma Cv_radius_weak_prod_prelim : forall An Bn r1 r2,
  Cv_radius_weak An r1 -> Cv_radius_weak Bn r2 ->
  Cv_radius_weak ((An # Bn) / Rseq_shift INR)%Rseq (Rmin (Rabs r1) (Rabs r2)).
Proof.
intros An Bn r1 r2 rAn rBn.
assert (rAn' : Cv_radius_weak An (Rmin (Rabs r1) (Rabs r2))).
 apply Cv_radius_weak_le_compat with r1.
 rewrite Rabs_pos_eq ; [apply Rmin_l | apply Rmin_pos ; apply Rabs_pos].
 assumption.
assert (rBn' : Cv_radius_weak Bn (Rmin (Rabs r1) (Rabs r2))).
 apply Cv_radius_weak_le_compat with r2.
 rewrite Rabs_pos_eq ; [apply Rmin_r | apply Rmin_pos ; apply Rabs_pos].
 assumption.
clear rAn rBn ; destruct rAn' as [B1 HB1] ; destruct rBn' as [B2 HB2] ;
 exists (B1 * B2).
assert (H1 : Rseq_bound (gt_abs_pser An (Rmin (Rabs r1) (Rabs r2))) B1).
 intro n ; apply HB1 ; exists n ; unfold gt_abs_pser, Rseq_abs ;
 rewrite Rabs_Rabsolu ; reflexivity.
assert (H2 : Rseq_bound (gt_abs_pser Bn (Rmin (Rabs r1) (Rabs r2))) B2).
 intro n ; apply HB2 ; exists n ; unfold gt_abs_pser, Rseq_abs ;
 rewrite Rabs_Rabsolu ; reflexivity.
clear HB1 HB2.
intros x [n Hn] ; subst.
 erewrite gt_abs_pser_ext ; [| eapply Rseq_div_simpl].
 rewrite gt_abs_pser_mult_compat_r.
 eapply Rle_trans ; [eapply Rmult_le_compat_r ; [unfold Rseq_abs ;
 apply Rabs_pos | eapply gt_abs_pser_prod_le_compat] |].
 eapply Rle_trans ; [| eapply Rseq_bound_prod ; try eassumption].
right ; unfold Rseq_div, Rdiv, Rseq_mult ; rewrite Rabs_mult.
 apply Rmult_eq_compat ; [| unfold Rseq_abs ; reflexivity].
symmetry ; apply Rabs_pos_eq.
unfold Rseq_prod ; apply Rseq_sum_pos_strong ; intros p p_bd.
 unfold Rseq_mult ; apply Rmult_le_pos ; apply gt_abs_pser_pos.
Qed.

(** Cv_radius_weak is compatible with zip *)

Lemma Cv_radius_weak_zip_l : forall An Bn (r : nonnegreal),
  Cv_radius_weak An r -> Cv_radius_weak Bn r -> Cv_radius_weak (Rseq_zip An Bn) (Rsqrt r).
Proof.
intros An Bn r [BAn HAn] [BBn HBn] ; exists (Rmax BAn (BBn * Rabs (Rsqrt r))) ;
 intros x [i Hi] ; subst.
 unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_zip, Rseq_mult.
  case (n_modulo_2 i) ; intros [p Hp] ; rewrite Hp.
   rewrite Rsqrt_pow_even ; transitivity BAn ;
   [apply HAn ; exists p ; reflexivity | apply RmaxLess1].
   rewrite <- tech_pow_Rmult, Rsqrt_pow_even ; transitivity (Rabs (Bn p * r ^ p) * Rabs (Rsqrt r)).
    right ; rewrite <- Rabs_mult ; apply Rabs_eq_compat ; ring.
    transitivity (BBn * Rabs (Rsqrt r)).
     apply Rmult_le_compat_r ; [apply Rabs_pos | apply HBn ; exists p ; reflexivity].
     apply RmaxLess2.
Qed.

Lemma Cv_radius_weak_zip_r1 : forall An Bn r,
  Cv_radius_weak (Rseq_zip An Bn) r -> Cv_radius_weak An (r ^ 2).
Proof.
intros An Bn r [B HB] ; exists B ; intros x [i Hi] ; subst.
 transitivity (gt_abs_pser (Rseq_zip An Bn) r (2 * i)).
 right ; unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult, Rseq_zip.
  case (n_modulo_2 (2 * i)) ; intros [p Hp].
   assert (Hip : i = p) by lia ; rewrite Hip, pow_mult ; reflexivity.
   apply False_ind ; lia.
 apply HB ; exists (2 * i)%nat ; reflexivity.
Qed.

Lemma Rabs_null_rev : forall r, Rabs r = 0 -> r = 0.
Proof.
intros r Hr ; destruct (Req_dec r 0) as [r_eq | r_neq].
 assumption.
 destruct (Rabs_no_R0 _ r_neq Hr).
Qed.

Lemma Rabs_neq_rev : forall r, Rabs r <> 0 -> r <> 0.
Proof.
intros r Hr Hf ; rewrite Hf, Rabs_R0 in Hr ; apply Hr ; reflexivity.
Qed.

Lemma Cv_radius_weak_zip_r2 : forall An Bn r,
  Cv_radius_weak (Rseq_zip An Bn) r -> Cv_radius_weak Bn (r ^ 2).
Proof.
intros An Bn r [B HB] ; destruct (Req_dec (Rabs r) 0) as [r_eq | r_neq].
 rewrite (Rabs_null_rev _ r_eq) ; simpl ; rewrite Rmult_0_l ; apply Cv_radius_weak_0.
 exists (B / Rabs r) ; intros x [i Hi] ; subst.
 transitivity (gt_abs_pser (Rseq_zip An Bn) r (S (2 * i)) / Rabs r).
 right ; unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult, Rseq_zip.
  case (n_modulo_2 (S (2 * i))) ; intros [p Hp].
   apply False_ind ; lia.
   assert (Hip : i = p) by lia ; rewrite Hip , <- pow_mult, <- tech_pow_Rmult.
   replace (Bn p * (r * r ^ (2 * p))) with (Bn p * r ^ (2 * p) * r) by ring.
   unfold Rdiv ; rewrite (Rabs_mult _ r), Rmult_assoc, Rinv_r, Rmult_1_r.
    reflexivity.
    assumption.
 apply Rmult_le_compat_r.
  left ; apply Rinv_0_lt_compat, Rabs_pos_lt, Rabs_neq_rev ; assumption.
  apply HB ; exists (S (2 * i))%nat ; reflexivity.
Qed.

(** The finite_cv_radius is exactly the upper bound. We choose our definitions
because it gives more information (the convexity of the radius for example). *)

Lemma finite_cv_radius_is_lub : forall (An : Rseq) (r : R),
  finite_cv_radius An r ->
  is_lub (Cv_radius_weak An) r.
Proof.
intros An r [rho rho_ub] ; split.

 intros r' Hr' ; destruct (Rle_lt_dec r' r) as [r'ler | rltr'].
  assumption.
  destruct (rho_ub _ rltr' Hr').

 intros r' Hr' ; destruct (Rle_lt_dec r r') as [rler' | r'ltr].
  assumption.
  assert (H : has_ub (gt_abs_pser An (middle r' r))).
   assert (r'_pos : 0 <= r').
    apply Hr' ; apply Cv_radius_weak_0.
   apply rho ; split ;
   [apply middle_le_le_pos ; [| left ; apply Rle_lt_trans with r']
   | apply middle_is_in_the_middle] ; assumption.
   assert (Hf := Hr' _ H).
   assert (Hf' : r' < middle r' r) by (apply middle_is_in_the_middle ;
    assumption).
   clear -Hf Hf' ; apply False_ind ; lra.
Qed.

(** The reciprocal implication needs the EM axiom because is_lub is not informative
enough. *)

Lemma lub_is_finite_cv_radius : (forall (P : Prop), P \/ ~P) ->
  forall (An : Rseq) (r : R),
  is_lub (Cv_radius_weak An) r ->
  finite_cv_radius An r.
Proof.
intros EM An r [rho_ub rho_l] ; split.

 intros r' [r'_pos r'_bd].
 destruct (EM (Cv_radius_weak An r')) as [P | nP].
  assumption.
  destruct (Rlt_irrefl r); apply Rle_lt_trans with r' ;
  [apply rho_l | assumption] ;
  intros b Hf ; fold (Cv_radius_weak An b) in Hf ;
  destruct (Rle_lt_dec b r') as [b_le_r' | r'_lt_b] ;
  [assumption | destruct nP] ; apply Cv_radius_weak_le_compat with b.
   rewrite Rabs_pos_eq ; [rewrite Rabs_pos_eq |] ; [left | left ;
   apply Rle_lt_trans with r' |] ; assumption.
   assumption.

 intros r' r'_lb Hf ; apply (Rlt_irrefl r) ; apply Rlt_le_trans with r' ;
  [| apply rho_ub] ; assumption.
Qed.

(** Compatibility of the finite_cv_radius concept with various operations. *)


Lemma finite_cv_radius_scal_compat : forall (An : Rseq) (lam r : R), lam <> 0 ->
  (finite_cv_radius An r <-> finite_cv_radius (lam * An)%Rseq r).
Proof.
intros An lam r lam_neq ; split ; intros [H_inf H_sup].
 split ; intros r' ; rewrite <- Cv_radius_weak_scal ;
  [apply H_inf | | apply H_sup |] ; assumption.
 split ; intros r' ; rewrite (Cv_radius_weak_scal _ lam) ;
  [apply H_inf | | apply H_sup |] ; assumption.
Qed.

Lemma finite_cv_radius_abs_compat : forall (An : Rseq) (r : R),
  finite_cv_radius An r <-> finite_cv_radius (| An |) r.
Proof.
intros An r ; split ; intros [H_inf H_sup].
 split ; intros r' ; rewrite <- Cv_radius_weak_abs ;
  [apply H_inf | apply H_sup].
 split ; intros r' ; rewrite Cv_radius_weak_abs ;
  [apply H_inf | apply H_sup] ; assumption.
Qed.

Lemma finite_cv_radius_alt_compat : forall (An : Rseq) (r : R),
  finite_cv_radius An r <-> finite_cv_radius (Rseq_alt An) r.
Proof.
intros An r ; split ; intros [r_ub r_lub] ; split.
 intros ; rewrite <- Cv_radius_weak_alt ; apply r_ub ; assumption.
 intros ; rewrite <- Cv_radius_weak_alt ; apply r_lub ; assumption.
 intros ; apply Cv_radius_weak_alt, r_ub ; assumption.
 intros ; rewrite Cv_radius_weak_alt ; apply r_lub ; assumption.
Qed. 

Lemma finite_cv_radius_pos : forall (An : Rseq) (r : R),
  finite_cv_radius An r -> 0 <= r.
Proof.
intros An r [_ Hf] ; destruct(Rle_lt_dec 0 r) as [H1 | H1] ;
 [| exfalso ; destruct (Hf 0) ; try apply Cv_radius_weak_0] ; assumption.
Qed.

Lemma finite_cv_radius_weakening : forall (An : Rseq) (r : R),
  finite_cv_radius An r ->
  forall x, Rabs x < r -> Cv_radius_weak An x.
Proof.
intros An r [H_sup _] x Hx ;
 apply Cv_radius_weak_Rabs ; apply H_sup ; split ;
 [apply Rabs_pos | assumption].
Qed.

Lemma finite_cv_radius_zip_compat_l : forall (An Bn : Rseq) (r : nonnegreal),
  finite_cv_radius An r ->
  (forall x, Rabs x < r -> Cv_radius_weak Bn x) ->
  finite_cv_radius (Rseq_zip An Bn) (Rsqrt r).
Proof.
intros An Bn r HAn HBn ; split.
 intros r' [r'_lb r'_ub] ; rewrite <- (Rsqrt_sqr r' (nnr_sqr r')).
  assert (r'2_encad : 0 <= nnr_sqr r' < r).
   split ; [apply cond_nonneg |].
    simpl ; fold (r' ^ 2) ; rewrite <- Rsqr_Rsqrt ; apply pow_lt_compat ; auto.
  apply Cv_radius_weak_zip_l.
   apply HAn ; assumption.
   apply HBn ; rewrite Rabs_right ; try apply Rle_ge ; apply r'2_encad.
   assumption.
   reflexivity.
  intros r' r'_lb Hf ; apply (proj2 HAn (r' ^ 2)), Cv_radius_weak_zip_r1 with Bn.
   rewrite <- Rsqr_Rsqrt ; apply pow_lt_compat.
    apply Rsqrt_positivity.
    assumption.
    auto.
   assumption.
Qed.

Lemma finite_cv_radius_zip_compat_r : forall (An Bn : Rseq) (r : nonnegreal),
  (forall x, Rabs x < r -> Cv_radius_weak An x) ->
  finite_cv_radius Bn r ->
  finite_cv_radius (Rseq_zip An Bn) (Rsqrt r).
Proof.
intros An Bn r HAn HBn ; split.
 intros r' [r'_lb r'_ub] ; rewrite <- (Rsqrt_sqr r' (nnr_sqr r')).
  assert (r'2_encad : 0 <= nnr_sqr r' < r).
   split ; [apply cond_nonneg |].
    simpl ; fold (r' ^ 2) ; rewrite <- Rsqr_Rsqrt ; apply pow_lt_compat ; auto.
  apply Cv_radius_weak_zip_l.
   apply HAn ; rewrite Rabs_right ; try apply Rle_ge ; apply r'2_encad.
   apply HBn ; assumption.
   assumption.
   reflexivity.
  intros r' r'_lb Hf ; apply (proj2 HBn (r' ^ 2)), Cv_radius_weak_zip_r2 with An.
   rewrite <- Rsqr_Rsqrt ; apply pow_lt_compat.
    apply Rsqrt_positivity.
    assumption.
    auto.
   assumption.
Qed.

(** Compatibility of the infinite_cv_radius concept with various operations. *)

Lemma infinite_cv_radius_zero : infinite_cv_radius 0.
Proof.
intro r ; exists 0 ; intros x [n Hn] ; subst ;
 unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult, Rseq_constant ;
 rewrite Rmult_0_l, Rabs_R0 ; reflexivity.
Qed.

Lemma infinite_cv_radius_shift_compat : forall An,
  infinite_cv_radius (Rseq_shift An) <-> infinite_cv_radius An.
Proof.
intro An ; split ; intros rAn r ;
 [ rewrite Cv_radius_weak_shift_compat
 | rewrite <- Cv_radius_weak_shift_compat ] ;
 trivial.
Qed.

Lemma infinite_cv_radius_subseq_compat : forall An Bn,
  subsequence Bn An -> infinite_cv_radius An -> infinite_cv_radius Bn.
Proof.
intros An Bn HAB HAn r ; pose (r' := Rmax (Rabs r) 1) ;
 assert (r'_pos : 0 <= r') by (apply Rmax_pos_l, Rabs_pos).
 apply Cv_radius_weak_le_compat with r'.
  rewrite (Rabs_right r') ; [apply Rmax_l | apply Rle_ge ; assumption].
  eapply Cv_radius_weak_subseq_compat.
  rewrite (Rabs_right r') ; [apply Rmax_r | apply Rle_ge ; assumption].
  eassumption.
 apply HAn.
Qed.

Lemma infinite_cv_radius_expand_compat : forall An l,
  infinite_cv_radius An -> infinite_cv_radius (An_expand An l).
Proof.
intros ; intro r ; rewrite <- Cv_radius_weak_expand_compat ; trivial.
Qed.

Lemma infinite_cv_radius_scal_compat : forall (An : Rseq) (lam : R), lam <> 0 ->
  (infinite_cv_radius An <-> infinite_cv_radius (lam * An)%Rseq).
Proof.
intros An lam lam_neq ; split ; intros rho r ;
 [rewrite <- Cv_radius_weak_scal | rewrite (Cv_radius_weak_scal _ lam)] ;
 auto.
Qed.

Lemma infinite_cv_radius_abs_compat : forall (An : Rseq),
  infinite_cv_radius An <-> infinite_cv_radius (| An |).
Proof.
intros An ; split ; intros rho r ;
 [rewrite <- Cv_radius_weak_abs | rewrite Cv_radius_weak_abs] ;
 apply rho.
Qed.

Lemma infinite_cv_radius_alt_compat : forall An,
  infinite_cv_radius An <-> infinite_cv_radius (Rseq_alt An).
Proof.
intro An ; split ; intros rAn r ;
 [rewrite <- Cv_radius_weak_alt | rewrite Cv_radius_weak_alt] ;
 apply rAn.
Qed.

Lemma infinite_cv_radius_opp_compat : forall (An : Rseq),
  infinite_cv_radius An <-> infinite_cv_radius (- An).
Proof.
intros An ; split ; intros rho r ;
 [rewrite <- Cv_radius_weak_opp | rewrite Cv_radius_weak_opp] ;
 apply rho.
Qed.

Section icvr_properties.

Variables (An Bn : Rseq).
Hypotheses (rAn : infinite_cv_radius An) (rBn : infinite_cv_radius Bn).

Lemma infinite_cv_radius_plus_compat : infinite_cv_radius (An + Bn).
Proof.
intro r ; rewrite <- Cv_radius_weak_Rabs, <- Rmin_diag ;
 apply Cv_radius_weak_plus ; [apply rAn | apply rBn].
Qed.

Lemma infinite_cv_radius_minus_compat : infinite_cv_radius (An - Bn).
Proof.
intro r ; rewrite <- Cv_radius_weak_Rabs, <- Rmin_diag ;
 apply Cv_radius_weak_minus ; [apply rAn | apply rBn].
Qed.

Lemma infinite_cv_radius_zip_compat_l : infinite_cv_radius (Rseq_zip An Bn).
Proof.
intro r ; apply Cv_radius_weak_Rabs ; rewrite <- Rsqrt_sqr with (y := nnr_sqr (Rabs r)).
 apply Cv_radius_weak_zip_l ; [apply rAn | apply rBn].
 apply Rabs_pos.
 reflexivity.
Qed.

End icvr_properties.

Lemma infinite_cv_radius_zip_compat_r1 : forall An Bn,
 infinite_cv_radius (Rseq_zip An Bn) -> infinite_cv_radius An.
Proof.
intros An Bn rAnBn r ; apply Cv_radius_weak_Rabs ;
 replace (Rabs r) with (nonneg (nnr_abs r)) by reflexivity ; 
 rewrite <- Rsqr_Rsqrt with (nnr_abs r).
 eapply Cv_radius_weak_zip_r1, rAnBn.
Qed.

Lemma infinite_cv_radius_zip_compat_r2 : forall An Bn,
 infinite_cv_radius (Rseq_zip An Bn) -> infinite_cv_radius Bn.
Proof.
intros An Bn rAnBn r ; apply Cv_radius_weak_Rabs ;
 replace (Rabs r) with (nonneg (nnr_abs r)) by reflexivity ; 
 rewrite <- Rsqr_Rsqrt with (nnr_abs r).
 eapply Cv_radius_weak_zip_r2, rAnBn.
Qed.

(** Pser and Un_cv are linked. See "tech12" for the reciprocal lemma *)

Lemma Pser_Rpser_link : forall An x l, Pser An x l <-> Rpser An x l.
Proof.
intros An x l ; split ; intro Hyp ; apply Hyp.
Qed.

Lemma Rpser_scal_compat : forall (r : R) An x l,
  Rpser An x l -> Rpser (r * An)%Rseq x (r * l).
Proof.
intros r An x l Hl eps eps_pos ; destruct (Req_dec r 0) as [Heq | Hneq].
exists O ; intros ; unfold R_dist ; rewrite Rseq_pps_scal_compat_l ;
 unfold Rseq_mult, Rseq_constant ; rewrite <- Rmult_minus_distr_l, Rabs_mult,
 Heq, Rabs_R0, Rmult_0_l ; assumption.
 pose (eps' := eps / Rabs r).
assert (eps'_pos : 0 < eps') by (unfold eps', Rdiv ;
  apply Rlt_mult_inv_pos ; [| apply Rabs_pos_lt] ; assumption).
 destruct (Hl eps' eps'_pos) as [N HN] ; exists N ; intros ; unfold R_dist ;
  rewrite Rseq_pps_scal_compat_l ; unfold Rseq_mult, Rseq_constant ;
  rewrite <- Rmult_minus_distr_l, Rabs_mult ; apply Rlt_le_trans with (Rabs r * eps').
  apply Rmult_lt_compat_l ; [apply Rabs_pos_lt | apply HN] ; assumption.
  right ; unfold eps' ; field ; apply Rabs_no_R0 ; assumption.
Qed.

Lemma Rpser_opp_compat : forall An x l,
  Rpser An x l -> Rpser (- An)%Rseq x (-l).
Proof.
intros An x l Hl eps eps_pos ; destruct (Hl _ eps_pos) as [N HN] ;
 exists N ; intros n n_lb ; unfold R_dist, Rminus in * ;
 rewrite Rseq_pps_opp_compat ; unfold Rseq_opp ; rewrite <- Ropp_plus_distr,
  Rabs_Ropp ; apply HN ; assumption.
Qed.

Lemma Rpser_add_compat : forall An Bn x la lb,
  Rpser An x la -> Rpser Bn x lb -> Rpser (An + Bn)%Rseq x (la + lb).
Proof.
intros An Bn x la lb Hla Hlb eps eps_pos.
 pose (eps' := middle 0 eps) ; assert (eps'_pos : 0 < eps')
 by (apply middle_is_in_the_middle ; assumption).
 destruct (Hla _ eps'_pos) as [Na HNa] ;
 destruct (Hlb _ eps'_pos) as [Nb HNb] ;
 exists (max Na Nb) ; intros n n_lb.
 rewrite Rseq_pps_plus_compat ; eapply Rle_lt_trans.
 eapply R_dist_plus.
 apply Rlt_le_trans with (eps' + eps').
  eapply Rlt_trans.
   eapply Rplus_lt_compat_l ; eapply HNb ;
    apply le_trans with (max Na Nb) ; [apply le_max_r | assumption].
   apply Rplus_lt_compat_r ; apply HNa ;
    apply le_trans with (max Na Nb) ; [apply le_max_l | assumption].
  right ; unfold eps', middle ; field.
Qed.

Lemma Rpser_minus_compat : forall An Bn x la lb,
  Rpser An x la -> Rpser Bn x lb -> Rpser (An - Bn)%Rseq x (la - lb).
Proof.
intros ; unfold Rseq_minus, Rminus ; apply Rpser_add_compat ;
 [| apply Rpser_opp_compat] ; assumption.
Qed.

Lemma Rpser_zip_compat : forall An Bn x la lb,
  Rpser An (x ^ 2) la -> Rpser Bn (x ^ 2) lb ->
  Rpser (Rseq_zip An Bn) x (la + x * lb).
Proof.
intros An Bn x la lb Hla Hlb ; unfold Rpser ; apply Rseq_cv_even_odd_compat.
 apply Rseq_cv_shift_compat ; rewrite Rseq_cv_eq_compat ;
  [| intro n ; apply Rseq_pps_zip_compat_even].
  apply Rseq_cv_plus_compat, Rseq_cv_mult_compat ; [| apply Rseq_constant_cv | apply Hlb].
  apply Rseq_cv_shift_compat_reciprocal, Hla.
 rewrite Rseq_cv_eq_compat ; [| intro n ; apply Rseq_pps_zip_compat_odd].
 apply Rseq_cv_plus_compat, Rseq_cv_mult_compat ; (assumption || apply Rseq_constant_cv).
Qed.

Lemma Rpser_alt_compat : forall An x la,
  Rpser An (- x) la -> Rpser (Rseq_alt An) x la.
Proof.
intros An x la Hla ; eapply Rseq_cv_eq_compat.
 apply Rseq_pps_alt_compat.
 assumption.
Qed.

Lemma Rpser_expand_compat : forall An l x la,
  Rpser An (l * x) la -> Rpser (An_expand An l) x la.
Proof.
intros ; eapply Rseq_cv_eq_compat.
 eapply Rseq_sum_ext ; intro ; apply gt_pser_expand_compat.
 assumption.
Qed.

Lemma Rpser_unique : forall An (x l1 l2 : R),
  Rpser An x l1 -> Rpser An x l2 -> l1 = l2.
Proof.
intros ; eapply Rseq_cv_unique ; eassumption.
Qed.

Lemma Rpser_unique_extentionality : forall An Bn (x l1 l2 : R),
  An == Bn -> Rpser An x l1 -> Rpser Bn x l2 -> l1 = l2.
Proof.
intros An Bn x l1 l2 Heq Hl1 Hl2 ; eapply Rseq_cv_unique ;
 [rewrite Rseq_cv_eq_compat |] ; [| eapply Rseq_pps_ext ; symmetry |] ;
 eassumption.
Qed.
