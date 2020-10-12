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
Require Import Rsequence_def Rsequence_base_facts Rsequence_cv_facts Rsequence_rewrite_facts.
Require Import Rpser_def Rpser_def_simpl.
Require Import MyRIneq MyNat Lra.

Open Scope R_scope.
Open Scope Rseq_scope.

(** * Rseq_sum properties *)

(** Basic properties *)

Lemma Rseq_sum_ext_strong : forall Un Vn n,
  (forall p, (p <= n)%nat -> Un p = Vn p) ->
  Rseq_sum Un n = Rseq_sum Vn n.
Proof.
intros Un Vn n ; induction n ; intro Heq.
 simpl ; apply Heq ; trivial.
 do 2 rewrite Rseq_sum_simpl ; rewrite IHn, Heq.
  reflexivity.
  trivial.
  intros ; apply Heq ; auto.
Qed.

Lemma Rseq_sum_ext : forall Un Vn,
  Un == Vn -> Rseq_sum Un == Rseq_sum Vn.
Proof.
intros Un Vn Heq n ; apply Rseq_sum_ext_strong ; trivial.
Qed.

Lemma Rseq_sum_scal_compat_l : forall (l : R) Un,
  Rseq_sum (l * Un) == l * (Rseq_sum Un).
Proof.
intros l Un n ; induction n.
 reflexivity.
 simpl ; rewrite IHn ;
  unfold Rseq_mult, Rseq_constant ;
  simpl ; ring.
Qed.

(** Compatibility with common operations *)

Lemma Rseq_sum_constant_compat: forall (l : R) n,
  (Rseq_sum l n = INR (S n) * l)%R.
Proof.
intros l n ; induction n.
 simpl ; symmetry ; apply Rmult_1_l.
 rewrite Rseq_sum_simpl, S_INR, IHn ; unfold Rseq_constant ; ring.
Qed.

Lemma Rseq_sum_scal_compat_r : forall (l : R) Un,
  Rseq_sum (Un * l) == Rseq_sum Un * l.
Proof.
intros l Un n ; induction n.
 reflexivity.
 simpl ; rewrite IHn ;
  unfold Rseq_mult, Rseq_constant ;
  simpl ; ring.
Qed.

Lemma Rseq_sum_opp_compat : forall Un,
  Rseq_sum (- Un) == - Rseq_sum Un.
Proof.
intros Un n ; induction n.
 reflexivity.
 simpl ; rewrite IHn ;
  unfold Rseq_opp ;
  simpl ; ring.
Qed.

Lemma Rseq_sum_plus_compat : forall Un Vn,
  Rseq_sum (Un + Vn) == Rseq_sum Un + Rseq_sum Vn.
Proof.
intros Un Vn n ; induction n.
 reflexivity.
 simpl ; rewrite IHn ;
  unfold Rseq_plus ; simpl ;
  ring.
Qed.

Lemma Rseq_sum_minus_compat : forall Un Vn,
  Rseq_sum (Un - Vn) == Rseq_sum Un - Rseq_sum Vn.
Proof.
intros Un Vn n ; rewrite Rseq_sum_ext with (Un - Vn) (Un + (- Vn)) _,
 Rseq_sum_plus_compat.
 unfold Rseq_plus, Rseq_minus ; rewrite Rseq_sum_opp_compat ; reflexivity.
 unfold Rseq_minus ; intro ; reflexivity.
Qed.

Lemma Rseq_sum_shift_compat : forall Un n,
  Rseq_sum (Rseq_shift Un) n = (Rseq_shift (Rseq_sum Un) n - Un O)%R.
Proof.
intros Un n ; induction n ;
 [| simpl ; rewrite IHn] ;
 unfold Rseq_shift, Rseq_minus ; simpl ; ring.
Qed.

Lemma Rseq_sum_shifts_compat : forall Un k n,
  Rseq_sum (Rseq_shifts Un (S k)) n = (Rseq_shifts (Rseq_sum Un) (S k) n - Rseq_sum Un k)%R.
Proof.
intros Un k n ; induction n.
 unfold Rseq_shifts, Rseq_minus ; simpl ; rewrite plus_0_r ; ring.
 simpl ; rewrite IHn ; unfold Rseq_minus, Rseq_shifts ;
  simpl ; rewrite <- (plus_n_Sm k n) ; simpl ; ring.
Qed.

Lemma Rseq_sum_split_compat : forall Un k n, (k < n)%nat ->
  (Rseq_sum Un n = Rseq_sum Un k + Rseq_sum (Rseq_shifts Un (S k)) (n - S k))%R.
Proof.
intros Un k n kltn ; rewrite Rseq_sum_shifts_compat ; ring_simplify.
 unfold Rseq_shifts ; rewrite le_plus_minus_r ; [reflexivity | lia].
Qed.

Lemma Rseq_sum_reindex_compat : forall Un n,
  Rseq_sum Un n = Rseq_sum (fun i => Un (n - i)%nat) n.
Proof.
intros Un n ; revert Un ; induction n ; intro Un.
 reflexivity.
 do 2 rewrite Rseq_sum_simpl.
 rewrite (IHn (fun i => Un (S n - i)%nat)), minus_diag.
 rewrite (Rseq_sum_ext_strong (fun i => Un (S n - (n - i))%nat) (Rseq_shift Un)).
 rewrite Rseq_sum_shift_compat ; unfold Rseq_shift ; simpl ; ring.
 intros m m_bd ; unfold Rseq_shift ; replace (S n - (n - m))%nat with (S m) by lia ;
 reflexivity.
Qed.

Lemma Rseq_prod_comm: forall An Bn, (An # Bn == Bn # An)%Rseq.
Proof.
intros An Bn n ; unfold Rseq_prod, Rseq_mult ;
 rewrite Rseq_sum_reindex_compat ; apply Rseq_sum_ext_strong ;
 intros p p_ub ; replace (n - (n - p))%nat with p by lia ;
 ring.
Qed.

Lemma Rseq_sum_prod_compat: forall An Bn n,
  Rseq_sum (An # Bn) n =
  Rseq_sum (fun i => (Rseq_sum Bn i) * An (n - i)%nat)%R n.
Proof.
intros An Bn n ; induction n.
 unfold Rseq_prod, Rseq_mult ; simpl ; apply Rmult_comm.
 transitivity (Rseq_sum ((fun i => (An i * (Rseq_sum Bn (n - i)%nat))%R) +
  (fun i => (An i * Bn (S (n - i))%nat))%R)%Rseq n + An (S n) * Bn O)%R.
 rewrite Rseq_sum_plus_compat, Rseq_sum_simpl, IHn ; unfold Rseq_plus ;
 rewrite Rplus_assoc ; apply Rplus_eq_compat.
 rewrite Rseq_sum_reindex_compat ; apply Rseq_sum_ext_strong ;
  intros p p_ub ; replace (n - (n - p))%nat with p by lia ; apply Rmult_comm.
 replace O with ((S n) - S n)%nat by lia ; unfold Rseq_prod ;
  rewrite Rseq_sum_simpl ; apply Rplus_eq_compat_r ; apply Rseq_sum_ext_strong ;
  intros p p_ub ; unfold Rseq_mult ; replace (S n - p)%nat with (S (n - p)) by lia ;
  reflexivity.
 transitivity (Rseq_sum (fun i => (An i * (Rseq_sum Bn (S n - i)))%R) (S n)).
 rewrite Rseq_sum_simpl, minus_diag ; apply Rplus_eq_compat ; [| trivial].
 apply Rseq_sum_ext_strong ; intros p p_ub ; unfold Rseq_plus ;
 replace (S n - p)%nat with (S (n - p)) by lia ; rewrite Rseq_sum_simpl ; ring.
 rewrite Rseq_sum_reindex_compat ; apply Rseq_sum_ext_strong ; intros p p_ub ;
 replace (S n - (S n - p))%nat with p by lia ; apply Rmult_comm.
Qed.

Lemma two_Sn : forall n, (2 * S n = S (S (2 * n)))%nat.
Proof.
intro n ; ring.
Qed.

Lemma Rseq_sum_zip_compat_odd : forall An Bn n,
  (Rseq_sum (Rseq_zip An Bn) (S (2 * n)) = Rseq_sum An n + Rseq_sum Bn n)%R.
Proof.
intros An Bn ; induction n.
 unfold Rseq_zip ; simpl.
  case (n_modulo_2 0) ; intros [p Hp] ; [| apply False_ind ; lia].
  case (n_modulo_2 1) ; intros [q Hq] ; [apply False_ind ; lia |].
  assert (Hp' : p = O) by lia ; assert (Hq' : q = O) by lia ; subst ; reflexivity.
 rewrite two_Sn ; do 2 rewrite Rseq_sum_simpl ; rewrite IHn ; do 2 rewrite Rseq_sum_simpl.
  repeat rewrite Rplus_assoc ; apply Rplus_eq_compat_l.
  rewrite (Rplus_comm (An (S n))), Rplus_assoc ; apply Rplus_eq_compat_l.
  rewrite Rplus_comm, <- two_Sn ; apply Rplus_eq_compat ; unfold Rseq_zip ;
   [ case (n_modulo_2 (S (2 * S n))) ; intros [p Hp] ; [apply False_ind ; lia |] |
     case (n_modulo_2 (2 * S n)) ; intros [p Hp] ; [| apply False_ind ; lia] ] ;
   assert (Hp' : p = S n) by lia ; subst ; reflexivity.
Qed.

Lemma Rseq_sum_zip_compat_even : forall An Bn n,
  (Rseq_sum (Rseq_zip An Bn) (2 * S n) = Rseq_sum An (S n) + Rseq_sum Bn n)%R.
Proof.
intros An Bn n ; rewrite two_Sn, Rseq_sum_simpl, Rseq_sum_zip_compat_odd,
 Rseq_sum_simpl, <- two_Sn ; unfold Rseq_zip.
 case (n_modulo_2 (2 * S n)) ; intros [p Hp] ; [| apply False_ind ; lia].
 assert (Hp' : p = S n) by lia ; subst ; ring.
Qed.

(** Compatibility with the orders *)

Lemma Rseq_sum_pos_strong : forall An n,
  (forall p, (p <= n)%nat -> 0 <= An p) ->
  0 <= Rseq_sum An n.
Proof.
intros An n ; induction n ; intro Hpos.
 simpl ; apply Hpos ; trivial.
 rewrite Rseq_sum_simpl ; apply Rplus_le_le_0_compat ;
 [apply IHn ; intros p p_bd |] ; apply Hpos ; lia.
Qed.

Lemma Rseq_sum_pos: forall An n,
 (forall n, 0 <= An n) ->  0 <= Rseq_sum An n.
Proof.
intros ; apply Rseq_sum_pos_strong ; trivial.
Qed.

Lemma Rseq_sum_le_compat_strong: forall An Bn n,
 (forall p, (p <= n)%nat -> An p <= Bn p) ->
 Rseq_sum An n <= Rseq_sum Bn n.
Proof.
intros An Bn n Hle ; induction n.
 simpl ; apply Hle ; trivial.
 simpl ; transitivity (Rseq_sum Bn n + An (S n))%R.
  apply Rplus_le_compat_r ; apply IHn ; auto.
  apply Rplus_le_compat_l ; apply Hle ; trivial.
Qed.

Lemma Rseq_sum_le_compat: forall An Bn n,
 (forall n, An n <= Bn n) -> Rseq_sum An n <= Rseq_sum Bn n.
Proof.
intros ; apply Rseq_sum_le_compat_strong ; trivial.
Qed.

Lemma Rseq_sum_lt_compat_strong: forall An Bn n,
 (forall p, (p <= n)%nat -> An p < Bn p) ->
 Rseq_sum An n < Rseq_sum Bn n.
Proof.
intros An Bn n Hlt ; induction n.
 simpl ; apply Hlt ; trivial.
 simpl ; transitivity (Rseq_sum Bn n + An (S n))%R.
  apply Rplus_lt_compat_r ; apply IHn ; auto.
  apply Rplus_lt_compat_l ; apply Hlt ; trivial.
Qed.

Lemma Rseq_sum_lt_compat: forall An Bn n,
 (forall n, An n < Bn n) -> Rseq_sum An n < Rseq_sum Bn n.
Proof.
intros ; apply Rseq_sum_lt_compat_strong ; trivial.
Qed.

Lemma Rseq_sum_triang: forall An n,
  Rabs (Rseq_sum An n) <= Rseq_sum (| An |) n.
Proof.
intros An n ; induction n.
 unfold Rseq_abs ; simpl ; reflexivity.
 do 2 rewrite Rseq_sum_simpl ; eapply Rle_trans ;
 [eapply Rabs_triang |] ; apply Rplus_le_compat ;
 [assumption | reflexivity].
Qed.

Lemma Rseq_sum_lower_bound : forall An n lb,
  (forall m, (m <= n)%nat -> lb <= An m) ->
  INR (S n) * lb <= Rseq_sum An n.
Proof.
intros An n lb HAn ; induction n.
 simpl ; rewrite Rmult_1_l ; apply HAn ; reflexivity.
 rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l, Rseq_sum_simpl ;
  apply Rplus_le_compat ; [apply IHn | apply HAn ; reflexivity].
  intros m m_lb ; apply HAn ; lia.
Qed.

Lemma Rseq_sum_upper_bound : forall An n ub,
  (forall m, (m <= n)%nat -> An m <= ub) ->
  Rseq_sum An n <= INR (S n) * ub.
Proof.
intros An n ub HAn ; induction n.
 simpl ; rewrite Rmult_1_l ; apply HAn ; reflexivity.
 rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l, Rseq_sum_simpl ;
  apply Rplus_le_compat ; [apply IHn | apply HAn ; reflexivity].
  intros m m_lb ; apply HAn ; lia.
Qed.

(** Convergence to infinity *)

Lemma Rseq_cv_pos_infty_criteria : forall An d, 0 < d ->
  (forall n, 0 <= An n) ->
  (forall M, exists N, (N >= M)%nat /\ d <= Rseq_sum (Rseq_shifts An M) (N - M)) ->
  Rseq_cv_pos_infty (Rseq_sum An).
Proof.
intros An d d_pos An_pos HAn.
 assert (HAn' : forall M, exists N, forall n, (N < n)%nat -> INR M * d <= Rseq_sum An n).
  intro M ; induction M.
   destruct (HAn O) as [N [_ HN]] ; exists N.
   intros n n_lb ; simpl ; rewrite Rmult_0_l.
    rewrite (Rseq_sum_split_compat _ _ _ n_lb) ; apply Rplus_le_le_0_compat.
     transitivity d.
      left ; assumption.
      rewrite (minus_n_O N) ;  erewrite Rseq_sum_ext ;
       [| symmetry ; eapply Rseq_shifts_0 ] ; assumption.
     apply Rseq_sum_pos ; intros ; apply An_pos.
    destruct IHM as [N HN] ; destruct (HAn (S (S N))) as [N' [N'_lb HN']] ; exists N' ;
     assert (N'_lb' : (S N < N')%nat) by lia.
    intros n n_lb ; rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l,
     (Rseq_sum_split_compat _ _ _ n_lb), (Rseq_sum_split_compat _ _ _ N'_lb'),
     Rplus_assoc.
    apply Rplus_le_compat.
     apply HN ; auto.
     rewrite <- (Rplus_0_r d) ; apply Rplus_le_compat.
      apply HN'.
      apply Rseq_sum_pos ; intros ; apply An_pos.
 intro B ; pose (M := up (Rabs B / d)) ; destruct (archimed (Rabs B / d)) as [HB _].
  assert (M_pos : (0 <= M)%Z).
   apply le_IZR ; simpl ; eapply Rle_trans ; [| left ; eassumption].
   apply Rle_mult_inv_pos ; [apply Rabs_pos | assumption].
  destruct (IZN _ M_pos) as [M' HM'] ; destruct (HAn' M') as [N HN] ; exists (S N) ; intros n n_lb.
   apply Rlt_le_trans with (INR M' * d)%R ; [| apply HN ; lia].
   apply Rle_lt_trans with (Rabs B) ; [apply Rle_abs |].
   rewrite <- (Rmult_1_r (Rabs B)), <- (Rinv_l d), <- Rmult_assoc, INR_IZR_INZ, <- HM'.
   apply Rmult_lt_compat_r ; [assumption | apply HB].
   apply Rgt_not_eq ; assumption.
Qed.

Lemma Rseq_cv_neg_infty_criteria : forall An d, d < 0 ->
  (forall n, An n <= 0) ->
  (forall M, exists N, (N >= M)%nat /\ Rseq_sum (Rseq_shifts An M) (N - M) <= d) ->
  Rseq_cv_neg_infty (Rseq_sum An).
Proof.
intros An d d_neg An_neg HAn ; apply Rseq_cv_neg_infty_eq_compat with (- Rseq_sum (- An)).
 intro n ; unfold Rseq_opp at 1 ; rewrite Rseq_sum_opp_compat ; unfold Rseq_opp ;
 apply Ropp_involutive.
 apply Rseq_cv_pos_infty_opp_compat, Rseq_cv_pos_infty_criteria with (- d)%R.
  lra.
  intro n ; unfold Rseq_opp ; pose (An_neg n) ; lra.
  intro M ; destruct (HAn M) as [N [N_lb HN]] ; exists N ; split.
   assumption.
   rewrite Rseq_sum_ext with (Vn := - Rseq_shifts An M).
    rewrite Rseq_sum_opp_compat ; apply Ropp_le_contravar, HN.
    apply Rseq_shifts_opp_compat.
Qed.

(** Partition *)

Lemma Rseq_sum_even_odd_split : forall (An : Rseq) n,
  (Rseq_sum (fun i => An (2 * i)%nat) n +
  Rseq_sum (fun i => An (S (2 * i))%nat) n
  = Rseq_sum An (S (2 * n)))%R.
Proof.
intros An n ; induction n.
 reflexivity.
 replace (2 * (S n))%nat with (S (S (2 * n))) by ring.
 do 4 rewrite Rseq_sum_simpl.
 replace (2 * (S n))%nat with (S (S (2 * n))) by ring.
 rewrite <- IHn ; ring.
Qed.

Lemma Rseq_sum_even_odd_split' : forall An n,
  (Rseq_sum (fun i => An (2 * i)%nat) (S n) +
  Rseq_sum (fun i => An (S (2 * i))) n
  = Rseq_sum An (2 * (S n)))%R.
Proof.
intros An n ; replace (2 * S n)%nat with (S (S (2 * n))) by ring ;
 do 2 rewrite Rseq_sum_simpl ; rewrite <- Rseq_sum_even_odd_split ;
 replace (2 * S n)%nat with (S (S (2 * n))) by ring ; ring.
Qed.

(** * Rseq_pps : compatibility with common operations. *)

Section Rseq_pps_facts.

Lemma Rseq_pps_simpl : forall An x n,
  Rseq_pps An x (S n) = (Rseq_pps An x n + (An (S n) * pow x (S n)))%R.
Proof.
intros ; reflexivity.
Qed.

Lemma Rseq_pps_0_simpl : forall An n,
 Rseq_pps An 0 n = An O.
Proof.
intros An n ; induction n.
 unfold Rseq_pps, gt_pser, Rseq_mult ; simpl ;
  rewrite Rmult_1_r ; reflexivity.
 rewrite Rseq_pps_simpl, IHn, pow_i ; [ring | lia].
Qed.

Lemma Rseq_pps_O_simpl : forall An x,
  Rseq_pps An x O = An O.
Proof.
intros An x ; unfold Rseq_pps ; apply gt_pser_0.
Qed.

Lemma Rseq_pps_ext : forall An Bn x,
  (An == Bn)%Rseq ->
  (Rseq_pps An x == Rseq_pps Bn x)%Rseq.
Proof.
intros An Bn x Hext ; apply Rseq_sum_ext ;
 intro n ; unfold gt_pser, Rseq_mult ; rewrite Hext ;
 reflexivity.
Qed.

Lemma Rseq_pps_scal_compat_l : forall (l : R) An x,
  (Rseq_pps (l * An) x == l * Rseq_pps An x)%Rseq.
Proof.
intros l An x n ; unfold Rseq_pps ;
 rewrite Rseq_sum_ext with _ (l * (An * (pow x)))%Rseq _.
 apply Rseq_sum_scal_compat_l.
 clear ; intro n ; unfold gt_pser, Rseq_mult, Rseq_constant ;
  ring.
Qed.

Lemma Rseq_pps_scal_compat_r : forall (l : R) An x,
  (Rseq_pps (An * l) x == Rseq_pps An x * l)%Rseq.
Proof.
intros l An x n ; unfold Rseq_pps ;
 rewrite Rseq_sum_ext with _ ((An * (pow x)) * l)%Rseq _.
 apply Rseq_sum_scal_compat_r.
 clear ; intro n ; unfold gt_pser, Rseq_mult, Rseq_constant ;
  ring.
Qed.

Lemma Rseq_pps_opp_compat : forall An x,
  (Rseq_pps (- An) x == - Rseq_pps An x)%Rseq.
Proof.
intros An x n ; unfold Rseq_pps ;
 rewrite Rseq_sum_ext with _ (- (An * (pow x))) _.
 apply Rseq_sum_opp_compat.
 clear ; intro n ; unfold gt_pser, Rseq_mult, Rseq_opp ;
  ring.
Qed.

Lemma Rseq_pps_plus_compat : forall An Bn x,
  Rseq_pps (An + Bn) x == Rseq_pps An x + Rseq_pps Bn x.
Proof.
intros An Bn x n ; unfold Rseq_pps ;
 rewrite Rseq_sum_ext with _ ((An * (pow x)) + (Bn * (pow x))) _.
 apply Rseq_sum_plus_compat.
 clear ; intro n ; unfold gt_pser, Rseq_mult, Rseq_plus ;
  ring.
Qed.

Lemma Rseq_pps_abs_unfold : forall An x,
  Rseq_pps_abs An x == Rseq_pps (| An |) (Rabs x).
Proof.
intros An x ; apply Rseq_sum_ext ; apply gt_abs_pser_unfold.
Qed.

Lemma Rseq_pps_prod_unfold: forall An Bn x,
  Rseq_pps (An # Bn) x == Rseq_sum (gt_pser An x # (gt_pser Bn x)).
Proof.
intros An Bn x n ; induction n.
 unfold Rseq_pps, gt_pser, Rseq_prod, Rseq_mult ; simpl ; ring.
 rewrite Rseq_sum_simpl, Rseq_pps_simpl, IHn ; apply Rplus_eq_compat_l.
 etransitivity.
 symmetry ; eapply (Rseq_sum_scal_compat_r _ _ (S n)).
 apply Rseq_sum_ext_strong ; fold (pow x (S n)) ; intros p p_lb ;
 unfold gt_pser, Rseq_mult, Rseq_constant.
 replace (S n) with (p + (S n - p))%nat by lia ; rewrite pow_add ;
 replace (p + (S n - p) -p)%nat with (S n - p)%nat by lia ; ring.
Qed.

Lemma Rseq_pps_zip_compat_odd : forall An Bn x n,
  (Rseq_pps (Rseq_zip An Bn) x (S (2 * n)) =
  Rseq_pps An (x ^ 2) n + x * Rseq_pps Bn (x ^ 2) n)%R.
Proof.
intros An Bn x n ; unfold Rseq_pps ; erewrite Rseq_sum_ext ; [| eapply gt_pser_zip_compat] ;
 rewrite Rseq_sum_zip_compat_odd, Rseq_sum_scal_compat_l ; reflexivity.
Qed.

Lemma Rseq_pps_zip_compat_even : forall An Bn x n,
  (Rseq_pps (Rseq_zip An Bn) x (2 * S n) =
  Rseq_pps An (x ^ 2) (S n) + x * Rseq_pps Bn (x ^ 2) n)%R.
Proof.
intros An Bn x n ; unfold Rseq_pps ; erewrite Rseq_sum_ext ; [| eapply gt_pser_zip_compat] ;
 rewrite Rseq_sum_zip_compat_even, Rseq_sum_scal_compat_l ; reflexivity.
Qed.

Lemma unfold_Ropp : forall x, (- x = - 1 * x)%R.
Proof.
intros ; ring.
Qed.

Lemma Rseq_pps_alt_compat : forall An x,
  Rseq_pps (Rseq_alt An) x == Rseq_pps An (- x).
Proof.
intros An x n ; induction n.
 do 2 rewrite Rseq_pps_O_simpl ; unfold Rseq_alt, Rseq_mult, Rseq_pow ;
  apply Rmult_1_l.
 do 2 rewrite Rseq_pps_simpl ; rewrite IHn ; apply Rplus_eq_compat_l.
  unfold Rseq_alt, Rseq_mult, Rseq_pow ;
  rewrite (unfold_Ropp x), Rpow_mult_distr ; ring.
Qed.

(** * Rpser_abs, Rpser *)

Lemma Rpser_abs_unfold : forall An r l,
  Rpser_abs An r l <-> Rpser (| An |) (Rabs r) l.
Proof.
intros An r l ; split ; intro Hyp ; unfold Rpser, Rpser_abs ;
assert (tmp := Rseq_pps_abs_unfold An r) ; eapply Rseq_cv_eq_compat ;
eauto ; symmetry ; assumption.
Qed.

End Rseq_pps_facts.
