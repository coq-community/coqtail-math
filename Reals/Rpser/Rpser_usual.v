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

Require Import MyReals MyINR.
Require Import Rsequence_def Rsequence_facts Rsequence_cv_facts Rsequence_sums_facts.
Require Import Rsequence_base_facts Rsequence_rewrite_facts Rsequence_usual_facts.

Require Import Max.
Require Import Fourier.

Require Import Rpser_def Rpser_def_simpl Rpser_base_facts Rpser_cv_facts Rpser_radius_facts.
Require Import Rpser_sums Rpser_derivative Rpser_derivative_facts.

Require Import Rfunction_def Functions.

Open Scope R_scope.

(** * Definition of the null power series. *)

Definition zero_seq := 0%Rseq.

Lemma zero_infinite_cv_radius : infinite_cv_radius zero_seq.
Proof.
intro r ; exists 0 ; intros x [n Hn] ; subst ;
 unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult, Rseq_constant ;
 rewrite Rmult_0_l, Rabs_R0 ; reflexivity.
Qed.

Lemma Pser_zero_seq : forall (x : R), Pser (zero_seq) x 0.
Proof.
intros x eps eps_pos ; exists O ; intros n _ ; unfold R_dist ;
 apply Rle_lt_trans with (Rabs 0) ; [right ; apply Rabs_eq_compat |
 rewrite Rabs_R0 ; assumption].
 unfold Rminus ; rewrite Ropp_0, Rplus_0_r ; induction n ; simpl ;
 [| rewrite IHn] ; unfold zero_seq, Rseq_constant ; ring.
Qed.

Definition zero := sum _ zero_infinite_cv_radius.

Lemma zero_is_zero : forall x, zero x = 0.
Proof.
intro x ;
 assert (Hl := sum_sums _ zero_infinite_cv_radius x) ;
 assert (Hr := Pser_zero_seq x) ;
 apply (Rpser_unique _ _ _ _ Hl Hr).
Qed.

(** * Definition of the constant power series. *)

Definition constant_seq (r : R) (n : nat) := if eq_nat_dec n 0 then r else 0.

Lemma constant_infinite_cv_radius : forall (r : R),
  infinite_cv_radius (constant_seq r).
Proof.
intros r n ; exists (Rabs r) ; intros x [i Hi] ; subst ;
 unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult, constant_seq ;
 destruct i ; simpl ; [rewrite Rmult_1_r ; right ; reflexivity |
 rewrite Rmult_0_l, Rabs_R0 ; apply Rabs_pos].
Qed.

Lemma Pser_constant_seq : forall (r : R) (x : R), Pser (constant_seq r) x r.
Proof.
intros r x.
  assert (Hrew : forall n, sum_f_R0 (fun n => (constant_seq r) n * x ^ n) n = r).
   induction n.
   unfold constant_seq ; simpl ; apply Rmult_1_r.
   simpl ; rewrite IHn ; unfold constant_seq ; simpl ; rewrite Rmult_0_l, Rplus_0_r ;
   reflexivity.
intros eps eps_pos ; exists O ; intros n n_lb ; rewrite Hrew, R_dist_eq ;
 assumption.
Qed.

Definition constant (r : R) := sum _ (constant_infinite_cv_radius r).

Lemma constant_is_cst : forall (r : R),
  constant r == (fun _ => r).
Proof.
intros r x ;
 assert (Hl := sum_sums _ (constant_infinite_cv_radius r) x) ;
 assert (Hr := Pser_constant_seq r x) ;
 apply (Rpser_unique _ _ _ _ Hl Hr).
Qed.

(** * Definition of the identity *)

Definition identity_seq (n : nat) := if eq_nat_dec n 1 then 1 else 0.

Lemma identity_infinite_cv_radius : infinite_cv_radius identity_seq.
Proof.
intros r ; exists (Rabs r) ; intros x [i Hi] ; subst ;
unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult, identity_seq ;
 destruct (eq_nat_dec i 1) as [Heq|Hneq].
 rewrite Heq ; right ; apply Rabs_eq_compat ; ring.
 rewrite Rmult_0_l, Rabs_R0 ; apply Rabs_pos.
Qed.

Definition identity := sum _ identity_infinite_cv_radius.

(** * Definition of exp, cosine and sine *)

(** Sequences *)

Definition exp_seq (n : nat) := / INR (fact n).

Definition cos_seq : nat -> R.
Proof.
intro n ; case (n_modulo_2 n) ; intros [p Hp].
 apply ((-1) ^ p / INR (fact n)).
 apply 0.
Defined.

Definition sin_seq : nat -> R.
Proof.
intro n ; case (n_modulo_2 n) ; intros [p Hp].
 apply 0.
 apply ((-1) ^ p / INR (fact n)).
Defined.

(** Infinite cv radius *)

Lemma exp_seq_neq : forall n : nat, exp_seq n <> 0.
Proof.
intro n ; unfold exp_seq ; apply Rinv_neq_0_compat ;
 apply not_0_INR ; apply fact_neq_0.
Qed.

Lemma Rdiv_exp_seq_simpl : forall n, (exp_seq (S n)) / (exp_seq n) = / INR (S n).
Proof.
intros n ; unfold exp_seq.
 replace (fact (S n))%nat with ((S n) * fact n)%nat by reflexivity ;
 unfold Rdiv ; rewrite mult_INR, Rinv_involutive ;
 [rewrite Rinv_mult_distr ;
  [rewrite Rmult_assoc, Rinv_l, Rmult_1_r ;
   [reflexivity |] | |] |] ;
   apply not_0_INR ; auto ;  apply fact_neq_0.
Qed.

Lemma exp_infinite_cv_radius : infinite_cv_radius exp_seq.
Proof.
intros r.
 pose (M := (/ (Rabs r + 1))%R) ; assert (M_pos : 0 < M).
  unfold M ; apply Rinv_0_lt_compat ;
  apply Rplus_le_lt_0_compat ; [apply Rabs_pos | apply Rlt_0_1].
 apply (Rpser_alembert_prelim2 exp_seq M M_pos exp_seq_neq).

assert (t : (1 > 0)%nat) by constructor ;
 assert (H := Rseq_poly_cv 1 t) ;
 assert (H2 := Rseq_cv_pos_infty_shift_compat_reciprocal _ H) ;
 assert (H3 := Rseq_cv_pos_infty_inv_compat _ H2) ;
 clear t H H2 ; destruct (H3 _ M_pos) as [N HN] ; exists N ;
 intro n ; unfold Rseq_shifts.
 rewrite Rdiv_exp_seq_simpl ;
 apply Rle_trans with (R_dist ((/ Rseq_shift (Rseq_poly 1))%Rseq (N + n)%nat) 0).
 right ; unfold R_dist, Rseq_shift, Rseq_poly, pow ; apply Rabs_eq_compat ;
 rewrite Rminus_0_r, <- (Rmult_1_r (INR (S (N + n)))) ; reflexivity.
 left ; apply HN ; intuition.
 unfold M ; rewrite Rinv_involutive ; [| apply Rgt_not_eq ; apply Rplus_le_lt_0_compat ;
 [apply Rabs_pos | apply Rlt_0_1]] ; intuition.
Qed.

Lemma cos_infinite_cv_radius : infinite_cv_radius cos_seq.
Proof.
intros r ; apply Rle_Cv_radius_weak_compat with (| exp_seq |).
 intro n ; unfold cos_seq, exp_seq ; destruct (n_modulo_2 n) as [[p Hp] | [p Hp]].
 unfold Rdiv, Rseq_abs ; rewrite Rabs_Rabsolu, Rabs_mult, pow_1_abs, Rmult_1_l ;
 right ; reflexivity.
 rewrite Rabs_R0 ; apply Rabs_pos.
 rewrite <- Cv_radius_weak_abs ; apply exp_infinite_cv_radius.
Qed.

Lemma sin_infinite_cv_radius : infinite_cv_radius sin_seq.
Proof.
intros r ; apply Rle_Cv_radius_weak_compat with (| exp_seq |)%R.
 intro n ; unfold sin_seq, exp_seq ; case (n_modulo_2 n) ; intros [p Hp].
 rewrite Rabs_R0 ; apply Rabs_pos.
 unfold Rdiv, Rseq_abs ; rewrite Rabs_Rabsolu, Rabs_mult, pow_1_abs, Rmult_1_l ;
 right ; reflexivity.
 rewrite <- Cv_radius_weak_abs ; apply exp_infinite_cv_radius.
Qed.

(** Defintion of the sums *)

Definition Rexp (x : R) := sum  _ exp_infinite_cv_radius x.

Definition cosine (x : R) : R := sum _ cos_infinite_cv_radius x.

Definition sine (x : R) : R := sum _ sin_infinite_cv_radius x.

(** * About the derivatives of these functions *)

(** Links between the sequences *)

Lemma Deriv_exp_seq_simpl : (An_deriv exp_seq == exp_seq)%Rseq.
Proof.
intro n ; unfold exp_seq, An_deriv, Rseq_shift, Rseq_mult.
 replace (fact (S n))%nat with ((S n) * fact n)%nat by reflexivity.
 rewrite mult_INR, Rinv_mult_distr, <- Rmult_assoc, Rinv_r, Rmult_1_l ;
 [reflexivity | | |] ; replace R0 with (INR O) by reflexivity ; apply not_INR ;
 try apply fact_neq_0 ; intuition.
Qed.

Lemma Deriv_cos_seq_simpl : (An_deriv cos_seq == - sin_seq)%Rseq.
Proof.
intro n ; unfold cos_seq, sin_seq, An_deriv, Rseq_shift, Rseq_mult, Rseq_opp ;
 case (n_modulo_2 n) ; intros [p Hp] ;
 case (n_modulo_2 (S n)) ; intros [p' Hp'].
 apply False_ind ; omega.
 ring.
 replace p' with (S p) by omega.
 rewrite Rmult_comm ; unfold Rdiv ; rewrite Rmult_assoc.
 replace (/ INR (fact (S n)) * INR (S n)) with (/ INR (fact n)).
 simpl ; ring.
 rewrite fact_simpl, mult_INR ; field ; split ; apply not_0_INR ; [apply fact_neq_0 | intuition].
 apply False_ind ; omega.
Qed.

Lemma Deriv_sin_seq_simpl : (An_deriv sin_seq == cos_seq)%Rseq.
intro n ; unfold cos_seq, sin_seq, An_deriv, Rseq_shift, Rseq_mult ;
 case (n_modulo_2 n) ; intros [p Hp] ;
 case (n_modulo_2 (S n)) ; intros [p' Hp'].
 apply False_ind ; omega.
 replace p' with p by omega.
 rewrite Rmult_comm ; unfold Rdiv ; rewrite Rmult_assoc.
 replace (/ INR (fact (S n)) * INR (S n)) with (/ INR (fact n)).
 simpl ; ring.
 rewrite fact_simpl, mult_INR ; field ; split ; apply not_0_INR ; [apply fact_neq_0 | intuition].
 ring.
 apply False_ind ; omega.
Qed.

(** Definition of the derivatives *)

Definition Deriv_Rexp (x : R) := sum_derive _ exp_infinite_cv_radius x.

Definition Deriv_cosine (x : R) := sum_derive _ cos_infinite_cv_radius x.

Definition Deriv_sine (x : R) := sum_derive _ sin_infinite_cv_radius x.

(** The exponential is its own derivative *)

Lemma Rexp_eq_Deriv_Rexp : forall x, Rexp x = Deriv_Rexp x.
Proof.
intro x.
 assert (T1 := sum_sums _ exp_infinite_cv_radius x) ;
 assert (T2 := sum_derive_sums _ exp_infinite_cv_radius x).
 symmetry ; eapply Rpser_unique_extentionality.
 apply Deriv_exp_seq_simpl.
 apply T2.
 apply T1.
Qed.

(** Cosine & sine are each other derivative *)

Lemma cosine_eq_Deriv_sine : forall x, cosine x = Deriv_sine x.
Proof.
intro x.
 assert (T1 := sum_sums _ cos_infinite_cv_radius x) ;
 assert (T2 := sum_derive_sums _ sin_infinite_cv_radius x).
 symmetry ; eapply Rpser_unique_extentionality.
 apply Deriv_sin_seq_simpl.
 apply T2.
 apply T1.
Qed.

Lemma sine_eq_Deriv_cosine : forall x, sine x = - Deriv_cosine x.
Proof.
intro x.
 assert (T1 := sum_sums _ sin_infinite_cv_radius x) ;
 assert (T2 := sum_derive_sums _ cos_infinite_cv_radius x).
 symmetry ; apply Rpser_unique_extentionality with (- An_deriv cos_seq)%Rseq (sin_seq) x.
 intro n ; rewrite <- Ropp_involutive ;
 apply Ropp_eq_compat ; apply Deriv_cos_seq_simpl.
 apply Rpser_opp_compat ; apply T2.
 apply T1.
Qed.

(** Conclusions *)

Lemma derivable_pt_lim_Rexp : forall x, derivable_pt_lim Rexp x (Rexp x).
Proof.
intro x ; rewrite Rexp_eq_Deriv_Rexp ;
 apply derivable_pt_lim_sum.
Qed.

Lemma derivable_pt_lim_cosine : forall x, derivable_pt_lim cosine x (- sine x).
Proof.
intro x ; rewrite sine_eq_Deriv_cosine, Ropp_involutive ;
 apply derivable_pt_lim_sum.
Qed.

Lemma derivable_pt_lim_sine : forall x, derivable_pt_lim sine x (cosine x).
Proof.
intro x ; rewrite cosine_eq_Deriv_sine ;
 apply derivable_pt_lim_sum.
Qed.

Lemma derivable_pt_Rexp : forall x, derivable_pt Rexp x.
Proof.
intro x ; exists (Rexp x) ; apply derivable_pt_lim_Rexp.
Qed.

Lemma derivable_pt_cosine : forall x, derivable_pt cosine x.
Proof.
intro x ; exists (- sine x) ; apply derivable_pt_lim_cosine.
Qed.

Lemma derivable_pt_sine : forall x, derivable_pt sine x.
Proof.
intro x ; exists (cosine x) ; apply derivable_pt_lim_sine.
Qed.

Lemma derivable_cosine : derivable cosine.
Proof.
intro x ; apply derivable_pt_cosine.
Qed.

Lemma derivable_sine : derivable sine.
Proof.
intro x ; apply derivable_pt_sine.
Qed.

Lemma derive_pt_sine_cosine : forall (x : R) (pr : derivable_pt sine x),
  derive_pt sine x pr = cosine x.
Proof.
intros x pr ; rewrite derive_pt_eq ; apply derivable_pt_lim_sine.
Qed.

Lemma derive_pt_cosine_sine : forall (x : R) (pr : derivable_pt cosine x),
  derive_pt cosine x pr = - sine x.
Proof.
intros x pr ; rewrite derive_pt_eq ; apply derivable_pt_lim_cosine.
Qed.

(* Link with the standard's library definitions. *)

Lemma sin_seq_even : forall n x, gt_pser sin_seq x (2 * n)%nat = 0.
Proof.
intros n x ; unfold gt_pser, sin_seq, Rseq_mult ;
 case (n_modulo_2 (2 * n)) ; intros [p Hp].
 ring.
 apply False_ind ; omega.
Qed.

Lemma cos_seq_odd : forall n x, gt_pser cos_seq x (S (2 * n))%nat = 0.
Proof.
intros n x ; unfold gt_pser, cos_seq, Rseq_mult ;
 case (n_modulo_2 (S (2 * n))) ; intros [p Hp].
 apply False_ind ; omega.
 ring.
Qed.

Lemma partial_sine_drop_even : forall x n,
  Rseq_sum (gt_pser sin_seq x) (2 * S n) = Rseq_sum (gt_pser sin_seq x) (S (2 * n)).
Proof.
intros x n ; replace (2 * S n)%nat with (S (S (2 * n))) by ring.
 rewrite Rseq_sum_simpl ; replace (S (S (2 * n)))%nat with (2 * S n)%nat by ring ;
 rewrite sin_seq_even ; ring.
Qed.

Lemma partial_cosine_drop_odd : forall x n,
  Rseq_sum (gt_pser cos_seq x) (S (2 * n)) = Rseq_sum (gt_pser cos_seq x) (2 * n).
Proof.
intros x n ; rewrite Rseq_sum_simpl, cos_seq_odd ; ring.
Qed.

Lemma partial_sin_sine_ext : forall x n,
  x * sum_f_R0 (fun i => sin_n i * x ² ^ i) n = Rseq_sum (gt_pser sin_seq x) (S (2 * n)).
Proof.
intros x n ; induction n.
 simpl ; unfold sin_n, sin_seq, gt_pser, Rseq_mult.
  case (n_modulo_2 0) ; intros [p Hp].
   case (n_modulo_2 1) ; intros [q Hq].
    apply False_ind ; omega.
    assert (Hqq : q = O) by omega ; subst ; assert (Hpp : p = O) by omega ; subst.
    simpl ; ring.
   apply False_ind ; omega.
  replace (2 * S n)%nat with (S (S (2 * n))) by ring.
   do 3 rewrite Rseq_sum_simpl ; rewrite <- IHn.
 replace (S (S (2 * n))) with (2 * (S n))%nat by ring ; rewrite sin_seq_even.
 rewrite Rmult_plus_distr_l, Rplus_assoc ; apply Rplus_eq_compat_l.
  unfold sin_n, gt_pser, sin_seq, Rseq_mult.
   case (n_modulo_2 (S (2 * S n))) ; intros [p Hp].
    apply False_ind ; omega.
    rewrite <- (tech_pow_Rmult x), pow_Rsqr, <- (tech_pow_Rmult x²) ;
    replace (S n) with p by omega ; replace (2 * p + 1)%nat with (S (2 * p)) by omega.
    ring.
Qed.

Lemma partial_cos_cosine_ext : forall x n,
  sum_f_R0 (fun i => cos_n i * x ² ^ i) n = Rseq_sum (gt_pser cos_seq x) (2 * n).
Proof.
intros x n ; induction n.
 simpl ; unfold cos_n, cos_seq, gt_pser, Rseq_mult.
  case (n_modulo_2 0) ; intros [p Hp].
   case (n_modulo_2 1) ; intros [q Hq].
    apply False_ind ; omega.
    assert (Hqq : q = O) by omega ; subst ; assert (Hpp : p = O) by omega ; subst.
    simpl ; ring.
  apply False_ind ; omega.
 replace (2 * S n)%nat with (S (S (2 * n))) by ring ; do 3 rewrite Rseq_sum_simpl.
 rewrite <- IHn, Rplus_assoc, cos_seq_odd ; apply Rplus_eq_compat_l.
 unfold cos_n, gt_pser, cos_seq, Rseq_mult.
  case (n_modulo_2 (S (S (2 * n)))) ; intros [p Hp].
  replace (S (S (2 * n))) with (2 * S n)%nat by omega ; rewrite pow_Rsqr ;
  replace (S n) with p by omega ; ring.
  apply False_ind ; omega.
Qed.

Lemma sin_sine : sin == sine.
Proof.
intro x ; unfold sin, sine ; destruct (exist_sin x²) as [l Hl] ;
 unfold sin_in, infinite_sum in Hl.
 apply Rseq_cv_unique with (Rseq_sum (gt_pser sin_seq x)).
 cut (Rseq_cv (fun n => Rseq_sum (gt_pser sin_seq x) (S (2 * n))) (x * l)).
  intro H ; apply Rseq_cv_even_odd_compat.
   eapply Rseq_cv_shift_compat, Rseq_cv_eq_compat ; [| eapply H].
    intro n ; unfold Rseq_shift ; apply partial_sine_drop_even ; apply H.
   apply H.
 apply Rseq_cv_eq_compat with (fun n => x * sum_f_R0 (fun i => sin_n i * x ² ^ i) n).
  intro n ; symmetry ; apply partial_sin_sine_ext.
  apply Rseq_cv_mult_compat ; [apply Rseq_constant_cv |].
   intros eps eps_pos ; destruct (Hl _ eps_pos) as [N HN] ; exists N ; apply HN.
 apply sum_sums.
Qed.

Lemma cos_cosine : cos == cosine.
Proof.
intro x ; unfold cos, cosine ; destruct (exist_cos x²) as [l Hl] ;
 unfold cos_in, infinite_sum in Hl.
 apply Rseq_cv_unique with (Rseq_sum (gt_pser cos_seq x)).
 cut (Rseq_cv (fun n => Rseq_sum (gt_pser cos_seq x) (2 * n)) l).
  intro H ; apply Rseq_cv_even_odd_compat.
   apply H.
   eapply Rseq_cv_eq_compat ; [| eapply H].
    intro n ; unfold Rseq_shift ; apply partial_cosine_drop_odd ; apply H.
 apply Rseq_cv_eq_compat with (fun n => sum_f_R0 (fun i => cos_n i * x ² ^ i) n).
  intro n ; symmetry ; apply partial_cos_cosine_ext.
 intros eps eps_pos ; destruct (Hl _ eps_pos) as [N HN] ; exists N ; apply HN.
 apply sum_sums.
Qed.

(** * Definition of arctan *)

Definition arctan_seq : Rseq.
Proof.
intro n ; case (n_modulo_2 n) ; intros [p Hp].
 exact 0.
 exact ((- 1) ^ p / INR n).
Defined.

Lemma arctan_seq_even : forall n x, gt_pser arctan_seq x (2 * n)%nat = 0.
Proof.
intros n x ; unfold gt_pser, arctan_seq, Rseq_mult ;
 case (n_modulo_2 (2 * n)) ; intros [p Hp].
 rewrite Rmult_0_l ; reflexivity.
 apply False_ind ; omega.
Qed.

Lemma arctan_seq_1_simpl : forall n,
  gt_pser arctan_seq 1 (S (2 * n)) = tg_alt PI_tg n.
Proof.
intro n ; unfold gt_pser, arctan_seq, tg_alt, PI_tg, Rseq_mult, Rdiv ;
 rewrite pow1 ; replace (2 * n + 1)%nat with (S (2 * n)) by omega.
 case (n_modulo_2 (S (2 * n))) ; intros [p Hp].
  apply False_ind ; omega.
  assert (Hpn : p = n) by omega ; subst ; ring.
Qed.

Lemma partial_arctan_drop_even : forall n x,
  Rseq_sum (gt_pser arctan_seq x) (2 * S n) = Rseq_sum (gt_pser arctan_seq x) (S (2 * n)).
Proof.
intros n x ; replace (2 * S n)%nat with (S (S (2 * n))) by ring.
 rewrite Rseq_sum_simpl ; replace (S (S (2 * n)))%nat with (2 * S n)%nat by ring ;
 rewrite arctan_seq_even ; ring.
Qed.

Lemma Rseq_sum_0 : forall An, Rseq_sum An 0 = An O.
Proof.
reflexivity.
Qed.

Lemma partial_arctan_drop_evens : forall n x f,
  Rseq_sum (fun i => gt_pser arctan_seq x (2 * f i)) n = 0.
Proof.
intros n x f ; induction n.
 rewrite Rseq_sum_0 ; apply arctan_seq_even.
 rewrite Rseq_sum_simpl, IHn, arctan_seq_even ; ring.
Qed.

Lemma partial_arctan_lower_bound : forall M, (0 < M)%nat ->
  / 7 <= Rseq_sum (Rseq_shifts (gt_abs_pser arctan_seq 1) (2 * M)) (2 * M).
Proof.
intros M M_lub ; transitivity (INR M * / (6 * INR M + 1)).
 transitivity (/ (6 + / INR M)).
  apply Rle_Rinv.
   apply Rplus_lt_0_compat ; [fourier | apply Rinv_0_lt_compat, lt_0_INR, M_lub].
   fourier.
   replace 7 with (6 + / 1) by (rewrite Rinv_1 ; ring) ; apply Rplus_le_compat_l.
   apply Rle_Rinv ; [fourier | apply lt_0_INR ; assumption |].
   rewrite <- INR_1 ; apply le_INR ; omega.
  right ; field ; split ; apply Rgt_not_eq.
   apply Rplus_lt_0_compat.
    apply Rmult_lt_0_compat ; [| apply lt_0_INR ; assumption] ; fourier.
    fourier.
    apply lt_0_INR ; assumption.
 destruct M as [| M] ; [inversion M_lub |] ; rewrite <- Rseq_sum_even_odd_split'.
  unfold Rseq_shifts.
  rewrite Rseq_sum_ext with (Vn := fun i : nat => gt_pser arctan_seq 1 (2 * (S M +  i))).
  rewrite partial_arctan_drop_evens, Rplus_0_l.
  apply Rseq_sum_lower_bound.
   intros m m_ub ; unfold gt_abs_pser, gt_pser, arctan_seq, Rseq_abs, Rseq_mult ;
   rewrite pow1, Rmult_1_r.
    case (n_modulo_2 (2 * S M + S (2 * m))) ; intros [p Hp].
     apply False_ind ; omega.
     unfold Rdiv ; rewrite Rabs_mult, Rabs_opp1, Rmult_1_l, Rabs_right.
     apply Rle_Rinv.
      apply lt_0_INR ; omega.
      apply Rplus_lt_0_compat ; [apply Rmult_lt_0_compat, lt_0_INR ; try assumption |] ; fourier.
      transitivity (INR (S (6 * S M))).
      apply le_INR ; omega.
      rewrite S_INR, mult_INR ; replace 6 with (INR 6) by (simpl ; ring) ; reflexivity.
      left ; apply Rinv_0_lt_compat, lt_0_INR ; omega.
  intro n ; unfold gt_abs_pser, gt_pser, Rseq_abs, Rseq_mult, arctan_seq.
   replace (2 * S M + 2 * n)%nat with (2 * (S M + n))%nat by ring.
   case (n_modulo_2 (2 * (S M + n))) ; intros [p Hp].
    rewrite Rmult_0_l ; apply Rabs_R0.
    apply False_ind ; omega.
Qed.

Lemma partial_PI_arctan1_ext : forall n,
  sum_f_R0 (tg_alt PI_tg) n = Rseq_sum (gt_pser arctan_seq 1) (S (2 * n)).
Proof.
intros n ; induction n.
 simpl ; unfold tg_alt, PI_tg, arctan_seq, gt_pser, Rseq_mult, Rdiv.
  case (n_modulo_2 0) ; intros [p Hp].
   case (n_modulo_2 1) ; intros [q Hq].
    apply False_ind ; omega.
    assert (Hp' : p = O) by omega ; assert (Hq' : q = O) by omega ; subst ; simpl ; ring.
   apply False_ind ; omega.
 replace (2 * S n)%nat with (S (S (2 * n))) by ring.
 do 3 rewrite Rseq_sum_simpl ; rewrite <- IHn, Rplus_assoc ; apply Rplus_eq_compat_l.
 replace (S (S (2 * n))) with (2 * S n)%nat by ring ; rewrite arctan_seq_even.
 unfold tg_alt, PI_tg, arctan_seq, gt_pser, Rseq_mult, Rdiv ; rewrite pow1.
 case (n_modulo_2 (S (2 * S n))) ; intros [p Hp].
  apply False_ind ; omega.
  assert (Hp' : S n = p) by omega ; rewrite Hp' ;
  replace (2 * p + 1)%nat with (S (2 * p)) by ring ; ring.
Qed.

Lemma arctan1_PI4 : Rpser arctan_seq 1 (PI / 4).
Proof.
assert (H : Rseq_cv (fun n => Rseq_sum (gt_pser arctan_seq 1) (S (2 * n))) (PI / 4)).
 apply Rseq_cv_eq_compat with (sum_f_R0 (tg_alt PI_tg)).
  intro n ; symmetry ; apply partial_PI_arctan1_ext.
 unfold PI ; destruct exist_PI as [pi Hpi] ;
 replace (4 * pi / 4) with pi by field ; apply Hpi.
apply Rseq_cv_even_odd_compat.
 eapply Rseq_cv_shift_compat, Rseq_cv_eq_compat ; [| eapply H].
  intro n ; unfold Rseq_shift ; apply partial_arctan_drop_even.
 apply H.
Qed.

Lemma gt_pser_1 : forall An n, gt_pser An 1 n = An n.
Proof.
intros An n ; unfold gt_pser, Rseq_mult ; rewrite pow1 ; ring.
Qed.

Lemma Rseq_shifts_fusion : forall An k m,
  (Rseq_shifts (Rseq_shifts An k) m == Rseq_shifts An (k + m))%Rseq.
Proof.
intros ; unfold Rseq_shifts ; intro ; rewrite plus_assoc ; reflexivity.
Qed.

Lemma arctan_cv_radius : finite_cv_radius arctan_seq 1.
Proof.
rewrite <- Rabs_R1 ; apply Rpser_finite_cv_radius_caracterization with (PI / 4).
 apply arctan1_PI4.
 intros l Hl ; eapply Rseq_cv_Rseq_cv_pos_infty_incompat ; [eassumption |].
 apply Rseq_cv_pos_infty_criteria with (/ 7).
  fourier.
  intro ; apply gt_abs_pser_pos.
  intro M ; destruct M as [| M].
   exists 1%nat ; split.
    omega.
    simpl ; unfold Rseq_shifts, gt_abs_pser, Rseq_abs ; simpl ;
    replace O with (2 * 0)%nat by reflexivity ;
    rewrite arctan_seq_even, Rabs_R0, Rplus_0_l, gt_pser_1.
    simpl ; unfold arctan_seq ; case (n_modulo_2 1) ; intros [p Hp].
     apply False_ind ; omega.
     unfold Rdiv ; rewrite Rabs_mult, Rabs_opp1, Rabs_Rinv.
      simpl ; rewrite Rabs_R1, Rinv_1 ; fourier.
      apply not_0_INR ; omega.
  case (n_modulo_2 (S M)) ; intros [P HP].
   exists (4 * P)%nat ; split.
    omega.
    rewrite HP ; replace (4 * P - 2 * P)%nat with (2 * P)%nat by omega.
    apply partial_arctan_lower_bound ; omega.
   exists (4 * S P)%nat ; split.
    omega.
    replace (4 * S P - S M)%nat with (S (2 * S P)) by (rewrite HP ; omega).
    rewrite Rseq_sum_split_compat with (k := O) ; [| omega].
    replace (/ 7) with (0 + / 7) by (apply Rplus_0_l) ; apply Rplus_le_compat.
    unfold Rseq_shifts ; simpl ; apply gt_abs_pser_pos.
    replace (S (2 * S P) - 1)%nat with (2 * S P)%nat by omega.
    rewrite Rseq_sum_ext with (Vn := Rseq_shifts (gt_abs_pser arctan_seq 1) (2 * S P)%nat).
    apply partial_arctan_lower_bound ; omega.
    intro n ; rewrite Rseq_shifts_fusion, HP ; f_equal ; ring.
Qed.

Definition arctan := sum_r _ _ arctan_cv_radius.

Lemma arctan_0 : arctan 0 = 0.
Proof.
assert (Hsum1 : Rpser arctan_seq 0 0).
 apply Rseq_cv_eq_compat with (fun _ => 0).
  intro n ; induction n.
   unfold Rseq_pps ; simpl ; rewrite <- (arctan_seq_even 0 0), mult_0_r ; reflexivity.
   rewrite Rseq_pps_simpl, IHn, pow_i ; [ring | intuition].
 apply Rseq_constant_cv.
assert (O_in : Rabs 0 < 1) by (rewrite Rabs_R0 ; fourier) ;
assert (Hsum2 := sum_r_sums _ _ arctan_cv_radius _ O_in).
eapply Rpser_unique ; eassumption.
Qed.