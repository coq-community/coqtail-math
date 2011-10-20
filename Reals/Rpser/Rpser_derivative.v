Require Import Reals Rpow_facts.
Require Import Rfunction_def Rinterval Rextensionality Ranalysis_def Ranalysis_facts.
Require Import Fourier MyRIneq.

Require Import Rsequence_facts Rsequence_sums_facts RFsequence RFsequence_facts.
Require Import Rpser_def Rpser_base_facts Rpser_radius_facts Rpser_sums Rpser_sums_facts.

Require Import Ass_handling.

Open Local Scope R_scope.

(** * Definition of the formal derivative *)

(** Derivability of partial sums *)

Definition Rpser_partial_sum_derive An n x := match n with
     | 0%nat => 0
     | S _      => Rseq_pps (An_deriv An) x (pred n)
end.

Lemma Rpser_partial_sum_derive_pt_lim: forall An n x,
  derivable_pt_lim (fun x => Rseq_pps An x n) x (Rpser_partial_sum_derive An n x).
Proof.
intros ; apply derivable_pt_lim_finite_sum.
Qed.

Lemma Rpser_partial_sum_derive_pt_lim_in: forall c r r_pos An n x,
  derivable_pt_lim_in (fun x => Rseq_pps An x n) (Rball c r r_pos) x
  (Rpser_partial_sum_derive An n x).
Proof.
intros c r r_pos An n x ; apply derivable_pt_lim_derivable_pt_lim_in,
  Rpser_partial_sum_derive_pt_lim.
Qed.

Lemma derivable_pt_lim_in_weaksum_r: forall An r r_pos (rho : Cv_radius_weak An r)
  (rho' : Cv_radius_weak (An_deriv An) r) x (x_in: Rball 0 r r_pos x),
  derivable_pt_lim_in (weaksum_r An r rho) (Rball 0 r r_pos) x
  (weaksum_r (An_deriv An) r rho' x).
Proof.
intros An r r_pos rho rho' x x_in.
 assert (x_bd : Rabs x < r).
  unfold Rball in x_in ; rewrite Rminus_0_r in x_in ; assumption.
 assert (x_bd' : Rabs x < Rabs r).
  apply Rlt_le_trans with r ; [assumption | right ; symmetry ; apply Rabs_right].
  apply Rle_ge ; apply Rle_trans with (Rabs x) ; [apply Rabs_pos | left ; assumption].
assert (lb_lt_x : - middle (Rabs x) (Rabs r) < x).
  apply Rlt_le_trans with (- Rabs x).
  apply Ropp_gt_lt_contravar ; apply Rlt_gt ;
   apply middle_is_in_the_middle ; assumption.
   apply Rabs_le.
 assert (x_lt_ub : x < middle (Rabs x) (Rabs r)).
  apply Rle_lt_trans with (Rabs x) ; [apply Rle_abs |
  apply middle_is_in_the_middle] ; assumption.
    pose (r' := middle (middle (Rabs x) (Rabs r)) (Rabs r)).
    assert (r'_bd1 := proj2 (middle_is_in_the_middle _ _ x_bd')).
    replace (middle (Rabs x) (Rabs r)) with (Rabs (middle (Rabs x) (Rabs r))) in r'_bd1 ; [| apply Rabs_right ;
    unfold r' ; apply Rle_ge ; unfold Rdiv ; apply Rle_mult_inv_pos ; [| fourier] ;
    apply Rplus_le_le_0_compat ; apply Rabs_pos].
    assert (r'_bd := proj2 (middle_is_in_the_middle _ _ r'_bd1)).
    assert (Temp : middle (Rabs (middle (Rabs x) (Rabs r))) (Rabs r) = r').
     unfold r' ; unfold Rdiv ; apply Rmult_eq_compat_r ; apply Rplus_eq_compat_r ;
     apply Rabs_right ; apply Rle_ge ; apply Rle_mult_inv_pos ; [| fourier] ;
     apply Rplus_le_le_0_compat ; apply Rabs_pos.
     rewrite Temp in r'_bd ; clear Temp ;
    fold r' in r'_bd ; replace r' with (Rabs r') in r'_bd ; [| apply Rabs_right ;
    unfold r' ; apply Rle_ge ; unfold Rdiv ; apply Rle_mult_inv_pos ; [| fourier] ;
    apply Rplus_le_le_0_compat ; [| apply Rabs_pos] ; unfold Rdiv ;
    apply Rle_mult_inv_pos ; [| fourier] ; apply Rplus_le_le_0_compat ; apply Rabs_pos].
    pose (r'' := middle (Rabs x) (Rabs r)).
    assert (r''_pos : 0 < r'').
    unfold r''. apply Rlt_mult_inv_pos ; [| fourier] ;
     apply Rplus_le_lt_0_compat ; [| apply Rle_lt_trans with (Rabs x) ; [| assumption]] ;
     apply Rabs_pos.
    assert (r''_bd : r'' < r').
     unfold r'', r'.
     unfold Rdiv ; apply Rmult_lt_compat_r ; [fourier |] ; apply Rplus_lt_compat_r.
     apply middle_is_in_the_middle ; assumption.
    pose (myR := mkposreal r'' r''_pos).
    assert (myR_ub : myR < r') by intuition.
    assert (Abel2' := Rpser_abel2 (An_deriv An) r'
         (Cv_radius_weak_derivable_compat An r rho r' r'_bd) myR myR_ub).
   assert (cv_interv : forall y : R, Boule 0 (mkposreal_lb_ub x (- middle (Rabs x) (Rabs r))
         (middle (Rabs x)(Rabs r)) lb_lt_x x_lt_ub) y ->
         {l : R | Un_cv (fun N : nat => SP
         (fun (n : nat) (x : R) => gt_pser (An_deriv An) x n) N y) l}).
    intros y y_bd.
    exists (weaksum_r (An_deriv An) r rho' y).
    assert (y_bd2 : Rabs y < r).
     unfold Boule, mkposreal_lb_ub in y_bd ; rewrite Rminus_0_r in y_bd.
     apply Rlt_trans with (middle (middle (Rabs x) (Rabs r)) (middle (Rabs x) (Rabs r))).
     rewrite (middle_unfold (middle _ _ )), <- Rminus_opp ; assumption.
     apply Rle_lt_trans with (middle (Rabs x) (Rabs r)).
     right ; unfold middle ; field.
     apply Rlt_le_trans with (Rabs r).
      apply middle_is_in_the_middle ; assumption.
      right ; apply Rabs_pos_eq ; left ; apply Rle_lt_trans with (Rabs x) ;
       [apply Rabs_pos |] ; assumption.
   intros alpha alpha_pos ; destruct (weaksum_r_sums (An_deriv An) r rho' y y_bd2
           alpha alpha_pos) as (N, HN) ; exists N ; intros n n_lb ;
           apply HN ; assumption.
   assert (CVN : CVN_r (fun (n : nat) (x : R) => gt_pser (An_deriv An) x n)
         (mkposreal_lb_ub x (- middle (Rabs x) (Rabs r)) (middle (Rabs x) (Rabs r))
         lb_lt_x x_lt_ub)).
    apply Rpser_abel2 with r'.
    apply Cv_radius_weak_derivable_compat with r ; assumption.
    unfold mkposreal_lb_ub.
    apply Rle_lt_trans with r'' ; [| assumption].
    right ; unfold r'' ; intuition.
     assert (Temp : (middle (Rabs x) (Rabs r) - - middle (Rabs x) (Rabs r)) / 2
           = middle (Rabs x) (Rabs r)) by field.
    intuition.
   assert (Main := CVN_CVU_interv (fun n x => gt_pser (An_deriv An) x n)
          (mkposreal_lb_ub x (- middle (Rabs x) (Rabs r)) (middle (Rabs x) (Rabs r))
          lb_lt_x x_lt_ub) cv_interv CVN).
   assert (Main2 : RFseq_cvu (Rpser_partial_sum_derive An) (weaksum_r (An_deriv An) r rho')
          (middle (- middle (Rabs x) (Rabs r)) (middle (Rabs x) (Rabs r)))
          (mkposreal_lb_ub x (- middle (Rabs x) (Rabs r)) (middle (Rabs x) (Rabs r))
          lb_lt_x x_lt_ub)).
    clear -Main x_bd x_bd'; intros eps eps_pos ; destruct (Main eps eps_pos) as (N, HN) ;
    exists (S N) ; intros n y n_lb y_bd.
    assert (y_bd2 : Boule 0
         (mkposreal_lb_ub x (- middle (Rabs x) (Rabs r)) (middle (Rabs x) (Rabs r))
         lb_lt_x x_lt_ub) y).
     unfold Boule in * ; rewrite middle_R0 in y_bd ; assumption.
    assert(n_lb2 : (N <= pred n)%nat) by intuition.
    assert (Temp := HN (pred n) y n_lb2 y_bd2).
    assert (T1 := SFL_interv_right (fun (n : nat) (x : R) => gt_pser (An_deriv An) x n)
            (mkposreal_lb_ub x (- middle (Rabs x) (Rabs r))
            (middle (Rabs x) (Rabs r)) lb_lt_x x_lt_ub) cv_interv y y_bd2).
    assert (y_bd3 : Rabs y < r).
     unfold Boule, mkposreal_lb_ub in y_bd2 ; rewrite Rminus_0_r in y_bd2.
     apply Rlt_trans with ((middle (Rabs x) (Rabs r) - - middle (Rabs x) (Rabs r)) / 2).
     assumption.
     apply Rle_lt_trans with (middle (Rabs x) (Rabs r)).
     right ; field.
     apply Rlt_le_trans with (Rabs r).
      apply middle_is_in_the_middle ; assumption.
      right ; apply Rabs_pos_eq ; apply Rle_trans with (Rabs x) ;
       [apply Rabs_pos | left ; assumption].
    assert (T2 := weaksum_r_sums (An_deriv An) r rho' y y_bd3) ;
     unfold Rpser, Rseq_pps in T2.
    rewrite Rseq_cv_eq_compat with (Vn := fun N => SP (fun (n : nat) (x : R) =>
     gt_pser (An_deriv An) x n) N y) in T2 ; [| intro ; reflexivity].
    assert (Lim_eq := UL_sequence _ _ _ T1 T2).
    rewrite <- Lim_eq.
    unfold SP in Temp ; unfold Rpser_partial_sum_derive.
    assert (Hrew : n = S (pred n)).
     apply S_pred with N ; intuition.
    rewrite Hrew.
    unfold R_dist ; rewrite Rabs_minus_sym ; apply Temp.
  assert (Dfn_eq_fn' : forall (x0 : R) (n : nat), - middle (Rabs x) (Rabs r) < x0 ->
          x0 < middle (Rabs x) (Rabs r) -> derivable_pt_lim
          ((fun (n0 : nat) (x : R) => sum_f_R0 (gt_pser An x) n0) n) x0
          (Rpser_partial_sum_derive An n x0)).
   intros y n y_lb y_ub.
   apply derivable_pt_lim_finite_sum.
  assert (fn_cv_f : RFseq_cv_interv (fun (n : nat) (x : R) => sum_f_R0 (gt_pser An x) n)
          (weaksum_r An r rho) (- middle (Rabs x) (Rabs r)) (middle (Rabs x) (Rabs r))).
   intros y lb_lt_y y_lt_ub eps eps_pos.
    assert(y_bd1 : - Rabs r < y).
     apply Rlt_trans with (- middle (Rabs x) (Rabs r)) ; [| assumption].
     apply Ropp_lt_contravar ; apply middle_is_in_the_middle ; assumption.
    assert(y_bd2 : y < Rabs r).
     apply Rlt_trans with (middle (Rabs x) (Rabs r)) ; [assumption |] ;
      apply middle_is_in_the_middle ; assumption.
   assert (y_bd : Rabs y < Rabs r).
    apply Rabs_def1 ; assumption.
    replace (Rabs r) with r in y_bd ; [| symmetry ; apply Rabs_right ; apply Rle_ge ;
    apply Rle_trans with (Rabs x) ; [apply Rabs_pos | left ; assumption]].
   destruct (weaksum_r_sums An r rho y y_bd eps eps_pos) as (N, HN) ; exists N ;
   intros n n_lb ; apply HN ; assumption.
    apply derivable_pt_lim_derivable_pt_lim_in.
    apply (RFseq_cvu_derivable (fun n x => sum_f_R0 (gt_pser An x) n)
         (Rpser_partial_sum_derive An)
         (weaksum_r An r rho) (weaksum_r (An_deriv An) r rho') x
         (- middle (Rabs x) (Rabs r)) (middle (Rabs x) (Rabs r))
         lb_lt_x x_lt_ub Dfn_eq_fn' fn_cv_f Main2).
   intros y y_lb y_ub.
   apply CVU_continuity with (fn:=Rpser_partial_sum_derive An) (x:=0)
    (r:=(mkposreal_lb_ub x (- middle (Rabs x) (Rabs r))
             (middle (Rabs x) (Rabs r)) lb_lt_x x_lt_ub)).
             intros eps eps_pos ; destruct (Main2 eps eps_pos) as (N, HN) ; exists N ; 
             intros n z n_lb z_bd.
             rewrite Rabs_minus_sym ; apply HN.
   assumption.
   replace (middle (- middle (Rabs x) (Rabs r)) (middle (Rabs x) (Rabs r))) with 0
    by (symmetry ; apply middle_R0).
   assumption.
   intros.
   destruct n.
   unfold Rpser_partial_sum_derive.
   apply continuity_const ; unfold constant ; intuition.
   unfold Rpser_partial_sum_derive ; apply continuity_finite_sum.
   unfold Boule ; rewrite Rminus_0_r.
   unfold mkposreal_lb_ub.
   replace ((middle (Rabs x) (Rabs r) - - middle (Rabs x) (Rabs r)) / 2) with
   (middle (Rabs x) (Rabs r)) by field.
   apply Rabs_def1 ; intuition.
Qed.

Lemma derivable_pt_lim_in_weaksum_r_strong:
  forall An r r' r_pos r'_pos (rho : Cv_radius_weak An r)
  (rho' : Cv_radius_weak (An_deriv An) r') x
  (x_in: Rball 0 r r_pos x) (x_in': Rball 0 r' r'_pos x),
  derivable_pt_lim_in (weaksum_r An r rho) (Rball 0 r r_pos) x
  (weaksum_r (An_deriv An) r' rho' x).
Proof.
intros An r r' rp r'p rho rho' x x_in x_in'.
 assert (min_pos: 0 <= Rmin r r') by (apply Rmin_pos ; assumption).
 assert (x_in_min: Rball 0 (Rmin r r') min_pos x).
  unfold Rmin, Rball ; destruct (Rle_dec r r') ; assumption.
 assert (rho'': Cv_radius_weak An (Rmin r r')).
  apply Cv_radius_weak_le_compat with r.
   rewrite Rabs_right ; [rewrite Rabs_right ; [apply Rmin_l | apply Rle_ge] |
   apply Rle_ge ] ; assumption.
  assumption.
 assert (rho2: Cv_radius_weak (An_deriv An) (Rmin r r')).
  apply Cv_radius_weak_le_compat with r'.
   rewrite Rabs_right ; [rewrite Rabs_right ; [apply Rmin_r | apply Rle_ge] |
   apply Rle_ge ] ; assumption.
  assumption.
 assert (Heq: weaksum_r (An_deriv An) r' rho' x =
  weaksum_r (An_deriv An) (Rmin r r') rho2 x).
  apply weaksum_r_unique_strong ; [| apply Rmin_glb_lt] ;
   erewrite <- Rball_0_simpl ; eassumption.
 rewrite Heq.
 apply derivable_pt_lim_Rball_included_rev with (Rmin r r') min_pos ;
 [assumption | apply Rmin_l |].
 apply derivable_pt_lim_Rball_ext with (weaksum_r An (Rmin r r') rho'')
  min_pos min_pos min_pos.
  intros y y_in ; apply weaksum_r_unique_strong.
   rewrite <- Rball_0_simpl ; eassumption.
   rewrite <- (Rball_0_simpl _ rp) ; eapply Rball_included ;
   [eapply Rmin_l |] ; eassumption.
   assumption.
 apply derivable_pt_lim_in_weaksum_r ; assumption.
Qed.

Lemma derivable_pt_in_weaksum_r: forall An r r_pos
  (rho : Cv_radius_weak An r) x (x_in: Rball 0 r r_pos x),
  derivable_pt_in (weaksum_r An r rho) (Rball 0 r r_pos) x.
Proof.
intros An r r_pos rho x x_in ; pose (r' := middle (Rabs x) r) ;
 assert (r'_pos: 0 <= r').
  apply middle_le_le_pos ; [apply Rabs_pos | assumption]. 
 assert (rho': Cv_radius_weak (An_deriv An) r').
  eapply Cv_radius_weak_derivable_compat ; [eassumption|].
   rewrite Rabs_right ; [rewrite (Rabs_right r) |].
   apply middle_is_in_the_middle ; erewrite <- Rball_0_simpl ; eassumption.
  apply Rle_ge ; assumption.
  apply Rle_ge ; assumption.
 exists (weaksum_r (An_deriv An) r' rho' x).
 apply derivable_pt_lim_in_weaksum_r_strong with r'_pos.
  assumption.
  apply Rball_0_simpl, middle_is_in_the_middle ;
  erewrite <- Rball_0_simpl ; eassumption.
Qed.

Lemma derivable_Rball_weaksum_r: forall An r r_pos (rho : Cv_radius_weak An r),
  derivable_Rball (weaksum_r An r rho) 0 r r_pos.
Proof.
intros An r r_pos rho x x_in ; apply derivable_pt_in_weaksum_r ; assumption.
Qed.
   
(** Sum of the formal derivative *)

Definition weaksum_r_derive An r (rho : Cv_radius_weak An r) (x : R) : R.
Proof.
destruct (Rlt_le_dec (Rabs x) r) as [x_bd | x_bd].
apply (weaksum_r (An_deriv An) (middle (Rabs x) r)).
apply Cv_radius_weak_derivable_compat with r.
 assumption.
 rewrite (Rabs_pos_eq r).
 apply Rabs_middle_is_in_the_middle ; [apply Rabs_pos | assumption].
 left ; apply Rle_lt_trans with (Rabs x) ; [apply Rabs_pos | assumption].
 exact x.
exact 0.
Defined.

Definition sum_r_derive An r (rho : finite_cv_radius An r) : R -> R.
Proof.
eapply sum_r, (proj1 (finite_cv_radius_derivable_compat _ _)), rho.
Defined.

Definition sum_derive An (rho : infinite_cv_radius An) : R -> R.
Proof.
eapply sum, (proj1 (infinite_cv_radius_derivable_compat _)), rho.
Defined.

(** Proof that it is really the sum *)

Lemma weaksum_r_derive_sums : forall An r (Pr : Cv_radius_weak An r) x,
  Rabs x < r -> Rpser (An_deriv An) x (weaksum_r_derive An r Pr x).
Proof.
intros An r Pr x x_bd ; unfold weaksum_r_derive ;
destruct (Rlt_le_dec (Rabs x) r) as [H | Hf].
 apply weaksum_r_sums ; apply middle_is_in_the_middle ; assumption.
 exfalso ; fourier.
Qed.

Lemma sum_r_derive_sums : forall An r (Pr : finite_cv_radius An r) x,
  Rabs x < r -> Rpser (An_deriv An) x (sum_r_derive An r Pr x).
Proof.
intros ; apply sum_r_sums ; assumption.
Qed.

Lemma sum_derive_sums : forall An (Pr : infinite_cv_radius An) x,
  Rpser (An_deriv An) x (sum_derive An Pr x).
Proof.
intros ; apply sum_sums.
Qed.

(** Proof that this derivative is unique *)

Lemma weaksum_r_derive_unique : forall An r (Pr1 Pr2 : Cv_radius_weak An r) z,
  Rabs z < r -> weaksum_r_derive An r Pr1 z = weaksum_r_derive An r Pr2 z.
Proof.
intros An r Pr1 Pr2 z z_bd ;
 assert (T1 := weaksum_r_derive_sums _ _ Pr1 _ z_bd) ;
 assert (T2 := weaksum_r_derive_sums _ _ Pr2 _ z_bd).
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_r_derive_unique : forall An r(Pr1 Pr2 : finite_cv_radius An r) z,
  Rabs z < r -> sum_r_derive An r Pr1 z = sum_r_derive An r Pr2 z .
Proof.
intros An r Pr1 Pr2 z z_bd ;
 assert (T1 := sum_r_derive_sums _ _ Pr1 _ z_bd) ;
 assert (T2 := sum_r_derive_sums _ _ Pr2 _ z_bd).
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_derive_unique : forall (An : nat -> R) (Pr1 Pr2 : infinite_cv_radius An) (z : R),
  sum_derive An Pr1 z = sum_derive An Pr2 z .
Proof.
intros An Pr1 Pr2 z ;
 assert (T1 := sum_derive_sums _ Pr1 z) ;
 assert (T2 := sum_derive_sums _ Pr2 z).
 eapply Rpser_unique ; eassumption.
Qed.

(** * The formal derivative is, inside the cv-disk, the actual derivative. *)

(** Weaksum_r's case. *)

Lemma derivable_pt_lim_weaksum_r : forall An r (Pr : Cv_radius_weak An r) x,
  Rabs x < r -> derivable_pt_lim (weaksum_r An r Pr) x (weaksum_r_derive An r Pr x).
Proof.
intros An r rho x x_in ; unfold weaksum_r_derive ;
  assert (r_pos: 0 <= r) by (left ; apply Rle_lt_trans with (Rabs x) ;
   [apply Rabs_pos | assumption]) ; destruct (Rlt_le_dec (Rabs x) r) as [x_bd | x_nbd].
  apply derivable_pt_lim_Rball_derivable_pt_lim with 0 r r_pos.
   apply Rball_0_simpl ; assumption.
  assert (r'_pos: 0 <= middle (Rabs x) r) by (apply middle_le_le_pos ;
   [apply Rabs_pos | assumption]).
  apply derivable_pt_lim_in_weaksum_r_strong with r'_pos ; rewrite Rball_0_simpl ;
    [| eapply middle_is_in_the_middle] ; assumption.
  exfalso ; apply Rlt_irrefl with (Rabs x), Rlt_le_trans with r ; assumption.
Qed.

(** This implies the derivability & continuity of the weaksum_rs. *)

Lemma derivable_pt_weaksum_r : forall An (r:R) (Pr : Cv_radius_weak An r) x,
  Rabs x < r -> derivable_pt (weaksum_r An r Pr) x.
Proof.
intros An r rho x x_bd ; eexists ; eapply derivable_pt_lim_weaksum_r ; assumption.
Qed.

Lemma derive_Rball_weaksum_r: forall An r r_pos (rho : Cv_radius_weak An r) pr,
  (derive_Rball (weaksum_r An r rho) 0 r r_pos pr ==
  weaksum_r_derive An r rho)%F.
Proof.
intros An r r_pos rho pr x ; unfold derive_Rball, weaksum_r_derive.
 destruct (Rlt_le_dec (Rabs x) r) as [x_bd | x_nbd] ;
 destruct (in_Rball_dec 0 r r_pos x) as [x_in | x_nin].
  destruct (pr x x_in) as [l Hl] ; simpl.
 eapply derivable_pt_lim_Rball_uniqueness ; try eassumption.
 assert (mid_pos: 0 <= middle (Rabs x) r) by (apply middle_le_le_pos ;
  [apply Rabs_pos | assumption]).
 apply derivable_pt_lim_in_weaksum_r_strong with mid_pos.
  assumption.
  apply Rball_0_simpl, middle_is_in_the_middle ; assumption.
 exfalso ; apply x_nin, Rball_0_simpl ; assumption.
 exfalso ; apply (Rlt_irrefl (Rabs x)) ; apply Rlt_le_trans with r.
  erewrite <- Rball_0_simpl ; eassumption.
  assumption.
 reflexivity.
Qed.

(* TODO: Lemma derive_pt_weaksum_r (see Lemma derive_pt_sum) *)

Lemma continuity_pt_weaksum_r : forall An r (Pr : Cv_radius_weak An r) x,
  Rabs x < r -> continuity_pt (weaksum_r An r Pr) x.
Proof.
intros An r rho x x_bd ; apply derivable_continuous_pt ; apply derivable_pt_weaksum_r ;
 assumption.
Qed.

(** Sum_r's case. *)

Lemma derivable_pt_lim_sum_r : forall An r (Pr : finite_cv_radius An r) z,
      Rabs z < r -> derivable_pt_lim (sum_r An r Pr) z (sum_r_derive An r Pr z).
Proof.
intros An r rho z z_bd eps eps_pos.
assert (z_bd2 : Rabs z < middle (Rabs z) r) by (apply middle_is_in_the_middle ;
 assumption).
assert (pr : Cv_radius_weak An (middle (Rabs z) r)).
 apply (proj1 rho) ; split ; [left ; apply middle_le_lt_pos_lt |
 apply middle_is_in_the_middle] ; [| apply Rle_lt_trans with (Rabs z) |] ;
 (apply Rabs_pos || assumption).
 destruct (derivable_pt_lim_weaksum_r _ _ pr z z_bd2 eps eps_pos)
 as [d1 Hd1].
 pose (d2 := middle (Rabs z) r - Rabs z).
 assert (d2_pos : 0 < d2).
  unfold d2 ; apply Rlt_Rminus ; apply middle_is_in_the_middle ; assumption.
 pose (d := Rmin d1 d2).
 assert (d_pos : 0 < d).
  unfold d ; apply Rmin_pos_lt ; [apply d1 | assumption].
 pose (delta := mkposreal d d_pos) ; exists delta ; intros h h_neq h_bd.
 assert (Rabs (z + h) < middle (Rabs z) r).
  apply Rle_lt_trans with (Rabs z + Rabs h) ; [apply Rabs_triang |].
  apply Rlt_le_trans with (Rabs z + delta).
  apply Rplus_lt_compat_l ; assumption.
  apply Rle_trans with (Rabs z + (middle (Rabs z) r - Rabs z)).
  apply Rplus_le_compat_l ; unfold delta ; apply Rmin_r.
  right ; ring.
 assert (Rabs (z + h) < r).
  apply Rlt_trans with (middle (Rabs z) r) ;
  [| apply middle_is_in_the_middle] ; assumption.
 specify2 Hd1 h h_neq.
 repeat erewrite sum_r_unfold.
 eapply Rle_lt_trans ; [| eapply Hd1].
 right ; apply Rabs_eq_compat ; apply Rminus_eq_compat.
 reflexivity.
 unfold weaksum_r_derive, sum_r_derive ;
 destruct (Rlt_le_dec (Rabs z) (middle (Rabs z) r)) as [z_bd' | Hf].
 apply sum_r_unfold ; [| do 2 apply middle_is_in_the_middle] ; assumption.
 assert (T := proj1 (middle_is_in_the_middle _ _ z_bd)) ; clear - Hf T ;
 exfalso ; fourier.
 apply Rlt_le_trans with delta ; [assumption | unfold delta ; apply Rmin_l].
 assumption.
 assumption.
 assumption.
 assumption.
Qed.

Lemma derivable_pt_lim_in_sum_r: forall An r r_pos (rho : finite_cv_radius An r) x,
  Rball 0 r r_pos x ->
  derivable_pt_lim_in (sum_r An r rho) (Rball 0 r r_pos) x (sum_r_derive An r rho x).
Proof.
intros ; apply derivable_pt_lim_derivable_pt_lim_in, derivable_pt_lim_sum_r ;
 erewrite <- Rball_0_simpl ; eassumption.
Qed.

(** This implies the derivability & continuity of the sum_rs. *)

Lemma derivable_Rball_sum_r: forall An r r_pos (rho: finite_cv_radius An r),
  derivable_Rball (sum_r An r rho) 0 r r_pos.
Proof.
intros An r r_pos rho x x_in ; eexists ;
  apply derivable_pt_lim_in_sum_r ; assumption.
Qed.

Lemma derive_Rball_sum_r: forall An r r_pos (rho: finite_cv_radius An r)
  (pr: derivable_Rball (sum_r An r rho) 0 r r_pos),
  Rball_eq 0 r r_pos (derive_Rball (sum_r An r rho) 0 r r_pos pr)
  (sum_r_derive An r rho).
Proof.
intros An r r_pos rho pr x x_in ;
 eapply derivable_pt_lim_in_derive_Rball, derivable_pt_lim_in_sum_r ;
 eassumption.
Qed.

Lemma derivable_pt_sum_r : forall An r (Pr : finite_cv_radius An r) x,
  Rabs x < r -> derivable_pt (sum_r An r Pr) x.
Proof.
intros An r rho x x_bd ; assert (r_pos: 0 <= r) by (transitivity (Rabs x) ;
 [apply Rabs_pos | left ; assumption]) ; eapply derivable_Rball_derivable_pt
 with (r_pos := r_pos) ; [eapply derivable_Rball_sum_r | eapply Rball_0_simpl ;
 eassumption].
Qed.

(* TODO: Lemma derive_pt_sum_r (see Lemma derive_pt_sum) *)

Lemma continuity_pt_sum_r : forall (An:nat->R) (r:R) (Pr : finite_cv_radius An r) x,
      Rabs x < r -> continuity_pt (sum_r An r Pr) x.
Proof.
intros An r rho x x_bd ; apply derivable_continuous_pt ; apply derivable_pt_sum_r ;
 assumption.
Qed.

(** Sum's case. *)

Lemma derivable_pt_lim_sum : forall An (Pr : infinite_cv_radius An), forall z,
      derivable_pt_lim (sum An Pr) z (sum_derive An Pr z).
Proof.
intros An rho z eps eps_pos.
 assert (z_bd : Rabs z < Rabs z + 1) by fourier. 
 destruct (derivable_pt_lim_weaksum_r _ _ (rho _) _ z_bd _ eps_pos) as [d Hd].
 pose (d' := Rmin d (1 / 2)).
 assert (d'_pos : 0 < d').
  unfold Rmin ; apply Rmin_pos_lt ; [apply d | fourier].
 pose (delta := mkposreal d' d'_pos) ; exists delta ; intros h h_neq h_bd ;
 specify2 Hd h h_neq ; eapply Rle_lt_trans ; [| eapply Hd].
 right ; apply Rabs_eq_compat ; apply Rminus_eq_compat.
 unfold Rdiv ; apply Rmult_eq_compat_r ; unfold sum ; apply Rminus_eq_compat ;
 apply weaksum_r_unique_strong ; auto.
 apply Rle_lt_trans with (Rabs (z + h) + 0) ; [right ; ring | fourier].
 apply Rle_lt_trans with (Rabs z + Rabs h) ; [apply Rabs_triang |] ;
 apply Rplus_lt_compat_l ; apply Rlt_trans with (1/2) ; [apply Rlt_le_trans with
 delta |] ; [| unfold delta ; apply Rmin_r |] ; fourier.
 unfold sum_derive, sum, weaksum_r_derive ;
 destruct (Rlt_le_dec (Rabs z) (Rabs z + 1)) as [H | Hf].
 apply weaksum_r_unique_strong ; [| apply middle_is_in_the_middle] ; assumption.
 exfalso ; apply (Rlt_irrefl (Rabs z)) ; apply Rlt_le_trans with (Rabs z + 1) ;
 fourier.
 apply Rlt_le_trans with delta ; [assumption | unfold delta ; apply Rmin_l].
Qed.
 

(** This implies the derivability & continuity of the sums. *)

Lemma derivable_pt_sum : forall (An : Rseq) (Pr : infinite_cv_radius An) x,
      derivable_pt (sum An Pr) x.
Proof.
intros An rho x.
 exists (sum_derive An rho x) ; apply derivable_pt_lim_sum ; assumption.
Qed.

Lemma derive_pt_sum : forall (An : Rseq)
  (rAn : infinite_cv_radius An) (rdAn : infinite_cv_radius (An_deriv An)) x
  (dAn : derivable_pt (sum An rAn) x),
  derive_pt (sum An rAn) x dAn = sum (An_deriv An) rdAn x.
Proof.
intros ; rewrite derive_pt_eq.
 replace (sum (An_deriv An) rdAn x) with (sum_derive An rAn x).
 apply derivable_pt_lim_sum.
 apply sum_unique.
Qed.

Lemma continuity_pt_sum : forall (An:nat->R) (Pr : infinite_cv_radius An) x,
  continuity_pt (sum An Pr) x.
Proof.
intros An rho x ; apply derivable_continuous_pt ; apply derivable_pt_sum.
Qed.

(** * Derivability / continuity of the sum when the cv disk as an infinite radius *)

Lemma derivable_sum : forall (An:nat->R) (Pr : infinite_cv_radius An),
  derivable (sum An Pr).
Proof.
intros An rho x ; apply derivable_pt_sum.
Qed.

Lemma continuity_sum : forall (An:nat->R) (Pr : infinite_cv_radius An),
  continuity (sum An Pr).
Proof.
intros An rho x ; apply derivable_continuous ; apply derivable_sum.
Qed.