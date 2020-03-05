Require Import Reals Lra.
Require Import Rsequence.
Require Import Rseries_def Rseries_cv_facts.
Require Import Rpser_def Rpser_sums Rpser_base_facts Rpser_cv_facts Rpser_radius_facts.

Require Import Rinterval Rfunction_def Rextensionality.

Local Open Scope R_scope.

(** * Compatibility of Rpser with Rseq_prod (Mertens' theorem) *)

Lemma Rpser_prod_compat: forall An Bn x la la' lb,
  Rpser An x la -> Rpser_abs An x la' -> Rpser Bn x lb ->
  Rpser (An # Bn) x (la * lb).
Proof.
intros An Bn x la la' lb Ha Ha' Hb.
 eapply Rseq_cv_eq_compat ; [apply Rseq_pps_prod_unfold |].
 eapply Rser_cv_prod_compat ; eassumption.
Qed.

(** * Unfolding sums. *)

Lemma sum_r_unfold : forall An r r' (pr1 : finite_cv_radius An r)
  (pr2 : Cv_radius_weak An r') x, Rabs x < r -> Rabs x < r' ->
  sum_r An r pr1 x = weaksum_r An r' pr2 x.
Proof.
intros An r r' pr1 pr2 x x_bd x_bd' ; unfold sum_r ;
 destruct (Rlt_le_dec (Rabs x) r) as [H1 | Hf] ; [| exfalso ; lra].
 apply weaksum_r_unique_strong ; [apply middle_is_in_the_middle |] ;
 assumption.
Qed.

Lemma sum_unfold : forall An r (pr1 : infinite_cv_radius An)
  (pr2 : Cv_radius_weak An r) x, Rabs x < r ->
  sum An pr1 x = weaksum_r An r pr2 x.
Proof.
intros An r pr1 pr2 x x_ub ; unfold sum ;
 apply weaksum_r_unique_strong ; [lra | assumption].
Qed.

(** * Compatibility of weaksum_r with the common operations. *)
Section weaksum_r_compatibilities.

Variable x r : R.
Variables An Bn : Rseq.
Hypotheses
  (x_bd : Rabs x < r)
  (rAn : Cv_radius_weak An r)
  (rBn : Cv_radius_weak Bn r).

Lemma weaksum_r_expand_compat : forall l (rAn' : Cv_radius_weak (An_expand An l) r),
  Rabs (l * x) < r ->
  weaksum_r (An_expand An l) r rAn' x = weaksum_r An r rAn (l * x).
Proof.
intros l rAn' xl_bd ;
 assert (H1 := weaksum_r_sums _ _ rAn' x x_bd) ;
 assert (H2 := Rpser_expand_compat _ _ _ _ (weaksum_r_sums _ _ rAn (l * x) xl_bd)) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma weaksum_r_scal_compat : forall (k: R) (rAn' : Cv_radius_weak (k * An)%Rseq r),
  weaksum_r (k * An)%Rseq r rAn' x = ((fun _ => k) * weaksum_r An r rAn)%F x.
Proof.
intros k rAn'.
 assert (H1 := weaksum_r_sums _ _ rAn' x x_bd) ;
 assert (H2 := Rpser_scal_compat k _ _ _ (weaksum_r_sums _ _ rAn x x_bd)) ;
 eapply Rpser_unique ; unfold mult_fct ; eassumption.
Qed.

Lemma weaksum_r_opp_compat : forall (rAn' : Cv_radius_weak (- An) r),
  weaksum_r (- An)%Rseq r rAn' x = (- weaksum_r An r rAn)%F x.
Proof.
intros rAn'.
 assert (H1 := weaksum_r_sums (- An)%Rseq _ rAn' x x_bd) ;
 assert (H2 := Rpser_opp_compat _ _ _ (weaksum_r_sums An _ rAn x x_bd)) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma weaksum_r_plus_compat : forall (rAnBn : Cv_radius_weak (An + Bn) r),
  weaksum_r (An + Bn)%Rseq r rAnBn x = (weaksum_r An r rAn + weaksum_r Bn r rBn)%F x.
Proof.
intros rAnBn.
 assert (Ha := weaksum_r_sums An r rAn x x_bd) ;
 assert (Hb := weaksum_r_sums Bn r rBn x x_bd) ;
 assert (H1 := weaksum_r_sums (An + Bn)%Rseq r rAnBn x x_bd) ;
 assert (H2 := Rpser_add_compat _ _ _ _ _ Ha Hb) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma weaksum_r_minus_compat : forall (rAnBn : Cv_radius_weak (An - Bn) r),
  weaksum_r (An - Bn)%Rseq r rAnBn x = (weaksum_r An r rAn - weaksum_r Bn r rBn)%F x.
Proof.
intros rAnBn.
 assert (Ha := weaksum_r_sums An r rAn x x_bd) ;
 assert (Hb := weaksum_r_sums Bn r rBn x x_bd) ;
 assert (H1 := weaksum_r_sums (An - Bn)%Rseq r rAnBn x x_bd) ;
 assert (H2 := Rpser_minus_compat _ _ _ _ _ Ha Hb) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma weaksum_r_mult_compat : forall (rAnBn : Cv_radius_weak (An # Bn) r),
  weaksum_r (An # Bn)%Rseq r rAnBn x = (weaksum_r An r rAn * weaksum_r Bn r rBn)%F x.
Proof.
intros rAnBn ; destruct (Rpser_abs_cv_radius_weak _ _ rAn x x_bd) as [l Ha'].
 assert (Ha := weaksum_r_sums An r rAn x x_bd) ;
 assert (Hb := weaksum_r_sums Bn r rBn x x_bd) ;
 assert (H1 := weaksum_r_sums (An # Bn)%Rseq r rAnBn x x_bd) ;
 assert (H2 := Rpser_prod_compat _ _ _ _ _ _ Ha Ha' Hb) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma weaksum_r_zip_compat : forall rAnBn, Rabs (x ^ 2) < r ->
  weaksum_r (Rseq_zip An Bn) r rAnBn x =
  weaksum_r An r rAn (x ^ 2) + x * weaksum_r Bn r rBn (x ^ 2).
Proof.
intros rAnBn x_bd' ;
 assert (Ha := weaksum_r_sums An r rAn (x ^ 2) x_bd') ;
 assert (Hb := weaksum_r_sums Bn r rBn (x ^ 2) x_bd') ;
 assert (Hab := weaksum_r_sums _ r rAnBn x x_bd) ;
 assert (Hab' := Rpser_zip_compat _ _ _ _ _ Ha Hb).
 eapply Rpser_unique ; eassumption.
Qed.

Lemma weaksum_r_alt_compat : forall rAn',
  weaksum_r (Rseq_alt An) r rAn' x = weaksum_r An r rAn (- x).
Proof.
intro rAn' ;
 assert (x_bd' : Rabs (- x) < r) by (rewrite Rabs_Ropp ; assumption) ;
 assert (Ha := weaksum_r_sums An r rAn _ x_bd') ;
 assert (Ha' := weaksum_r_sums _ r rAn' _ x_bd) ;
 assert (Ha'' := Rpser_alt_compat _ _ _ Ha) ;
 eapply Rpser_unique ; eassumption.
Qed.

End weaksum_r_compatibilities.

(** * Compatibility of sum_r with the common operations. *)
Section sum_r_compatibilities.

Variable x r : R.
Variables An Bn : Rseq.
Hypotheses
  (x_bd : Rabs x < r)
  (rAn : finite_cv_radius An r)
  (rBn : finite_cv_radius Bn r).

Lemma sum_r_expand_compat : forall l (rAn' : finite_cv_radius (An_expand An l) r),
  Rabs (l * x) < r ->
  sum_r (An_expand An l) r rAn' x = sum_r An r rAn (l * x).
Proof.
intros l rAn' xl_bd ;
 assert (H1 := sum_r_sums _ _ rAn' x x_bd) ;
 assert (H2 := Rpser_expand_compat _ _ _ _ (sum_r_sums _ _ rAn (l * x) xl_bd)) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_r_scal_compat : forall (k: R) (rAn' : finite_cv_radius (k * An)%Rseq r),
  sum_r (k * An)%Rseq r rAn' x = ((fun _ => k) * sum_r An r rAn)%F x.
Proof.
intros k rAn'.
 assert (H1 := sum_r_sums _ _ rAn' x x_bd) ;
 assert (H2 := Rpser_scal_compat k _ _ _ (sum_r_sums _ _ rAn x x_bd)) ;
 eapply Rpser_unique ; unfold mult_fct ; eassumption.
Qed.

Lemma sum_r_opp_compat : forall (rAn' : finite_cv_radius (- An) r),
  sum_r (- An)%Rseq r rAn' x = (- sum_r An r rAn)%F x.
Proof.
intros rAn'.
 assert (H1 := sum_r_sums (- An)%Rseq _ rAn' x x_bd) ;
 assert (H2 := Rpser_opp_compat _ _ _ (sum_r_sums An _ rAn x x_bd)) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_r_plus_compat : forall (rAnBn : finite_cv_radius (An + Bn) r),
  sum_r (An + Bn)%Rseq r rAnBn x = (sum_r An r rAn + sum_r Bn r rBn)%F x.
Proof.
intros rAnBn.
 assert (Ha := sum_r_sums An r rAn x x_bd) ;
 assert (Hb := sum_r_sums Bn r rBn x x_bd) ;
 assert (H1 := sum_r_sums (An + Bn)%Rseq r rAnBn x x_bd) ;
 assert (H2 := Rpser_add_compat _ _ _ _ _ Ha Hb) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_r_minus_compat : forall (rAnBn : finite_cv_radius (An - Bn) r),
  sum_r (An - Bn)%Rseq r rAnBn x = (sum_r An r rAn - sum_r Bn r rBn)%F x.
Proof.
intros rAnBn.
 assert (Ha := sum_r_sums An r rAn x x_bd) ;
 assert (Hb := sum_r_sums Bn r rBn x x_bd) ;
 assert (H1 := sum_r_sums (An - Bn)%Rseq r rAnBn x x_bd) ;
 assert (H2 := Rpser_minus_compat _ _ _ _ _ Ha Hb) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_r_mult_compat : forall (rAnBn : finite_cv_radius (An # Bn) r),
  sum_r (An # Bn)%Rseq r rAnBn x = (sum_r An r rAn * sum_r Bn r rBn)%F x.
Proof.
intros rAnBn.
 assert (rAn' : Cv_radius_weak An (middle (Rabs x) r)).
  apply rAn ; split ; [apply middle_le_le_pos | apply middle_is_in_the_middle].
   apply Rabs_pos.
   transitivity (Rabs x) ; [apply Rabs_pos | left ; assumption].
   assumption.
 destruct (Rpser_abs_cv_radius_weak _ _ rAn' x
  (proj1 (middle_is_in_the_middle _ _ x_bd))) as [l Ha'].
 assert (Ha := sum_r_sums An r rAn x x_bd) ;
 assert (Hb := sum_r_sums Bn r rBn x x_bd) ;
 assert (H1 := sum_r_sums (An # Bn)%Rseq r rAnBn x x_bd) ;
 assert (H2 := Rpser_prod_compat _ _ _ _ _ _ Ha Ha' Hb) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_r_zip_compat : forall rAnBn, Rabs (x ^ 2) < r ->
  sum_r (Rseq_zip An Bn) r rAnBn x =
  sum_r An r rAn (x ^ 2) + x * sum_r Bn r rBn (x ^ 2).
Proof.
intros rAnBn x_bd' ;
 assert (Ha := sum_r_sums An r rAn (x ^ 2) x_bd') ;
 assert (Hb := sum_r_sums Bn r rBn (x ^ 2) x_bd') ;
 assert (Hab := sum_r_sums _ r rAnBn x x_bd) ;
 assert (Hab' := Rpser_zip_compat _ _ _ _ _ Ha Hb).
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_r_alt_compat : forall rAn',
  sum_r (Rseq_alt An) r rAn' x = sum_r An r rAn (- x).
Proof.
intro rAn' ;
 assert (x_bd' : Rabs (- x) < r) by (rewrite Rabs_Ropp ; assumption) ;
 assert (Ha := sum_r_sums An r rAn _ x_bd') ;
 assert (Ha' := sum_r_sums _ r rAn' _ x_bd) ;
 assert (Ha'' := Rpser_alt_compat _ _ _ Ha) ;
 eapply Rpser_unique ; eassumption.
Qed.

End sum_r_compatibilities.

(** * Compatibility of sum with the common operations. *)
Section sum_compatibilities.

Variables An Bn : Rseq.
Hypotheses
  (rAn : infinite_cv_radius An)
  (rBn : infinite_cv_radius Bn).

Lemma sum_expand_compat : forall l (rAn' : infinite_cv_radius (An_expand An l)),
  forall x, sum (An_expand An l) rAn' x = sum An rAn (l * x).
Proof.
intros l rAn' x ;
 assert (H1 := sum_sums _ rAn' x) ;
 assert (H2 := Rpser_expand_compat _ _ _ _ (sum_sums An rAn (l * x))) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_scal_compat : forall (r : R) (rAn' : infinite_cv_radius (r * An)%Rseq),
  sum (r * An)%Rseq rAn' == ((fun _ => r) * sum An rAn)%F.
Proof.
intros r rAn' x.
 assert (H1 := sum_sums (r * An)%Rseq rAn' x) ;
 assert (H2 := Rpser_scal_compat r _ _ _ (sum_sums An rAn x)) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_opp_compat : forall (rAn' : infinite_cv_radius (- An)),
  sum (- An)%Rseq rAn' == (- sum An rAn)%F.
Proof.
intros rAn' x.
 assert (H1 := sum_sums (- An)%Rseq rAn' x) ;
 assert (H2 := Rpser_opp_compat _ _ _ (sum_sums An rAn x)) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_plus_compat : forall (rAnBn : infinite_cv_radius (An + Bn)),
  sum (An + Bn)%Rseq rAnBn == (sum An rAn + sum Bn rBn)%F.
Proof.
intros rAnBn x.
 assert (Ha := sum_sums An rAn x) ;
 assert (Hb := sum_sums Bn rBn x) ;
 assert (H1 := sum_sums (An + Bn)%Rseq rAnBn x) ;
 assert (H2 := Rpser_add_compat _ _ _ _ _ Ha Hb) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_minus_compat : forall (rAnBn : infinite_cv_radius (An - Bn)),
  sum (An - Bn)%Rseq rAnBn == (sum An rAn - sum Bn rBn)%F.
Proof.
intros rAnBn x.
 assert (Ha := sum_sums An rAn x) ;
 assert (Hb := sum_sums Bn rBn x) ;
 assert (H1 := sum_sums (An - Bn)%Rseq rAnBn x) ;
 assert (H2 := Rpser_minus_compat _ _ _ _ _ Ha Hb) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_mult_compat: forall (rAnBn: infinite_cv_radius (An # Bn)),
  sum (An # Bn) rAnBn == (sum An rAn * sum Bn rBn)%F.
Proof.
intros rAnBn x ; destruct (Rpser_abs_infinite_cv_radius _ rAn x) as [l Ha'].
 assert (Ha := sum_sums _ rAn x) ;
 assert (Hb := sum_sums _ rBn x) ;
 assert (Hab := Rpser_prod_compat _ _ _ _ _ _ Ha Ha' Hb) ;
 assert (Hab' := sum_sums _ rAnBn x) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_zip_compat : forall rAnBn x,
  sum (Rseq_zip An Bn) rAnBn x =
  sum An rAn (x ^ 2) + x * sum Bn rBn (x ^ 2).
Proof.
intros rAnBn x ;
 assert (Ha := sum_sums An rAn (x ^ 2)) ;
 assert (Hb := sum_sums Bn rBn (x ^ 2)) ;
 assert (Hab := sum_sums _ rAnBn x) ;
 assert (Hab' := Rpser_zip_compat _ _ _ _ _ Ha Hb).
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_alt_compat : forall rAn' x,
  sum (Rseq_alt An) rAn' x = sum An rAn (- x).
Proof.
intros rAn' x ;
 assert (Ha := sum_sums An rAn (- x)) ;
 assert (Ha' := sum_sums _ rAn' x) ;
 assert (Ha'' := Rpser_alt_compat _ _ _ Ha) ;
 eapply Rpser_unique ; eassumption.
Qed.

End sum_compatibilities.