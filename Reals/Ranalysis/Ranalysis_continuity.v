Require Import Rbase Ranalysis.
Require Import Rinterval Rfunctions Rfunction_def.
Require Import Ranalysis_def Ranalysis_def_simpl Rfunction_facts.
Require Import MyRIneq MyR_dist Lra.

Require Import Tactics.

Local Open Scope R_scope.

(** * Extensionality of continuity_pt_in *)

Lemma continuity_pt_in_ext : forall D (f g : R -> R) x,
  (f == g)%F -> continuity_pt_in D f x -> continuity_pt_in D g x.
Proof.
intros D f g x Heq Hf Dx ; eapply limit1_in_ext.
 intros ; apply Heq.
 rewrite <- (Heq x) ; apply Hf ; assumption.
Qed.

Lemma continuity_pt_in_ext_strong : forall (D : R -> Prop) (f g : R -> R) x,
  (forall x, D x -> f x = g x)%F ->
  continuity_pt_in D f x -> continuity_pt_in D g x.
Proof.
intros D f g x Heq Hf Dx ; eapply limit1_in_ext.
 eexact Heq.
 rewrite <- (Heq x) ; [apply Hf |] ; assumption.
Qed.

Lemma continuity_in_ext : forall D (f g : R -> R),
  (f == g)%F -> continuity_in D f -> continuity_in D g.
Proof.
intros D f g Heq Hf x ; eapply continuity_pt_in_ext, Hf ; eassumption.
Qed.

Lemma continuity_in_ext_strong : forall (D : R -> Prop) f g,
  (forall x, D x -> f x = g x)%F ->
  continuity_in D f -> continuity_in D g.
Proof.
intros D f g Heq Hf x ; eapply continuity_pt_in_ext_strong, Hf ; eassumption.
Qed.

(** * How to relate the different notions of continuity. *)

Lemma continuity_pt_continuity_pt_in: forall f (D : R -> Prop) x,
  continuity_pt f x -> continuity_pt_in D f x.
Proof.
intros f D x Hf Dx eps eps_pos ;
 destruct (Hf _ eps_pos) as [alp [alp_pos Halp]] ;
 exists alp ; split ; [assumption | intros y [Dy y_bd]].
 destruct (Req_dec x y) as [Heq | Hneq].
 subst ; rewrite R_dist_eq ; assumption.
 apply Halp ; repeat split ; assumption.
Qed.

Lemma continuity_continuity_in: forall D f,
  continuity f -> continuity_in D f.
Proof.
intros D f f_cont x x_in ; apply continuity_pt_continuity_pt_in ;
 [apply f_cont |] ; assumption.
Qed.

Lemma continuity_interval_continuity_pt: forall f lb ub x, lb < ub ->
  continuity_interval lb ub f -> open_interval lb ub x ->
  continuity_pt f x.
Proof.
intros f lb ub x lb_lt_ub Hf x_in eps eps_pos ;
 assert (x_in' := open_interval_interval _ _ _ x_in) ;
 destruct (Hf _ x_in' _ eps_pos) as [alpha [alpha_pos Halpha]].
 exists (Rmin alpha (interval_dist lb ub x)) ; split.
  apply Rmin_pos_lt, open_interval_dist_pos ; assumption.
  intros y [[_ x_neq_y] y_bd] ; apply Halpha ; split.
   replace y with (x + (y -x)) by ring ; apply interval_dist_bound.
    assumption.
    left ; eapply Rlt_le_trans ; [eassumption | apply Rmin_r].
    eapply Rlt_le_trans ; [eassumption | apply Rmin_l].
Qed.

Lemma continuity_open_interval_continuity : forall f,
  (forall lb ub, continuity_open_interval lb ub f) ->
  continuity f.
Proof.
intros f Hf x eps eps_pos ;
 destruct (Hf _ _ _ (center_in_open_interval x 1 Rlt_0_1) _ eps_pos) as [delta [delta_pos Hdelta]] ;
 exists (Rmin delta 1) ; split.
  apply Rmin_pos_lt ; lra.
  simpl ; intros y [[_ y_neq] y_b] ; apply Hdelta ; split.
   rewrite <- Rball_rewrite ; eapply Rlt_le_trans ; [eassumption | apply Rmin_r].
   eapply Rlt_le_trans ; [eassumption | apply Rmin_l].
Qed.

(** * Simple compatibility results on continuity_in *)

Lemma continuity_in_const : forall D c, continuity_in D (fun _ => c).
Proof.
intros ; exists 1 ; split ; [lra |] ;
 intros ; rewrite R_dist_eq ; assumption.
Qed.

Lemma continuity_in_opp : forall D f,
  continuity_in D f -> continuity_in D (- f)%F.
Proof.
intros D f Hf x x_in ; apply limit_Ropp ; eapply_assumption ; assumption.
Qed.

Lemma continuity_pt_in_opp_rev : forall f D x,
  continuity_pt_in D (- f)%F x -> continuity_pt_in D f x.
Proof.
intros f D x Hf x_in ; apply limit1_in_ext with (- - f)%F.
 intros y y_in ; apply Ropp_involutive.
 rewrite <- (Ropp_involutive (f x)) ;
 apply limit_Ropp, Hf ; assumption.
Qed.

Lemma continuity_in_plus : forall D f g,
  continuity_in D f -> continuity_in D g ->
  continuity_in D (f + g)%F.
Proof.
intros f g a b Hf Hg x x_in ; apply limit_plus ; eapply_assumption ;
 assumption.
Qed.

Lemma continuity_in_minus : forall D f g,
  continuity_in D f -> continuity_in D g ->
  continuity_in D (f - g)%F.
Proof.
intros f g a b Hf Hg x x_in ; apply limit_minus ; eapply_assumption ;
 assumption.
Qed.

Lemma continuity_in_mult : forall D f g,
  continuity_in D f -> continuity_in D g ->
  continuity_in D (f * g)%F.
Proof.
intros f g a b Hf Hg x x_in ; apply limit_mul ; eapply_assumption ;
 assumption.
Qed.

(** Special case: (open) interval *)

Lemma continuity_open_interval_Ropp_compat : forall f lb ub,
  continuity_open_interval lb ub f ->
  continuity_open_interval (- ub) (- lb) (fun x => f (- x)).
Proof.
intros f lb ub Hf b b_in eps eps_pos.
 assert (mb_in : open_interval lb ub (- b)).
  destruct b_in ; split ; lra.
 destruct (Hf _ mb_in _ eps_pos) as [alpha [alpha_pos Halpha]] ;
 exists alpha ; split ; [assumption | intros x [x_in x_bd]].
 apply Halpha ; split ; simpl.
  destruct x_in ; split ; lra.
  rewrite R_dist_opp_compat ; assumption.
Qed.

Lemma continuity_open_interval_Ropp_compat_rev : forall f lb ub,
  continuity_open_interval (- ub) (- lb) (fun x => f (- x)) ->
  continuity_open_interval lb ub f.
Proof.
intros f lb ub Hf ; pose (F := fun x => f (- x)) ;
 apply continuity_in_ext with (fun x => F (- x)).
 intro x ; unfold F ; f_equal ; apply Ropp_involutive.
  rewrite <- (Ropp_involutive lb), <- (Ropp_involutive ub) ;
  apply continuity_open_interval_Ropp_compat, Hf.
Qed.

Lemma continuity_interval_Ropp_compat : forall f lb ub,
  continuity_interval lb ub f ->
  continuity_interval (- ub) (- lb) (fun x => f (- x)).
Proof.
intros f lb ub Hf b b_in eps eps_pos.
 assert (mb_in : interval lb ub (- b)).
  destruct b_in ; split ; lra.
 destruct (Hf _ mb_in _ eps_pos) as [alpha [alpha_pos Halpha]] ;
 exists alpha ; split ; [assumption | intros x [x_in x_bd]].
 apply Halpha ; split ; simpl.
  destruct x_in ; split ; lra.
  rewrite R_dist_opp_compat ; assumption.
Qed.

Lemma continuity_interval_Ropp_compat_rev : forall f lb ub,
  continuity_interval (- ub) (- lb) (fun x => f (- x)) ->
  continuity_interval lb ub f.
Proof.
intros f lb ub Hf ; pose (F := fun x => f (- x)) ;
 apply continuity_in_ext with (fun x => F (- x)).
 intro x ; unfold F ; f_equal ; apply Ropp_involutive.
  rewrite <- (Ropp_involutive lb), <- (Ropp_involutive ub) ;
  apply continuity_interval_Ropp_compat, Hf.
Qed.

(** If f x <> y and f continue then there is a ball B around x such that y is not in f B. *)

(* TODO: move this *)

Lemma continuity_not_eq_Rball : forall f (D : R -> Prop) x y,
  D x -> continuity_pt_in D f x -> f x <> y ->
  exists alp, 0 < alp /\ forall a, D a -> Rball x alp a -> f a <> y.
Proof.
intros f D x y Dx f_cont Hneq ; pose (eps := R_dist (f x) y / 2).
 assert (eps_pos: 0 < eps).
  unfold eps, Rdiv ; apply Rlt_mult_inv_pos.
   apply Rabs_pos_lt ; intro Hf ; apply Hneq, Rminus_diag_uniq ; assumption.
   lra.
 destruct (f_cont Dx eps eps_pos) as [alp [alp_pos Halp]] ; exists alp ; split.
  assumption.
  intros a Da a_in ; apply Rminus_not_eq, Rabs_pos_lt_contravar.
  transitivity (Rabs (f x - y) - eps).
   apply Rlt_le_trans with eps ; [assumption | right ; unfold eps, R_dist ; field].
   apply Rlt_minus_swap ; apply Rle_lt_trans with (dist R_met (f x - y) (f a - y)) ;
   [apply Rabs_triang_inv | rewrite R_dist_sym, R_dist_minus_compat].
 apply Halp ; split ; [| unfold R_dist] ; assumption.
Qed.
