Require Import Rbase Rfunctions Fourier.
Require Import MyRIneq MyNeq.
Require Import Ass_handling.

(** * The definitions used in this file: [middle], [interval], [Rball]. *)

Definition middle (x:R) (y:R) : R := (x + y) / 2.
Definition interval_dist lb ub x := Rmin (x - lb) (ub - x).

Definition interval (lb ub x : R) := lb <= x <= ub.
Definition open_interval (lb ub x:R) := lb < x < ub.

Definition Rball c r (r_pos: 0 <= r) x := Rabs (x - c) < r.
Definition Rball_dist c r := interval_dist (c - r) (c + r).

Definition Rball_eq c r r_pos (f g : R -> R) := forall x,
  Rball c r r_pos x -> f x = g x.

Lemma Rball_eq_refl: forall c r r_pos f, Rball_eq c r r_pos f f.
Proof.
unfold Rball_eq ; trivial.
Qed.

Lemma Rball_eq_sym: forall c r r_pos f g, Rball_eq c r r_pos f g -> Rball_eq c r r_pos g f.
Proof.
unfold Rball_eq ; intros ; symmetry ; auto.
Qed.

Lemma Rball_eq_trans: forall c r r_pos f g h, Rball_eq c r r_pos f g ->
  Rball_eq c r r_pos g h -> Rball_eq c r r_pos f h.
Proof.
unfold Rball_eq ; intros ; transitivity (g x) ; auto.
Qed.

Require Setoid.

Add Parametric Relation (c r: R) (r_pos: 0 <= r): (R -> R) (Rball_eq c r r_pos)
reflexivity proved by (Rball_eq_refl c r r_pos)
symmetry proved by (Rball_eq_sym c r r_pos)
transitivity proved by (Rball_eq_trans c r r_pos) as Rball_eq'.

(** * [middle]'s properties. *)

(** Remarkable properties. *)

Lemma middle_identity : forall x, middle x x = x.
Proof.
intros ; unfold middle ; field.
Qed.

Lemma middle_comm : forall x y, middle x y = middle y x.
Proof.
intros ; unfold middle ; field.
Qed.

Lemma middle_unfold : forall x y, middle x y = (x + y) / 2.
Proof.
intros ; reflexivity.
Qed.

Lemma middle_R0 : forall x, middle (- x) x = 0.
Proof.
intros ; unfold middle ; field.
Qed.

(** Compatibility with the orders. *)

Lemma middle_is_in_the_middle : forall x y, x < y -> x < middle x y < y.
Proof.
intros x y x_lt_y ; split.
 apply Rle_lt_trans with (middle x x).
 right ; symmetry ; apply middle_identity.
 unfold middle, Rdiv ; apply Rmult_lt_compat_r ; [fourier |] ;
 apply Rplus_lt_compat_l ; assumption.
 apply Rlt_le_trans with (middle y y).
 unfold middle, Rdiv ; apply Rmult_lt_compat_r ; [fourier |] ;
 apply Rplus_lt_compat_r ; assumption.
 right ; apply middle_identity.
Qed.

Lemma middle_is_in_the_middle': forall x y, x <= y -> x <= middle x y <= y.
Proof.
intros x y xley ; destruct (Req_dec x y).
 subst ; rewrite middle_identity ; auto.
 split ; left ; apply middle_is_in_the_middle, Rle_neq_lt ; assumption.
Qed.

Lemma Rabs_middle_is_in_the_middle : forall x y, 0 <= x -> x < y ->
  x < Rabs (middle x y) < y.
Proof.
intros x y x_pos x_lt_y.
 assert (mxy_pos : 0 < middle x y).
  apply Rle_lt_trans with x ;
  [| apply middle_is_in_the_middle] ;
  assumption.
 rewrite Rabs_pos_eq ;
 [ apply middle_is_in_the_middle |] ;
 intuition.
Qed.

Lemma middle_le_le_pos : forall x y, 0 <= x -> 0 <= y -> 0 <= middle x y.
Proof.
intros x y x_pos y_pos ; unfold middle, Rdiv ;
 apply Rle_mult_inv_pos ; fourier.
Qed.

Lemma middle_lt_lt_pos_lt : forall x y, 0 < x -> 0 < y -> 0 < middle x y.
Proof.
intros x y x_pos y_pos ; unfold middle, Rdiv ;
 apply Rlt_mult_inv_pos ; fourier.
Qed.

Lemma middle_le_lt_pos_lt : forall x y, 0 <= x -> 0 < y -> 0 < middle x y.
Proof.
intros x y x_pos y_pos ; unfold middle, Rdiv ;
 apply Rlt_mult_inv_pos ; fourier.
Qed.

Lemma middle_lt_le_pos_lt : forall x y, 0 < x -> 0 <= y -> 0 < middle x y.
Proof.
intros x y x_pos y_pos ; rewrite middle_comm ;
 apply middle_le_lt_pos_lt ; assumption.
Qed.

Lemma middle_lt_lt_neg_lt : forall x y, x < 0 -> y < 0 -> middle x y < 0.
Proof.
intros x y x_neg y_neg ; unfold middle, Rdiv ;
 replace 0 with ((x + y) * 0) by ring ;
 apply Rmult_lt_gt_compat_neg_l ; fourier.
Qed.

Lemma middle_le_lt_neg_lt : forall x y, x <= 0 -> y < 0 -> middle x y < 0.
Proof.
intros x y x_pos y_pos ; unfold middle, Rdiv ;
  replace 0 with ((x + y) * 0) by ring ;
 apply Rmult_lt_gt_compat_neg_l ; fourier.
Qed.

Lemma middle_lt_le_neg_lt : forall x y, x < 0 -> y <= 0 -> middle x y < 0.
Proof.
intros x y x_neg y_neg ; rewrite middle_comm ;
 apply middle_le_lt_neg_lt ; assumption.
Qed.

(** * [interval]'s properties. *)

Lemma interval_l : forall lb ub, lb <= ub -> interval lb ub lb.
Proof.
intros ; split ; [right |] ; trivial.
Qed.

Lemma interval_r : forall lb ub, lb <= ub -> interval lb ub ub.
Proof.
intros ; split ; [| right] ; trivial.
Qed.

Lemma open_interval_interval : forall lb ub x,
     open_interval lb ub x -> interval lb ub x.
Proof.
 intros ; split ; unfold open_interval in * ; intuition.
Qed.

Lemma interval_opp_compat : forall lb ub x,
     interval lb ub x ->
     interval (-ub) (-lb) (-x).
Proof.
intros ; unfold interval in * ; split ; intuition ; fourier.
Qed.

Lemma open_interval_opp_compat : forall lb ub x,
     open_interval lb ub x ->
     open_interval (-ub) (-lb) (-x).
Proof.
intros ; unfold open_interval in * ; split ; intuition ; fourier.
Qed.

Lemma interval_middle_compat: forall lb ub x y,
  interval lb ub x -> interval lb ub y ->
  interval lb ub (middle x y).
Proof.
intros lb ub x y x_in_I y_in_I.
  split ; unfold middle, interval in *.
  replace lb with ((lb + lb) * /2) by field.
  unfold Rdiv ; apply Rmult_le_compat_r ; intuition.
  replace ub with ((ub + ub) * /2) by field.
  unfold Rdiv ; apply Rmult_le_compat_r ; intuition.
Qed.

Lemma open_interval_middle_compat:  forall lb ub x y,
  open_interval lb ub x -> open_interval lb ub y ->
  open_interval lb ub (middle x y).
Proof.
intros lb ub x y x_in_I y_in_I.
  split ; unfold middle, open_interval in *.
  replace lb with ((lb + lb) * /2) by field.
  unfold Rdiv ; apply Rmult_lt_compat_r ; intuition.
  replace ub with ((ub + ub) * /2) by field.
  unfold Rdiv ; apply Rmult_lt_compat_r ; intuition.
Qed.

(** Decidability results. *)

Lemma in_interval_dec: forall lb ub x,
  { interval lb ub x } + { ~ interval lb ub x }.
Proof.
intros lb ub x.
  destruct (Rle_lt_dec lb x).
   destruct (Rle_lt_dec x ub).
    left ; split ; assumption.
    right ; intros [_ Hf] ; fourier.
   right ; intros [Hf _] ; fourier.
Qed.

Lemma in_open_interval_dec: forall lb ub x,
  { open_interval lb ub x } + { ~ open_interval lb ub x }.
intros lb ub x.
  destruct (Rlt_le_dec lb x).
   destruct (Rlt_le_dec x ub).
    left ; split ; assumption.
    right ; intros [_ Hf] ; fourier.
   right ; intros [Hf _] ; fourier.
Qed.

Lemma interval_open_interval_dec: forall lb ub x,
  interval lb ub x ->
  { x = lb } + { open_interval lb ub x } + { x = ub }.
Proof.
intros lb ub x [H1 H2].
  destruct (Req_dec x lb).
   left ; left ; assumption.
   destruct (Req_dec x ub).
    right ; assumption.
    left ; right ; split.
     apply Rneq_le_lt ; [symmetry |] ; assumption.
     apply Rneq_le_lt ; assumption.
Qed.

(** Extensional equality implies equality. *)

Lemma open_interval_ext_eq: forall lb1 lb2 ub1 ub2, lb1 < ub1 ->
  (forall x, open_interval lb1 ub1 x <-> open_interval lb2 ub2 x) ->
  lb1 = lb2 /\ ub1 = ub2.
Proof.
intros lb1 lb2 ub1 ub2 Hord Hext.
 assert (Hord': lb2 < ub2) by (transitivity (middle lb1 ub1) ;
  apply Hext, middle_is_in_the_middle ; assumption).
 destruct (Rlt_le_dec lb1 lb2).
  destruct (Rlt_le_dec ub1 lb2).
   assert (Hf: ~ open_interval lb2 ub2 (middle lb1 ub1)).
    intro Hf ; apply Rlt_irrefl with lb2 ; transitivity (middle lb1 ub1) ;
    [apply Hf | transitivity ub1 ; [apply middle_is_in_the_middle |]] ;
    assumption.
   apply False_ind, Hf, Hext, middle_is_in_the_middle ; assumption.
   assert (Hf: ~ open_interval lb2 ub2 (middle lb1 lb2)).
    intro Hf ; apply Rlt_irrefl with (middle lb1 lb2) ; transitivity lb2 ;
    [apply middle_is_in_the_middle | apply Hf] ; assumption.
   apply False_ind, Hf, Hext ; split ; [| apply Rlt_le_trans with lb2] ;
   trivial ; apply middle_is_in_the_middle ; assumption.
  destruct (Rlt_le_dec lb2 lb1).
   destruct (Rlt_le_dec lb1 ub2).
    assert (Hf: ~ open_interval lb1 ub1 (middle lb2 lb1)).
     intro Hf ; apply Rlt_irrefl with lb1 ; transitivity (middle lb2 lb1) ;
     [apply Hf | apply middle_is_in_the_middle] ; assumption.
    apply False_ind, Hf, Hext ; split ; [| transitivity lb1] ; auto ;
    apply middle_is_in_the_middle ; assumption.
    assert (Hf: ~ open_interval lb2 ub2 (middle lb1 ub1)).
     intro Hf ; apply False_ind, Rlt_irrefl with ub2, Rle_lt_trans with lb1 ;
     [| transitivity (middle lb1 ub1) ; [apply middle_is_in_the_middle | apply Hf]] ;
     assumption.
    apply False_ind, Hf, Hext, middle_is_in_the_middle ; assumption.
   assert (lb_eq: lb1 = lb2) by intuition ; split ; trivial.
  destruct (Rlt_le_dec ub1 ub2).
   assert (Hf: ~ open_interval lb1 ub1 (middle ub1 ub2)).
    intro Hf ; apply Rlt_irrefl with ub1 ; transitivity (middle ub1 ub2) ;
    [apply middle_is_in_the_middle | apply Hf] ; assumption.
   apply False_ind, Hf, Hext ; rewrite <- lb_eq ; split ; [transitivity ub1 |] ;
   auto ; apply middle_is_in_the_middle ; assumption.
  destruct (Rlt_le_dec ub2 ub1).
   assert (Hf: ~ open_interval lb2 ub2 (middle ub2 ub1)).
    intro Hf ; apply Rlt_irrefl with ub2 ; transitivity (middle ub2 ub1) ;
    [apply middle_is_in_the_middle | apply Hf] ; assumption.
   apply False_ind, Hf, Hext ; rewrite lb_eq ; split ; [transitivity ub2 |] ;
   auto ; apply middle_is_in_the_middle ; assumption.
  intuition.
Qed.


(** * [Rabll]'s properties. *)

Lemma Rball_PI: forall c r (r_pos1 r_pos2: 0 <= r) x,
  Rball c r r_pos1 x <-> Rball c r r_pos2 x.
Proof.
intros ; split ; trivial.
Qed.

(** [Rball] describes intervals. *)

Lemma Rball_interval: forall c r r_pos x,
  Rball c r r_pos x -> open_interval (c - r) (c + r) x.
Proof.
intros c r r_pos x H ; assert (H' := Rabs_def2 _ _ H) ;
 destruct H' ; split ; fourier.
Qed.

Lemma interval_Rball: forall c r r_pos x,
  open_interval (c - r) (c + r) x -> Rball c r r_pos x.
Proof.
intros c r r_pos x [H1 H2] ;
 apply Rabs_def1 ; fourier.
Qed.

Lemma Rball_rewrite: forall c r r_pos x,
  Rball c r r_pos x <-> open_interval (c - r) (c + r) x.
Proof.
intros ; split ; [apply Rball_interval | apply interval_Rball].
Qed.

(** Inclusion of [Rball]s. *)

Lemma Rball_included: forall c r1 r2 r1_pos r2_pos x,
  r1 < r2 -> Rball c r1 r1_pos x -> Rball c r2 r2_pos x.
Proof.
unfold Rball ; intros ; fourier.
Qed.

Lemma Rball_from_middle: forall lb ub x, lb < x < ub ->
  { pr | Rball (middle lb ub) (ub - lb) pr x}.
Proof.
intros lb ub x [x_lb x_ub] ;
 assert (lbub: lb < ub) by (transitivity x ; assumption).
 assert (pr: 0 <= ub - lb) by fourier ; exists pr.
 apply Rabs_def1 ; destruct (middle_is_in_the_middle _ _ lbub) ;
 fourier.
Qed.

(** The specific case where the center of the ball is 0. *)

Lemma Rball_0_simpl: forall r r_pos x,
  Rball 0 r r_pos x <-> Rabs x < r.
Proof.
intros ; unfold Rball ; rewrite Rminus_0_r ; split ; trivial.
Qed.

Lemma Rball_c_0_empty: forall c (pr : 0 <= 0) x,
  ~ Rball c 0 pr x.
Proof.
intros c pr x Hf ; eapply Rlt_irrefl, Rle_lt_trans ;
 [eapply Rabs_pos | eassumption].
Qed.

(** Decidability result. *)

Lemma in_Rball_dec: forall c r r_pos x,
  { Rball c r r_pos x } + { ~ Rball c r r_pos x }.
Proof.
intros c r r_pos x ;
 destruct (in_open_interval_dec (c - r) (c + r) x) as [Ht | Hf].
  left ; apply interval_Rball ; assumption.
  right ; intro ; eapply Hf, Rball_interval ; eassumption.
Qed.

(** Extensional equality implies equality. *)

Lemma Rball_ext_eq: forall c1 c2 r1 r2 r1_pos r2_pos, 0 < r1 ->
  (forall x, Rball c1 r1 r1_pos x <-> Rball c2 r2 r2_pos x) ->
  c1 = c2 /\ r1 = r2.
Proof.
intros c1 c2 r1 r2 r1_pos r2_pos r1_pos_lt Hext.
 assert (Hord: c1 - r1 < c1 + r1) by fourier.
 assert (Heq: c1 - r1 = c2 - r2 /\ c1 + r1 = c2 + r2).
  apply open_interval_ext_eq.
   assumption.
   intro x ; split ; intro H ; eapply Rball_interval,
   Hext, interval_Rball ; assumption.
 split.
  replace c1 with ((c1 - r1 + (c1 + r1)) / 2) by field ;
  replace c2 with ((c2 - r2 + (c2 + r2)) / 2) by field ;
  destruct Heq as [H1 H2] ; rewrite H1, H2 ; field.
  replace r1 with ((c1 + r1 - (c1 - r1)) / 2) by field ;
  replace r2 with ((c2 + r2 - (c2 - r2)) / 2) by field ;
  destruct Heq as [H1 H2] ; rewrite H1, H2 ; field.
Qed.

(** * dist properties *)

Lemma open_interval_dist_pos: forall lb ub x,
  open_interval lb ub x ->
  0 < interval_dist lb ub x.
Proof.
intros lb ub x [x_lb x_ub] ;
 apply Rmin_pos_lt ; fourier.
Qed.

Lemma interval_dist_pos: forall lb ub x,
  interval lb ub x -> 0 <= interval_dist lb ub x.
Proof.
intros lb ub x [x_lb x_ub] ; apply Rmin_pos ; fourier.
Qed.

Lemma interval_dist_bound: forall lb ub x,
  open_interval lb ub x ->
  forall h, Rabs h < interval_dist lb ub x ->
  open_interval lb ub (x + h).
Proof.
intros lb ub x x_in h h_bd ;
 assert (H := Rabs_def2 _ _ h_bd) ;
 destruct H as [x_lb x_ub].
 unfold interval_dist in *.
  assert (H1: - (x - lb) < h).
   apply Rle_lt_trans with (- Rmin (x - lb) (ub - x)).
    apply Ropp_le_contravar, Rmin_l.
    assumption.
  assert (H2: h < ub - x).
   apply Rlt_le_trans with (Rmin (x - lb) (ub - x)).
    assumption.
    apply Rmin_r.
  unfold open_interval ; clear -H1 H2 ; split ; fourier.
Qed.

Lemma Rball_dist_pos: forall c r r_pos x,
  Rball c r r_pos x ->
  0 < Rball_dist c r x.
Proof.
intros ; eapply open_interval_dist_pos, Rball_interval ;
 eassumption.
Qed.

Lemma Rball_dist_bound: forall c r r_pos x,
  Rball c r r_pos x ->
  forall h, Rabs h < Rball_dist c r x ->
  Rball c r r_pos (x + h).
Proof.
intros ; apply interval_Rball, interval_dist_bound.
 eapply Rball_interval ; eassumption.
 assumption.
Qed.