Require Import Rbase Rfunctions Rfunction_def Rtopology Lra.
Require Import MyRIneq MyNeq PSeries_reg.
Require Import Tactics.

(** * The definitions used in this file: [middle], [interval], [Rball]. *)

Definition middle (x:R) (y:R) : R := (x + y) / 2.
Definition interval_dist lb ub x := Rmin (x - lb) (ub - x).
Definition interval_size lb ub : R := (ub - lb) / 2.

Lemma interval_size_pos : forall lb ub, lb < ub -> 0 < interval_size lb ub.
Proof.
unfold interval_size.
intros ; lra.
Qed.

Definition whole_R := fun (_ : R) => True.
Definition interval (lb ub x : R) := lb <= x <= ub.
Definition open_interval (lb ub x:R) := lb < x < ub.

Definition Rball c r x := Rabs (x - c) < r.
Definition Rball_dist c r := interval_dist (c - r) (c + r).

Definition Rball_eq c r (f g : R -> R) := forall x,
  Rball c r x -> f x = g x.

Lemma Req_Rball_eq: forall f g c r,
  f == g -> Rball_eq c r f g.
Proof.
intros f g c r Heq x x_in ; apply Heq.
Qed.

Lemma Rball_eq_refl: forall c r f, Rball_eq c r f f.
Proof.
unfold Rball_eq ; trivial.
Qed.

Lemma Rball_eq_sym: forall c r f g, Rball_eq c r f g -> Rball_eq c r g f.
Proof.
unfold Rball_eq ; intros ; symmetry ; auto.
Qed.

Lemma Rball_eq_trans: forall c r f g h, Rball_eq c r f g ->
  Rball_eq c r g h -> Rball_eq c r f h.
Proof.
unfold Rball_eq ; intros ; transitivity (g x) ; auto.
Qed.

Lemma Rball_radius_pos : forall c r x,
  Rball c r x -> 0 < r.
Proof.
unfold Rball ; intros c r x Hx ; eapply Rle_lt_trans ;
 [apply Rabs_pos | eassumption].
Qed.

Require Setoid.

Add Parametric Relation (c r: R) : (R -> R) (Rball_eq c r)
reflexivity proved by (Rball_eq_refl c r)
symmetry proved by (Rball_eq_sym c r)
transitivity proved by (Rball_eq_trans c r) as Rball_eq'.

(** The center of the (interval / ball) is in the interval *)

Lemma center_in_Rball : forall c r, 0 < r -> Rball c r c.
Proof.
intros ; apply Rabs_def1 ; lra.
Qed.

Lemma center_in_interval : forall c r, 0 <= r -> interval (c - r) (c + r) c.
Proof.
intros ; split ; lra.
Qed.

Lemma center_in_open_interval : forall c r, 0 < r -> open_interval (c - r) (c + r) c.
Proof.
intros ; split ; lra.
Qed.

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
 unfold middle, Rdiv ; apply Rmult_lt_compat_r ; [lra |] ;
 apply Rplus_lt_compat_l ; assumption.
 apply Rlt_le_trans with (middle y y).
 unfold middle, Rdiv ; apply Rmult_lt_compat_r ; [lra |] ;
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
  lra.
Qed.

Lemma middle_lt_lt_pos_lt : forall x y, 0 < x -> 0 < y -> 0 < middle x y.
Proof.
intros x y x_pos y_pos ; unfold middle, Rdiv ;
 lra.
Qed.

Lemma middle_le_lt_pos_lt : forall x y, 0 <= x -> 0 < y -> 0 < middle x y.
Proof.
intros x y x_pos y_pos ; unfold middle, Rdiv ;
 lra.
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
 apply Rmult_lt_gt_compat_neg_l ; lra.
Qed.

Lemma middle_le_lt_neg_lt : forall x y, x <= 0 -> y < 0 -> middle x y < 0.
Proof.
intros x y x_pos y_pos ; unfold middle, Rdiv ;
  replace 0 with ((x + y) * 0) by ring ;
 apply Rmult_lt_gt_compat_neg_l ; lra.
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

Lemma interval_restriction : forall lb ub a b,
  interval lb ub a -> interval lb ub b ->
  included (interval a b) (interval lb ub).
Proof.
intros lb ub a b a_in b_in x x_in ; split.
 transitivity a ; [apply a_in | apply x_in].
 transitivity b ; [apply x_in | apply b_in].
Qed.

Lemma open_interval_restriction : forall lb ub a b,
  interval lb ub a -> interval lb ub b ->
  included (open_interval a b) (open_interval lb ub).
Proof.
intros lb ub a b a_in b_in x x_in ; split.
 eapply Rle_lt_trans ; [eapply a_in | eapply x_in].
 eapply Rlt_le_trans ; [eapply x_in | eapply b_in].
Qed.

Lemma interval_open_restriction : forall lb ub a b,
  open_interval lb ub a -> open_interval lb ub b ->
  included (interval a b) (open_interval lb ub).
Proof.
intros lb ub a b a_in b_in x x_in ; split.
 eapply Rlt_le_trans ; [eapply a_in | eapply x_in].
 eapply Rle_lt_trans ; [eapply x_in | eapply b_in].
Qed.

Lemma open_interval_interval : forall lb ub x,
     open_interval lb ub x -> interval lb ub x.
Proof.
 intros ; split ; unfold open_interval in * ; intuition.
Qed.

Lemma interval_inhabited : forall lb ub x,
  interval lb ub x -> lb <= ub.
Proof.
intros ; etransitivity ; eapply_assumption.
Qed.

Lemma open_interval_inhabited : forall lb ub x,
  open_interval lb ub x -> lb < ub.
Proof.
intros ; etransitivity ; eapply_assumption.
Qed.

Lemma interval_opp_compat : forall lb ub x,
     interval lb ub x ->
     interval (-ub) (-lb) (-x).
Proof.
intros ; unfold interval in * ; split ; intuition ; lra.
Qed.

Lemma interval_minus_compat : forall lb ub x y,
  interval lb ub x -> interval (lb - y) (ub - y) (x - y).
Proof.
intros lb ub x y [Hlb Hub] ; split ; lra.
Qed.

Lemma interval_minus_compat_0 : forall lb ub x,
  interval lb ub x -> interval (lb - x) (ub - x) 0.
Proof.
intros lb ub x ; replace 0 with (x - x) by ring ;
 apply interval_minus_compat.
Qed.

Lemma open_interval_opp_compat : forall lb ub x,
     open_interval lb ub x ->
     open_interval (-ub) (-lb) (-x).
Proof.
intros ; unfold open_interval in * ; split ; intuition ; lra.
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
    right ; intros [_ Hf] ; lra.
   right ; intros [Hf _] ; lra.
Qed.

Lemma in_open_interval_dec: forall lb ub x,
  { open_interval lb ub x } + { ~ open_interval lb ub x }.
intros lb ub x.
  destruct (Rlt_le_dec lb x).
   destruct (Rlt_le_dec x ub).
    left ; split ; assumption.
    right ; intros [_ Hf] ; lra.
   right ; intros [Hf _] ; lra.
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

(** open interval are included into interval *)

Lemma included_open_interval_interval : forall a b,
  included (open_interval a b) (interval a b).
Proof.
intros a b x [x_l x_r] ; split ; left ; assumption.
Qed.

(** [Rball] describes intervals. *)

Lemma included_Rball_open_interval : forall c r,
  included (Rball c r) (open_interval (c - r) (c + r)).
Proof.
intros c r x H ; assert (H' := Rabs_def2 _ _ H) ;
 destruct H' ; split ; lra.
Qed.

Lemma included_Rball_open_interval2 : forall lb ub,
  included (Rball (middle lb ub) (interval_size lb ub)) (open_interval lb ub).
Proof.
intros lb ub x x_in ; destruct (Rabs_def2 _ _ x_in) as [x_lb x_ub] ; split.
 apply Rle_lt_trans with (middle lb ub - interval_size lb ub).
  right ; unfold middle, interval_size ; field.
  lra.
 apply Rlt_le_trans with (middle lb ub + interval_size lb ub).
  lra.
  right ; unfold middle, interval_size ; field.
Qed.

Lemma included_open_interval_Rball : forall lb ub,
  included (open_interval lb ub) (Rball (middle lb ub) (interval_size lb ub)).
Proof.
intros lb ub x x_in ; apply Rabs_def1.
 apply Rlt_minus_sort, Rlt_le_trans with ub.
  apply x_in.
  unfold middle, interval_size ; right ; field.
 apply Rlt_minus_sort2, Rle_lt_trans with lb.
  unfold middle, interval_size ; right ; field.
  apply x_in.
Qed.

Lemma included_open_interval_Rball2 : forall c r,
  included (open_interval (c - r) (c + r)) (Rball c r).
Proof.
intros c r x [x_lb x_ub] ; apply Rabs_def1 ; lra.
Qed.

Lemma Rball_rewrite: forall c r x,
  Rball c r x <-> open_interval (c - r) (c + r) x.
Proof.
intros ; split ; [apply included_Rball_open_interval | apply included_open_interval_Rball2].
Qed.

Lemma Rball_rewrite2: forall lb ub x,
  Rball (middle lb ub) (interval_size lb ub) x <-> open_interval lb ub x.
Proof.
intros ; split ; [apply included_Rball_open_interval2 | apply included_open_interval_Rball].
Qed.

(** Inclusion of [Rball]s. *)

Lemma Rball_included: forall c r1 r2 x,
  r1 <= r2 -> Rball c r1 x -> Rball c r2 x.
Proof.
unfold Rball ; intros ; lra.
Qed.

(** The specific case where the center of the ball is 0. *)

Lemma Rball_0_simpl: forall r x,
  Rball 0 r x <-> Rabs x < r.
Proof.
intros ; unfold Rball ; rewrite Rminus_0_r ; split ; trivial.
Qed.

Lemma Rball_c_0_empty: forall c r x, r <= 0 ->
  ~ Rball c r x.
Proof.
intros c r x Hr Hf ; eapply (Rlt_irrefl 0).
 eapply Rle_lt_trans ; [eapply Rabs_pos |].
 eapply Rlt_le_trans ; [eapply Hf | eassumption].
Qed.

(** Decidability result. *)

Lemma in_Rball_dec: forall c r x,
  { Rball c r x } + { ~ Rball c r x }.
Proof.
intros c r x ;
 destruct (in_open_interval_dec (c - r) (c + r) x) as [Ht | Hf].
  left ; rewrite Rball_rewrite ; assumption.
  right ; intro ; eapply Hf ; rewrite <- Rball_rewrite ; eassumption.
Qed.

(** Extensional equality implies equality. *)

Lemma Rball_ext_eq: forall c1 c2 r1 r2, r1 > 0 ->
  (forall x, Rball c1 r1 x <-> Rball c2 r2 x) ->
  c1 = c2 /\ r1 = r2.
Proof.
intros c1 c2 r1 r2 r1_pos Hext.
 assert (Hord: c1 - r1 < c1 + r1) by lra.
 assert (Heq: c1 - r1 = c2 - r2 /\ c1 + r1 = c2 + r2).
  apply open_interval_ext_eq.
   assumption.
   intro x ; split ; intro H ; eapply included_Rball_open_interval,
   Hext, included_open_interval_Rball2 ; assumption.
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
 apply Rmin_pos_lt ; lra.
Qed.

Lemma interval_dist_pos: forall lb ub x,
  interval lb ub x -> 0 <= interval_dist lb ub x.
Proof.
intros lb ub x [x_lb x_ub] ; apply Rmin_pos ; lra.
Qed.

Lemma open_interval_dist_bound:
  forall lb ub x, interval lb ub x ->
  forall h, Rabs h < interval_dist lb ub x ->
  open_interval lb ub (x + h).
Proof.
intros lb ub x x_in h h_bd ;
 assert (H := Rabs_def2 _ _ h_bd) ;
 destruct H as [x_lb x_ub].
  assert (H1: - (x - lb) < h).
   apply Rle_lt_trans with (- Rmin (x - lb) (ub - x)).
    apply Ropp_le_contravar, Rmin_l.
    assumption.
  assert (H2: h < ub - x).
   apply Rlt_le_trans with (Rmin (x - lb) (ub - x)).
    assumption.
    apply Rmin_r.
  split ; clear -H1 H2 ; lra.
Qed.

(* TODO : move *)

Lemma Ropp_eq_compat_l : forall x y, - x = y -> x = - y.
Proof.
intros x y [] ; symmetry ; apply Ropp_involutive.
Qed.

Lemma interval_dist_bound:
  forall lb ub x : R, interval lb ub x ->
  forall h : R,
  Rabs h <= interval_dist lb ub x -> interval lb ub (x + h).
Proof.
intros lb ub x x_in h [h_bd | heq].
 apply open_interval_interval, open_interval_dist_bound ;
  assumption.
 unfold Rabs in heq ; destruct (Rcase_abs h).
  split ; rewrite (Ropp_eq_compat_l _ _ heq).
   transitivity (x + - (x - lb)) ; [right ; ring |] ;
   apply Rplus_le_compat_l, Ropp_le_contravar, Rmin_l.
   transitivity (ub + - (interval_dist lb ub x)).
    apply Rplus_le_compat_r, x_in.
    transitivity (ub + - 0) ; [| right ; ring].
    apply Rplus_le_compat_l, Ropp_le_contravar,
     interval_dist_pos ; assumption.
  split ; subst.
   transitivity (x + 0) ; [ring_simplify ; apply x_in |].
    apply Rplus_le_compat_l, interval_dist_pos ; assumption.
   transitivity (x + (ub - x)) ; [| right ; ring].
    apply Rplus_le_compat_l, Rmin_r.
Qed.

Lemma Rball_dist_pos: forall c r x,
  Rball c r x -> 0 < Rball_dist c r x.
Proof.
intros ; eapply open_interval_dist_pos, included_Rball_open_interval ;
 eassumption.
Qed.

Lemma Rball_dist_bound: forall c r x,
  Rball c r x -> forall h, Rabs h < Rball_dist c r x ->
  Rball c r (x + h).
Proof.
intros ; apply included_open_interval_Rball2, open_interval_dist_bound.
 eapply open_interval_interval, included_Rball_open_interval ; eassumption.
 assumption.
Qed.
