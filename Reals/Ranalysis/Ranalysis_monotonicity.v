Require Import Rbase Ranalysis.
Require Import Rinterval Rfunctions Rfunction_def Rfunction_facts.
Require Import Ranalysis_def Ranalysis_def_simpl.
Require Import MyRIneq MyR_dist Lra.

Local Open Scope R_scope.

(** stricly_whatever implies whatever *)

Lemma strictly_increasing_in_increasing_in : forall D f,
  strictly_increasing_in D f -> increasing_in D f.
Proof.
intros D f f_incr x y Dx Dy [Hlt | Heq].
 left ; apply f_incr ; assumption.
 subst ; reflexivity.
Qed.

Lemma strictly_decreasing_in_decreasing_in : forall D f,
  strictly_decreasing_in D f -> decreasing_in D f.
Proof.
intros D f f_decr x y Dx Dy [Hlt | Heq].
 left ; apply f_decr ; assumption.
 subst ; reflexivity.
Qed.

Lemma strictly_monotonous_in_monotonous_in : forall D f,
 strictly_monotonous_in D f -> monotonous_in D f.
Proof.
intros D f [Hd | Hi] ;
 [left ; apply strictly_decreasing_in_decreasing_in |
 right ; apply strictly_increasing_in_increasing_in] ; assumption.
Qed.

Lemma strictly_increasing_increasing f : strictly_increasing f -> increasing f.
Proof.
  apply strictly_increasing_in_increasing_in.
Qed.

Lemma strictly_decreasing_decreasing f : strictly_decreasing f -> decreasing f.
Proof.
  apply strictly_decreasing_in_decreasing_in.
Qed.

Lemma strictly_monotonous_monotonous f : strictly_monotonous f -> monotonous f.
Proof.
  apply strictly_monotonous_in_monotonous_in.
Qed.

(** Strict monotonicity implies injectivity *)

Lemma strictly_increasing_in_injective_in : forall D f,
  strictly_increasing_in D f -> injective_in D f.
Proof.
intros D f f_inc x y x_in y_in feq ; destruct (Rtotal_order x y) as [Hlt | [Heq | Hgt]].
 destruct (Rlt_irrefl (f y)) ; apply Rle_lt_trans with (f x).
  rewrite feq ; reflexivity.
  apply f_inc ; assumption.
 assumption.
 destruct (Rlt_irrefl (f x)) ; apply Rle_lt_trans with (f y).
  rewrite feq ; reflexivity.
  apply f_inc ; assumption.
Qed.

Lemma strictly_decreasing_in_injective_in : forall D f,
  strictly_decreasing_in D f -> injective_in D f.
Proof.
intros D f f_dec x y x_in y_in feq ; destruct (Rtotal_order x y) as [Hlt | [Heq | Hgt]].
 destruct (Rlt_irrefl (f x)) ; apply Rle_lt_trans with (f y).
  rewrite feq ; reflexivity.
  apply f_dec ; assumption.
 assumption.
 destruct (Rlt_irrefl (f y)) ; apply Rle_lt_trans with (f x).
  rewrite feq ; reflexivity.
  apply f_dec ; assumption.
Qed.

Lemma strictly_monotonous_in_injective_in : forall D f,
  strictly_monotonous_in D f -> injective_in D f.
Proof.
intros D f [f_dec | f_inc] ;
 [apply strictly_decreasing_in_injective_in |
  apply strictly_increasing_in_injective_in] ; assumption.
Qed.

Lemma strictly_increasing_injective f : strictly_increasing f -> injective f.
Proof.
  apply strictly_increasing_in_injective_in.
Qed.

Lemma strictly_decreasing_injective f : strictly_decreasing f -> injective f.
Proof.
  apply strictly_decreasing_in_injective_in.
Qed.

Lemma strictly_monotonous_injective f : strictly_monotonous f -> injective f.
Proof.
  apply strictly_monotonous_in_injective_in.
Qed.

(** It also helps simplify Rmin / Rmax statements *)

Lemma increasing_in_Rmin_simpl :
  forall D f, increasing_in D f ->
  forall x y, D x -> D y -> x <= y -> Rmin (f x) (f y) = f x.
Proof.
intros D f f_inc x y Dx Dy Hxy ;
 assert (flb_lt_fub : f x <= f y) by (apply f_inc ; assumption) ;
 unfold Rmin ; destruct (Rle_dec (f x) (f y)) ; intuition.
Qed.

Lemma increasing_in_Rmax_simpl :
  forall D f, increasing_in D f ->
  forall x y, D x -> D y -> x <= y -> Rmax (f x) (f y) = f y.
Proof.
intros D f f_inc x y Dx Dy Hxy ;
 assert (flb_lt_fub : f x <= f y) by (apply f_inc ; assumption) ;
 unfold Rmax ; destruct (Rle_dec (f x) (f y)) ; intuition.
Qed.

Lemma decreasing_in_Rmin_simpl :
  forall D f, decreasing_in D f ->
  forall x y, D x -> D y -> x <= y -> Rmin (f x) (f y) = f y.
Proof.
intros D f f_dec x y Dx Dy Hxy ;
 assert (flb_lt_fub : f y <= f x) by (apply f_dec ; assumption) ;
 unfold Rmin ; destruct (Rle_dec (f x) (f y)) ; intuition.
Qed.

Lemma decreasing_in_Rmax_simpl :
  forall D f, decreasing_in D f ->
  forall x y, D x -> D y -> x <= y -> Rmax (f x) (f y) = f x.
Proof.
intros D f f_dec x y Dx Dy Hxy ;
 assert (flb_lt_fub : f y <= f x) by (apply f_dec ; assumption) ;
 unfold Rmax ; destruct (Rle_dec (f x) (f y)) ; intuition.
Qed.

(** Image of an interval throught a monotonous function *)

Lemma increasing_interval_image : forall f lb ub x,
  increasing_interval lb ub f -> interval lb ub x ->
  interval (f lb) (f ub) (f x).
Proof.
intros f lb ub x Hf x_in ; assert (lb_le_ub : lb <= ub) by
 (eapply interval_inhabited ; eassumption) ; split ; apply Hf.
 apply interval_l ; assumption.
 assumption.
 apply x_in.
 assumption.
 apply interval_r ; assumption.
 apply x_in.
Qed. 

Lemma decreasing_interval_image : forall f lb ub x,
  decreasing_interval lb ub f -> interval lb ub x ->
  interval (f ub) (f lb) (f x).
Proof.
intros f lb ub x Hf x_in ; assert (lb_le_ub : lb <= ub) by
 (eapply interval_inhabited ; eassumption) ; split ; apply Hf.
 assumption.
 apply interval_r ; assumption.
 apply x_in.
 apply interval_l ; assumption.
 assumption.
 apply x_in.
Qed.

Lemma monotonous_interval_image : forall f lb ub x,
  monotonous_interval lb ub f -> interval lb ub x ->
  interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) (f x).
Proof.
intros f lb ub x [f_dec | f_inc] x_in ;
 assert (lbub : lb <= ub) by (eapply interval_inhabited, x_in).
 erewrite decreasing_in_Rmax_simpl, decreasing_in_Rmin_simpl ; try eassumption.
  apply decreasing_interval_image ; assumption.
  apply interval_l ; assumption.
  apply interval_r ; assumption.
  apply interval_l ; assumption.
  apply interval_r ; assumption.
 erewrite increasing_in_Rmax_simpl, increasing_in_Rmin_simpl ; try eassumption.
  apply increasing_interval_image ; assumption.
  apply interval_l ; assumption.
  apply interval_r ; assumption.
  apply interval_l ; assumption.
  apply interval_r ; assumption.
Qed.

Lemma strictly_increasing_interval_image : forall f lb ub x,
  strictly_increasing_interval lb ub f -> open_interval lb ub x ->
  open_interval (f lb) (f ub) (f x).
Proof.
intros f lb ub x Hf x_in ; assert (lb_le_ub : lb <= ub) by
 (left ; eapply open_interval_inhabited ; eassumption) ; split ; apply Hf.
 apply interval_l ; assumption.
 apply open_interval_interval ; assumption.
 apply x_in.
 apply open_interval_interval ; assumption.
 apply interval_r ; assumption.
 apply x_in.
Qed. 

Lemma strictly_decreasing_interval_image : forall f lb ub x,
  strictly_decreasing_interval lb ub f -> open_interval lb ub x ->
  open_interval (f ub) (f lb) (f x).
Proof.
intros f lb ub x Hf x_in ; assert (lb_le_ub : lb <= ub) by
 (left ; eapply open_interval_inhabited ; eassumption) ; split ; apply Hf.
 apply open_interval_interval ; assumption.
 apply interval_r ; assumption.
 apply x_in.
 apply interval_l ; assumption.
 apply open_interval_interval ; assumption.
 apply x_in.
Qed.

Lemma strictly_monotonous_interval_image : forall f lb ub x,
  strictly_monotonous_interval lb ub f -> open_interval lb ub x ->
  open_interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) (f x).
Proof.
intros f lb ub x [f_dec | f_inc] x_in ;
 assert (lbub : lb <= ub) by (left ; eapply open_interval_inhabited, x_in).
 erewrite decreasing_in_Rmax_simpl, decreasing_in_Rmin_simpl.
  apply strictly_decreasing_interval_image ; assumption.
  apply strictly_decreasing_in_decreasing_in ; eassumption.
  apply interval_l ; assumption.
  apply interval_r ; assumption.
  assumption.
  apply strictly_decreasing_in_decreasing_in ; eassumption.
  apply interval_l ; assumption.
  apply interval_r ; assumption.
  assumption.
 erewrite increasing_in_Rmax_simpl, increasing_in_Rmin_simpl.
  apply strictly_increasing_interval_image ; assumption.
  apply strictly_increasing_in_increasing_in ; eassumption.
  apply interval_l ; assumption.
  apply interval_r ; assumption.
  assumption.
  apply strictly_increasing_in_increasing_in ; eassumption.
  apply interval_l ; assumption.
  apply interval_r ; assumption.
  assumption.
Qed.

(** Compatibility of variations with operations *)

Lemma increasing_in_opp : forall D f,
  increasing_in D f -> decreasing_in D (-f)%F.
Proof.
intros D f Hf x y Dx Dy Hxy ; unfold opp_fct ;
 apply Ropp_le_contravar, Hf ; assumption.
Qed.

Lemma increasing_in_opp_rev : forall D f,
  increasing_in D (- f)%F -> decreasing_in D f.
Proof.
intros D f Hf x y Dx Dy Hxy ; unfold opp_fct ;
 apply Ropp_le_cancel, Hf ; assumption.
Qed.

Lemma strictly_increasing_in_opp : forall D f,
  strictly_increasing_in D f -> strictly_decreasing_in D (-f)%F.
Proof.
intros D f Hf x y Dx Dy Hxy ; unfold opp_fct ;
 apply Ropp_lt_contravar, Hf ; assumption.
Qed.

Lemma strictly_increasing_in_opp_rev : forall D f,
  strictly_increasing_in D (- f)%F -> strictly_decreasing_in D f.
Proof.
intros D f Hf x y Dx Dy Hxy ; unfold opp_fct ;
 apply Ropp_lt_cancel, Hf ; assumption.
Qed.

Lemma decreasing_in_opp : forall D f,
  decreasing_in D f -> increasing_in D (-f)%F.
Proof.
intros D f Hf x y Dx Dy Hxy ; unfold opp_fct ;
 apply Ropp_le_contravar, Hf ; assumption.
Qed.

Lemma decreasing_in_opp_rev : forall D f,
  decreasing_in D (- f)%F -> increasing_in D f.
Proof.
intros D f Hf x y Dx Dy Hxy ; unfold opp_fct ;
 apply Ropp_le_cancel, Hf ; assumption.
Qed.

Lemma strictly_decreasing_in_opp : forall D f,
  strictly_decreasing_in D f -> strictly_increasing_in D (-f)%F.
Proof.
intros D f Hf x y Dx Dy Hxy ; unfold opp_fct ;
 apply Ropp_lt_contravar, Hf ; assumption.
Qed.

Lemma strictly_decreasing_in_opp_rev : forall D f,
  strictly_decreasing_in D (- f)%F -> strictly_increasing_in D f.
Proof.
intros D f Hf x y Dx Dy Hxy ; unfold opp_fct ;
 apply Ropp_lt_cancel, Hf ; assumption.
Qed.

(* TODO: more generic lemmas like these ones *)

Lemma increasing_in_plus : forall D f g,
  increasing_in D f -> increasing_in D g -> increasing_in D (f + g)%F.
Proof.
intros D f g Hf Hg x y Dx Dy Hxy ; unfold plus_fct ;
 apply Rplus_le_compat ; [apply Hf | apply Hg] ; assumption.
Qed.

Lemma increasing_in_minus : forall D f g,
  increasing_in D f -> decreasing_in D g -> increasing_in D (f - g)%F.
Proof.
intros D f g Hf Hg x y Dx Dy Hxy ; unfold plus_fct ;
 apply Rplus_le_compat ; [apply Hf | apply Ropp_le_contravar, Hg] ; assumption.
Qed.


Lemma strictly_increasing_strictly_decreasing_interval2 : forall f lb ub,
  strictly_increasing_interval lb ub f ->
  strictly_decreasing_interval (- ub) (- lb) (fun x => f(-x)).
Proof.
intros f c r f_incr ; intros x y x_in_B y_in_B x_lt_y.
 apply f_incr ; unfold interval in * ; try split ; intuition ; lra.
Qed.

Lemma strictly_decreasing_strictly_increasing_interval2 : forall f lb ub,
  strictly_decreasing_interval lb ub f ->
  strictly_increasing_interval (-ub) (-lb) (fun x => f(-x)).
Proof.
intros f c r f_decr ; intros x y x_in_B y_in_B x_lt_y.
 apply f_decr ; unfold interval in * ; try split ; intuition ; lra.
Qed.

Lemma strictly_increasing_reciprocal_interval_compat : forall f g lb ub,
  strictly_increasing_interval lb ub f ->
  reciprocal_interval (f lb) (f ub) f g ->
  (forall x, interval (f lb) (f ub) x -> interval lb ub (g x)) ->
  strictly_increasing_interval (f lb) (f ub) g.
Proof.
intros f g lb ub f_incr f_recip_g g_ok x y x_in_I y_in_I x_lt_y.
 destruct (Rlt_le_dec (g x) (g y)) as [T | F].
  assumption.
  destruct F as [F | F].
   assert (Hf : y < x).
    unfold reciprocal_interval, id in f_recip_g ; rewrite <- f_recip_g.
    apply Rgt_lt ; rewrite <- f_recip_g.
    unfold comp ; apply f_incr ; [apply g_ok | apply g_ok |] ; assumption.
    assumption.
    assumption.
   apply False_ind ; apply Rlt_irrefl with x ; apply Rlt_trans with y ; assumption.
   assert (Hf : x = y).
    unfold reciprocal_interval, id in f_recip_g ; rewrite <- f_recip_g.
    symmetry ; rewrite <- f_recip_g.
    unfold comp ; rewrite F ; reflexivity.
    assumption.
    assumption.
   rewrite Hf in x_lt_y ; elim (Rlt_irrefl _ x_lt_y).
Qed.

Lemma strictly_increasing_reciprocal_interval_comm: forall f g lb ub,
  (forall x, interval (f lb) (f ub) x -> interval lb ub (g x)) ->
  strictly_increasing_interval lb ub f ->
  reciprocal_interval (f lb) (f ub) f g ->
  reciprocal_interval lb ub g f.
Proof.
intros f g lb ub g_ok f_sinc Hfg x x_in ;
 assert (f_inc : increasing_interval lb ub f).
  apply strictly_increasing_in_increasing_in ; assumption.
 destruct (Req_dec (g (f x)) x) as [Heq | Hneq].
  assumption.
  destruct (Rlt_irrefl (f x)).
  destruct (Rdichotomy _ _ Hneq) as [Hlt | Hlt].
  apply Rle_lt_trans with (f (g (f x))).
   right ; rewrite Hfg.
    reflexivity.
    apply increasing_interval_image ; [apply strictly_increasing_in_increasing_in |] ; assumption.
   apply f_sinc ; [apply g_ok, increasing_interval_image | |] ; assumption.
  apply Rlt_le_trans with (f (g (f x))).
   apply f_sinc ; [| apply g_ok, increasing_interval_image |] ; assumption.
  right ; rewrite Hfg.
   reflexivity.
   apply increasing_interval_image ; assumption.
Qed.

Lemma strictly_decreasing_reciprocal_interval_comm: forall f g lb ub,
  (forall x, interval (f ub) (f lb) x -> interval lb ub (g x)) ->
  strictly_decreasing_interval lb ub f ->
  reciprocal_interval (f ub) (f lb) f g ->
  reciprocal_interval lb ub g f.
Proof.
intros f g lb ub g_ok f_sdec Hfg x x_in ;
 assert (f_dec : decreasing_interval lb ub f).
  apply strictly_decreasing_in_decreasing_in ; assumption.
 destruct (Req_dec (g (f x)) x) as [Heq | Hneq].
  assumption.
  destruct (Rlt_irrefl (f x)).
  destruct (Rdichotomy _ _ Hneq) as [Hlt | Hlt].
  apply Rlt_le_trans with (f (g (f x))).
   apply f_sdec ; [apply g_ok, decreasing_interval_image | |] ; assumption.
  right ; rewrite Hfg.
   reflexivity.
   apply decreasing_interval_image ; assumption.
  apply Rle_lt_trans with (f (g (f x))).
   right ; rewrite Hfg.
    reflexivity.
    apply decreasing_interval_image ; assumption.
   apply f_sdec ; [| apply g_ok, decreasing_interval_image |] ; assumption.
Qed.

(** Knowing f's variations and the ordering of f a and f b we can deduce a and b's ordering *)

Lemma strictly_increasing_open_interval_order : forall f lb ub a b,
  open_interval lb ub a -> open_interval lb ub b ->
  strictly_increasing_open_interval lb ub f ->
  f a < f b -> a < b.
Proof.
intros f lb ub a b a_in b_in Hf Hfafb ; destruct (Rlt_le_dec a b) as [altb | blea].
 assumption.
 destruct blea as [blta | beqa].
  destruct (Rlt_irrefl (f a)) ; transitivity (f b).
   assumption.
   apply Hf ; assumption.
  rewrite beqa in Hfafb ; destruct (Rlt_irrefl _ Hfafb).
Qed.

Lemma strictly_increasing_interval_order : forall f lb ub a b,
  open_interval lb ub a -> open_interval lb ub b ->
  strictly_increasing_open_interval lb ub f ->
  f a <= f b -> a <= b.
Proof.
intros f lb ub a b a_in b_in Hf Hfafb ; destruct (Rle_lt_dec a b) as [aleb | blta].
 assumption.
 destruct (Rlt_irrefl (f a)) ; apply Rle_lt_trans with (f b).
  assumption.
  apply Hf ; assumption.
Qed.
