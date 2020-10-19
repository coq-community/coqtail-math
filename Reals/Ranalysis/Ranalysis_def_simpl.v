Require Import Rbase Ranalysis.
Require Import Rinterval Rfunctions Rfunction_def.
Require Import Ranalysis_def Rfunction_facts.
Require Import MyRIneq MyR_dist Lra.

Local Open Scope R_scope.

(** * Example of dense domains *)

(* TODO: move this 3 lemmas *)

Lemma middle_r_in_Rball : forall c r, 0 < r -> Rball c r (middle c (c + r)).
Proof.
intros c r r_pos ; apply included_open_interval_Rball2 ; split.
 transitivity c.
  lra.
  apply middle_is_in_the_middle ; lra.
 apply middle_is_in_the_middle ; lra.
Qed.

Lemma middle_l_in_Rball : forall c r, 0 < r -> Rball c r (middle (c - r) c).
Proof.
intros c r r_pos ; apply included_open_interval_Rball2 ; split.
 apply middle_is_in_the_middle ; lra.
 transitivity c.
  apply middle_is_in_the_middle ; lra.
  lra.
Qed.

Lemma Rlt_div_2 : forall x, 0 < x -> x / 2 < x.
Proof.
intros ; lra.
Qed.

Lemma dense_interval: forall lb ub x, lb < ub ->
  interval lb ub x -> dense (interval lb ub) x.
Proof.
intros lb ub x Hlt [xlb xub] eps eps_pos ; destruct xlb as [xlb | xeq].
 destruct xub as [xub | xeq].
  pose (h := Rmin (eps / 2) (interval_dist lb ub x)) ;
  assert (h_pos : 0 < h).
   apply Rmin_pos_lt, open_interval_dist_pos ;
   [lra | split ; assumption].
  exists (x + h) ; split.
   split.
    apply interval_dist_bound ; [split ; left ; assumption |].
    rewrite Rabs_right ; [apply Rmin_r | left ; assumption].
    apply Rplus_pos_neq ; assumption.
   rewrite R_dist_Rplus_compat, Rabs_right ; [| left ; assumption].
    apply Rle_lt_trans with (eps / 2) ; [apply Rmin_l | lra].
  pose (h := Rmin (eps / 2) (ub - lb)) ;
  assert (h_pos : 0 < h) by (apply Rmin_pos_lt ; lra).
   exists (x - h) ; split. split. split.
    transitivity (x - (ub - lb)).
     right ; subst ; ring.
     apply Rplus_le_compat_l, Ropp_le_contravar, Rmin_r.
     left ; subst ; apply Rminus_pos_lt ; assumption.
     subst ; apply Rgt_not_eq, Rminus_pos_lt ; assumption.
     rewrite R_dist_Rminus_compat, Rabs_right ; [| left ; assumption].
     apply Rle_lt_trans with (eps / 2) ; [apply Rmin_l | lra].
  pose (h := Rmin (eps / 2) (ub - lb)) ;
  assert (h_pos : 0 < h) by (apply Rmin_pos_lt ; lra).
   exists (x + h) ; split. split. split.
    left ; rewrite xeq ; apply Rplus_pos_lt ; assumption.
    transitivity (x + (ub - lb)) ; [| right ; rewrite xeq ; ring].
     apply Rplus_le_compat_l, Rmin_r.
     apply Rlt_not_eq, Rplus_pos_lt ; assumption.
     rewrite R_dist_Rplus_compat, Rabs_right ; [| left ; assumption].
     apply Rle_lt_trans with (eps / 2) ; [apply Rmin_l | lra].
Qed.

Lemma dense_open_interval: forall lb ub x, lb < ub ->
  interval lb ub x -> dense (open_interval lb ub) x.
Proof.
intros lb ub x Hlt [xlb xub] eps eps_pos ; assert (lbub : 0 < ub - lb) by lra.
destruct xlb as [xlb | xeq].
 destruct xub as [xub | xeq].
  assert (d_pos : 0 < interval_dist lb ub x / 2).
   apply Rlt_mult_inv_pos ; [apply open_interval_dist_pos | lra].
   split ; assumption.
  pose (h := Rmin (eps / 2) (interval_dist lb ub x / 2)) ;
  assert (h_pos : 0 < h) by (apply Rmin_pos_lt ; lra).
  exists (x + h) ; split.
   split.
    apply open_interval_dist_bound ; [split ; left ; assumption |].
    apply Rle_lt_trans with (interval_dist lb ub x / 2).
    rewrite Rabs_right ; [apply Rmin_r | left ; assumption].
    lra.
    apply Rplus_pos_neq ; assumption.
   rewrite R_dist_Rplus_compat, Rabs_right ; [| left ; assumption].
    apply Rle_lt_trans with (eps / 2) ; [apply Rmin_l | lra].
  pose (h := Rmin (eps / 2) ((ub - lb) / 2)) ;
  assert (h_pos : 0 < h) by (apply Rmin_pos_lt ; [| apply Rlt_mult_inv_pos] ; lra).
   exists (x - h) ; repeat split.
    apply Rle_lt_trans with (x - (ub - lb)).
     right ; subst ; ring.
     apply Rplus_lt_compat_l, Ropp_lt_contravar.
     apply Rle_lt_trans with ((ub - lb) / 2) ; [apply Rmin_r | apply Rlt_div_2 ; assumption].
     subst ; apply Rminus_pos_lt ; assumption.
     subst ; apply Rgt_not_eq, Rminus_pos_lt ; assumption.
     rewrite R_dist_Rminus_compat, Rabs_right ; [| left ; assumption].
     apply Rle_lt_trans with (eps / 2) ; [apply Rmin_l | lra].
  pose (h := Rmin (eps / 2) ((ub - lb)/2)) ;
  assert (h_pos : 0 < h) by (apply Rmin_pos_lt ; [| apply Rlt_mult_inv_pos] ; lra).
   exists (x + h) ; repeat split.
    rewrite xeq ; apply Rplus_pos_lt ; assumption.
    apply Rlt_le_trans with (x + (ub - lb)) ; [| right ; rewrite xeq ; ring].
     apply Rplus_lt_compat_l, Rle_lt_trans with ((ub - lb)/2) ; [apply Rmin_r |].
     apply Rlt_div_2 ; assumption.
     apply Rlt_not_eq, Rplus_pos_lt ; assumption.
     rewrite R_dist_Rplus_compat, Rabs_right ; [| left ; assumption].
     apply Rle_lt_trans with (eps / 2) ; [apply Rmin_l | lra].
Qed.

Lemma dense_Rball : forall c r x, Rball c r x -> dense (Rball c r) x.
Proof.
intros c r x x_in eps eps_pos ;
 assert (r_pos : 0 < r) by (eapply Rball_radius_pos ; eassumption) ;
 assert (Hlbub : c - r < c + r) by lra ;
 assert (x_in' : interval (c - r) (c + r) x).
  apply open_interval_interval, included_Rball_open_interval ; assumption.
 destruct (dense_open_interval (c - r) (c + r) x Hlbub x_in' eps eps_pos) as [y [[y_in y_neq] Hy]] ;
 exists y ; repeat split ; [apply included_open_interval_Rball2 | |] ; assumption.
Qed.

(** * Extensionality of growth_rate *)

Lemma growth_rate_ext: forall f g x, f == g ->
  growth_rate f x == growth_rate g x.
Proof.
intros f g x Heq y ; unfold growth_rate ;
 do 2 rewrite Heq ; reflexivity.
Qed.

Lemma growth_rate_ext_strong: forall (D : R -> Prop) f g x, D x ->
  (forall x, D x -> f x = g x) ->
  forall y, D y -> growth_rate f x y = growth_rate g x y.
Proof.
intros D f g x Dx Heq y y_in ; unfold growth_rate ;
 do 2 (rewrite Heq ; [| assumption]) ; reflexivity.  
Qed.

(** * growth_rate is compatible with common operations. *)

Lemma growth_rate_mult_real_fct_compat: forall f (l:R) x y, D_x no_cond x y ->
  growth_rate (mult_real_fct l f)%F x y = l * growth_rate f x y.
Proof.
intros f l x y Dxy ; unfold growth_rate, mult_real_fct ; field ;
 apply Rminus_eq_contra ; symmetry ; apply Dxy.
Qed.

Lemma growth_rate_scal_compat: forall f (l:R) x y, D_x no_cond x y ->
  growth_rate ((fun _ => l) * f)%F x y = l * growth_rate f x y.
Proof.
intros f l x y Dxy ; unfold growth_rate, mult_fct ; field ;
 apply Rminus_eq_contra ; symmetry ; apply Dxy.
Qed.

Lemma growth_rate_opp_compat: forall f x y, D_x no_cond x y ->
  growth_rate (- f)%F x y = - growth_rate f x y.
Proof.
intros f x y Dxy ; unfold growth_rate, opp_fct ; field ;
 apply Rminus_eq_contra ; symmetry ; apply Dxy.
Qed.

Lemma growth_rate_plus_compat: forall f g x y, D_x no_cond x y ->
  growth_rate (f + g)%F x y = growth_rate f x y + growth_rate g x y.
Proof.
intros f g x y Dxy ; unfold growth_rate, plus_fct ; field ;
 apply Rminus_eq_contra ; symmetry ; apply Dxy.
Qed.

Lemma growth_rate_minus_compat: forall f g x y, D_x no_cond x y ->
  growth_rate (f - g)%F x y = growth_rate f x y - growth_rate g x y.
Proof.
intros f g x y Dxy ; unfold growth_rate, minus_fct ; field ;
 apply Rminus_eq_contra ; symmetry ; apply Dxy.
Qed.

Lemma growth_rate_mult_decomp: forall f g x y, x <> y ->
  growth_rate (f * g)%F x y =
 (growth_rate f x y) * g x + f y * growth_rate g x y.
Proof.
intros f g x y Hneq ; unfold growth_rate, mult_fct ; field ;
 apply Rminus_eq_contra ; symmetry ; assumption.
Qed.

Lemma growth_rate_inv_decomp: forall f x y,
  x <> y -> f x <> 0 -> f y <> 0 ->
  growth_rate (/ f)%F x y =
  - ((growth_rate f x y) * / (f x * f y)).
Proof.
intros ; unfold growth_rate, inv_fct ; field ;
 repeat split ; [| | apply Rminus_eq_contra ; symmetry ] ;
 assumption.
Qed.

(** * All the definitions using _in are contravariant in their domain *)

Lemma D_x_covariant : forall D E x,
  included D E -> included (D_x D x) (D_x E x).
Proof.
intros D E x inc y [y_neq y_in] ; split ; [apply inc |] ; assumption.
Qed. 

Lemma limit1_in_contravariant : forall D E f x l, included D E ->
  limit1_in f E x l -> limit1_in f D x l.
Proof.
intros D E f x l inc Hfxl eps eps_pos ;
 destruct (Hfxl _ eps_pos) as [alp [alp_pos Halp]] ; exists alp ; split.
  assumption.
  intros y [Dy y_bd] ; apply Halp ; split ; [apply inc |] ; assumption.
Qed.

Lemma continuity_pt_in_contravariant : forall D E f x, included D E ->
  continuity_pt_in E f x -> continuity_pt_in D f x.
Proof.
intros D E f x inc f_cont Dx ; apply limit1_in_contravariant with E.
 assumption.
 apply f_cont, inc ; assumption.
Qed.

Lemma continuity_in_contravariant : forall D E f, included D E ->
  continuity_in E f -> continuity_in D f.
Proof.
intros D E f inc f_cont x ;
 apply continuity_pt_in_contravariant with E, f_cont ; assumption.
Qed.

Lemma derivable_pt_lim_in_contravariant : forall D E f x l, included D E ->
  derivable_pt_lim_in E f x l -> derivable_pt_lim_in D f x l.
Proof.
intros D E f x l inc f_der ; apply limit1_in_contravariant with (D_x E x).
 apply D_x_covariant ; assumption.
 apply f_der.
Qed.

Lemma derivable_pt_in_contravariant : forall D E f x, included D E ->
  derivable_pt_in E f x -> derivable_pt_in D f x.
Proof.
intros D E f x inc [l Hl] ; exists l ;
 apply derivable_pt_lim_in_contravariant with E ; assumption.
Qed.

Lemma derivable_in_contravariant : forall D E f, included D E ->
  derivable_in E f -> derivable_in D f.
Proof.
intros D E f inc f_der x Dx ; apply derivable_pt_in_contravariant with E.
 assumption.
 apply f_der, inc ; assumption.
Qed.

Lemma injective_in_contravariant : forall D E f, included D E ->
  injective_in E f -> injective_in D f.
Proof.
intros D E f inc f_inj x y x_in y_in Hxy ; apply f_inj ; try apply inc ; assumption.
Qed.

Lemma surjective_in_contravariant : forall D E f, included D E ->
  surjective_in E f -> surjective_in D f.
Proof.
intros D E f inc f_surj y y_in ; apply f_surj ; try apply inc ; assumption.
Qed.

Lemma increasing_in_contravariant : forall D E f, included D E ->
  increasing_in E f -> increasing_in D f.
Proof.
intros D E f inc f_inc x y x_in y_in Hxy ; apply f_inc ; try apply inc ; assumption.
Qed.

Lemma decreasing_in_contravariant : forall D E f, included D E ->
  decreasing_in E f -> decreasing_in D f.
Proof.
intros D E f inc f_dec x y x_in y_in Hxy ; apply f_dec ; try apply inc ; assumption.
Qed.

Lemma monotonous_in_contravariant : forall D E f, included D E ->
  monotonous_in E f -> monotonous_in D f.
Proof.
intros D E f inc [f_dec | f_inc] ;
 [left ; eapply decreasing_in_contravariant |
 right ; eapply increasing_in_contravariant] ; eassumption.
Qed.

Lemma strictly_increasing_in_contravariant : forall D E f, included D E ->
  strictly_increasing_in E f -> strictly_increasing_in D f.
Proof.
intros D E f inc f_inc x y x_in y_in Hxy ; apply f_inc ; try apply inc ; assumption.
Qed.

Lemma strictly_decreasing_in_contravariant : forall D E f, included D E ->
  strictly_decreasing_in E f -> strictly_decreasing_in D f.
Proof.
intros D E f inc f_dec x y x_in y_in Hxy ; apply f_dec ; try apply inc ; assumption.
Qed.

Lemma strictly_monotonous_in_contravariant : forall D E f, included D E ->
  strictly_monotonous_in E f -> strictly_monotonous_in D f.
Proof.
intros D E f inc [f_dec | f_inc] ;
 [left ; eapply strictly_decreasing_in_contravariant |
 right ; eapply strictly_increasing_in_contravariant] ; eassumption.
Qed.

Definition reciprocal_in_contravariant : forall D E f g, included D E ->
  reciprocal_in E f g -> reciprocal_in D f g.
Proof.
intros D E f g inc Hfg x x_in ; apply Hfg, inc ; assumption.
Qed.

(** * Extensionality of limit1_in *)

Lemma limit1_in_ext: forall (D : R -> Prop) f g x l,
  (forall x, D x -> f x = g x) ->
  limit1_in f D l x -> limit1_in g D l x.
Proof.
intros D f g x l Heq Hf eps eps_pos ;
 destruct (Hf _ eps_pos) as [alp [alp_pos Halp]] ;
 exists alp ; split ; [assumption |].
 intros y Hy ; rewrite <- Heq ; [apply Halp |] ; apply Hy.
Qed.

Lemma limit1_in_ext_strong: forall (D : R -> Prop) r f g x l, 0 < r ->
  (forall y, Rball x r y -> D y -> f y = g y) ->
  limit1_in f D l x -> limit1_in g D l x.
Proof.
intros D alp f g x l alp_pos Heq Hf eps eps_pos ;
 destruct (Hf _ eps_pos) as [bet [bet_pos Hbet]] ;
 exists (Rmin alp bet) ; split.
 apply Rmin_pos_lt ; assumption.
 intros y [Dy y_bd] ; rewrite <- Heq.
  apply Hbet ; split ; [assumption | apply Rlt_le_trans with (Rmin alp bet) ;
  [assumption | apply Rmin_r]].
 apply Rlt_le_trans with (Rmin alp bet) ; [apply y_bd | apply Rmin_l].
 assumption.
Qed.

(* TODO: WTF does this do here? *)
(** pr_nu_var restricted to a specific interval *)

Lemma pr_nu_var2_interv : forall (f g : R -> R) (lb ub x : R) (pr1 : derivable_pt f x)
       (pr2 : derivable_pt g x),
       open_interval lb ub x ->
       (forall h : R, lb < h < ub -> f h = g h) ->
       derive_pt f x pr1 = derive_pt g x pr2.
Proof.
intros f g lb ub x Prf Prg x_encad local_eq.
assert (forall x l, lb < x < ub -> (derivable_pt_abs f x l <-> derivable_pt_abs g x l)).
 intros a l a_encad.
 unfold derivable_pt_abs, derivable_pt_lim.
 split.
 intros Hyp eps eps_pos.
 elim (Hyp eps eps_pos) ; intros delta Hyp2.
 assert (Pos_cond : Rmin delta (Rmin (ub - a) (a - lb)) > 0).
  clear-a lb ub a_encad delta.
  apply Rmin_pos_lt ; [exact (delta.(cond_pos)) | apply Rmin_pos_lt ] ;
  apply Rlt_Rminus ; intuition.
 exists (mkposreal (Rmin delta (Rmin (ub - a) (a - lb))) Pos_cond).
 intros h h_neq h_encad.
 replace (g (a + h) - g a) with (f (a + h) - f a).
 apply Hyp2 ; intuition.
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))).
 assumption. apply Rmin_l.
 assert (local_eq2 : forall h : R, lb < h < ub -> - f h = - g h).
  intros ; apply Ropp_eq_compat ; intuition.
 rewrite local_eq ; unfold Rminus. rewrite local_eq2. reflexivity.
 assumption.
 assert (Sublemma2 : forall x y, Rabs x < Rabs y -> y > 0 -> x < y).
  intros m n Hyp_abs y_pos. apply Rlt_le_trans with (r2:=Rabs n).
   apply Rle_lt_trans with (r2:=Rabs m) ; [ | assumption] ; apply RRle_abs.
   apply Req_le ; apply Rabs_right ; apply Rgt_ge ; assumption.
 split.
 assert (Sublemma : forall x y z, -z < y - x -> x < y + z).
  intros ; lra.
 apply Sublemma.
 apply Sublemma2. rewrite Rabs_Ropp.
 apply Rlt_le_trans with (r2:=a-lb) ; [| apply RRle_abs] ;
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 assert (Sublemma : forall x y z, y < z - x -> x + y < z).
  intros ; lra.
 apply Sublemma.
 apply Sublemma2.
 apply Rlt_le_trans with (r2:=ub-a) ; [| apply RRle_abs] ;
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_l] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_l] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 intros Hyp eps eps_pos.
 elim (Hyp eps eps_pos) ; intros delta Hyp2.
 assert (Pos_cond : Rmin delta (Rmin (ub - a) (a - lb)) > 0).
  clear-a lb ub a_encad delta.
  apply Rmin_pos_lt ; [exact (delta.(cond_pos)) | apply Rmin_pos_lt ] ;
  apply Rlt_Rminus ; intuition.
 exists (mkposreal (Rmin delta (Rmin (ub - a) (a - lb))) Pos_cond).
 intros h h_neq h_encad.
 replace (f (a + h) - f a) with (g (a + h) - g a).
 apply Hyp2 ; intuition.
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))).
 assumption. apply Rmin_l.
 assert (local_eq2 : forall h : R, lb < h < ub -> - f h = - g h).
  intros ; apply Ropp_eq_compat ; intuition.
 rewrite local_eq ; unfold Rminus. rewrite local_eq2. reflexivity.
 assumption.
 assert (Sublemma2 : forall x y, Rabs x < Rabs y -> y > 0 -> x < y).
  intros m n Hyp_abs y_pos. apply Rlt_le_trans with (r2:=Rabs n).
   apply Rle_lt_trans with (r2:=Rabs m) ; [ | assumption] ; apply RRle_abs.
   apply Req_le ; apply Rabs_right ; apply Rgt_ge ; assumption.
 split.
 assert (Sublemma : forall x y z, -z < y - x -> x < y + z).
  intros ; lra.
 apply Sublemma.
 apply Sublemma2. rewrite Rabs_Ropp.
 apply Rlt_le_trans with (r2:=a-lb) ; [| apply RRle_abs] ;
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 assert (Sublemma : forall x y z, y < z - x -> x + y < z).
  intros ; lra.
 apply Sublemma.
 apply Sublemma2.
 apply Rlt_le_trans with (r2:=ub-a) ; [| apply RRle_abs] ;
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_l] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_l] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 unfold derivable_pt in Prf.
  unfold derivable_pt in Prg.
  elim Prf; intros.
  elim Prg; intros.
  assert (Temp := p); rewrite H in Temp.
  unfold derivable_pt_abs in p.
  unfold derivable_pt_abs in p0.
  simpl in |- *.
  apply (uniqueness_limite g x x0 x1 Temp p0).
  assumption.
Qed.

(** Simplification lemmas on mult_real_fun *)

Lemma mult_real_fct_0: forall f,
  mult_real_fct 0 f == (fun _ => 0).
Proof.
intros f x ; unfold mult_real_fct ; apply Rmult_0_l.
Qed.
