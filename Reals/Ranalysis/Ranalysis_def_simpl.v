Require Import Rbase Ranalysis.
Require Import Rinterval Rfunctions Rfunction_def.
Require Import Ranalysis_def Rfunction_facts.
Require Import MyRIneq MyR_dist Fourier.

Require Import Ass_handling.


Local Open Scope R_scope.


(** * How to relate the different notions of continuity. *)

Lemma continuity_pt_continue_in: forall f (D : R -> Prop) x,
  continuity_pt f x -> continue_pt_in f D x.
Proof.
intros f D x Hf Dx eps eps_pos ;
 destruct (Hf _ eps_pos) as [alp [alp_pos Halp]] ;
 exists alp ; split ; [assumption | intros y [Dy y_bd]].
 destruct (Req_dec x y) as [Heq | Hneq].
 subst ; rewrite R_dist_eq ; assumption.
 apply Halp ; repeat split ; assumption.
Qed.

Lemma continuity_continuity_Rball: forall c r r_pos f,
  continuity f -> continuity_Rball f c r r_pos.
Proof.
intros c r r_pos f f_cont x x_in ; apply continuity_pt_continue_in ;
 [apply f_cont |] ; assumption.
Qed.

Lemma continuity_interval_continuity_pt: forall f lb ub x, lb < ub ->
  continuity_interval f lb ub -> open_interval lb ub x ->
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

Lemma continuity_interval_restriction_compat : forall f a b a' b',
  continuity_interval f a b -> interval a b a' ->
  interval a b b' -> continuity_interval f a' b'.
Proof.
intros f a b a' b' Hf a'_in b'_in x x_in ;
 assert (Himp : forall x, interval a' b' x -> interval a b x) by
 (intros y [ya' yb'] ; split ; destruct a'_in, b'_in ; fourier)
 ; eapply limit1_imp, Hf, Himp ; assumption.
Qed.

Lemma continuity_interval_const : forall c a b,
  continuity_interval (fun _ => c) a b.
Proof.
intros c a b eps eps_pos ; exists 1 ; split ; [fourier |] ;
 intros x x_in ; rewrite R_dist_eq ; assumption.
Qed.

Lemma continuity_interval_opp_compat : forall f a b,
  continuity_interval f a b -> continuity_interval (- f)%F a b.
Proof.
intros f a b Hf x x_in ; apply limit_Ropp, Hf ; assumption.
Qed.

Lemma continuity_interval_plus_compat : forall f g a b,
  continuity_interval f a b -> continuity_interval g a b ->
  continuity_interval (f + g)%F a b.
Proof.
intros f g a b Hf Hg x x_in ; apply limit_plus ; ass_apply ;
 assumption.
Qed.

Lemma continuity_interval_minus_compat : forall f g a b,
  continuity_interval f a b -> continuity_interval g a b ->
  continuity_interval (f - g)%F a b.
Proof.
intros f g a b Hf Hg x x_in ; apply limit_minus ; ass_apply ;
 assumption.
Qed.

Lemma continuity_interval_mult_compat : forall f g a b,
  continuity_interval f a b -> continuity_interval g a b ->
  continuity_interval (f * g)%F a b.
Proof.
intros f g a b Hf Hg x x_in ; apply limit_mul ; ass_apply ;
 assumption.
Qed.

(** * Idem for derivatives *)


Lemma limit1_in_ext: forall (D : R -> Prop) f g x l,
  (forall x, D x -> f x = g x) ->
  limit1_in f D l x -> limit1_in g D l x.
Proof.
intros D f g x l Heq Hf eps eps_pos ;
 destruct (Hf _ eps_pos) as [alp [alp_pos Halp]] ;
 exists alp ; split ; [assumption |].
 intros y Hy ; rewrite <- Heq ; [apply Halp |] ; apply Hy.
Qed.

Lemma limit1_in_ext_strong: forall (D : R -> Prop) alp f g x l,
  0 < alp -> (forall y, Rabs (y - x) < alp -> D y -> f y = g y) ->
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

Lemma derivable_pt_lim_open_interval_Rball: forall f x c r r_pos l,
  derivable_pt_lim_in f (open_interval (c - r) (c + r)) x l ->
  derivable_pt_lim_in f (Rball c r r_pos) x l.
Proof.
intros f x c r r_pos l Hl eps eps_pos ;
 destruct (Hl _ eps_pos) as [delta [delta_pos Hdelta]] ;
 exists delta ; split ; [assumption |].
 intros y [[y_in y_neq] y_bd] ; apply Hdelta ; split ;
 [split ; [eapply Rball_interval |] |] ; eassumption.
Qed.

Lemma derivable_pt_lim_Rball_open_interval: forall f x c r r_pos l,
  derivable_pt_lim_in f (Rball c r r_pos) x l ->
  derivable_pt_lim_in f (open_interval (c - r) (c + r)) x l.
Proof.
intros f x lb ub pr l Hl eps eps_pos ;
 destruct (Hl _ eps_pos) as [delta [delta_pos Hdelta]] ;
 exists delta ; split ; [assumption |].
 intros y [[y_in y_neq] y_bd] ; apply Hdelta ; split ;
 [split ; [eapply interval_Rball |] |] ; eassumption.
Qed.

Lemma derivable_open_interval_Rball: forall f c r r_pos,
  derivable_open_interval f (c - r) (c + r) ->
  derivable_Rball f c r r_pos.
Proof.
intros f c r r_pos Hoi x x_in ;
 destruct (Hoi x (Rball_interval _ _ _ _ x_in)) as [l Hl] ;
 exists l ; apply derivable_pt_lim_open_interval_Rball, Hl.
Qed.

Lemma derivable_Rball_open_interval: forall f c r r_pos,
  derivable_Rball f c r r_pos ->
  derivable_open_interval f (c - r) (c + r).
Proof.
intros f c r r_pos Hoi x x_in ;
 destruct (Hoi x (interval_Rball _ _ _ _ x_in)) as [l Hl] ;
 exists l ; eapply derivable_pt_lim_Rball_open_interval, Hl.
Qed.

(** This new definition is obviously related to the old one. *)

Lemma derivable_pt_lim_derivable_pt_lim_in: forall f D x l,
  derivable_pt_lim f x l -> derivable_pt_lim_in f D x l.
Proof.
intros f D x l Hl eps eps_pos ; destruct (Hl _ eps_pos) as [delta Hdelta] ;
 exists delta ; split.
  apply delta.
  intros y [[Dy xny] xy_bd] ; simpl ; unfold R_dist, growth_rate ;
   replace (f y) with (f (x + (y - x))) by (f_equal ; ring) ; apply Hdelta.
   intro Hf ; apply xny ; revert Hf ; clear ; intuition.
   apply xy_bd.
Qed.

Lemma derivable_pt_derivable_pt_in: forall f D x,
  derivable_pt f x -> derivable_pt_in f D x.
Proof.
intros f D x [l Hl] ; exists l ;
 apply derivable_pt_lim_derivable_pt_lim_in ;
 assumption.
Qed.

Lemma derivable_derivable_in : forall f D,
  derivable f -> derivable_in f D.
Proof.
intros f D Hf x Dx ; apply derivable_pt_derivable_pt_in, Hf.
Qed.

(** In specific cases we can come back from the specific case to the one
    with no limitation. *)

Lemma derivable_pt_lim_open_interval_derivable_pt_lim: forall f lb ub x l,
  open_interval lb ub x -> derivable_pt_lim_in f (open_interval lb ub) x l ->
  derivable_pt_lim f x l.
Proof.
intros f lb ub x l pr Hl eps eps_pos ; destruct (Hl _ eps_pos) as [d [d_pos Hd]] ;
 simpl in Hd ; unfold R_dist in Hd.
 pose (delta := Rmin (interval_dist lb ub x) d).
 assert (delta_pos : 0 < delta).
  apply Rmin_pos_lt ; [apply open_interval_dist_pos |] ; assumption.
 exists (mkposreal _ delta_pos) ; intros h h_neq h_bd ;
 specify Hd (x + h) ; unfold growth_rate in * ;
 replace (x + h - x) with h in Hd by ring ; apply Hd ; split.
  split.
   apply open_interval_dist_bound ; [apply open_interval_interval
   | eapply Rlt_le_trans ; [| eapply Rmin_l]] ; eassumption.
   clear -h_neq ; intro Hf ; apply h_neq, Rplus_eq_reg_l with x ;
   rewrite <- Hf ; ring.
  eapply Rlt_le_trans ; [eassumption | eapply Rmin_r].
Qed.

Lemma derivable_pt_lim_Rball_included: forall f c r r' r_pos r'_pos x l,
  Rball c r' r'_pos x -> r' <= r ->
  derivable_pt_lim_in f (Rball c r r_pos) x l ->
  derivable_pt_lim_in f (Rball c r' r'_pos) x l.
Proof.
intros ; eapply limit1_imp ; [| eassumption] ; intros y [y_in y_neq] ;
 split ; [eapply Rball_included |] ; eassumption.
Qed.

Lemma derivable_pt_lim_Rball_included_rev: forall f c r r' r_pos r'_pos x l,
  Rball c r' r'_pos x -> r' <= r ->
  derivable_pt_lim_in f (Rball c r' r'_pos) x l ->
  derivable_pt_lim_in f (Rball c r r_pos) x l.
Proof.
intros f c r r' r_pos r'_pos x l x_in r'ler Hl eps eps_pos.
 destruct (Hl _ eps_pos) as [alp [alp_pos Halp]] ;
 exists (Rmin alp (Rball_dist c r' x)) ; split.
  apply Rmin_pos_lt ; [assumption |].
  eapply Rball_dist_pos ; eassumption.
  intros y [[y_in y_neq] y_bd] ; apply Halp ; repeat split.
   replace y with (x + (y - x)) by ring ; apply Rball_dist_bound.
    assumption.
    apply Rlt_le_trans with (Rmin alp (Rball_dist c r' x)) ;
     [apply y_bd | apply Rmin_r].
   assumption.
   apply Rlt_le_trans with (Rmin alp (Rball_dist c r' x)) ;
    [apply y_bd | apply Rmin_l].
Qed.

Lemma derivable_pt_lim_Rball_derivable_pt_lim: forall f c r r_pos x l,
  Rball c r r_pos x -> derivable_pt_lim_in f (Rball c r r_pos) x l ->
  derivable_pt_lim f x l.
Proof.
intros ; eapply derivable_pt_lim_open_interval_derivable_pt_lim ;
 [eapply Rball_interval | eapply derivable_pt_lim_Rball_open_interval] ;
 eassumption.
Qed.

Lemma derivable_open_interval_derivable_pt: forall f lb ub,
  derivable_open_interval f lb ub ->
  forall x, open_interval lb ub x -> derivable_pt f x.
Proof.
intros f lb ub H x Dx ; destruct (H x Dx) as [l Hl] ;
 exists l ; eapply derivable_pt_lim_open_interval_derivable_pt_lim ;
 eassumption.
Qed.

Lemma derivable_Rball_derivable_pt: forall f c r r_pos,
  derivable_Rball f c r r_pos ->
  forall x, Rball c r r_pos x -> derivable_pt f x.
Proof.
intros ; eapply derivable_open_interval_derivable_pt ;
 [eapply derivable_Rball_open_interval | eapply Rball_interval] ;
 eassumption.
Qed.

(** This allows us to get back the unicity of the derivative. *)

Lemma derivable_pt_lim_in_uniqueness: forall (D : R -> Prop) f x l l',
  dense D x -> derivable_pt_lim_in f D x l ->
  derivable_pt_lim_in f D x l' ->
  l = l'.
Proof.
intros D f x l l' Dx Hl ; eapply single_limit ; try eassumption ;
 intros eps eps_pos ; destruct (Dx _ eps_pos) as [y [y_h y_bd]] ;
 exists y.
Qed.

Lemma derivable_pt_lim_open_interval_uniqueness: forall f lb ub x l l',
  open_interval lb ub x ->
  derivable_pt_lim_in f (open_interval lb ub) x l ->
  derivable_pt_lim_in f (open_interval lb ub) x l' ->
  l = l'.
Proof.
intros f lb ub x l l' x_in Hl Hl' ; eapply uniqueness_limite ;
 eapply derivable_pt_lim_open_interval_derivable_pt_lim ;
 eassumption.
Qed.

Lemma derivable_pt_lim_Rball_uniqueness: forall f c r r_pos x l l',
  Rball c r r_pos x ->
  derivable_pt_lim_in f (Rball c r r_pos) x l ->
  derivable_pt_lim_in f (Rball c r r_pos) x l' ->
  l = l'.
Proof.
intros f c r r_pos x l l' x_in Hl Hl' ; eapply uniqueness_limite ;
 eapply derivable_pt_lim_Rball_derivable_pt_lim ;
 eassumption.
Qed.

Lemma derivable_Rball_continuity_Rball: forall c r r_pos f,
  derivable_Rball f c r r_pos ->
  continuity_Rball f c r r_pos.
Proof.
intros c r r_pos f Hf x x_in ; apply continuity_pt_continue_in ;
 [eapply derivable_continuous_pt, derivable_Rball_derivable_pt |] ;
 eassumption.
Qed.


(** Value of the derivative *)

Lemma derivable_pt_lim_derive_pt_Rball: forall f c r rp1 rp2 rp3 x l pr,
  Rball c r rp1 x ->
  derivable_pt_lim_in f (Rball c r rp2) x l ->
  derive_pt_in f (Rball c r rp3) x pr = l.
Proof.
intros f c r rp1 rp2 rp3 x l [l' Hl'] x_in  Hl ; simpl ;
 eapply derivable_pt_lim_Rball_uniqueness ;
 eassumption.
Qed.

Lemma derivable_pt_lim_in_derive_Rball: forall f c r rp1 rp2 rp3 x l pr,
  Rball c r rp1 x ->
  derivable_pt_lim_in f (Rball c r rp2) x l ->
  derive_Rball f c r rp3 pr x = l.
Proof.
intros f c r rp1 rp2 rp3 x l pr x_in Hl ; unfold derive_Rball ;
 destruct (in_Rball_dec c r rp3 x) as [x_in2 | x_nin].
 eapply derivable_pt_lim_derive_pt_Rball ; eassumption.
 contradiction.
Qed.

(** Extensionality of the definitions *)

Lemma derivable_pt_lim_Rball_ext: forall f g c r rp1 rp2 rp3 rp4,
  Rball_eq c r rp1 f g -> forall x l,
  Rball c r rp2 x ->
  derivable_pt_lim_in f (Rball c r rp3) x l ->
  derivable_pt_lim_in g (Rball c r rp4) x l.
Proof.
intros f g c r rp1 rp2 rp3 rp4 Heq x l x_in Hf eps eps_pos ;
 destruct (Hf _ eps_pos) as [delta [delta_pos Hdelta]] ;
 exists delta ; split.
  assumption.
  intros y [[Hy y_neq] y_bd] ; unfold growth_rate ; rewrite <- Heq, <- Heq ;
  [apply Hdelta ; repeat split | |] ; assumption.
Qed.

Lemma derivable_Rball_ext: forall f g c r rp1 rp2 rp3,
  Rball_eq c r rp1 f g ->
  derivable_Rball f c r rp2 ->
  derivable_Rball g c r rp3.
Proof.
intros f g c r rp1 rp2 rp3 heq Hf x x_in ;
 destruct (Hf _ x_in) as [l Hl] ; exists l ;
 eapply derivable_pt_lim_Rball_ext ; eassumption.
Qed.

Lemma derive_pt_in_Rball_ext: forall f g c r rp1 rp2 rp3 rp4 rp5 rp6 x
  (prf: derivable_pt_in f (Rball c r rp1) x)
  (prg: derivable_pt_in g (Rball c r rp2) x),
  Rball c r rp3 x ->
  Rball_eq c r rp4 f g ->
  derive_pt_in f (Rball c r rp5) x prf =
  derive_pt_in g (Rball c r rp6) x prg.
Proof.
intros f g c r rp1 rp2 rp3 rp4 rp5 rp6 x [l1 Hl1] [l2 Hl2] x_in Heq ; simpl ;
 eapply derivable_pt_lim_Rball_uniqueness ; [eassumption | | eassumption].
 eapply derivable_pt_lim_Rball_ext ; eassumption.
Qed.

Lemma derive_Rball_ext: forall f g c r rp1 rp2 rp3 rp4 rp5
  (prf: derivable_Rball f c r rp1)
  (prg: derivable_Rball g c r rp2),
  Rball_eq c r rp3 f g ->
  derive_Rball f c r rp4 prf == derive_Rball g c r rp5 prg.
Proof.
intros f g c r rp1 rp2 rp3 rp4 rp5 prf prg Heq x ; unfold derive_Rball ;
 destruct (in_Rball_dec c r rp4 x) as [HT1 | HF1] ;
 destruct (in_Rball_dec c r rp5 x) as [HT2 | HF2].
 eapply derive_pt_in_Rball_ext ; eassumption.
 contradiction.
 contradiction.
 reflexivity.
Qed.

Lemma derive_derive_Rball: forall f c r rp1 rp2 pr pr',
  Rball_eq c r rp1 (derive f pr) (derive_Rball f c r rp2 pr').
Proof.
intros f c r rp1 rp2 pr pr' x x_in ; unfold derive_Rball ;
 destruct (in_Rball_dec c r rp2 x) as [HT | HF].
 destruct (pr' x HT) as [l Hl] ; simpl ; unfold derive ;
  rewrite derive_pt_eq ; eapply derivable_pt_lim_Rball_derivable_pt_lim ;
  eassumption.
 destruct (HF x_in).
Qed.

Lemma strictly_increasing_interval_image : forall f lb ub x,
  strictly_increasing_interval f lb ub -> open_interval lb ub x ->
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

(** Manipulation *)

Lemma strictly_increasing_strictly_monotonous_interval : forall f lb ub,
      strictly_increasing_interval f lb ub -> strictly_monotonous_interval f lb ub.
Proof.
intros ; left ; assumption.
Qed.

Lemma strictly_decreasing_strictly_monotonous_interval : forall f lb ub,
      strictly_decreasing_interval f lb ub -> strictly_monotonous_interval f lb ub.
Proof.
intros ; right ; assumption.
Qed.

Lemma strictly_increasing_increasing_interval : forall f lb ub,
     strictly_increasing_interval f lb ub -> increasing_interval f lb ub.
Proof.
intros f lb ub f_incr x y x_in_I y_in_I x_le_y.
 destruct x_le_y as [x_lt_y | x_eq_y].
 left ; apply f_incr ; assumption.
 right ; subst ; reflexivity.
Qed.

Lemma strictly_decreasing_decreasing_interval : forall f lb ub,
     strictly_decreasing_interval f lb ub -> decreasing_interval f lb ub.
Proof.
intros f lb ub f_incr x y x_in_I y_in_I x_le_y.
 destruct x_le_y as [x_lt_y | x_eq_y].
 left ; apply f_incr ; assumption.
 right ; subst ; reflexivity.
Qed.

Lemma strictly_monotonous_monotonous_interval : forall f lb ub,
     strictly_monotonous_interval f lb ub ->
     monotonous_interval f lb ub.
Proof.
intros f lb ub [H | H] ; [left ; apply strictly_increasing_increasing_interval
 | right ; apply strictly_decreasing_decreasing_interval] ; apply H.
Qed.

Lemma strictly_monotonous_injective_interval : forall f lb ub,
      strictly_monotonous_interval f lb ub -> injective_interval f lb ub.
Proof.
intros f c r Hf ; destruct Hf as [f_incr | f_decr] ;
 intros x y x_in_B y_in_B fx_eq_fy ;
 destruct (Rlt_le_dec x y) as [x_lt_y | x_ge_y].
  assert (H := f_incr _ _ x_in_B y_in_B x_lt_y) ; rewrite fx_eq_fy in H ;
  elim (Rlt_irrefl _ H).
  destruct x_ge_y as [y_lt_x | x_eq_y].
   assert (H := f_incr _ _ y_in_B x_in_B y_lt_x) ; rewrite fx_eq_fy in H ;
   elim (Rlt_irrefl _ H).
   symmetry ; assumption.
  assert (H := f_decr _ _ x_in_B y_in_B x_lt_y) ; rewrite fx_eq_fy in H ;
  elim (Rlt_irrefl _ H).
  destruct x_ge_y as [y_lt_x | x_eq_y].
   assert (H := f_decr _ _ y_in_B x_in_B y_lt_x) ; rewrite fx_eq_fy in H ;
   elim (Rlt_irrefl _ H).
   symmetry ; assumption.
Qed.

Lemma strictly_increasing_Rmin_simpl : forall f lb ub,
     lb <= ub -> strictly_increasing_interval f lb ub ->
     Rmin (f lb) (f ub) = f lb.
Proof.
intros f lb ub [Hneq | Heq] f_incr. 
 assert (flb_lt_fub : f lb < f ub).
 apply f_incr ; [apply interval_l | apply interval_r |] ; intuition.
 unfold Rmin ; destruct (Rle_dec (f lb) (f ub)) ; intuition.
 subst ; apply Rmin_diag.
Qed.

Lemma strictly_increasing_Rmax_simpl : forall f lb ub,
     lb <= ub -> strictly_increasing_interval f lb ub ->
     Rmax (f lb) (f ub) = f ub.
Proof.
intros f lb ub [Hneq | Heq] f_incr.
 assert (flb_lt_fub : f lb < f ub).
 apply f_incr ; [apply interval_l | apply interval_r |] ; intuition.
 unfold Rmax ; destruct (Rle_dec (f lb) (f ub)) ; intuition.
 subst ; apply Rmax_diag.
Qed.

Lemma strictly_decreasing_Rmin_simpl : forall f lb ub,
     lb <= ub -> strictly_decreasing_interval f lb ub ->
     Rmin (f lb) (f ub) = f ub.
Proof.
intros f lb ub [Hneq | Heq] f_decr. assert (flb_lt_fub : f ub < f lb).
 apply f_decr ; [apply interval_l | apply interval_r |] ; intuition.
 unfold Rmin ; destruct (Rle_dec (f lb) (f ub)) ; intuition.
 subst ; apply Rmin_diag.
Qed.

Lemma strictly_decreasing_Rmax_simpl : forall f lb ub,
     lb <= ub -> strictly_decreasing_interval f lb ub ->
     Rmax (f lb) (f ub) = f lb.
Proof.
intros f lb ub [Hneq | Heq] f_decr. assert (flb_lt_fub : f ub < f lb).
 apply f_decr ; [apply interval_l | apply interval_r |] ; intuition.
 unfold Rmax ; destruct (Rle_dec (f lb) (f ub)) ; intuition.
 subst ; apply Rmax_diag.
Qed.

Lemma derivable_pt_in_continue_pt_in : forall f D x,
    derivable_pt_in f D x -> continue_pt_in f D x.
Proof.
intros f D x [l Hl] Dx eps eps_pos.
 pose (eps' := Rmin eps (eps / (eps + Rabs l))).
 assert (eps'_pos: 0 < eps').
  apply Rmin_pos_lt, Rlt_mult_inv_pos, Rplus_lt_le_0_compat ;
  [| | | apply Rabs_pos] ; assumption.
 destruct (Hl _ eps'_pos) as [alp [alp_pos Halp]] ;
 exists (Rmin alp eps') ; split ; [apply Rmin_pos_lt ; assumption |].
 intros y [Dy y_bd] ; destruct (Req_dec y x) as [Heq | Hneq].
  subst ; rewrite R_dist_eq ; assumption.
  transitivity ((eps + Rabs l) * Rabs (y - x)).
  apply Rle_lt_trans with (Rabs (growth_rate f x y) * Rabs (y - x)).
   right ; simpl ; unfold R_dist, growth_rate ; rewrite <- Rabs_mult ;
   apply Rabs_eq_compat ; field ; apply Rminus_eq_contra ; assumption.
   apply Rle_lt_trans with ((dist R_met (growth_rate f x y) l + Rabs l) * Rabs (y - x)).
   apply Rmult_le_compat_r ; [apply Rabs_pos |].
   apply Rle_trans with (Rabs (growth_rate f x y - l + l)) ;
   [right ; apply Rabs_eq_compat ; ring | apply Rabs_triang].
   apply Rmult_lt_compat_r ; [apply Rabs_pos_lt, Rminus_eq_contra ; assumption |].
   apply Rplus_lt_compat_r, Rlt_le_trans with eps'.
   apply Halp ; repeat split ; [assumption | symmetry ; assumption |].
   apply Rlt_le_trans with (Rmin alp eps'), Rmin_l ; assumption.
   apply Rmin_l.
   apply Rlt_le_trans with ((eps + Rabs l) * eps').
   apply Rmult_lt_compat_l.
    apply Rplus_lt_le_0_compat ; [assumption | apply Rabs_pos].
    apply Rlt_le_trans with (Rmin alp eps') ; [apply y_bd | apply Rmin_r].
   transitivity ((eps + Rabs l) * (eps / (eps + Rabs l))).
   apply Rmult_le_compat_l, Rmin_r ; apply Rplus_le_le_0_compat ;
   [left ; assumption | apply Rabs_pos].
   right ; field ; apply Rgt_not_eq, Rplus_lt_le_0_compat, Rabs_pos ; assumption.
Qed.

Lemma derivable_continuous_interval : forall f lb ub,
  derivable_interval f lb ub -> continuity_interval f lb ub.
Proof.
intros f lb ub H x x_in ; apply derivable_pt_in_continue_pt_in ;
 [apply H |] ; assumption.
Qed.

Lemma derivable_continuous_open_interval : forall f lb ub,
	derivable_open_interval f lb ub -> continuity_open_interval f lb ub.
Proof.
intros f lb ub H x x_in ; apply derivable_pt_in_continue_pt_in ;
 [apply H |] ; assumption.
Qed.

Lemma continue_pt_in_opp_rev : forall f D x,
      continue_pt_in (-f)%F D x ->
      continue_pt_in f D x.
Proof.
intros f D x Hf x_in ; apply limit1_in_ext with (- - f)%F.
 intros y y_in ; apply Ropp_involutive.
 rewrite <- (Ropp_involutive (f x)) ;
 apply limit_Ropp, Hf ; assumption.
Qed.

Lemma strictly_increasing_strictly_decreasing_interval : forall f lb ub,
    strictly_increasing_interval f lb ub -> strictly_decreasing_interval (-f)%F lb ub.
Proof.
intros f c r f_incr ; intros x y x_in_B y_in_B x_lt_y.
 assert (H := f_incr _ _ x_in_B y_in_B x_lt_y).
 unfold opp_fct ; intuition.
Qed.

Lemma strictly_increasing_strictly_decreasing_interval2 : forall f lb ub,
       strictly_increasing_interval f lb ub ->
       strictly_decreasing_interval (fun x => f(-x)) (-ub) (-lb).
Proof.
intros f c r f_incr ; intros x y x_in_B y_in_B x_lt_y.
 apply f_incr ; unfold interval in * ; try split ; intuition ; fourier.
Qed.

Lemma strictly_decreasing_strictly_increasing_interval : forall f lb ub,
    strictly_decreasing_interval f lb ub -> strictly_increasing_interval (-f)%F lb ub.
Proof.
intros f c r f_decr ; intros x y x_in_B y_in_B x_lt_y.
 assert (H := f_decr _ _ x_in_B y_in_B x_lt_y).
 unfold opp_fct ; intuition.
Qed.

Lemma strictly_decreasing_strictly_increasing_interval2 : forall f lb ub,
    strictly_decreasing_interval f lb ub -> strictly_increasing_interval (fun x => f(-x)) (-ub) (-lb).
Proof.
intros f c r f_decr ; intros x y x_in_B y_in_B x_lt_y.
 apply f_decr ; unfold interval in * ; try split ; intuition ; fourier.
Qed.


Lemma strictly_increasing_reciprocal_interval_compat : forall f g lb ub,
           strictly_increasing_interval f lb ub ->
	   reciprocal_interval f g (f lb) (f ub) ->
           (forall x, interval (f lb) (f ub) x -> interval lb ub (g x)) ->
           strictly_increasing_interval g (f lb) (f ub).
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

Lemma strictly_increasing_interval_compat: forall f lb ub x,
  strictly_increasing_interval f lb ub -> interval lb ub x ->
  interval (f lb) (f ub) (f x).
Proof.
intros f lb ub x Hf x_in ; split ;
 apply (strictly_increasing_increasing_interval _ _ _ Hf) ;
 (apply x_in || apply interval_l || apply interval_r) ;
 eapply interval_inhabited ; eassumption.
Qed.

Lemma strictly_decreasing_interval_compat: forall f lb ub x,
  strictly_decreasing_interval f lb ub -> interval lb ub x ->
  interval (f ub) (f lb) (f x).
Proof.
intros f lb ub x Hf x_in ; split ;
 apply (strictly_decreasing_decreasing_interval _ _ _ Hf) ;
 (apply x_in || apply interval_l || apply interval_r) ;
 eapply interval_inhabited ; eassumption.
Qed.

Lemma strictly_increasing_reciprocal_interval_comm: forall f g lb ub,
  (forall x, interval (f lb) (f ub) x -> interval lb ub (g x)) ->
  strictly_increasing_interval f lb ub ->
  reciprocal_interval f g (f lb) (f ub) ->
  reciprocal_interval g f lb ub.
Proof.
intros f g lb ub g_ok Hf Hfg x x_in ; unfold comp, id.
 destruct (Req_dec (g (f x)) x) as [Heq | Hneq].
  assumption.
  destruct (Rlt_irrefl (f x)).
  destruct (Rdichotomy _ _ Hneq) as [Hlt | Hlt].
  apply Rle_lt_trans with ((comp f g) (f x)).
   right ; rewrite Hfg.
    reflexivity.
    apply strictly_increasing_interval_compat ; assumption.
   unfold comp ; apply Hf ; [apply g_ok, strictly_increasing_interval_compat | |] ; assumption.
  apply Rlt_le_trans with ((comp f g) (f x)).
   unfold comp ; apply Hf ; [| apply g_ok, strictly_increasing_interval_compat |] ; assumption.
  right ; rewrite Hfg.
   reflexivity.
   apply strictly_increasing_interval_compat ; assumption.
Qed.

Lemma strictly_decreasing_reciprocal_interval_comm: forall f g lb ub,
  (forall x, interval (f ub) (f lb) x -> interval lb ub (g x)) ->
  strictly_decreasing_interval f lb ub ->
  reciprocal_interval f g (f ub) (f lb) ->
  reciprocal_interval g f lb ub.
Proof.
intros f g lb ub g_ok Hf Hfg x x_in ; unfold comp, id.
 destruct (Req_dec (g (f x)) x) as [Heq | Hneq].
  assumption.
  destruct (Rlt_irrefl (f x)).
  destruct (Rdichotomy _ _ Hneq) as [Hlt | Hlt].
  apply Rlt_le_trans with ((comp f g) (f x)).
   unfold comp ; apply Hf ; [apply g_ok, strictly_decreasing_interval_compat | |] ; assumption.
  right ; rewrite Hfg.
   reflexivity.
   apply strictly_decreasing_interval_compat ; assumption.
  apply Rle_lt_trans with ((comp f g) (f x)).
   right ; rewrite Hfg.
    reflexivity.
    apply strictly_decreasing_interval_compat ; assumption.
   unfold comp ; apply Hf ; [| apply g_ok, strictly_decreasing_interval_compat |] ; assumption.
Qed.

Lemma reciprocal_opp_compat_interval : forall f g lb ub,
       reciprocal_interval f g lb ub ->
       reciprocal_interval (fun x =>f(-x)) (-g)%F lb ub.
Proof.
intros f g lb ub f_recip_g x x_in_I.
 unfold comp, opp_fct ; simpl ; rewrite Ropp_involutive ;
 apply f_recip_g ; assumption.
Qed.

Lemma reciprocal_opp_compat_interval2 : forall f g lb ub,
       reciprocal_interval f g lb ub ->
       reciprocal_interval (-f)%F (fun x => g (-x)) (-ub) (-lb).
Proof.
intros f g lb ub f_recip_g x x_in_I.
 unfold comp.
 replace ((- f)%F (g (- x))) with (- (comp f g) (-x)).
 rewrite f_recip_g.
 unfold id ; ring.
 unfold interval in * ; destruct x_in_I.
 split ; fourier.
 reflexivity.
Qed.

Lemma strictly_increasing_open_interval_image : forall f lb ub b,
       lb <= ub -> increasing_interval f lb ub ->
       open_interval (Rmin (f lb) (f ub)) (Rmax (f lb) (f ub)) b ->
       open_interval (f lb) (f ub) b.
Proof.
intros f lb ub b lb_le_ub f_incr b_bd.
 assert (Hf : f lb <= f ub).
   apply f_incr.
   split ; [right ; reflexivity | apply lb_le_ub].
   split ; [apply lb_le_ub | right ; reflexivity].
   assumption.
 split.
 apply Rle_lt_trans with (Rmin (f lb) (f ub)).
  right ; unfold Rmin ; destruct (Rle_dec (f lb) (f ub)) as [flb_le_fub | fub_lt_flb].
  reflexivity.
  elim (fub_lt_flb Hf).
  unfold open_interval in b_bd ; intuition.
  apply Rlt_le_trans with (Rmax (f lb) (f ub)).
   unfold open_interval in b_bd ; intuition.
   right ; unfold Rmax ; destruct (Rle_dec (f lb) (f ub)) as [flb_le_fub | fub_lt_flb].
  reflexivity.
  elim (fub_lt_flb Hf).
Qed.

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
  intros ; fourier.
 apply Sublemma.
 apply Sublemma2. rewrite Rabs_Ropp.
 apply Rlt_le_trans with (r2:=a-lb) ; [| apply RRle_abs] ;
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 assert (Sublemma : forall x y z, y < z - x -> x + y < z).
  intros ; fourier.
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
  intros ; fourier.
 apply Sublemma.
 apply Sublemma2. rewrite Rabs_Ropp.
 apply Rlt_le_trans with (r2:=a-lb) ; [| apply RRle_abs] ;
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 assert (Sublemma : forall x y z, y < z - x -> x + y < z).
  intros ; fourier.
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

Lemma growth_rate_ext: forall f g x, f == g ->
  growth_rate f x == growth_rate g x.
Proof.
intros f g x Heq y ; unfold growth_rate ;
 do 2 rewrite Heq ; reflexivity.
Qed.

Lemma derivable_pt_lim_in_ext: forall f g x D l, f == g ->
  derivable_pt_lim_in f D x l -> derivable_pt_lim_in g D x l.
Proof.
intros f g x D l Heq Hf eps eps_pos ;
 destruct (Hf _ eps_pos) as [alpha [alpha_pos Halpha]] ;
 exists alpha ; split ; [assumption |].
 intros ; erewrite growth_rate_ext ; [eapply Halpha | symmetry] ;
 eassumption.
Qed.

(** Simplification lemmas on mult_real_fun *)

Lemma mult_real_fct_0: forall f,
  mult_real_fct 0 f == (fun _ => 0).
Proof.
intros f x ; unfold mult_real_fct ; apply Rmult_0_l.
Qed.

(** Compatibility of growth_rate with common operations *)

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


(** * Compatibility with restrictions *)

Lemma interval_restriction_compat : forall a b a' b' x,
  interval a b a' -> interval a b b' ->
  interval a' b' x -> interval a b x.
Proof.
intros a b a' b' x [] [] [] ; split ; fourier.
Qed.

Lemma open_interval_restriction_compat : forall a b a' b' x,
  interval a b a' -> interval a b b' ->
  open_interval a' b' x -> open_interval a b x.
Proof.
intros a b a' b' x [] [] [] ; split ; fourier.
Qed.

Lemma interval_open_restriction_compat : forall a b a' b' x,
  open_interval a b a' -> open_interval a b b' ->
  interval a' b' x -> open_interval a b x.
Proof.
intros a b a' b' x [] [] [] ; split ; fourier.
Qed.

Lemma strictly_increasing_interval_restriction_compat :
 forall f a b a' b', interval a b a' -> interval a b b' ->
 strictly_increasing_interval f a b ->
 strictly_increasing_interval f a' b'.
Proof.
intros f a b a' b' a'_in b'_in Hf x y x_in y_in ;
 apply Hf ; apply interval_restriction_compat with a' b' ;
 assumption.
Qed.

Lemma derivable_pt_lim_in_imp_compat: forall f (D E : R -> Prop) x l,
  (forall y, E y -> D y) -> derivable_pt_lim_in f D x l->
  derivable_pt_lim_in f E x l.
Proof.
intros ; eapply limit1_imp ; [| eassumption].
 intros z [z_in z_neq] ; split ; [ass_apply |] ; assumption.
Qed.

Lemma derivable_pt_in_imp_compat: forall f (D E : R -> Prop) x,
  (forall y, E y -> D y) -> derivable_pt_in f D x ->
  derivable_pt_in f E x.
Proof.
intros f D E x EinD [l Hl] ; exists l ;
 eapply derivable_pt_lim_in_imp_compat ; eassumption.
Qed.

Lemma continuity_open_interval_opp_compat : forall f lb ub,
  continuity_open_interval f lb ub ->
  continuity_open_interval (- f)%F lb ub.
Proof.
intros f lb ub Hf b b_in ; apply limit_Ropp, Hf ; assumption.
Qed.

Lemma continuity_open_interval_ext : forall (f g : R -> R) lb ub,
  (f == g)%F -> continuity_open_interval f lb ub ->
  continuity_open_interval g lb ub.
Proof.
intros f g lb ub Heq Hf b b_in ; eapply limit1_in_ext.
 intros ; apply Heq.
 rewrite <- (Heq b) ; apply Hf ; assumption.
Qed.

Lemma continuity_open_interval_Ropp_compat : forall f lb ub,
  continuity_open_interval f lb ub ->
  continuity_open_interval (fun x => f (- x)) (- ub) (- lb).
Proof.
intros f lb ub Hf b b_in eps eps_pos.
 assert (mb_in : open_interval lb ub (- b)).
  destruct b_in ; split ; fourier.
 destruct (Hf _ mb_in _ eps_pos) as [alpha [alpha_pos Halpha]] ;
 exists alpha ; split ; [assumption | intros x [x_in x_bd]].
 apply Halpha ; split ; simpl.
  destruct x_in ; split ; fourier.
  rewrite R_dist_opp_compat ; assumption.
Qed.

Lemma continuity_open_interval_Ropp_compat_rev : forall f lb ub,
  continuity_open_interval (fun x => f (- x)) (- ub) (- lb) ->
  continuity_open_interval f lb ub.
Proof.
intros f lb ub Hf ; pose (F := fun x => f (- x)) ;
 apply continuity_open_interval_ext with (fun x => F (- x)).
 intro x ; unfold F ; f_equal ; apply Ropp_involutive.
  rewrite <- (Ropp_involutive lb), <- (Ropp_involutive ub) ;
  apply continuity_open_interval_Ropp_compat, Hf.
Qed.

Lemma derivable_pt_lim_open_interval_restriction_compat :
  forall (f : R -> R) (a b a' b' : R) l x,
  interval a' b' x ->
  open_interval a b a' -> open_interval a b b' ->
  derivable_pt_lim_in f (open_interval a b) x l ->
  derivable_pt_lim_in f (interval a' b') x l.
Proof.
intros ; eapply derivable_pt_lim_in_imp_compat ; [| eassumption].
 intros y y_in ; eapply interval_open_restriction_compat ;
  try eapply y_in ; assumption.
Qed.

Lemma derivable_pt_lim_open_interval_restriction_compat' :
  forall (f : R -> R) (a b a' b' : R) l x,
  open_interval a' b' x ->
  open_interval a b a' -> open_interval a b b' ->
  derivable_pt_lim_in f (open_interval a b) x l ->
  derivable_pt_lim_in f (open_interval a' b') x l.
Proof.
intros ; eapply derivable_pt_lim_in_imp_compat ; [| eassumption].
 intros y y_in ; eapply open_interval_restriction_compat ; try eassumption ;
  eapply open_interval_interval ; eassumption.
Qed.

Lemma strictly_increasing_open_interval_restriction_compat :
  forall (f : R -> R) (a b a' b' : R),
  open_interval a b a' -> open_interval a b b' ->
  strictly_increasing_open_interval f a b ->
  strictly_increasing_interval f a' b'.
Proof.
intros f a b a' b' a'_in b'_in Hf x y x_in y_in Hxy ;
 apply Hf ; try (apply interval_open_restriction_compat with a' b' ; assumption).
 assumption.
Qed.

Lemma derivable_open_interval_restriction_compat :
  forall (f : R -> R) (a b a' b' : R),
  open_interval a b a' -> open_interval a b b' ->
  derivable_open_interval f a b ->
  derivable_interval f a' b'.
Proof.
intros f a b a' b' a'_in b'_in Hf x x_in ; destruct (Hf x) as [l Hl].
 eapply interval_open_restriction_compat ; try eapply x_in ; eassumption.
 exists l ; eapply derivable_pt_lim_open_interval_restriction_compat ;
  eassumption.
Qed.

Lemma derivable_open_interval_restriction_compat' :
  forall (f : R -> R) (a b a' b' : R),
  open_interval a b a' -> open_interval a b b' ->
  derivable_open_interval f a b ->
  derivable_open_interval f a' b'.
Proof.
intros f a b a' b' a'_in b'_in Hf x x_in ; destruct (Hf x) as [l Hl].
 eapply open_interval_restriction_compat ; try eapply x_in ;
  eapply open_interval_interval ; eassumption.
 exists l ; eapply derivable_pt_lim_open_interval_restriction_compat' ;
  eassumption.
Qed.

Lemma strictly_increasing_interval_restriction : forall f lb ub,
  strictly_increasing f -> strictly_increasing_interval f lb ub.
Proof.
intros f lb ub Hf x y x_in y_in Hxy ; apply Hf ; assumption.
Qed.

Lemma strictly_increasing_open_interval_restriction : forall f lb ub,
  strictly_increasing f -> strictly_increasing_open_interval f lb ub.
Proof.
intros f lb ub Hf x y x_in y_in Hxy ; apply Hf ; assumption.
Qed.


Lemma derivable_pt_lim_interval_uniqueness:
  forall (f : R -> R) (lb ub x l l' : R),
  lb < ub -> interval lb ub x ->
  derivable_pt_lim_in f (interval lb ub) x l ->
  derivable_pt_lim_in f (interval lb ub) x l' -> l = l'.
Proof.
intros ; eapply derivable_pt_lim_in_uniqueness ; try eassumption.
 apply dense_interval ; assumption.
Qed.

Lemma derivable_pt_lim_derive_pt_interval: forall f lb ub x l
  (pr : derivable_pt_in f (interval lb ub) x),
  lb < ub -> interval lb ub x ->
  derivable_pt_lim_in f (interval lb ub) x l ->
  derive_pt_in f (interval lb ub) x pr = l.
Proof.
intros f lb ub x l [l' Hl'] x_in Hl ;
 eapply derivable_pt_lim_interval_uniqueness ;
 eassumption.
Qed.

Lemma derivable_pt_lim_derive_pt_open_interval: forall f lb ub x l
  (pr : derivable_pt_in f (open_interval lb ub) x),
  open_interval lb ub x ->
  derivable_pt_lim_in f (open_interval lb ub) x l ->
  derive_pt_in f (open_interval lb ub) x pr = l.
Proof.
intros f lb ub x l [l' Hl'] x_in Hl ;
 eapply derivable_pt_lim_open_interval_uniqueness ;
 eassumption.
Qed.

Lemma derive_pt_derivable_pt_lim_interval: forall f lb ub x l
  (pr : derivable_pt_in f (interval lb ub) x),
  lb < ub -> interval lb ub x ->
  derive_pt_in f (interval lb ub) x pr = l ->
  derivable_pt_lim_in f (interval lb ub) x l.
Proof.
intros f lb ub x l [l' Hl'] Hlt x_in Hl ; subst ; assumption.
Qed.
