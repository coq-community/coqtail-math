Require Import Rbase Ranalysis.
Require Import Ranalysis_def Rfunction_facts.
Require Import MyRIneq.

Local Open Scope R_scope.

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