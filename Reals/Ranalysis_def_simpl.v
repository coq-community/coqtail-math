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

(** Compatibility of growth_rate with common operations *)

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