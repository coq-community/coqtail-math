Require Import Reals.
Require Import Rintegral Riemann_integrable.
Require Import Rfunction_classes Nth_derivative_def.
Require Import Lra Ring.
Require Import Ranalysis.
Require Import Rextensionality.

(* Trivial version of linear Cauchy-Lipschitz*)

Section Trivial.

Lemma C_Sn_derivable : forall f n, C (S n) f -> derivable f.
Proof.
 intros.
 inversion H. subst. apply pr.
Qed.

Lemma C_Sm_derive_C_m : forall f n pr, C (S n) f -> C n (derive f pr).
Proof.
 intros.
 inversion H.
 eapply C_ext. 2: apply H1. intro. apply pr_nu.
Qed.

Lemma C_continuity : forall f n, C n f -> continuity f.
Proof.
intros.
inversion H. apply H0.
apply derivable_continuous. assumption.
Qed.

Lemma CL_tr : forall a t0 V0, C 0 a ->
  {y : R -> R & {pr : (D 1 y) | forall (t : R), (nth_derive y pr) t = (a t) * (y t) /\ y t0 = V0}}.
Proof.
 intros a t0 V0 H ; assert (Hcont : continuity a) by (inversion H ; assumption).
 assert (forall t0 t, Riemann_integrable a t0 t).
  intros ; apply continuity_RiemannInt_1.
  intros ; inversion H ; auto.
 assert (pr : C 1 (fun t => V0 * exp (@RiemannInt a t0 t (X t0 t)))).
  apply C_scal; apply (C_comp 1 exp); [apply C_infty_exp |
  apply derivable_pt_continuity_Riemann_implies_C1] ; reg.

 exists (fun t => V0 * exp (@RiemannInt a t0 t (X t0 t))) ; exists (C_implies_D _ _ pr).

 intro t ; split.
  rewrite <- (derive_pt_RiemannInt a t0 t X (Hcont t)), <-(derive_pt_exp ),
  <- derive_pt_scal, Rmult_comm, <- (derive_pt_comp (fun t1 => RiemannInt (X t0 t1))
  (mult_real_fct V0 exp)) ; apply pr_nu_var ; reflexivity.
  rewrite RiemannInt_singleton, exp_0 ; apply Rmult_1_r.
Qed.

Lemma RiemannInt_continuity : forall a t0 (Hconta : continuity a) (Ha : forall t0 t, 
   Riemann_integrable a t0 t), continuity (fun t => RiemannInt (Ha t0 t)).
Proof.
 intros ; apply derivable_continuous ; intro ; apply RiemannInt_derivable_pt ; apply Hconta.
Qed.

Lemma CL_tr_second_member : forall a b t0 V0, C 0 a -> C 0 b ->
  {y : R -> R & { pr : (D 1 y) | 
    forall (t : R), (nth_derive y pr) t - (a t) * (y t) = b t /\ y t0 = V0}}.
Proof.
 intros a b t0 V0 Ha0 Hb0 ;
 assert (Ha: forall t0 t, Riemann_integrable a t0 t) 
    by (intros ; apply continuity_RiemannInt_1 ; inversion Ha0 ; intuition) ;
 assert (Hconta : continuity a)
    by (inversion Ha0 ; assumption) ;
 assert (Hcontb : continuity b)
    by (inversion Hb0 ; assumption).

 assert (Hcontsol : forall t1 t, continuity_pt
   (b * (comp exp (- (fun t => RiemannInt (Ha t1 t)))))%F t).
  intros ; reg ; apply (C_continuity _ 1) ;
  apply derivable_pt_continuity_Riemann_implies_C1 ; assumption.

 assert (Hsol : forall t1 t0 t, Riemann_integrable
  (b * (comp exp (- (fun t => RiemannInt (Ha t1 t)))))%F t0 t)
    by (intros ; apply continuity_RiemannInt_1 ; intuition).

 assert (pr : C 1 (((fct_cte V0) + (fun t => RiemannInt (Hsol t0 t0 t))) *
  (comp exp (fun t => RiemannInt (Ha t0 t))))%F).
  apply C_mult ; [apply C_plus ; [apply C_infty_const |] | apply C_comp ;
  [apply C_infty_exp |]] ; apply derivable_pt_continuity_Riemann_implies_C1 ; reg ;
  apply RiemannInt_continuity ; assumption.

 exists (((fct_cte V0) + (fun t => RiemannInt (Hsol t0 t0 t))) *
  (comp exp (fun t => RiemannInt (Ha t0 t))))%F ; exists (C_implies_D _ _ pr).

 intros t ; simpl ; split.
 assert (Hpr1 : derivable_pt (fun t => RiemannInt (Hsol t0 t0 t)) t)
   by (apply RiemannInt_derivable_pt ; reg ; apply RiemannInt_continuity ;
   assumption).
 assert (Hpr2 : derivable_pt (fun t => RiemannInt (Ha t0 t)) t)
   by (apply RiemannInt_derivable_pt ; auto).

 unfold derive ; rewrite (pr_nu_var _ (((fct_cte V0) +
  (fun t => RiemannInt (Hsol t0 t0 t))) * (comp exp (fun t => RiemannInt (Ha t0 t))))%F _ _ 
  (derivable_pt_mult _ _ _ (derivable_pt_plus _ _ _ (derivable_pt_const V0 t) Hpr1) 
  (derivable_pt_comp _ _ _ Hpr2 (derivable_pt_exp _)))).

 rewrite derive_pt_mult, derive_pt_comp, derive_pt_exp, derive_pt_RiemannInt_1,
 derive_pt_plus, derive_pt_const ; unfold plus_fct, comp, fct_cte, mult_fct ; simpl.
 rewrite derive_pt_RiemannInt_1.
 ring_simplify ; unfold opp_fct ; rewrite exp_Ropp ; field.
 apply Rgt_not_eq ; apply exp_pos.
 apply Hcontsol.
 apply Hconta.
 reflexivity.
 unfold comp, plus_fct, mult_fct, fct_cte ; do 2 rewrite RiemannInt_singleton ;
 rewrite exp_0 ; ring.
Qed.

End Trivial.
