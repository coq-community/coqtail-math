Require Import Reals.
Require Import Rintegral.
Require Import Riemann_integrable.
Require Import C_n_def.
Require Import C_n.
Require Import Fourier.
Require Import Ring.
Require Import Ranalysis.
Require Import Rextensionality.

(* Trivial version of linear Cauchy-Lipschitz*)

Section Trivial.

Lemma derivable_pt_eq :
  forall (f g : R -> R) x (H: f = g), derivable_pt f x -> derivable_pt g x.
Proof.
intros. subst. assumption.
Qed.

Lemma CL_tr : forall a t0 V0, C 0 a -> 
  {y : R -> R & {pr : (C 1 y) | forall (t : R), (nth_derive 1 y pr) t = (a t) * (y t) /\ y t0 = V0}}.
Proof.
 intros.
 assert (Hcont : forall x, continuity_pt a x). inversion H. apply H0.
 assert (forall t0 t, Riemann_integrable a t0 t). intros. apply continuity_RiemannInt_1.
 intros. inversion H. apply H1.
 exists (fun t => V0 * exp (@RiemannInt a t0 t (X t0 t))).
 assert (pr : C 1 (fun t => V0 * exp (@RiemannInt a t0 t (X t0 t)))).
  apply C_scal. apply C_comp. apply C_exp. 
  apply derivable_pt_continuity_Riemann_implies_C1. inversion H. apply H0.
 exists (pr). intros. simpl. split.
  unfold derive.
  pose (p:= (C_Sn_derivable (fun t1 : R => V0 * exp (RiemannInt (X t0 t1))) 0 pr)). fold p.
  rewrite <- (derive_pt_RiemannInt a t0 t X (Hcont t)).
  rewrite <- (derive_pt_exp ). rewrite <- derive_pt_scal.
  rewrite Rmult_comm.
  rewrite <- (derive_pt_comp (fun t1 => RiemannInt (X t0 t1)) (mult_real_fct V0 exp)). 
  apply pr_nu_var. unfold comp, mult_real_fct. reflexivity.
  rewrite RiemannInt_singleton. rewrite exp_0.
  ring.
Qed.

Lemma RiemannInt_continuity : forall a t0 (Hconta : continuity a) (Ha : forall t0 t, 
(* TODO preuve à raffiner *)
   Riemann_integrable a t0 t), continuity (fun t => RiemannInt (Ha t0 t)).
Proof.
 intros.
 apply derivable_continuous. unfold derivable. intros. apply RiemannInt_derivable_pt.
 apply Hconta.
Qed.

Lemma CL_tr_second_member : forall a b t0 V0, C 0 a -> C 0 b ->
  {y : R -> R & { pr : (C 1 y) | 
    forall (t : R), (nth_derive 1 y pr) t - (a t) * (y t) = b t /\ y t0 = V0}}.
Proof.
 intros.
 assert (Ha: forall t0 t, Riemann_integrable a t0 t) 
  by (intros ; apply continuity_RiemannInt_1 ; inversion H ; intuition).
 
 assert (Hconta : continuity a) by (inversion H ; assumption).

 assert (Hcontb : continuity b) by (inversion H0 ; assumption).

 assert (Hcontsol : forall t1 t, continuity_pt (mult_fct b (comp exp (opp_fct (fun t => RiemannInt (Ha t1 t))))) t).  intros. reg. apply (C_continuity _ 1).
  apply derivable_pt_continuity_Riemann_implies_C1. apply Hconta.

 assert (Hsol : forall t1 t0 t, 
   Riemann_integrable (mult_fct b (comp exp (opp_fct (fun t => RiemannInt (Ha t1 t))))) t0 t)
   by (intros ; apply continuity_RiemannInt_1 ; intuition).

 exists (mult_fct (plus_fct (fct_cte V0)(fun t => RiemannInt (Hsol t0 t0 t))) (comp exp (fun t => RiemannInt (Ha t0 t)))).
 assert (pr : C 1 (mult_fct (plus_fct (fct_cte V0)(fun t => RiemannInt (Hsol t0 t0 t))) (comp exp (fun t => RiemannInt (Ha t0 t))))).
  apply C_mult. apply C_plus. apply C_infty_n. apply const_C_infty. 
  apply derivable_pt_continuity_Riemann_implies_C1. reg.
  apply RiemannInt_continuity. unfold continuity. apply Hconta.
  apply C_comp. apply C_exp. apply derivable_pt_continuity_Riemann_implies_C1. unfold continuity. 
  apply Hconta.
 exists pr.
 intros. simpl. split. unfold derive.
 assert (Hpr1 : derivable_pt (fun t => RiemannInt (Hsol t0 t0 t)) t). apply RiemannInt_derivable_pt. 
 reg. apply RiemannInt_continuity. apply Hconta.
 unfold derive.
 assert (Hpr2 : derivable_pt (fun t => RiemannInt (Ha t0 t)) t). apply RiemannInt_derivable_pt. apply Hconta.
 rewrite (pr_nu_var _ (mult_fct (plus_fct (fct_cte V0)(fun t => RiemannInt (Hsol t0 t0 t))) (comp exp (fun t => RiemannInt (Ha t0 t)))) _ _ 
  (derivable_pt_mult _ _ _ 
    (derivable_pt_plus _ _ _ (derivable_pt_const V0 t) Hpr1) 
      (derivable_pt_comp _ _ _ Hpr2 (derivable_pt_exp _)))).
 rewrite derive_pt_mult. 
 rewrite derive_pt_comp.
 rewrite derive_pt_exp. rewrite derive_pt_RiemannInt_1. rewrite derive_pt_plus.
 rewrite derive_pt_const. unfold plus_fct, comp, fct_cte. simpl.
 unfold mult_fct. rewrite derive_pt_RiemannInt_1. ring_simplify. unfold opp_fct. rewrite exp_Ropp.
 field. 
 generalize (exp_pos (RiemannInt (Ha t0 t))). intros Habs Habs2. fourier.
 apply Hcontsol.
 apply Hconta.
 reflexivity.
 unfold comp, plus_fct, mult_fct, fct_cte. rewrite RiemannInt_singleton.
 rewrite RiemannInt_singleton. rewrite exp_0.
 ring.
Qed.

End Trivial.

