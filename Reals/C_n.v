Require Import Reals.
Require Import Rfunction_facts.
Require Import FunctionalExtensionality.

Open Local Scope R_scope.

Inductive C : nat -> (R -> R) -> Set :=
  | C_0 : forall f, continuity f -> C 0 f
  | C_Sn : forall f n (pr : derivable f), C n (derive f pr) -> C (S n) f.

Inductive C_infty (f : R -> R) : Set :=
  | C_infty_const : (forall n, C n f) -> C_infty f.

Lemma zero_C_infty : C_infty (fct_cte 0).
Proof.
 apply C_infty_const ;  intro n; induction n.
  constructor; reg.
  
  apply C_Sn with (derivable_const 0).

  replace (derive (fct_cte 0) (derivable_const 0)) with (fct_cte 0).
  apply IHn.
  extensionality x ; unfold derive , fct_cte.
  symmetry ; rewrite derive_pt_eq.
  apply derivable_pt_lim_const.
Qed.

Lemma const_C_infty : forall c, C_infty (fct_cte c).
Proof.
 intro c ; apply C_infty_const ; intros [|n].
  constructor; reg.
  apply C_Sn with (derivable_const c).
  replace (derive (fct_cte c) (derivable_const c)) with (fun (_:R) => 0).
  apply zero_C_infty.
  extensionality x ; unfold derive ; symmetry ;
  rewrite derive_pt_eq ; apply derivable_pt_lim_const.
Qed.

Lemma id_C_infty : C_infty id.
Proof.
 apply C_infty_const ; intro n ; destruct n.
  constructor ; apply derivable_continuous ; apply derivable_id.
  apply C_Sn with derivable_id.
  replace (derive id derivable_id) with (fct_cte 1).
  assert (H := const_C_infty 1) ; inversion H ; auto.
  extensionality x ; unfold derive.
  symmetry ; rewrite derive_pt_eq ; unfold fct_cte.
  apply derivable_pt_lim_id.
Qed.

Lemma derivable_pt_eq_compat : forall f g,
  (forall x, f x = g x) ->
  forall x, derivable_pt f x -> derivable_pt g x.
Proof.
intros f g Heq x Hf.
destruct Hf as [l Hl]; exists l.
intros e epos.
destruct (Hl e epos) as [delta Hdelta].
exists delta.
intros h hnn Hh.
repeat rewrite <- Heq.
auto.
Qed.

Lemma derivable_eq_compat : forall f g,
  (forall x, f x = g x) ->
  derivable f -> derivable g.
Proof.
intros f g Heq Hf x.
apply derivable_pt_eq_compat with f; auto.
Qed.

Lemma C_eq_compat : forall f g,
  (forall x, f x = g x) ->
  forall n, C n f -> C n g.
Proof.
intros f g Heq n Hf.
destruct Hf as [| f n Df HDf].
 constructor.
 refine (Rfun_continuity_eq_compat f g _ _); auto.
 
 assert (Dg : derivable g).
  eapply derivable_eq_compat; auto.
 refine (C_Sn _ _ Dg _).
 assert (T := functional_extensionality _ _ Heq).

 replace (derive g Dg) with (derive f Df) ; [assumption |].
  extensionality x ; unfold derive ; symmetry ;
  rewrite derive_pt_eq.
  rewrite <- T.
  apply derive_pt_eq_1 with (Df x).
  reflexivity.
Qed.

Lemma monomial_C_infty : forall d a,
  C_infty (fun x => Rmult a (pow x d)).
Proof.
intro d ; induction d ; intro a ; apply C_infty_const ; intro n.
 apply C_eq_compat with (fct_cte a).
  intro; ring_simplify; reflexivity.
  assert (H := const_C_infty a) ; inversion H ; auto.
  destruct n.
   constructor; intro; reg.
   
   assert (pr : derivable (fun x : R => (a * x ^ S d)%R)) by reg.
   refine (C_Sn _ _ pr _).
   replace (derive (fun x : R => (a * x ^ S d)%R) pr) with (fun x => (a * INR (S d) * pow x d)%R).
   assert (H := IHd (a * INR (S d))) ; inversion H ; auto.
   extensionality x ; symmetry.
    pose (fmod := mult_real_fct a (fun x0 : R => (x0 ^ S d)%R)).
    transitivity (derive_pt _ x (derivable_pt_scal _ a x (derivable_pt_pow (S d) _))).
     apply pr_nu.
     
     rewrite derive_pt_scal.
     rewrite Rmult_assoc.
     apply Rmult_eq_compat_l.
     apply derive_pt_pow.
Qed.

Lemma C_pred_compat : forall n f,
  C (S n) f -> C n f.
Proof.
 induction n ; intros f Hf.
  constructor.
  inversion Hf; reg.
  
  inversion Hf; subst.
  apply C_Sn with pr ; apply IHn ; assumption.
Qed.

Lemma C_plus_compat : forall n f g,
  C n f -> C n g -> C n (plus_fct f g).
Proof.
induction n.
 intros f g Hf Hg.
 inversion Hf; inversion Hg; subst.
 constructor; intro; reg.
 
 intros f g Hf Hg.
 inversion Hf; inversion Hg; subst.
 refine (C_Sn _ _ (derivable_plus _ _ pr pr0) _).
 replace (derive (f + g) (derivable_plus f g pr pr0)) with (plus_fct (derive f pr) (derive g pr0)).
 apply IHn ; assumption.
 extensionality x ; symmetry.
 transitivity (derive f pr x + derive g pr0 x).
 unfold derive ; rewrite derive_pt_eq ;
 apply derivable_pt_lim_plus ; eapply derive_pt_eq_1 ;
 reflexivity.
 auto.
Qed.

Lemma C_infty_plus_compat : forall f g,
  C_infty f -> C_infty g -> C_infty (plus_fct f g).
Proof.
 intros f g H H0; constructor; intro; apply C_plus_compat; inversion H ; inversion H0 ; auto.
Qed.

Lemma C_scal_compat : forall n f a,
  C n f -> C n (mult_real_fct a f).
Proof.
induction n.
 intros f a Hf.
 inversion Hf; subst.
 constructor; intro; reg.
 
 intros f a Hf.
 inversion Hf; subst.
 refine (C_Sn _ _ (derivable_scal _ _ pr) _).
 replace (derive (mult_real_fct a f) (derivable_scal f a pr)) with (mult_real_fct a (derive f pr)).
 apply IHn ; assumption.
  unfold mult_real_fct ; symmetry ; extensionality x ; unfold derive ; rewrite derive_pt_eq.
  eapply derive_pt_eq_1 ; apply derive_pt_scal.
Qed.

Lemma C_infty_scal_compat : forall f a,
  C_infty f -> C_infty (mult_real_fct a f).
Proof.
 intros f a H; constructor ; intro; apply C_scal_compat; inversion H ; auto.
Qed.

Lemma C_mult_compat : forall n f g,
  C n f -> C n g -> C n (mult_fct f g).
Proof.
 induction n.
  intros f g Hf Hg.
  inversion Hf; inversion Hg; subst.
  constructor; intro; reg.
  
  intros f g Hf Hg.
  inversion Hf; inversion Hg; subst.
  refine (C_Sn _ _ (derivable_mult _ _ pr pr0) _).
  replace (derive (f * g) (derivable_mult f g pr pr0)) with (fun x => (derive f pr) x * g x + f x * (derive g pr0) x)%R.
  apply C_plus_compat ; apply IHn ; [| apply C_pred_compat | apply C_pred_compat |] ; assumption.
  
  extensionality x ; symmetry ; unfold derive ; rewrite derive_pt_eq ; eapply derive_pt_eq_1 ;
  apply derive_pt_mult.
Qed.

Lemma C_infty_mult_compat : forall f g,
  C_infty f -> C_infty g -> C_infty (mult_fct f g).
Proof.
 intros f g H H0 ; constructor ; intro; apply C_mult_compat; inversion H ;
 inversion H0 ; auto.
Qed.

Lemma C_comp_compat : forall n f g,
  C n f -> C n g -> C n (comp f g).
Proof.
 induction n.
  intros f g Hf Hg.
  inversion Hf; inversion Hg; subst.
  constructor; intro; reg.
  
  intros f g Hf Hg.
  inversion Hf; inversion Hg; subst.
  refine (C_Sn _ _ (derivable_comp _ _ pr0 pr) _).
  replace (derive (comp f g) (derivable_comp g f pr0 pr)) with (fun x => (derive f pr) (g x) * (derive g pr0) x)%R.
   eapply C_mult_compat.
   fold (comp (derive f pr) g).
   apply IHn ; [| apply C_pred_compat] ; assumption.
   assumption.
   
  extensionality x ; symmetry ; unfold derive.
  rewrite derive_pt_eq ; eapply derive_pt_eq_1 ; apply derive_pt_comp.
Qed.

Lemma C_infty_comp_compat : forall f g,
  C_infty f -> C_infty g -> C_infty (comp f g).
Proof.
 intros f g H H0; constructor ; intro; apply C_comp_compat;
 inversion H ; inversion H0 ; auto.
Qed.

Lemma C_cos_sin : forall n, C n sin * C n cos * C n (-sin)%F * C n (-cos)%F.
 induction n.
  repeat split; constructor; reg.
  
  destruct IHn as [[[IHs IHc] IHns] IHnc].
  repeat split.

   apply C_Sn with derivable_sin.
   replace (derive sin derivable_sin) with cos.
   assumption.
   extensionality x ; symmetry ; unfold derive ; reg.

   apply C_Sn with derivable_cos.
   replace (derive cos derivable_cos) with (-sin)%F.
   assumption.
   extensionality x ; symmetry ; unfold derive ; reg.

   assert (dns : derivable (-sin)) by reg.
   apply C_Sn with dns.
   replace (derive (-sin) dns) with (-cos)%F.
   assumption.
   extensionality x ; symmetry ; unfold derive ; reg.
   
   assert (dnc : derivable (-cos)) by reg.
   apply C_Sn with dnc.
   replace (derive (-cos) dnc) with sin.
   assumption.
   extensionality x ; symmetry ; unfold derive ; reg.
Qed.

Lemma C_infty_sin : C_infty sin.
Proof.
 constructor ; intro ; eapply C_cos_sin.
Qed.

Lemma C_infty_cos : C_infty cos.
Proof.
 constructor; intro; eapply C_cos_sin.
Qed.

Require Import Rpser_def.
Require Import Rpser_facts.

Lemma C_n_Rpser : forall (An  : nat -> R) (Rho : infinite_cv_radius An), C_infty (sum An Rho).
Proof.
intros An Rho ; constructor ; intro n ; generalize Rho ; generalize An.
 clear An Rho ; induction n.
  intros An Rho ; constructor.
  intro x ; apply continuity_pt_sum.
  intros An Rho.
  apply C_Sn with (derivable_sum An Rho).
  replace (derive (sum An Rho) (derivable_sum An Rho)) with (sum_derive An Rho).
  apply IHn.
  extensionality x ; symmetry ; apply derive_pt_eq_0 ; apply derivable_pt_lim_sum.
Qed.





(** nth derivative *)

Fixpoint nth_derive (n : nat) (f : R -> R) (pr : C n f) : R -> R := match pr with
   | C_0 f0 H => f
   | C_Sn f0 n0 pr H => nth_derive n0 (derive f0 pr) H
end.
