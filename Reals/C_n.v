Require Import Reals.
Require Import Rfunction_facts.

Open Local Scope R_scope.

Inductive C : nat -> (R -> R) -> Set :=
  | C_0 : forall f, continuity f -> C 0 f
  | C_Sn : forall f n (pr : derivable f), { f' : R -> R & {p : C n f' | forall x, derive_pt f x (pr x) = (f' x)}} -> C (S n) f.

Definition C_infty (f : R -> R) : Type := forall n, C n f.

Lemma zero_C_infty : C_infty (fct_cte 0).
Proof.
 intro n; induction n.
  constructor; reg.
  
  apply C_Sn with (derivable_const 0).
  exists (fct_cte 0).
  split.
   apply IHn.
   intro; reg.
Qed.

Lemma const_C_infty : forall c, C_infty (fct_cte c).
Proof.
 intros c [|n].
  constructor; reg.
  apply C_Sn with (derivable_const c).
  exists (fct_cte 0).
  split.
   apply zero_C_infty.
   intro; reg.
Qed.

Lemma id_C_infty : C_infty id.
Proof.
 intro n ; destruct n.
  constructor ; apply derivable_continuous ; apply derivable_id.
  apply C_Sn with derivable_id.
  exists (fct_cte 1); split.
   apply const_C_infty.
   intro; reg.
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
destruct Hf as [|f n Hdf [f' [Hdf' Heqf']]].
 constructor.
 refine (Rfun_continuity_eq_compat f g _ _); auto.
 
 assert (prg : derivable g).
  eapply derivable_eq_compat; auto.
 refine (C_Sn _ _ prg _).
 exists f'; split.
  auto.
  intros x.
  rewrite <- Heqf'.
  apply pr_nu_var2.
  auto.
Qed.

Lemma monomial_C_infty : forall d a,
  C_infty (fun x => Rmult a (pow x d)).
Proof.
induction d.
 intros a n.
 apply C_eq_compat with (fct_cte a).
  intro; ring_simplify; reflexivity.
  apply const_C_infty.
  
  intros a n.
  destruct n.
   constructor; intro; reg.
   
   assert (pr : derivable (fun x : R => (a * x ^ S d)%R)) by reg.
   refine (C_Sn _ _ pr _).
   exists (fun x => (a * INR (S d) * pow x d)%R); split.
    apply IHd.
    intros x.
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
 induction n.
  intros f Hf.
  constructor.
  inversion Hf; reg.
  
  intros f Hf.
  inversion Hf; subst.
  destruct H0 as [f' [Hcf' Hf']].
  apply C_Sn with pr.
  exists f'; exists (IHn _ Hcf') ; auto.
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
 destruct H0 as [f' [Hcf' Hf']].
 destruct H3 as [g' [Hcg' Hg']].
 refine (C_Sn _ _ (derivable_plus _ _ pr pr0) _).
 exists (plus_fct f' g').
 split.
  apply IHn; auto.
  intros x.
  unfold plus_fct.
  rewrite <- Hf'; rewrite <- Hg'.
  reg.
  rewrite (pr_nu _ _ H (pr x)).
  rewrite (pr_nu _ _ H0 (pr0 x)).
  reflexivity.
Qed.

Lemma C_infty_plus_compat : forall f g,
  C_infty f -> C_infty g -> C_infty (plus_fct f g).
Proof.
 intros; intro; apply C_plus_compat; auto.
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
 destruct H0 as [f' [Hcf' Hf']].
 refine (C_Sn _ _ (derivable_scal _ _ pr) _).
 exists (mult_real_fct a f').
 split.
  apply IHn; auto.
  intros x.
  unfold mult_real_fct.
  rewrite <- Hf'.
  reg.
  rewrite (pr_nu _ _ H (pr x)).
  reflexivity.
Qed.

Lemma C_infty_scal_compat : forall f a,
  C_infty f -> C_infty (mult_real_fct a f).
Proof.
 intros; intro; apply C_scal_compat; auto.
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
  destruct H0 as [f' [Hcf' Hf']].
  destruct H3 as [g' [Hcg' Hg']].
  refine (C_Sn _ _ (derivable_mult _ _ pr pr0) _).
  exists (fun x => f' x * g x + g' x * f x)%R.
  split.
   eapply C_plus_compat.
    apply IHn.
     apply Hcf'.
     apply C_pred_compat, Hg.
    apply IHn.
     apply Hcg'.
     apply C_pred_compat, Hf.
   intros x.
   rewrite <- Hf'; rewrite <- Hg'.
   reg.
   rewrite (pr_nu _ _ H (pr x)).
   rewrite (pr_nu _ _ H0 (pr0 x)).
   ring.
Qed.

Lemma C_infty_mult_compat : forall f g,
  C_infty f -> C_infty g -> C_infty (mult_fct f g).
Proof.
 intros; intro; apply C_mult_compat; auto.
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
  destruct H0 as [f' [Hcf' Hf']].
  destruct H3 as [g' [Hcg' Hg']].
  refine (C_Sn _ _ (derivable_comp _ _ pr0 pr) _).
  exists (fun x => g' x * f' (g x))%R.
  split.

   eapply C_mult_compat.
    auto.
    fold (comp f' g).
    apply IHn.
     auto.
     destruct n.
      constructor; intro; reg.
      
      apply (C_Sn _ _ pr0).
      exists g' ; exists (C_pred_compat _ _ Hcg').
       auto.

   intros x.
   rewrite <- Hf'; rewrite <- Hg'.
   reg.
   rewrite (pr_nu _ _ H (pr (g x))).
   rewrite (pr_nu _ _ H0 (pr0 x)).
   ring.
Qed.

Lemma C_infty_comp_compat : forall f g,
  C_infty f -> C_infty g -> C_infty (comp f g).
Proof.
 intros; intro; apply C_comp_compat; auto.
Qed.

Lemma C_cos_sin : forall n, C n sin * C n cos * C n (-sin)%F * C n (-cos)%F.
 induction n.
  repeat split; constructor; reg.
  
  destruct IHn as [[[IHs IHc] IHns] IHnc].
  repeat split.
   apply C_Sn with derivable_sin.
   eexists cos ; exists IHc ; intro; reg.
   
   apply C_Sn with derivable_cos.
   eexists (-sin)%F ; exists IHns ; intro ; reg.
   
   assert (dns : derivable (-sin)) by reg.
   apply C_Sn with dns.
   eexists (-cos)%F; exists IHnc ; intro ; reg.
   
   assert (dnc : derivable (-cos)) by reg.
   apply C_Sn with dnc.
   eexists sin; exists IHs ; intro ; reg.
Qed.

Lemma C_infty_sin : C_infty sin.
Proof.
 intro; eapply C_cos_sin.
Qed.

Lemma C_infty_cos : C_infty cos.
Proof.
 intro; eapply C_cos_sin.
Qed.

Require Import Rpser_def.
Require Import Rpser_facts.

Lemma C_n_Rpser : forall (An  : nat -> R) (Rho : infinite_cv_radius An), C_infty (sum An Rho).
Proof.
intros An Rho n ; generalize Rho ; generalize An.
 clear An Rho ; induction n.
  intros An Rho ; constructor.
  intro x ; apply continuity_pt_sum.
  intros An Rho.
  apply C_Sn with (derivable_sum An Rho).
  exists (sum_derive An Rho) ; split.
  apply IHn.
  intro x ; apply derive_pt_eq_0 ; apply derivable_pt_lim_sum.
Qed.

Definition derive (n : nat) (f : R -> R) (p : C n f) : R -> R.
Proof.
intro n ; induction n ; intros f Cnf.
 exact f.
 inversion Cnf ; subst ; destruct H0 as [f' [Cnf' _]].
 apply IHn with f' ; assumption.
Defined.
