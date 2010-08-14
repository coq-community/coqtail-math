Require Import Reals.
Require Import Rfunction_facts.

Open Local Scope R_scope.

Inductive C : nat -> (R -> R) -> Set :=
  | C_0 : forall f, continuity f -> C 0 f
  | C_Sn : forall f n (pr : derivable f), 
    C n (derive f pr) -> C (S n) f.

Inductive C_infty (f : R -> R) : Set :=
  | C_infty_const : (forall n, C n f) -> C_infty f.

Lemma continuity_ext : forall f g, f == g -> 
  continuity f -> continuity g.
Proof.
intros. unfold continuity in *.
intro. unfold continuity_pt, continue_in, limit1_in, limit_in in *.
intros.
specialize (H0 x eps H1). destruct H0.
exists x0. split. intuition.
destruct H0. intros.
specialize (H2 x1 H3).
unfold dist in *. simpl in *. unfold R_dist in *.
rewrite <- H. rewrite <- H. apply H2.
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

(*
Lemma derivable_ext : forall f g, f == g -> 
  derivable f -> derivable g.
Proof.
intros.
unfold derivable, derivable_pt in *.
intro x. specialize (H0 x).
destruct H0 as (l, H2).
exists l. unfold derivable_pt_abs, derivable_pt_lim in *.
intros. 
destruct (H2 eps H0) as (delta, H3).
exists delta. intros.
specialize (H3 h H1 H4). do 2 rewrite <- H.
apply H3.
Qed.
*)


Lemma C_ext : forall n f f', f == f' -> C n f -> C n f'.
Proof.
induction n ; intros.
 inversion H0.
 apply (C_0 f'). 
 apply continuity_ext with f. apply H.
 reg.

 inversion_clear H0.
 assert (pr1 : derivable f').
 apply derivable_eq_compat with f ; intuition.
 apply (C_Sn f' _ pr1).
 apply IHn with (derive f pr). intro.
 unfold derive.
 rewrite (pr_nu_var2 _ _ _ (pr x) (pr1 x) H).
 reflexivity.
 apply H1.
Qed.

Lemma zero_C_infty : C_infty (fct_cte 0).
Proof.
 apply C_infty_const ;  intro n; induction n.
  constructor; reg.
  
  apply C_Sn with (derivable_const 0).

  apply C_ext with (fct_cte 0).
  intro. unfold derive , fct_cte.
  symmetry ; rewrite derive_pt_eq.
  apply derivable_pt_lim_const.
  apply IHn.
Qed.

Lemma const_C_infty : forall c, C_infty (fct_cte c).
Proof.
 intro c ; apply C_infty_const ; intros [|n].
  constructor; reg.
  apply C_Sn with (derivable_const c).
  apply C_ext with (fun (_:R) => 0).
  intro. unfold derive ; symmetry ;
  rewrite derive_pt_eq ; apply derivable_pt_lim_const.

  apply zero_C_infty.
Qed.

Lemma id_C_infty : C_infty id.
Proof.
 apply C_infty_const ; intro n ; destruct n.
  constructor ; apply derivable_continuous ; apply derivable_id.
  apply C_Sn with derivable_id.
  apply C_ext with (fct_cte 1).
  intro ; unfold derive.
  symmetry ; rewrite derive_pt_eq ; unfold fct_cte.
  apply derivable_pt_lim_id.
  assert (H := const_C_infty 1) ; inversion H ; auto.
Qed.

(*
Lemma C_eq_compat : forall f g,
  (forall x, f x = g x) ->
  forall n, C n f -> C n g.
Proof.
intros f g Heq n Hf.
destruct Hf as [| n Df HDf].
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
*)
Lemma monomial_C_infty : forall d a,
  C_infty (fun x => Rmult a (pow x d)).
Proof.
intro d ; induction d ; intro a ; apply C_infty_const ; intro n.
 apply C_ext with (fct_cte a).
  intro; ring_simplify; reflexivity.
  assert (H := const_C_infty a) ; inversion H ; auto.
  destruct n.
   constructor; intro; reg.
   
   assert (pr : derivable (fun x : R => (a * x ^ S d)%R)) by reg.
   
   apply C_Sn with pr.
   apply C_ext with (fun x => (a * INR (S d) * pow x d)%R).
   intro ; symmetry.
    pose (fmod := mult_real_fct a (fun x0 : R => (x0 ^ S d)%R)).
    transitivity (derive_pt _ x (derivable_pt_scal _ a x (derivable_pt_pow (S d) _))).
     apply pr_nu.
     
     rewrite derive_pt_scal.
     rewrite Rmult_assoc.
     apply Rmult_eq_compat_l.
     apply derive_pt_pow.
   
   assert (H := IHd (a * INR (S d))) ; inversion H ; auto.
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
 apply C_ext with (plus_fct (derive f pr) (derive g pr0)).
 intro ; symmetry.
 transitivity (derive f pr x + derive g pr0 x).
 unfold derive ; rewrite derive_pt_eq ;
 apply derivable_pt_lim_plus ; eapply derive_pt_eq_1 ;
 reflexivity.
 auto.
 apply IHn ; assumption.
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
 apply C_ext with  (mult_real_fct a (derive f pr)).
  unfold mult_real_fct ; intro ; symmetry ; unfold derive ; rewrite derive_pt_eq.
  eapply derive_pt_eq_1 ; apply derive_pt_scal.
 apply IHn ; assumption.
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
  assert (pr1 : derivable (f * g)%F) by reg.
  apply C_Sn with pr1.
  apply C_ext with (fun x => (derive f pr) x * g x + f x * (derive g pr0) x)%R.
  intro x ; symmetry ; unfold derive ;
  rewrite derive_pt_eq ; eapply derive_pt_eq_1 ;
  apply derive_pt_mult.
  
  apply C_plus_compat ; apply IHn ; [| apply C_pred_compat | apply C_pred_compat |] ; assumption.
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
  apply C_ext with (fun x => (derive f pr) (g x) * (derive g pr0) x)%R.
  intro x ; symmetry ; unfold derive.
  rewrite derive_pt_eq ; eapply derive_pt_eq_1 ; apply derive_pt_comp.

   eapply C_mult_compat.
   fold (comp (derive f pr) g).
   apply IHn ; [| apply C_pred_compat] ; assumption.
   assumption.
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
   apply C_ext with cos.
   intro x ; symmetry ; unfold derive ; reg.
   assumption.

   apply C_Sn with derivable_cos.
   apply C_ext with (-sin)%F.
   intro x ; symmetry ; unfold derive ; reg.
   assumption.
 
   assert (dns : derivable (-sin)) by reg.
   apply C_Sn with dns.
   apply C_ext with (-cos)%F.
   intro x ; symmetry ; unfold derive ; reg.
   assumption.
   
   assert (dnc : derivable (-cos)) by reg.
   apply C_Sn with dnc.
   apply C_ext with sin.
   intro x ; symmetry ; unfold derive ; reg.
   assumption.
Qed.

Lemma C_infty_sin : C_infty sin.
Proof.
 constructor ; intro ; eapply C_cos_sin.
Qed.

Lemma C_infty_cos : C_infty cos.
Proof.
 constructor; intro; eapply C_cos_sin.
Qed.
(*
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
*)




(** nth derivative *)

Fixpoint nth_derive {n : nat} (f : R -> R) (pr : C n f) : R -> R := 
match pr with
   | C_0 f H => f
   | C_Sn f n0 pr H => nth_derive (derive f pr) H
end.



















