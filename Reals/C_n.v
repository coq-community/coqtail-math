Require Import Reals.
Require Import Rfunction_facts.

Inductive C : nat -> (R -> R) -> Prop :=
  | C_0 : forall f, continuity f -> C 0 f
  | C_Sn : forall f n (pr : derivable f), { f' : R -> R | (forall x, derive_pt f x (pr x) = (f' x)) /\ C n f' } -> C (S n) f.

Definition C_infty (f : R -> R) : Prop := forall n, C n f.

Lemma zero_C_infty : C_infty (fct_cte 0).
Proof.
 intro n; induction n.
  constructor; reg.
  
  apply C_Sn with (derivable_const 0).
  exists (fct_cte 0).
  split.
   intro; reg.
   apply IHn.
Qed.

Lemma const_C_infty : forall c, C_infty (fct_cte c).
Proof.
 intros c [|n].
  constructor; reg.
  apply C_Sn with (derivable_const c).
  exists (fct_cte 0).
  split.
   intro; reg.
   apply zero_C_infty.
Qed.

Lemma id_C_infty : C_infty id.
Proof.
 intro n ; destruct n.
  constructor ; apply derivable_continuous ; apply derivable_id.
  apply C_Sn with derivable_id.
  exists (fct_cte 1); split.
   intro; reg.
   apply const_C_infty.
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
destruct Hf as [|f n Hdf [f' [Heqf' Hdf']]].
 constructor.
 refine (Rfun_continuity_eq_compat f g _ _); auto.
 
 assert (prg : derivable g).
  eapply derivable_eq_compat; auto.
 refine (C_Sn _ _ prg _).
 exists f'; split.
  intros x.
  rewrite <- Heqf'.
  apply pr_nu_var2.
  auto.
  
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
    intros x.
    pose (fmod := mult_real_fct a (fun x0 : R => (x0 ^ S d)%R)).
    transitivity (derive_pt _ x (derivable_pt_scal _ a x (derivable_pt_pow (S d) _))).
     apply pr_nu.
     
     rewrite derive_pt_scal.
     rewrite Rmult_assoc.
     apply Rmult_eq_compat_l.
     apply derive_pt_pow.
    
    apply IHd.
Qed.
