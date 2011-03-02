Require Import Reals.
Require Import Rfunction_facts.
Require Import Rextensionality.
Require Import C_n_def.

Local Open Scope R_scope.

(** * Basic Properties *)

Lemma C_pred : forall n f,
  C (S n) f -> C n f.
Proof.
 induction n ; intros f Cnf.
  constructor ; inversion Cnf ; reg.
  inversion_clear Cnf ; apply C_Sn with pr ;
  apply IHn ; assumption.
Qed.

Lemma C_le : forall m n f, (n <= m)%nat ->
  C m f -> C n f.
Proof.
intro m ; induction m ; intros n f H Cmf.
 destruct n ; [apply Cmf | apply False_rec ; inversion H].
 destruct (eq_nat_dec n (S m)) as [Heq | Hneq].
  subst ; assumption.
  apply IHm ; [omega | apply C_pred ; assumption].
Qed.

Lemma C_ext : forall n f g, f == g -> C n f -> C n g.
Proof.
intro n ; induction n ; intros f g f_eq_g Cnf.
 inversion Cnf ; constructor ; eapply continuity_ext ; eassumption.
 inversion_clear Cnf.
 assert (g_deriv : derivable g) by (eapply derivable_ext ; eassumption).
 apply (C_Sn _ _ g_deriv).
 apply IHn with (derive _ pr).
 intro x ; unfold derive ; rewrite (pr_nu_var2 _ _ _ (pr x) (g_deriv x) f_eq_g) ;
 reflexivity.
 assumption.
Qed.

(** * Compatibility with common operators *)

Lemma C_opp :  forall n f,
  C n f -> C n (- f)%F.
Proof.
intro n ; induction n ; intros f Cnf.
 inversion_clear Cnf ; constructor ; reg.
 inversion_clear Cnf ; pose (pr2 := derivable_opp _ pr) ;
 apply C_Sn with pr2 ; apply C_ext with (- derive f pr)%F.
  intro x ; symmetry ; unfold derive ; rewrite derive_pt_eq ;
  apply derivable_pt_lim_opp; destruct (pr x) as [? Hd]; apply Hd.
  apply IHn ; assumption.
Qed.

Lemma C_infty_opp : forall f,
 C_infty f -> C_infty (- f)%F.
Proof.
intros f Cf n ; apply C_opp ;
 apply Cf.
Qed.

Lemma C_plus : forall n f g,
  C n f -> C n g -> C n (plus_fct f g).
Proof.
intro n ; induction n ; intros f g Cnf Cng ;
 inversion_clear Cnf ; inversion_clear Cng.

 constructor ; reg.
 
 apply C_Sn with (derivable_plus _ _ pr pr0) ;
 apply C_ext with (plus_fct (derive f pr) (derive g pr0)).
 intro x ; symmetry ; transitivity (derive f pr x + derive g pr0 x).
 unfold derive ; rewrite derive_pt_eq ;
 apply derivable_pt_lim_plus ; eapply derive_pt_eq_1 ;
 reflexivity.
 auto.
 apply IHn ; assumption.
Qed.

Lemma C_infty_plus : forall f g,
  C_infty f -> C_infty g -> C_infty (plus_fct f g).
Proof.
 intros f g Cf Cg n ; apply C_plus ;
 [ apply Cf | apply Cg].
Qed.

Lemma C_minus : forall n f g,
  C n f -> C n g -> C n (minus_fct f g).
Proof.
intros n f g Cnf Cng ; unfold minus_fct ; unfold Rminus ;
 apply C_plus ; [| apply C_opp] ; assumption.
Qed.

Lemma C_infty_minus : forall f g,
  C_infty f -> C_infty g -> C_infty (minus_fct f g).
Proof.
 intros f g Cf Cg n ; apply C_minus ;
 [ apply Cf | apply Cg].
Qed.

Lemma C_scal : forall n f a,
  C n f -> C n (mult_real_fct a f).
Proof.
intro n ; induction n ; intros f a Cnf ; inversion_clear Cnf.
 constructor ; reg.

 apply C_Sn with (derivable_scal _ _ pr) ;
 apply C_ext with  (mult_real_fct a (derive f pr)).
  unfold mult_real_fct ; intro x ; symmetry ; unfold derive ;
  rewrite derive_pt_eq ; apply derivable_pt_lim_scal ;
  eapply derive_pt_eq_1 ; auto.
 apply IHn ; assumption.
Qed.

Lemma C_infty_scal : forall f a,
  C_infty f -> C_infty (mult_real_fct a f).
Proof.
 intros f a Cf n ; apply C_scal ;
 apply Cf.
Qed.

Lemma C_mult : forall n f g,
  C n f -> C n g -> C n (mult_fct f g).
Proof.
intro n ; induction n ; intros f g Cnf Cng ;
 inversion Cnf ; inversion Cng ; subst.
  constructor ; reg.

  assert (pr1 : derivable (f * g)%F) by reg ;
  apply C_Sn with pr1 ;
  apply C_ext with (fun x => (derive f pr) x * g x + f x * (derive g pr0) x)%R.
  intro x ; symmetry ; unfold derive ;
  rewrite derive_pt_eq ; eapply derive_pt_eq_1 ;
  apply derive_pt_mult.
  
  apply C_plus ; apply IHn ; [| apply C_pred | apply C_pred |] ;
  assumption.
Qed.

Lemma C_infty_mult : forall f g,
  C_infty f -> C_infty g -> C_infty (mult_fct f g).
Proof.
 intros f g Cf Cg n ; apply C_mult ;
 [apply Cf | apply Cg].
Qed.

Lemma C_comp : forall n f g,
  C n f -> C n g -> C n (comp f g).
Proof.
 intro n ; induction n ; intros f g Cnf Cng ;
 inversion Cnf ; inversion Cng ; subst.
  constructor ; reg.
  
  apply C_Sn with (derivable_comp _ _ pr0 pr) ;
  apply C_ext with (fun x => (derive f pr) (g x) * (derive g pr0) x)%R.
  intro x ; symmetry ; unfold derive ; rewrite derive_pt_eq ;
  eapply derive_pt_eq_1 ; apply derive_pt_comp.

   eapply C_mult.
   fold (comp (derive f pr) g).
   apply IHn ; [| apply C_pred] ; assumption.
   assumption.
Qed.

Lemma C_infty_comp : forall f g,
  C_infty f -> C_infty g -> C_infty (comp f g).
Proof.
 intros f g Cf Cg n ; apply C_comp ;
 [apply Cf | apply Cg].
Qed.

Hint Resolve C_opp : C_hint.
Hint Resolve C_plus : C_hint.
Hint Resolve C_minus : C_hint.
Hint Resolve C_scal : C_hint.
Hint Resolve C_mult : C_hint.
Hint Resolve C_comp : C_hint.

(** * Compatibility with derivation *)

Lemma C_derive : forall n f (pr : derivable f),
  C (S n) f -> C n (derive f pr).
Proof.
intros n f pr Cnf ; inversion Cnf ;
 eapply C_ext ; [| eassumption] ;
 intro x ; eapply pr_nu ; reflexivity.
Qed.

(** * Definition of the nth derivative *)

Program Fixpoint nth_derive {n : nat} (f : R -> R) (pr : C n f) : R -> R := match n with
   | O   => f
   | S n' => @nth_derive n' (derive f _) _
end.
Next Obligation.
inversion pr ; assumption.
Qed.
Next Obligation.
apply C_derive ; assumption.
Qed.

Definition nth_derive' {m : nat} (n : nat) (f : R -> R) (pr : C m f)
          (nlem : (n <= m)%nat) : R -> R.
Proof.
intros ; eapply nth_derive ;
 [eapply C_le |] ; eassumption.
Defined.

Lemma nth_derive_ext : forall {n : nat} (f g : R -> R) (pr1 : C n f) (pr2 : C n g),
  f == g ->
  nth_derive f pr1 == nth_derive g pr2.
Proof.
intro n ; induction n ; intros.
 intro x ; auto.
 simpl ; apply IHn ; apply derive_ext ; assumption.
Qed.

Lemma nth_derive_PI : forall {n : nat} (f : R -> R) (pr1 pr2 : C n f),
  nth_derive f pr1 == nth_derive f pr2.
Proof.
intros ; apply nth_derive_ext ; intro x ; reflexivity.
Qed.

Lemma nth_derive'_ext : forall {k m n : nat} (f g : R -> R)
 (pr1 : C k f) (pr2 : C m g) (nlek : (n <= k)%nat) (nlem : (n <= m)%nat),
  f == g ->
  nth_derive' n f pr1 nlek == nth_derive' n g pr2 nlem.
Proof.
intros ; unfold nth_derive' ; intro x ; apply nth_derive_ext ;
 assumption.
Qed.

Lemma nth_derive'_PI : forall {k m n : nat} (f : R -> R)
 (pr1 : C k f) (pr2 : C m f) (nlek : (n <= k)%nat) (nlem : (n <= m)%nat),
  nth_derive' n f pr1 nlek == nth_derive' n f pr2 nlem.
Proof.
intros ; apply nth_derive'_ext ; intro x ; reflexivity.
Qed.