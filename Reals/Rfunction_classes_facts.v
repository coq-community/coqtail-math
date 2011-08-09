Require Import Rbase Ranalysis.
Require Import Rfunction_facts Rextensionality.
Require Import Rinterval Ranalysis_def.
Require Import Rfunction_classes_def.

Local Open Scope R_scope.

(** * Extensionality of the properties. *)

Lemma D_ext: forall n f g, f == g -> D n f -> D n g.
Proof.
intro n ; induction n ; intros f g f_eq_g Dnf.
 constructor.
 inversion_clear Dnf.
 assert (g_deriv : derivable g) by (eapply derivable_ext ; eassumption).
 apply (D_S _ _ g_deriv).
 apply IHn with (derive _ pr).
 intro x ; unfold derive ; rewrite (pr_nu_var2 _ _ _ (pr x) (g_deriv x) f_eq_g) ;
 reflexivity.
 assumption.
Qed.

Lemma C_ext : forall n f g, f == g -> C n f -> C n g.
Proof.
intro n ; induction n ; intros f g f_eq_g Cnf.
 inversion Cnf ; constructor ; eapply continuity_ext ; eassumption.
 inversion_clear Cnf.
 assert (g_deriv : derivable g) by (eapply derivable_ext ; eassumption).
 apply (C_S _ _ g_deriv).
 apply IHn with (derive _ pr).
 intro x ; unfold derive ; rewrite (pr_nu_var2 _ _ _ (pr x) (g_deriv x) f_eq_g) ;
 reflexivity.
 assumption.
Qed.

(** * Relations between the D and the C class. *)

(** For the full classes. *)

Lemma C_implies_D : forall n f, C n f -> D n f.
Proof.
intro n ; induction n ; intros f H.
 constructor.
 inversion H ; apply D_S with pr ; apply IHn ; assumption.
Qed.

Lemma D_S_implies_C : forall n f, D (S n) f -> C n f.
Proof.
intro n ; induction n ; intros f H ; inversion H.
 constructor ; apply derivable_continuous ; assumption.
 apply C_S with pr ; apply IHn ; assumption.
Qed.

Lemma C_infty_implies_D_infty : forall f, C_infty f -> D_infty f.
Proof.
intros f H n ; apply C_implies_D ; trivial.
Qed.

Lemma D_infty_implies_C_infty : forall f, D_infty f -> C_infty f.
Proof.
intros f H n ; apply D_S_implies_C ; trivial.
Qed.

(** Corresponding lemmas for the restrictions. *)

Lemma C_Rball_implies_D_Rball : forall n f c r r_pos,
  C_Rball c r r_pos n f -> D_Rball c r r_pos n f.
Proof.
intro n ; induction n ; intros f c r r_pos H.
 constructor.
 inversion H ; eapply Db_S with pr ; apply IHn ; assumption.
Qed.

Lemma C_Rball_infty_implies_D_Rball_infty : forall c r r_pos f,
  C_Rball_infty c r r_pos f -> D_Rball_infty c r r_pos f.
Proof.
intros ; intro ; apply C_Rball_implies_D_Rball ; trivial.
Qed.

(** Links between the full classes and the restrictions. *)

(*
Lemma C_C_Rball: forall c r r_pos n f,
  C n f -> C_Rball c r r_pos n f.
Proof.
intros c r r_pos n ; induction n ; intros f Cnf ; inversion_clear Cnf.
 constructor ; apply continuity_continuity_Rball ; assumption.
 apply Cb_S with (derivable_derivable_Rball c r r_pos f pr).

Need for C_Rball_ext HERE

 apply IHn.
*)

(** * Basic Properties *)

Lemma D_pred : forall n f, D (S n) f -> D n f.
Proof.
intros ; apply C_implies_D, D_S_implies_C ; assumption.
Qed.

Lemma C_pred : forall n f, C (S n) f -> C n f.
Proof.
 intros ; apply D_S_implies_C, C_implies_D ; assumption.
Qed.

Lemma D_le: forall m n f, (n <= m)%nat -> D m f -> D n f.
Proof.
intro m ; induction m ; intros n f Hnm Dmf.
 destruct n ; [apply Dmf | elim (le_Sn_O _ Hnm)].
 destruct (eq_nat_dec n (S m)) as [Heq | Hneq].
  subst ; assumption.
  apply IHm ; [| apply D_pred] ; intuition.
Qed.

Lemma C_le : forall m n f, (n <= m)%nat -> C m f -> C n f.
Proof.
intro m ; induction m ; intros n f H Cmf.
 destruct n ; [apply Cmf | elim (le_Sn_O _ H)].
 destruct (eq_nat_dec n (S m)) as [Heq | Hneq].
  subst ; assumption.
  apply IHm ; [| apply C_pred] ; intuition.
Qed.

(** * Compatibility of C, D with common operators *)

Lemma D_opp: forall n f, D n f -> D n (- f)%F.
Proof.
intro n ; induction n ; intros f Dnf.
 inversion_clear Dnf ; constructor ; reg.
 inversion_clear Dnf ; pose (pr2 := derivable_opp _ pr) ;
 apply D_S with pr2 ; apply D_ext with (- derive f pr)%F.
  intro x ; symmetry ; unfold derive ; rewrite derive_pt_eq ;
  apply derivable_pt_lim_opp; destruct (pr x) as [? Hd]; apply Hd.
  apply IHn ; assumption.
Qed.

Lemma C_opp: forall n f, C n f -> C n (- f)%F.
Proof.
intro n ; induction n ; intros f Cnf.
 inversion_clear Cnf ; constructor ; reg.
 inversion_clear Cnf ; pose (pr2 := derivable_opp _ pr) ;
 apply C_S with pr2 ; apply C_ext with (- derive f pr)%F.
  intro x ; symmetry ; unfold derive ; rewrite derive_pt_eq ;
  apply derivable_pt_lim_opp; destruct (pr x) as [? Hd]; apply Hd.
  apply IHn ; assumption.
Qed.

Lemma D_plus: forall n f g,
  D n f -> D n g -> D n (f + g)%F.
Proof.
intro n ; induction n ; intros f g Dnf Dng ;
 inversion_clear Dnf ; inversion_clear Dng.

 constructor.
 
 apply D_S with (derivable_plus _ _ pr pr0) ;
 apply D_ext with (plus_fct (derive f pr) (derive g pr0)).
 intro x ; symmetry ; transitivity (derive f pr x + derive g pr0 x).
 unfold derive ; rewrite derive_pt_eq ;
 apply derivable_pt_lim_plus ; eapply derive_pt_eq_1 ;
 reflexivity.
 auto.
 apply IHn ; assumption.
Qed.

Lemma C_plus : forall n f g,
  C n f -> C n g -> C n (f + g)%F.
Proof.
intro n ; induction n ; intros f g Cnf Cng ;
 inversion_clear Cnf ; inversion_clear Cng.

 constructor ; reg.
 
 apply C_S with (derivable_plus _ _ pr pr0) ;
 apply C_ext with (plus_fct (derive f pr) (derive g pr0)).
 intro x ; symmetry ; transitivity (derive f pr x + derive g pr0 x).
 unfold derive ; rewrite derive_pt_eq ;
 apply derivable_pt_lim_plus ; eapply derive_pt_eq_1 ;
 reflexivity.
 auto.
 apply IHn ; assumption.
Qed.

Lemma D_minus: forall n f g,
  D n f -> D n g -> D n (f - g)%F.
Proof.
intros ; unfold minus_fct, Rminus ; apply D_plus ;
 [| apply D_opp] ; assumption.
Qed.

Lemma C_minus : forall n f g,
  C n f -> C n g -> C n (f - g)%F.
Proof.
intros ; unfold minus_fct, Rminus ; apply C_plus ;
 [| apply C_opp] ; assumption.
Qed.

Lemma D_scal : forall n f a,
  D n f -> D n (mult_real_fct a f).
Proof.
intro n ; induction n ; intros f a Dnf ; inversion_clear Dnf.
 constructor.

 apply D_S with (derivable_scal _ _ pr) ;
 apply D_ext with  (mult_real_fct a (derive f pr)).
  unfold mult_real_fct ; intro x ; symmetry ; unfold derive ;
  rewrite derive_pt_eq ; apply derivable_pt_lim_scal ;
  eapply derive_pt_eq_1 ; auto.
 apply IHn ; assumption.
Qed.

Lemma C_scal : forall n f a,
  C n f -> C n (mult_real_fct a f).
Proof.
intro n ; induction n ; intros f a Cnf ; inversion_clear Cnf.
 constructor ; reg.

 apply C_S with (derivable_scal _ _ pr) ;
 apply C_ext with  (mult_real_fct a (derive f pr)).
  unfold mult_real_fct ; intro x ; symmetry ; unfold derive ;
  rewrite derive_pt_eq ; apply derivable_pt_lim_scal ;
  eapply derive_pt_eq_1 ; auto.
 apply IHn ; assumption.
Qed.

Lemma D_mult : forall n f g,
  D n f -> D n g -> D n (f * g)%F.
Proof.
intro n ; induction n ; intros f g Dnf Dng ;
 inversion Dnf ; inversion Dng ; subst.
  constructor.

  assert (pr1 : derivable (f * g)%F) by reg ;
  apply D_S with pr1 ;
  apply D_ext with (fun x => (derive f pr) x * g x + f x * (derive g pr0) x)%R.
  intro x ; symmetry ; unfold derive ;
  rewrite derive_pt_eq ; eapply derive_pt_eq_1 ;
  apply derive_pt_mult.
  
  apply D_plus ; apply IHn ; [| apply D_pred | apply D_pred |] ;
  assumption.
Qed.

Lemma C_mult : forall n f g,
  C n f -> C n g -> C n (f * g)%F.
Proof.
intro n ; induction n ; intros f g Cnf Cng ;
 inversion Cnf ; inversion Cng ; subst.
  constructor ; reg.

  assert (pr1 : derivable (f * g)%F) by reg ;
  apply C_S with pr1 ;
  apply C_ext with (fun x => (derive f pr) x * g x + f x * (derive g pr0) x)%R.
  intro x ; symmetry ; unfold derive ;
  rewrite derive_pt_eq ; eapply derive_pt_eq_1 ;
  apply derive_pt_mult.
  
  apply C_plus ; apply IHn ; [| apply C_pred | apply C_pred |] ;
  assumption.
Qed.

Lemma D_comp : forall n f g,
  D n f -> D n g -> D n (comp f g).
Proof.
 intro n ; induction n ; intros f g Dnf Dng ;
 inversion Dnf ; inversion Dng ; subst.
  constructor.
  
  apply D_S with (derivable_comp _ _ pr0 pr) ;
  apply D_ext with (fun x => (derive f pr) (g x) * (derive g pr0) x)%R.
  intro x ; symmetry ; unfold derive ; rewrite derive_pt_eq ;
  eapply derive_pt_eq_1 ; apply derive_pt_comp.

   eapply D_mult.
   fold (comp (derive f pr) g).
   apply IHn ; [| apply D_pred] ; assumption.
   assumption.
Qed.

Lemma C_comp : forall n f g,
  C n f -> C n g -> C n (comp f g).
Proof.
 intro n ; induction n ; intros f g Cnf Cng ;
 inversion Cnf ; inversion Cng ; subst.
  constructor ; reg.
  
  apply C_S with (derivable_comp _ _ pr0 pr) ;
  apply C_ext with (fun x => (derive f pr) (g x) * (derive g pr0) x)%R.
  intro x ; symmetry ; unfold derive ; rewrite derive_pt_eq ;
  eapply derive_pt_eq_1 ; apply derive_pt_comp.

   eapply C_mult.
   fold (comp (derive f pr) g).
   apply IHn ; [| apply C_pred] ; assumption.
   assumption.
Qed.

Hint Resolve D_opp : CD_hint.
Hint Resolve C_opp : CD_hint.
Hint Resolve D_plus : CD_hint.
Hint Resolve C_plus : CD_hint.
Hint Resolve D_minus : CD_hint.
Hint Resolve C_minus : CD_hint.
Hint Resolve D_scal : CD_hint.
Hint Resolve C_scal : CD_hint.
Hint Resolve D_mult : CD_hint.
Hint Resolve C_mult : CD_hint.
Hint Resolve D_comp : CD_hint.
Hint Resolve C_comp : CD_hint.

(** * Compatibility with derivation *)

Lemma D_derive: forall n f (pr : derivable f),
  D (S n) f -> D n (derive f pr).
Proof.
intros n f pr Dnf ; inversion_clear Dnf ; eapply D_ext ;
 [| eassumption] ; intro ; eapply pr_nu.
Qed.

Lemma C_derive : forall n f (pr : derivable f),
  C (S n) f -> C n (derive f pr).
Proof.
intros n f pr Cnf ; inversion_clear Cnf ; eapply C_ext ;
 [| eassumption] ; intro ; eapply pr_nu.
Qed.

(** Compatibility of C_infty, D_infty with common operators *)

Lemma D_infty_opp : forall f, D_infty f -> D_infty (- f)%F.
Proof.
intros f Df n ; apply D_opp ; trivial.
Qed.

Lemma C_infty_opp : forall f, C_infty f -> C_infty (- f)%F.
Proof.
intros f Cf n ; apply C_opp ; trivial.
Qed.

Lemma D_infty_plus : forall f g,
  D_infty f -> D_infty g -> D_infty (f + g)%F.
Proof.
 intros f g Df Dg n ; apply D_plus ; trivial.
Qed.

Lemma C_infty_plus : forall f g,
  C_infty f -> C_infty g -> C_infty (plus_fct f g).
Proof.
 intros f g Cf Cg n ; apply C_plus ; trivial.
Qed.

Lemma D_infty_minus : forall f g,
  D_infty f -> D_infty g -> D_infty (f - g)%F.
Proof.
 intros f g Df Dg n ; apply D_minus ; trivial.
Qed.

Lemma C_infty_minus : forall f g,
  C_infty f -> C_infty g -> C_infty (minus_fct f g).
Proof.
 intros f g Cf Cg n ; apply C_minus ; trivial.
Qed.

Lemma D_infty_scal : forall f a,
  D_infty f -> D_infty (mult_real_fct a f).
Proof.
 intros f a Df n ; apply D_scal ; trivial.
Qed.

Lemma C_infty_scal : forall f a,
  C_infty f -> C_infty (mult_real_fct a f).
Proof.
 intros f a Cf n ; apply C_scal ; trivial.
Qed.

Lemma D_infty_mult : forall f g,
  D_infty f -> D_infty g -> D_infty (f * g)%F.
Proof.
 intros f g Df Dg n ; apply D_mult ; trivial.
Qed.

Lemma C_infty_mult : forall f g,
  C_infty f -> C_infty g -> C_infty (mult_fct f g).
Proof.
 intros f g Cf Cg n ; apply C_mult ; trivial.
Qed.

Lemma D_infty_comp : forall f g,
  D_infty f -> D_infty g -> D_infty (comp f g).
Proof.
 intros f g Df Dg n ; apply D_comp ; trivial.
Qed.

Lemma C_infty_comp : forall f g,
  C_infty f -> C_infty g -> C_infty (comp f g).
Proof.
 intros f g Cf Cg n ; apply C_comp ; trivial.
Qed.
