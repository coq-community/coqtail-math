Require Import Reals.
Require Import Rfunction_classes.
Require Import Ranalysis_def Ranalysis_def_simpl Rfunction_def Rextensionality.
Require Import Ranalysis_continuity Ranalysis_derivability Ranalysis_monotonicity.
Require Import Rinterval.
Require Import Nth_derivative_def.

Local Open Scope R_scope.

(** * Simple equivalences *)

(** Simplification lemmas *)

Lemma nth_derive_0: forall (f : R -> R) (pr : D O f),
  nth_derive f pr == f.
Proof.
intros ; reflexivity.
Qed.

Lemma nth_derive_Rball_0: forall c r f (pr : D_Rball c r O f),
  nth_derive_Rball c r f pr == f.
Proof.
intros ; reflexivity.
Qed.

Lemma nth_derive_1 : forall (f : R -> R) (pr : D 1 f) (pr' : derivable f),
  nth_derive f pr == derive f pr'.
Proof.
intros f pr pr' x ; apply derive_ext ; reflexivity.
Qed.

Lemma nth_derive_Rball_1: forall c r f (pr : D_Rball c r 1 f) pr',
  nth_derive_Rball c r f pr == derive_Rball c r f pr'.
Proof.
intros ; eapply derive_Rball_ext ; reflexivity.
Qed.

(** Extensionality of nth_derive (and equality with nth_derive' as a corrolary). *)

Lemma nth_derive_ext : forall (n : nat) (f g : R -> R)
  (pr1 : D n f) (pr2 : D n g), f == g ->
  nth_derive f pr1 == nth_derive g pr2.
Proof.
intro n ; induction n ; intros ; simpl ;
 [| apply IHn ; apply derive_ext] ; assumption.
Qed.

Lemma nth_derive_Rball_ext : forall c r (n : nat) (f g : R -> R)
  (pr1 : D_Rball c r n f) (pr2 : D_Rball c r n g), Rball_eq c r f g ->
  Rball_eq c r (nth_derive_Rball c r f pr1) (nth_derive_Rball c r g pr2).
Proof.
intros c r n ; induction n ; intros f g pr1 pr2 Heq.
 apply Heq.
 apply IHn ; intros x x_in ; eapply derive_Rball_ext_strong ; eassumption.
Qed.

Lemma nth_derive_Rball_ext_weak: forall c r n f g
  (pr1 : D_Rball c r n f) (pr2 : D_Rball c r n g), f == g ->
  nth_derive_Rball c r f pr1 == nth_derive_Rball c r g pr2.
Proof.
intros c r n ; induction n ; intros f g pr1 pr2 Heq.
 apply Heq.
 apply IHn, derive_Rball_ext_strong, Req_Rball_eq ; assumption.
Qed.

Lemma nth_derive_nth_derive': forall m n f g (pr : D n f)
  (pr' : D m g) (le: (n <= m)%nat), f == g ->
  nth_derive f pr == nth_derive' n g pr' le.
Proof.
intros ; apply nth_derive_ext ; assumption.
Qed.

Lemma nth_derive_Rball_nth_derive_Rball': forall c r m n f g
  (pr : D_Rball c r n f) (pr' : D_Rball c r m g) (le: (n <= m)%nat),
  Rball_eq c r f g ->
  Rball_eq c r (nth_derive_Rball c r f pr) (nth_derive_Rball' c r n g pr' le).
Proof.
intro_all ; eapply nth_derive_Rball_ext ; eassumption.
Qed.

Lemma nth_derive'_ext : forall (f g : R -> R) (k m n : nat)
  (pr1 : D k f) (pr2 : D m g) (nlek : (n <= k)%nat)
  (nlem : (n <= m)%nat), f == g ->
  nth_derive' n f pr1 nlek == nth_derive' n g pr2 nlem.
Proof.
intros ; apply nth_derive_ext ; assumption.
Qed.

(** * nth_derive is not proof-sensible. *)

Lemma nth_derive_PI : forall (n : nat) (f : R -> R) (pr1 pr2 : D n f),
  nth_derive f pr1 == nth_derive f pr2.
Proof.
intros ; apply nth_derive_ext ; reflexivity.
Qed.

Lemma nth_derive_Rball_PI: forall c r n f
  (pr1: D_Rball c r n f) (pr2: D_Rball c r n f),
  Rball_eq c r (nth_derive_Rball c r f pr1) (nth_derive_Rball c r f pr2).
Proof.
intros ; apply nth_derive_Rball_ext ; reflexivity.
Qed.

Lemma nth_derive'_PI : forall {k m n : nat} (f : R -> R)
 (pr1 : D k f) (pr2 : D m f) (nlek : (n <= k)%nat) (nlem : (n <= m)%nat),
  nth_derive' n f pr1 nlek == nth_derive' n f pr2 nlem.
Proof.
intros ; apply nth_derive'_ext ; reflexivity.
Qed.

Lemma nth_derive_Rball'_PI: forall c r m n f
  (pr1: D_Rball c r m f) (pr2: D_Rball c r m f) (le1 le2: (n <= m)%nat),
  Rball_eq c r (nth_derive_Rball' c r n f pr1 le1)
  (nth_derive_Rball' c r n f pr2 le2).
Proof.
intros ; apply nth_derive_Rball_ext ; reflexivity.
Qed.

(** * Relation between nth_derive and derive. *)

Lemma derivable_nth_derive : forall n f (pr : derivable f) (pr1 : D (S n) f)
 (pr2 : D n (derive f pr)) l x, nth_derive (derive f pr) pr2 x = l ->
 nth_derive f pr1 x = l.
Proof.
intros n f pr pr1 pr2 l x Hl.
 simpl.
  rewrite nth_derive_ext with (g := derive f pr) (pr2 := pr2).
  assumption.
  intro ; unfold derive ; apply pr_nu_var ; reflexivity.
Qed.

Lemma derivable_nth_derive_Rball : forall c r n f (pr : derivable_Rball c r f)
  (pr1 : D_Rball c r (S n) f) (pr2 : D_Rball c r n (derive_Rball c r f pr)) l x,
  Rball c r x ->
  nth_derive_Rball c r (derive_Rball c r f pr) pr2 x = l ->
  nth_derive_Rball c r f pr1 x = l.
Proof.
intros c r n f pr pr1 pr2 l x Hl x_in.
 simpl.
  rewrite nth_derive_Rball_ext with (g := derive_Rball c r f pr) (pr2 := pr2).
  assumption.
  apply Req_Rball_eq, derive_Rball_ext_strong ; reflexivity.
  assumption.
Qed.