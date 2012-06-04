Require Import Reals.
Require Import Rfunction_classes.
Require Import Ranalysis_def Ranalysis_def_simpl Rfunction_def Rextensionality.
Require Import Rinterval.
Require Import Nth_derivative_def.

Open Local Scope R_scope.

(** * Simple equivalences *)

(** Simplification lemmas *)

Lemma nth_derive_0: forall (f : R -> R) (pr : D O f),
  nth_derive f pr == f.
Proof.
intros ; reflexivity.
Qed.

Lemma nth_derive_Rball_0: forall c r r_pos f (pr : D_Rball c r r_pos O f),
  nth_derive_Rball c r r_pos f pr == f.
Proof.
intros ; reflexivity.
Qed.

Lemma nth_derive_1 : forall (f : R -> R) (pr : D 1 f) (pr' : derivable f),
  nth_derive f pr == derive f pr'.
Proof.
intros f pr pr' x ; apply derive_ext ; reflexivity.
Qed.

Lemma nth_derive_Rball_1: forall c r r_pos f (pr : D_Rball c r r_pos 1 f) pr',
  nth_derive_Rball c r r_pos f pr == derive_Rball f c r r_pos pr'.
Proof.
intros ; eapply (derive_Rball_ext _ _ _ _ _ _ r_pos) ; reflexivity.
Qed.

(** Extensionality of nth_derive (and equality with nth_derive' as a corrolary). *)

Lemma nth_derive_ext : forall (n : nat) (f g : R -> R)
  (pr1 : D n f) (pr2 : D n g), f == g ->
  nth_derive f pr1 == nth_derive g pr2.
Proof.
intro n ; induction n ; intros ; simpl ;
 [| apply IHn ; apply derive_ext] ; assumption.
Qed.

Lemma nth_derive_Rball_ext : forall c r rp1 rp2 rp3 (n : nat) (f g : R -> R)
  (pr1 : D_Rball c r rp1 n f) (pr2 : D_Rball c r rp2 n g), Rball_eq c r rp3 f g ->
  Rball_eq c r rp3 (nth_derive_Rball c r rp1 f pr1) (nth_derive_Rball c r rp2 g pr2).
Proof.
intros c r rp1 rp2 rp3 n ; induction n ; intros f g pr1 pr2 Heq.
 apply Heq.
 apply IHn ; intros x x_in ; eapply derive_Rball_ext ; eassumption.
Qed.

Lemma nth_derive_Rball_ext_weak: forall c r rp1 rp2 n f g
  (pr1 : D_Rball c r rp1 n f) (pr2 : D_Rball c r rp2 n g), f == g ->
  nth_derive_Rball c r rp1 f pr1 == nth_derive_Rball c r rp2 g pr2.
Proof.
intros c r rp1 rp2 n ; induction n ; intros f g pr1 pr2 Heq.
 apply Heq.
 apply IHn, derive_Rball_ext with (rp3 := rp1), Req_Rball_eq ; assumption.
Qed.

Lemma nth_derive_nth_derive': forall m n f g (pr : D n f)
  (pr' : D m g) (le: (n <= m)%nat), f == g ->
  nth_derive f pr == nth_derive' n g pr' le.
Proof.
intros ; apply nth_derive_ext ; assumption.
Qed.

Lemma nth_derive_Rball_nth_derive_Rball': forall c r rp m n f g
  (pr : D_Rball c r rp n f) (pr' : D_Rball c r rp m g) (le: (n <= m)%nat),
  Rball_eq c r rp f g ->
  Rball_eq c r rp (nth_derive_Rball c r rp f pr) (nth_derive_Rball' c r rp n g pr' le).
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

Lemma nth_derive_Rball_PI: forall c r rp1 rp2 rp3 n f
  (pr1: D_Rball c r rp1 n f) (pr2: D_Rball c r rp2 n f),
  Rball_eq c r rp3 (nth_derive_Rball c r rp1 f pr1) (nth_derive_Rball c r rp2 f pr2).
Proof.
intros ; apply nth_derive_Rball_ext ; reflexivity.
Qed.

Lemma nth_derive'_PI : forall {k m n : nat} (f : R -> R)
 (pr1 : D k f) (pr2 : D m f) (nlek : (n <= k)%nat) (nlem : (n <= m)%nat),
  nth_derive' n f pr1 nlek == nth_derive' n f pr2 nlem.
Proof.
intros ; apply nth_derive'_ext ; reflexivity.
Qed.

Lemma nth_derive_Rball'_PI: forall c r rp1 rp2 rp3 m n f
  (pr1: D_Rball c r rp1 m f) (pr2: D_Rball c r rp2 m f) (le1 le2: (n <= m)%nat),
  Rball_eq c r rp3 (nth_derive_Rball' c r rp1 n f pr1 le1)
  (nth_derive_Rball' c r rp2 n f pr2 le2).
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

Lemma derivable_nth_derive_Rball : forall c r rp n f (pr : derivable_Rball f c r rp)
  (pr1 : D_Rball c r rp (S n) f) (pr2 : D_Rball c r rp n (derive_Rball f c r rp pr)) l x,
  Rball c r rp x ->
  nth_derive_Rball c r rp (derive_Rball f c r rp pr) pr2 x = l ->
  nth_derive_Rball c r rp f pr1 x = l.
Proof.
intros c r rp n f pr pr1 pr2 l x Hl x_in.
 simpl.
  rewrite nth_derive_Rball_ext with (g := derive_Rball f c r rp pr) (pr2 := pr2) (rp3 := rp).
  assumption.


  apply Req_Rball_eq, derive_Rball_ext with (rp3 := rp) ; reflexivity.
  assumption.
Qed.