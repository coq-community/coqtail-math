Require Import Reals.
Require Import Rinterval.
Require Import Lra.

Require Import Rpser_def Rpser_base_facts Rpser_cv_facts.

(** In this library, we define the sum of a power serie with respect to the
3 notions of convergence radius that we used until now.

- weaksum_r sums a power serie on a disk that is smaller than the maximal
convergence disk
- sum_r sums a power serie on its (finite) convergence disk
- sum sums a power serie on its (infinite) convergence disk

In all the cases, the function outputed is proved to be unique and is
exactly the one that equals the sum of the power serie inside the cv disk
and is equal to 0 outside. *)

(** * Definition of weaksum_r *)

Local Open Scope R_scope.

Definition weaksum_r : forall (An : nat -> R) (r : R) (Pr : Cv_radius_weak An r), R -> R.
Proof.
intros An r Rho x.
 case (Rlt_le_dec (Rabs x) r) ; intro x_bd.
 elim (Rpser_abel _ _ Rho _ x_bd) ; intros y Hy ; exact y.
 exact 0.
Defined.

(** Proof that it is really the sum *)

Lemma weaksum_r_sums : forall (An : nat -> R) (r : R) (Pr : Cv_radius_weak An r) (x : R),
      Rabs x < r -> Rpser An x (weaksum_r An r Pr x).
Proof.
intros An r Pr x x_bd.
 unfold weaksum_r ; case (Rlt_le_dec (Rabs x) r) ; intro s.
 destruct (Rpser_abel An r Pr x s) as (l,Hl) ; simpl ; assumption.
 apply False_ind ; lra.
Qed.

(** Proof that the sum is unique *)

Lemma weaksum_r_unique : forall (An : nat -> R) (r : R) (Pr1 Pr2 : Cv_radius_weak An r) (x : R),
     Rabs x < r -> weaksum_r An r Pr1 x = weaksum_r An r Pr2 x.
Proof.
intros An r Pr1 Pr2 x x_bd ;
 assert (T1 := weaksum_r_sums _ _ Pr1 _ x_bd) ;
 assert (T2 := weaksum_r_sums _ _ Pr2 _ x_bd) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma weaksum_r_unique_strong : forall (An : nat -> R) (r1 r2 : R) (Pr1 : Cv_radius_weak An r1)
     (Pr2 : Cv_radius_weak An r2) (x : R), Rabs x < r1 -> Rabs x < r2 ->
     weaksum_r An r1 Pr1 x = weaksum_r An r2 Pr2 x.
Proof.
intros An r1 r2 Pr1 Pr2 x x_bd1 x_bd2.
  assert (T1 := weaksum_r_sums _ _ Pr1 _ x_bd1) ;
  assert (T2 := weaksum_r_sums _ _ Pr2 _ x_bd2) ;
 eapply Rpser_unique ; eassumption.
Qed.

(** * Definition of sum_r *)

Definition sum_r : forall (An : nat -> R) (r : R) (Pr : finite_cv_radius An r), R -> R.
Proof.
intros An r Pr x.
 case (Rlt_le_dec (Rabs x) r) ; intro x_bd.
  assert (rho : Cv_radius_weak An (middle (Rabs x) r)).
  apply Pr; split.
  apply Rle_trans with (Rabs x).
   apply Rabs_pos.
   left ; apply (proj1 (middle_is_in_the_middle _ _ x_bd)).
   apply (proj2 (middle_is_in_the_middle _ _ x_bd)).
 apply (weaksum_r An (middle (Rabs x) r) rho x).
 exact 0.
Defined.

(** Proof that it is really the sum *)

Lemma sum_r_sums : forall  (An : nat -> R) (r : R) (Pr : finite_cv_radius An r),
      forall x, Rabs x < r -> Rpser An x (sum_r An r Pr x).
Proof.
intros An r Pr x x_ub.
 unfold sum_r ; destruct (Rlt_le_dec (Rabs x) r) as [x_bd | x_nbd].
 apply weaksum_r_sums.
 apply (proj1 (middle_is_in_the_middle _ _ x_bd)).
  apply False_ind ; lra.
Qed.

(** Proof that the sum is unique *)

Lemma sum_r_unique : forall (An : nat -> R) (r : R) (Pr1 Pr2 : finite_cv_radius An r) (x : R),
     Rabs x < r -> sum_r An r Pr1 x = sum_r An r Pr2 x.
Proof.
intros An r Pr1 Pr2 x x_bd ;
 assert (T1 := sum_r_sums _ _ Pr1 _ x_bd) ;
 assert (T2 := sum_r_sums _ _ Pr2 _ x_bd) ;
 eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_r_unique_strong : forall (An : nat -> R) (r1 r2 : R) (Pr1 : finite_cv_radius An r1)
     (Pr2 : finite_cv_radius An r2) (x : R), Rabs x < r1 -> Rabs x < r2 ->
     sum_r An r1 Pr1 x = sum_r An r2 Pr2 x.
Proof.
intros An r1 r2 Pr1 Pr2 x x_bd1 x_bd2 ;
 assert (T1 := sum_r_sums _ _ Pr1 _ x_bd1) ;
 assert (T2 := sum_r_sums _ _ Pr2 _ x_bd2) ;
 eapply Rpser_unique ; eassumption.
Qed.

(** * Definition of sum *)

Definition sum : forall (An : nat -> R) (Pr : infinite_cv_radius An), R -> R.
Proof.
intros An Pr r.
 apply (weaksum_r An (Rabs r +1) (Pr (Rabs r + 1)) r).
Defined.

(** Proof that it is really the sum *)

Lemma sum_sums : forall  (An : nat -> R) (Pr : infinite_cv_radius An),
      forall x, Rpser An x (sum An Pr x).
Proof.
intros An Pr x.
 apply weaksum_r_sums ; intuition.
Qed.

(** Proof that the sum is unique *)

Lemma sum_unique : forall (An : nat -> R) (Pr1 Pr2 : infinite_cv_radius An) (x : R),
      sum An Pr1 x = sum An Pr2 x.
Proof.
intros An Pr1 Pr2 x ;
 assert (T1 := sum_sums  _ Pr1 x) ;
 assert (T2 := sum_sums  _ Pr2 x) ;
 eapply Rpser_unique ; eassumption.
Qed.
