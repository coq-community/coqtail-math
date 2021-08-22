(*
(C) Copyright 2010, COQTAIL team

Project Info: http://sourceforge.net/projects/coqtail/

This library is free software; you can redistribute it and/or modify it
under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation; either version 2.1 of the License, or
(at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301,
USA.
*)

Require Import Arith ZArith.
Require Import RelationClasses.
Require Import Type_class_definition.
Require Import Lia.

(*proof that nat = semiring_commutative*)

(* begin hide *)
Ltac int_hierarchy := match goal with
  | |- forall a, ?b => intro; int_hierarchy
  | |- ?a = ?b => rewrite mult_plus_distr_l; int_hierarchy
  | |- ?a = ?b => rewrite mult_plus_distr_r; int_hierarchy
  | |- ?a = ?b => progress auto
  | |- ?a = ?b => lia
  | |- ?a = ?b => progress auto with *
  | |- ?a = ?b => subst; progress trivial
  | |- _ => constructor; int_hierarchy
  | |- _ => intro; int_hierarchy
end.
(* end hide *)

Program Instance monoid_nat : Monoid nat eq plus 0 :=
{monoid_iden_l := plus_0_l}.
Solve All Obligations with int_hierarchy.

Program Instance monoid_commutative_nat : Monoid_Commutative nat eq plus 0 :=
{monoid_comm_monoid := monoid_nat}.
Solve All Obligations with int_hierarchy.

Program Instance monoid_nat_mult_1 : Monoid nat eq mult 1 :=
{monoid_iden_l := mult_1_l }.
Solve All Obligations with int_hierarchy.

Program Instance semiring_nat : SemiRing nat eq plus mult 0 1 :=
{semiring_monoid_comm := monoid_commutative_nat}.
Solve All Obligations with int_hierarchy.

Program Instance semiring_commutative_nat : SemiRing_Commutative nat eq plus mult 0 1 :=
{semiring_comm_semiring := semiring_nat}.
Solve All Obligations with int_hierarchy.

(*proof that Z = ring_commutative*)

Program Instance monoid_Z : Monoid Z eq Zplus 0%Z :=
{monoid_iden_l := Zplus_0_l}.
Solve All Obligations with int_hierarchy.

Program Instance monoid_mult_Z : Monoid Z eq Zmult 1%Z :=
{monoid_iden_l := Zmult_1_l}.
Solve All Obligations with int_hierarchy.

Program Instance group_Z : Group Z eq Zplus 0%Z :=
{group_monoid := monoid_Z}.
Next Obligation.
exists (-x)%Z.
int_hierarchy.
Qed.

Program Instance group_commutative_Z : Group_Commutative Z eq Zplus 0%Z :=
{group_comm_group := group_Z}.
Solve All Obligations with int_hierarchy.

Program Instance ring_Z : Ring Z eq Zplus Zmult 0%Z 1%Z :=
{ring_group_comm := group_commutative_Z}.
Solve All Obligations with int_hierarchy.

Program Instance ring_commutative_Z : Ring_Commutative Z eq Zplus Zmult 0%Z 1%Z :=
{ring_comm_ring := ring_Z}.
Solve All Obligations with int_hierarchy.

Require Import ZArith.
Require Import Znumtheory.

Section Z_nZ.

Hypothesis n : Z.
Definition mod_eq x y := ( n | y - x ).
Notation "x %= y" := (mod_eq x y) (at level 0).

Lemma mod_eq_refl : Reflexive mod_eq.
Proof.
intro.
unfold mod_eq.
ring_simplify.
auto with *.
Qed.

Lemma mod_eq_sym : Symmetric mod_eq.
Proof.
repeat intro.
destruct H as [q H].
exists (-q).
rewrite Zopp_mult_distr_l_reverse.
rewrite <- H.
ring.
Qed.

Lemma mod_eq_trans : Transitive mod_eq.
Proof.
intros q1 q2 q3 Hl Hr. destruct Hl as [q4 Hl], Hr as [q5 Hr]; exists (q4 + q5).
rewrite Zmult_plus_distr_l; rewrite <- Hl; rewrite <- Hr; ring.
Qed.

(* begin hide *)
Hint Resolve
 mod_eq_refl
 mod_eq_sym
 mod_eq_trans
  : modarith.
(* end hide *)

Instance mod_eq_equiv : Equivalence mod_eq.
Proof.
constructor; auto with modarith.
Qed.

Lemma Zmod_plus_0_l : forall x : Z, (0 + x) %= x.
Proof.
intro; unfold mod_eq; ring_simplify; apply Zdivide_0.
Qed.

Lemma Zmod_plus_0_r : forall x : Z, (x + 0) %= x.
Proof.
intros; rewrite Zplus_comm; apply Zmod_plus_0_l.
Qed.

Lemma Zmod_plus_compat_r: forall x y z : Z, x %=y -> (x+z) %= (y+z).
Proof.
intros; unfold mod_eq in H; unfold mod_eq; rewrite Zminus_plus_simpl_r; exact H.
Qed.

Lemma Zmod_plus_compat_l: forall x y z : Z, y %=z -> (x+y) %= (x+z).
Proof.
intros; unfold mod_eq in H; unfold mod_eq; rewrite Zminus_plus_simpl_l; exact H.
Qed.

Instance mod_eq_plus_assoc : Associative mod_eq Zplus.
Proof.
repeat intro; unfold mod_eq; ring_simplify; apply Zdivide_0.
Qed.

Lemma Zmod_mult_1_r : forall x : Z, (x * 1) %= x.
Proof.
intro; ring_simplify; apply mod_eq_refl.
Qed.

Lemma Zmod_mult_1_l : forall x : Z, (1 * x) %= x.
Proof.
intro; rewrite Zmult_comm; apply Zmod_mult_1_r.
Qed.

Lemma Zmod_mult_compat_l : forall x y z : Z, y%=z -> (x*y) %= (x*z).
Proof.
intros x y z [q H]; unfold mod_eq in *.
apply Zdivide_intro with (x*q).
rewrite <- Zmult_minus_distr_l with z y x.
rewrite H.
rewrite Zmult_assoc.
reflexivity.
Qed.

Lemma Zmod_mult_compat_r : forall x y z : Z, x%=y -> (x*z) %= (y*z).
Proof.
intros x y z [q H]; unfold mod_eq in H; unfold mod_eq.
apply Zdivide_intro with (z*q).
rewrite <- Zmult_minus_distr_r with y x z.
rewrite H.
rewrite Zmult_comm.
rewrite Zmult_assoc.
reflexivity.
Qed.


Program Instance monoid_Z_nZ : Monoid Z mod_eq Zplus 0%Z :=
{monoid_iden_l := Zmod_plus_0_l}.
Next Obligation. now apply Zmod_plus_0_r. Qed.
Next Obligation. now apply Zmod_plus_compat_l. Qed.
Next Obligation. now apply Zmod_plus_compat_r. Qed.

Instance mod_eq_mult_assoc : Associative mod_eq Zmult.
Proof.
repeat intro; ring_simplify; apply mod_eq_refl.
Qed.

Program Instance monoid_mult_Z_nZ : Monoid Z mod_eq Zmult 1%Z :=
{monoid_iden_l := Zmod_mult_1_l}.
Next Obligation. now apply Zmod_mult_1_r. Qed.
Next Obligation. now apply Zmod_mult_compat_l. Qed.
Next Obligation. now apply Zmod_mult_compat_r. Qed.

Lemma mod_eq_plus_invert : forall x : Z, sig (fun y => (x + y) %= 0).
Proof.
intros; exists (-x); ring_simplify; apply mod_eq_refl.
Qed.

Program Instance group_Z_nZ : Group Z mod_eq Zplus 0%Z :=
{group_monoid := monoid_Z_nZ}.
Next Obligation.
apply mod_eq_plus_invert.
Qed.

Instance Zmod_plus_comm : Commutative mod_eq Zplus.
Proof.
  exists 0. ring.
Qed.

Instance group_commutative_Z_nZ : Group_Commutative Z mod_eq Zplus 0%Z :=
{group_comm_group := group_Z_nZ}.

Lemma Zmod_mult_plus_distr_r : forall n m p : Z, (n * (m + p)) %= (n * m + n * p).
Proof.
intros; ring_simplify; apply mod_eq_refl.
Qed.

Lemma Zmod_mult_plus_distr_l : forall n m p : Z, ((n + m) * p) %= (n * p + m * p).
Proof.
intros; ring_simplify; apply mod_eq_refl.
Qed.

Program Instance ring_Z_nZ : Ring Z mod_eq Zplus Zmult 0%Z 1%Z :=
{ring_group_comm := group_commutative_Z_nZ}.
Next Obligation. apply Zmod_mult_plus_distr_r. Qed.
Next Obligation. apply Zmod_mult_plus_distr_l. Qed.

Instance Zmod_mult_comm : Commutative mod_eq Zmult.
Proof.
repeat intro; rewrite Zmult_comm; apply mod_eq_refl.
Qed.

Instance ring_commutative_Z_nZ : Ring_Commutative Z mod_eq Zplus Zmult 0%Z 1%Z :=
{ring_comm_ring := ring_Z_nZ}.

End Z_nZ.

Require Import ZArith.
Require Import Znumtheory.
Require Import ConstructiveEpsilon.

Section Fp.

Hypothesis p : Z.
Hypothesis p_prime : prime p.
Definition rel := mod_eq p.
Notation "x %= y" := (rel x y) (at level 0).

Lemma Zmult_iden_l : forall x : Z,  (1 * x) %= x.
Proof.
intros.
ring_simplify; apply mod_eq_refl.
Qed.

Lemma Zmult_iden_r : forall x : Z, (x * 1) %= x.
Proof.
intros.
rewrite Zmult_comm; apply Zmult_iden_l; assumption.
Qed.

Section ConstructiveZ.
  Variable P : Z -> Prop.
  Hypothesis P_decidable : forall x, {P x} + {~ P x}.
  
  Theorem constructive_indefinite_description_Z : ex P -> sig P.
  Proof.
    intros H.
    case (P_decidable 0).
     intro.
     econstructor.
     eauto.
     
     intro nP0.
     pose (fun n => P (Z_of_nat n) \/ P (- Z_of_nat n)) as P'.
     assert (ex P').
      destruct H as [z].
      exists (Z.abs_nat z).
      destruct z; [contradiction | left | right];
       simpl; rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; assumption.
     destruct (constructive_indefinite_description_nat P').
      intro n.
      unfold P'.
      destruct P_decidable with (Z_of_nat n); intuition.
      destruct P_decidable with (- Z_of_nat n); intuition.
      
      assumption.
     
     destruct P_decidable with (Z_of_nat x).
      econstructor; apply p1.
      destruct P_decidable with (- Z_of_nat x).
       econstructor; apply p1.
       subst P'; simpl in *.
       assert False by tauto.
       contradiction.
  Defined.
End ConstructiveZ.


Lemma Zmult_reverse : forall x : Z, ~ x %= 0 -> sig (fun y => (x * y) %= 1).
Proof.
intros.
apply constructive_indefinite_description_Z.
 intro.
 unfold "%=", mod_eq.
 apply Zdivide_dec.
cut (Zis_gcd x p 1).
 intro H0; destruct (Zis_gcd_bezout _ _ _ H0) as [u v H1].
 exists u; exists v.
 rewrite <- H1; ring.
constructor; try apply Zone_divide.
intros.
assert (Z.abs x0<=Z.abs p) by (apply Zdivide_bounds; trivial; destruct p_prime; lia).
replace (Z.abs p) with p in H2 by (destruct p; trivial; destruct p_prime; inversion H3).
assert(exists x1, 0<=x1<=p /\ (x1 | x) /\ (x1 | p) /\ Z.abs x0 = x1).
 destruct x0.
  now destruct H1; ring_simplify in H1; destruct p_prime; clear H; subst; inversion H3.
  exists (Zpos p0); repeat split; auto; apply Zle_0_pos.
  exists (-Zneg p0); repeat split; try rewrite Zopp_neg; auto with *.
clear H0 H1 H2.
destruct H3; destruct H0; destruct H1; destruct H0; destruct H2.
cut (x1 | 1).
 intro; destruct x0; simpl in H4; try (subst; assumption).
 apply Zdivide_opp_l_rev; rewrite Zopp_neg; rewrite H4; assumption.
destruct (dec_Zle x1 1).
 apply Zle_lt_or_eq in H0.
 destruct H0.
  replace x1 with 1 by (apply Zlt_le_succ in H0; simpl in H0; apply Zle_antisym; assumption).
  apply Zone_divide.
  
  rewrite <- H0 in H2; destruct H2; ring_simplify in H2.
  destruct p_prime; rewrite H2 in H6; inversion H6.
 
 apply Znot_le_gt in H5.
 destruct (dec_Zlt x1 p).
  destruct p_prime.
  apply (H8 x1).
   split; lia.
   apply Z.divide_refl.
   assumption.
  
  apply False_ind; apply H.
  ring_simplify.
  apply Zdivide_opp_r.
  replace p with x1 by (apply Zle_antisym; lia).
  assumption.
Qed.

Lemma Zmult_compat_l: forall x y z : Z, (y) %= (z) -> (x * y) %= (x * z).
Proof.
intros.
unfold rel; unfold mod_eq; unfold rel in H; unfold mod_eq in H.
destruct H as [q H].
apply Zdivide_intro with (x*q).
rewrite <- Zmult_minus_distr_l.
rewrite H.
rewrite Zmult_assoc.
reflexivity.
Qed.

Lemma Zmult_compat_r: forall x y z : Z, (x) %= (y) -> (x * z) %= (y * z).
Proof.
intros.
unfold rel; unfold mod_eq; unfold rel in H; unfold mod_eq in H.
destruct H as [q H].
apply Zdivide_intro with (z*q).
rewrite <- Zmult_minus_distr_r.
rewrite H.
rewrite Zmult_comm.
rewrite Zmult_assoc.
reflexivity.
Qed.

Program Instance group_multiplicative_Fp : Group_Multiplicative Z rel Zmult 0 1 :=
{group_setoid := mod_eq_equiv p}.
Next Obligation. now apply Zmult_iden_l. Qed.
Next Obligation. now apply Zmult_iden_r. Qed.
Next Obligation. now apply Zmult_reverse. Qed.
Next Obligation. now apply mod_eq_mult_assoc. Qed.
Next Obligation. now apply Zmult_compat_l. Qed.
Next Obligation. now apply Zmult_compat_r. Qed.

Program Instance field_Fp : Field Z rel Zplus Zmult 0%Z 1%Z :=
{field_group_comm := group_commutative_Z_nZ p}.
Next Obligation. apply Zmod_mult_plus_distr_r. Qed.
Next Obligation. apply Zmod_mult_plus_distr_l. Qed.

Program Instance field_commutative_Fp : Field_Commutative Z rel Zplus Zmult 0%Z 1%Z :=
{field_comm_field := field_Fp}.
Next Obligation. apply Zmod_mult_comm. Qed.

End Fp.
