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

Require Import Type_class_definition.
Require Import Type_class_instance.
Require Import Coq.Relations.Relation_Definitions.
Require Import Lia.
Require Import Arith.
Require Import Nbinomial.
Require Import Setoid.

Definition iter_l (A : Type) (op : operation A) (neutral : A) (x : A) :=
fix s n := match n with 
  | O => neutral
  | S n' => op x (s n')
end.

Definition iter_r (A : Type) (op : operation A) (neutral : A) (x : A) :=
fix s n := match n with 
  | O => neutral
  | S n' => op (s n') x
end.

Definition iter1 (A : Type) (op : operation A) (f : nat -> A) :=
fix s n := match n with 
  | O => f O
  | S n' => op (f n) (s n')
end.

Section Commutative_Ring.
  Variable X : Type.
  Variable eqr : relation X.
  Variable add mul : operation X.
  Variable zero one : X.
  Variable CR : Ring_Commutative X eqr add mul zero one.
  
  Definition CRpow : X -> nat -> X := iter_r X mul one.
  Definition CRsum : (nat -> X) -> nat -> X  := iter1 X add.
  Definition CRnatmul : nat -> X -> X := fun n x => iter_l X add zero x n.
  
  Notation " a ^^ b " := (CRpow a b) (at level 30, right associativity).
  Notation " a * b " := (mul a b).
  Notation " a == b " := (eqr a b) (at level 90, no associativity).
  Notation " a + b " := (add a b).
  Notation " a ** b " := (CRnatmul a b) (at level 60).
  
  Definition newton_sum n a b : X :=
    CRsum (fun k => (Nbinomial n k) ** (a ^^ k) * (b ^^ (n - k))) n.
  
  Definition opp : X -> X.
  Proof.
    intros x.
    destruct (group_reverse x) as [y ?].
    exact y.
  Defined.
  
  Definition sub : X -> X -> X := fun a b => add a (opp b).
  
  Add Setoid X eqr monoid_setoid as setoid_X.
  
  Add Morphism add with signature eqr ==> eqr ==> eqr as add_wd.
  intros.
  transitivity (x + y0).
   apply monoid_eq_compat_l; assumption.
   apply monoid_eq_compat_r; assumption.
  Qed.
  
  Add Morphism mul with signature eqr ==> eqr ==> eqr as mul_wd.
  intros.
  transitivity (x * y0).
   apply monoid_eq_compat_l; assumption.
   apply monoid_eq_compat_r; assumption.
  Qed.
  
  Add Morphism opp with signature eqr ==> eqr as opp_wd.
  Proof.
  intros.
  unfold opp.
  destruct (group_reverse x) as [x' ?].
  destruct (group_reverse y) as [y' ?].
  transitivity (zero + y'); [ | apply monoid_iden_l].
  transitivity (x' + x + y'); [ | apply monoid_eq_compat_r; rewrite op_comm; assumption].
  transitivity (x' + y + y'); [ | apply monoid_eq_compat_r; apply monoid_eq_compat_l; symmetry; assumption].
  transitivity (zero + x').
   symmetry; apply monoid_iden_l.
   transitivity (x' + x + x').
    apply monoid_eq_compat_r; symmetry; transitivity (x + x'); auto; apply op_comm.
    transitivity (x' + (y + y')).
     transitivity (x' + (x + x')).
      symmetry; apply op_assoc.
      apply monoid_eq_compat_l; transitivity zero; auto with relations.
     apply op_assoc.
  Qed.
  
  Lemma Xring : @ring_theory X zero one add mul sub opp eqr.
  Proof.
    split; intros.
     apply monoid_iden_l.
     apply op_comm.
     apply op_assoc.
     apply monoid_iden_l.
     apply op_comm.
     apply op_assoc.
     apply ring_distributive_l.
     reflexivity.
     
     unfold opp.
     destruct (group_reverse x) as [y ?].
     assumption.
  Qed.
  
  Add Ring X : Xring.
  
  Lemma CRsum_simpl f n : CRsum f (S n) = f (S n) + CRsum f n.
  Proof.
  reflexivity.
  Qed.
  
  Lemma CRsum_simpl_r f n : CRsum f (S n) == CRsum f n + f (S n).
  Proof.
  intros; simpl; ring.
  Qed.
  
  Lemma CRsum_reindex : forall n f, f O + CRsum (fun k => f (S k)) n == CRsum f (S n).
  Proof.
  intros n f.
  induction n.
   simpl; ring.
   
   do 2 rewrite CRsum_simpl.
   rewrite <- IHn.
   ring.
  Qed.
  
  Lemma CRsum_eq_compat_weak : forall a b n, (forall n, a n == b n) -> CRsum a n == CRsum b n.
  Proof.
  intros a b n H.
  induction n.
   simpl; apply H.
   
   simpl.
   rewrite IHn.
   rewrite H.
   reflexivity.
  Qed.
  
  Lemma CRsum_eq_compat : forall a b n, (forall i, i <= n -> a i == b i) -> CRsum a n == CRsum b n.
  Proof.
  intros a b n H.
  induction n.
   simpl; apply H.
   constructor.
   
   simpl.
   rewrite IHn.
    rewrite H.
     reflexivity.
     constructor.
    intros; apply H; auto.
  Qed.
  
  Lemma CRsum_add_compat : forall a b n, CRsum (fun i => a i + b i) n == CRsum a n + CRsum b n.
  Proof.
  intros a b n.
  induction n.
   simpl; reflexivity.
   
   simpl.
   rewrite IHn.
   ring.
  Qed.
  
  Lemma CRsum_scal_compat : forall x f n, x * CRsum f n == CRsum (fun n => x * f n) n.
  Proof.
  intros a b n.
  induction n.
   simpl; reflexivity.
   
   simpl.
   ring_simplify.
   rewrite IHn.
   reflexivity.
  Qed.
  
  Lemma CRpow_simpl : forall a n, a ^^ (S n) = a ^^ n * a.
  Proof.
  reflexivity.
  Qed.
  
  Lemma CRadd_eq_compat : forall a b c d, a == c -> b == d -> a + b == c + d.
  Proof.
  intros ? ? ? ? H H'.
  rewrite H; rewrite H'.
  ring.
  Qed.
  
  Lemma CRmul_scal_compat : forall a b n, n ** a * b == a * (n ** b).
  Proof.
  intros a b n.
  induction n.
   simpl; ring.
   
   simpl.
   rewrite IHn.
   ring.
  Qed.
  
  Lemma CRscal_eq_compat : forall a b n, a == b -> n ** a == n ** b.
  Proof.
  intros a b n H.
  induction n.
   simpl; ring.
   
   simpl.
   rewrite IHn.
   rewrite H.
   ring.
  Qed.
  
  Lemma CRscal_mult_scal_one : forall a n, (n ** one) * a == n ** a.
  Proof.
  intros a n.
  induction n.
   simpl; ring.
   
   simpl.
   rewrite <- IHn.
   ring.
  Qed.
  
  Lemma CRscal_add_eq_compat : forall a b n, (n ** a) + (n ** b) == n ** (a + b).
  Proof.
  intros a b n.
  induction n.
   simpl; ring.
   
   simpl.
   rewrite <- IHn.
   ring.
  Qed.
  
  Lemma CRadd_scal_eq_compat : forall a n p, (n ** a) + (p ** a) == (n + p) ** a.
  Proof.
  intros a n p.
  induction n.
   simpl; ring.
   
   simpl.
   rewrite <- IHn.
   ring.
  Qed.
  
  Theorem Newton : forall n a b, (a + b) ^^ n == newton_sum n a b.
  Proof.
  intros n a b.
  induction n; [compute; ring | ].
  destruct n; [compute; ring | ].
  
  unfold newton_sum.
  rewrite CRsum_simpl.
  rewrite <- CRsum_reindex.
  
  rewrite <- (CRsum_eq_compat (fun k => 
    (Nbinomial (S n)    k  ** a ^^ S k * b ^^ (S (S n) - S k)) +
    (Nbinomial (S n) (S k) ** a ^^ S k * b ^^ (S (S n) - S k)))).
   rewrite CRsum_add_compat.
   rewrite CRpow_simpl.
   rewrite IHn.
   rewrite ring_distributive_r.
   unfold newton_sum.
   do 2 (rewrite (op_comm (O:=mul)); rewrite CRsum_scal_compat).
   assert (AP:forall a b c d e f, a == e + c -> b == d + f -> a + b == c + (d + (e + f)))
     by (intros ? ? ? ? ? ? Hi Hj; rewrite Hi; rewrite Hj; ring);
     apply AP; clear AP.
    rewrite CRsum_simpl_r.
    repeat rewrite Nbinomial_diag.
    repeat rewrite minus_diag.
    apply CRadd_eq_compat.
     apply CRsum_eq_compat_weak.
     intro.
     rewrite <- CRmul_scal_compat.
     apply CRscal_eq_compat.
     rewrite CRpow_simpl.
     simpl; ring.
     
     simpl; ring.
    
    rewrite <- CRsum_reindex.
    apply CRadd_eq_compat.
     simpl; repeat rewrite binomial_zero; ring.
     apply CRsum_eq_compat; intros j Hj.
     rewrite <- minus_Sn_m with (S n) _; [|lia].
     simpl.
     rewrite <- CRmul_scal_compat.
     apply CRscal_eq_compat.
     ring.
   
   intros j Hj.
   rewrite <- CRscal_mult_scal_one.
   rewrite <- (CRscal_mult_scal_one _ (Nbinomial (S n) (S j))).
   rewrite <- ring_distributive_l.
   rewrite CRadd_scal_eq_compat.
   rewrite Nbinomial_pascal; [ | lia].
   rewrite CRscal_mult_scal_one.
   reflexivity.
  Qed.

End Commutative_Ring.
