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

Require Import Coq.Relations.Relation_Definitions.
Require Import SetoidClass.
Require Import Reals.

Open Scope R_scope.

Definition operation A := A -> A -> A.

Class Associative {A : Type} (rel : relation A) (O : operation A) :=
 op_assoc : forall x y z, rel (O x (O y z)) (O (O x y) z).

Class Commutative {A : Type} (rel : relation A) (O : operation A) :=
 op_comm : forall x y, rel (O x y) (O y x).

Definition scalar A B := A -> B -> B.

Definition value A := A -> R.

Class Metric_Space (A : Type) (eqA : relation A) (d : A -> A -> R) := {
  metric_space_setoid :> Equivalence eqA ;
  metric_space_positive : forall x y : A, 0 <= d x y ;
  metric_space_symmetry : forall x y : A, d x y = d y x ;
  metric_space_separation : forall x y : A, (0 = d x y -> eqA x y) /\ (eqA x y -> 0 = d x y);
  metric_space_triangular_inequality : forall x y z : A, d x z <= (d x y) + (d y z)
}.

Class Monoid (M : Type) (eqM : relation M) (f : operation M) (eps : M) := {
  monoid_setoid :> Equivalence eqM ;
  monoid_iden_l : forall x : M, eqM (f eps x) x ;
  monoid_iden_r : forall x : M, eqM (f x eps) x ;
  monoid_assoc :> Associative eqM f;
  monoid_eq_compat_l : forall x y z : M, eqM y z -> eqM (f x y) (f x z);
  monoid_eq_compat_r: forall x y z : M, eqM x y -> eqM (f x z) (f y z)
}.

Class Monoid_Commutative (M : Type) (eqM : relation M) (f : operation M) (eps : M) := {
  monoid_comm_monoid :> Monoid M eqM f eps ;
  monoid_comm :> Commutative eqM f
}.

Class Group (G : Type) (eqG : relation G) (f : operation G) (eps : G) := {
  group_monoid :> Monoid G eqG f eps;
  group_reverse : forall x : G, sig (fun y => eqG (f x y) eps)
}.

Class Group_Commutative (G : Type) (eqG : relation G) (f : operation G) (eps : G) := {
  group_comm_group :> Group G eqG f eps ;
  group_comm :> Commutative eqG f
}.

Class Group_Multiplicative (G : Type) (eqG : relation G) (mult : operation G) (eps0 : G) (eps1 : G) := {
  group_setoid :> Equivalence eqG ;
  group_multiplicative_iden_l : forall x : G, eqG (mult eps1 x) x ;
  group_multiplicative_iden_r : forall x : G, eqG (mult x eps1) x ;
  group_multiplicative_reverse : forall x : G, ~(eqG x eps0) -> sig (fun y => eqG (mult x y) eps1);
  group_multiplicative_assoc :> Associative eqG mult;
  group_multiplicative_eq_compat_l : forall x y z : G, eqG y z -> eqG (mult x y) (mult x z);
  group_multiplicative_eq_compat_r: forall x y z : G, eqG x y -> eqG (mult x z) (mult y z)
}.

Class SemiRing (S : Type) (eqS : relation S) (add : operation S) (mult : operation S) (eps0 : S) (eps1 : S) := {
  semiring_monoid_comm :> Monoid_Commutative S eqS add eps0 ;
  semiring_monoid :> Monoid S eqS mult eps1 ;
  semiring_distributive_r : forall x y z : S, eqS (mult x (add y z)) (add (mult x y) (mult x z)) ;
  semiring_distributive_l : forall x y z : S, eqS (mult (add x y) z) (add (mult x z) (mult y z)) ;
  semiring_absorption_r : forall x : S, eqS (mult x eps0) eps0 ;
  semiring_absorption_l : forall x : S, eqS (mult eps0 x) eps0
}.

Class SemiRing_Commutative (S : Type) (eqS : relation S) (add : operation S) (mult : operation S) (eps0 : S) (eps1 : S) := {
  semiring_comm_semiring :> SemiRing S eqS add mult eps0 eps1 ;
  semiring_comm :> Commutative eqS mult
}.

Class Ring (R : Type) (eqR : relation R) (add : operation R) (mult : operation R) (eps0 : R) (eps1 : R) := {
  ring_group_comm :> Group_Commutative R eqR add eps0 ;
  ring_monoid :> Monoid R eqR mult eps1 ;
  ring_distributive_r : forall x y z : R, eqR (mult x (add y z)) (add (mult x y) (mult x z)) ;
  ring_distributive_l : forall x y z : R, eqR (mult (add x y) z) (add (mult x z) (mult y z))
}.

Class Ring_Commutative (R : Type) (eqR : relation R) (add : operation R) (mult : operation R) (eps0 : R) (eps1 : R) := {
  ring_comm_ring :> Ring R eqR add mult eps0 eps1 ;
  ring_comm :> Commutative eqR mult
}.

Class Field (F : Type) (eqF : relation F) (add : operation F) (mult : operation F) (eps0 : F) (eps1 : F) := {
  field_group_comm :> Group_Commutative F eqF add eps0 ;
  field_group_multiplicative :> Group_Multiplicative F eqF mult eps0 eps1 ;
  field_distributive_r : forall x y z : F, eqF (mult x (add y z)) (add (mult x y) (mult x z)) ;
  field_distributive_l : forall x y z : F, eqF (mult (add x y) z) (add (mult x z) (mult y z))
}.

Class Field_Commutative (F : Type) (eqF : relation F) (add : operation F) (mult : operation F) (eps0 : F) (eps1 : F) := {
  field_comm_field :> Field F eqF add mult eps0 eps1 ;
  field_comm :> Commutative eqF mult
}.

Class Field_Valued (F : Type) (eqF : relation F) (add : operation F) (mult : operation F) (eps0 : F) (eps1 : F) (abs : value F) := {
  field_valued_field_commutative :> Field_Commutative F eqF add mult eps0 eps1 ;
  field_valued_positive : forall x : F, 0 <= (abs x) ;
  field_valued_separation : (abs eps0) = 0 /\ forall x : F, (abs x) = 0 -> eqF x eps0 ;
  field_valued_triangular_inequality : forall x y : F, abs (add x y) <= (abs x) + (abs y);
  field_valued_homogeneity : forall x y : F, abs (mult x y) = (abs x) * (abs y)
}.

Class Vector_Space (E : Type) (eqE : relation E) (F : Type) (eqF : relation F)
                                 (v_add : operation E) (v_mult : scalar F E)
                                 (add : operation F) (mult : operation F)
                                 (v_null : E)
                                 (eps0 : F) (eps1 : F):= {
  vector_space_field :> Field_Commutative F eqF add mult eps0 eps1 ;
  vector_space_group_comm :> Group_Commutative E eqE v_add v_null ;
  vector_space_distributive_r : forall a : F, forall x y : E, eqE (v_mult a (v_add x y)) (v_add (v_mult a x) (v_mult a y)) ;
  vector_space_distributive_l : forall a b : F, forall x : E, eqE (v_mult (add a b) x) (v_add (v_mult a x) (v_mult b x)) ;
  vector_space_assoc : forall a b : F, forall x : E, eqE (v_mult (mult a b) x) (v_mult a (v_mult b x)) ;
  vector_space_iden_l : forall a : F, forall x : E, eqE (v_mult eps1 x) x;
  vector_space_eq_compat_l : forall a : F, forall x y :E, eqE x y -> eqE (v_mult a x) (v_mult a y);
  vector_space_eq_compat_r : forall a b : F, forall x : E, eqF a b -> (eqE (v_mult a x) (v_mult b x))
}.

Class Vector_Space_Normed (E : Type) (eqE : relation E) (F : Type) (eqF : relation F)
                                 (v_add : operation E) (v_mult : scalar F E)
                                 (add : operation F) (mult : operation F)
                                 (v_null : E)
                                 (eps0 : F) (eps1 : F)
                                 (norm: value E) (abs : value F) := {
  vector_space_normed_field_valued :> Field_Valued F eqF add mult eps0 eps1 abs ;
  vector_space_normed_vector_space :> Vector_Space E eqE F eqF v_add v_mult add mult v_null eps0 eps1 ;
  vector_space_normed_separation : forall v : E, (norm v) = 0 -> eqE v v_null ;
  vector_space_normed_triangular_inequality : forall v w : E, norm (v_add v w) <= (norm v) + (norm w) ;
  vector_space_normed_homogeneity : forall x : F, forall v : E, norm (v_mult x v) = (abs x) * (norm v)
}.

Close Scope R_scope.

(* Can be improved 
Hint Resolve
  @monoid_setoid
  @monoid_assoc
: typeclass.

Hint Rewrite
  @monoid_iden_l
  @monoid_iden_r
  @monoid_eq_compat_l
  @monoid_eq_compat_r
  @op_assoc
  @op_comm
: typeclass.*)