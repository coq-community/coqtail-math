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

Class Associative {A : Type} (P : A -> Prop) (rel : relation A) (O : operation A) :=
 op_assoc : forall x y z, P x -> P y -> P z -> rel (O x (O y z)) (O (O x y) z).

Class Commutative {A : Type} (P : A -> Prop) (rel : relation A) (O : operation A) :=
 op_comm : forall x y, P x -> P y -> rel (O x y) (O y x).

Definition scalar A B := A -> B -> B.

Definition value A := A -> R.

Class Morphism_value {A : Type} (rel : relation A) (abs : value A) :=
 val_compat_eq : forall a a' : A, rel a a' -> (abs a) = (abs a').

Class Morphism_arit_2 {A : Type} {B : Type} (rel_a : relation A) (rel_b : relation B) (O : A -> B -> B) := {
 op_compat_eq_l : forall a a' : A, forall b : B, rel_a a a' -> rel_b (O a b) (O a' b) ;
 op_compat_eq_r : forall a : A, forall b b' : B, rel_b b b' -> rel_b (O a b) (O a b')
}.

Class Metric_Space (A : Type) (P : A -> Prop) (eqA : relation A) (d : A -> A -> R) := {
  metric_space_setoid :> Equivalence eqA ;
  metric_space_positive : forall x y : A, P x -> P y -> 0 <= d x y ;
  metric_space_symmetry : forall x y : A, P x -> P y -> d x y = d y x ;
  metric_space_separation : forall x y : A, P x -> P y -> (0 = d x y -> eqA x y) /\ (eqA x y -> 0 = d x y);
  metric_space_triangular_inequality : forall x y z : A, P x -> P y -> P z -> d x z <= (d x y) + (d y z)
}.

Class Monoid (M : Type) (P : M -> Prop) (eqM : relation M) (f : operation M) (eps : M) := {
  monoid_setoid :> Equivalence eqM ;
  monoid_eq_compat :> Morphism_arit_2 eqM eqM f ;
  monoid_contains_eps : P eps ;
  monoid_iden_l : forall x : M, P x -> eqM (f eps x) x ;
  monoid_iden_r : forall x : M, P x -> eqM (f x eps) x ;
  monoid_assoc :> Associative P eqM f
}.

Class Monoid_Commutative (M : Type) (P : M -> Prop) (eqM : relation M) (f : operation M) (eps : M) := {
  monoid_comm_monoid :> Monoid M P eqM f eps ;
  monoid_comm :> Commutative P eqM f
}.

Class Group (G : Type) (P : G -> Prop) (eqG : relation G) (f : operation G) (eps : G) := {
  group_monoid :> Monoid G P eqG f eps;
  group_reverse : forall x : G, P x -> exists y : G, (P y) /\ (eqG (f x y) eps)
}.

Class Group_Commutative (G : Type) (P : G -> Prop) (eqG : relation G) (f : operation G) (eps : G) := {
  group_comm_group :> Group G P eqG f eps ;
  group_comm :> Commutative P eqG f
}.
(*
Class Group_Multiplicative (G : Type) (eqG : relation G) (mult : operation G) (eps0 : G) (eps1 : G) := {
  group_multiplicative_setoid :> Equivalence eqG ;
  group_multiplicative_eq_compat :> Morphism_arit_2 eqG eqG mult ;
  group_multiplicative_iden_l : forall x : G, eqG (mult eps1 x) x ;
  group_multiplicative_iden_r : forall x : G, eqG (mult x eps1) x ;
  group_multiplicative_reverse : forall x : G, ~(eqG x eps0) -> exists y : G, eqG (mult x y) eps1 ;
  group_multiplicative_assoc :> Associative eqG mult
}.
*)
Class SemiRing (S : Type) (P : S -> Prop) (eqS : relation S) (add : operation S) (mult : operation S) (eps0 : S) (eps1 : S) := {
  semiring_monoid_comm :> Monoid_Commutative S P eqS add eps0 ;
  semiring_monoid :> Monoid S P eqS mult eps1 ;
  semiring_distributive_r : forall x y z : S, P x -> P y -> P z -> eqS (mult x (add y z)) (add (mult x y) (mult x z)) ;
  semiring_distributive_l : forall x y z : S, P x -> P y -> P z -> eqS (mult (add x y) z) (add (mult x z) (mult y z)) ;
  semiring_absorption_r : forall x : S, P x -> eqS (mult x eps0) eps0 ;
  semiring_absorption_l : forall x : S, P x -> eqS (mult eps0 x) eps0
}.

Class SemiRing_Commutative (S : Type) (P : S -> Prop) (eqS : relation S) (add : operation S) (mult : operation S) (eps0 : S) (eps1 : S) := {
  semiring_comm_semiring :> SemiRing S P eqS add mult eps0 eps1 ;
  semiring_comm :> Commutative P eqS mult
}.

Class Ring (R : Type) (P : R -> Prop) (eqR : relation R) (add : operation R) (mult : operation R) (eps0 : R) (eps1 : R) := {
  ring_group_comm :> Group_Commutative R P eqR add eps0 ;
  ring_monoid :> Monoid R P eqR mult eps1 ;
  ring_distributive_r : forall x y z : R, P x -> P y -> P z -> eqR (mult x (add y z)) (add (mult x y) (mult x z)) ;
  ring_distributive_l : forall x y z : R, P x -> P y -> P z -> eqR (mult (add x y) z) (add (mult x z) (mult y z))
}.

Class Ring_Commutative (R : Type) (P : R -> Prop) (eqR : relation R) (add : operation R) (mult : operation R) (eps0 : R) (eps1 : R) := {
  ring_comm_ring :> Ring R P eqR add mult eps0 eps1 ;
  ring_comm :> Commutative P eqR mult
}.

Class Field (F : Type) (P : F -> Prop) (eqF : relation F) (add : operation F) (mult : operation F) (eps0 : F) (eps1 : F) := {
  field_group_comm :> Group_Commutative F P eqF add eps0 ;
  field_group_multiplicative :> Group F (fun x:F => (P x)/\~(eqF x eps0)) eqF mult eps1 ;
  field_distributive_r : forall x y z : F, P x -> P y -> P z -> eqF (mult x (add y z)) (add (mult x y) (mult x z)) ;
  field_distributive_l : forall x y z : F, P x -> P y -> P z -> eqF (mult (add x y) z) (add (mult x z) (mult y z))
}.

Class Field_Commutative (F : Type) (P : F -> Prop) (eqF : relation F) (add : operation F) (mult : operation F) (eps0 : F) (eps1 : F) := {
  field_comm_field :> Field F P eqF add mult eps0 eps1 ;
  field_comm :> Commutative P eqF mult
}.

Class Field_Valued (F : Type) (P : F -> Prop) (eqF : relation F) (add : operation F) (mult : operation F) (eps0 : F) (eps1 : F) (abs : value F) := {
  field_valued_field_commutative :> Field_Commutative F P eqF add mult eps0 eps1 ;
  field_valued_eq_compat :> Morphism_value eqF abs ;
  field_valued_positive : forall x : F, P x -> 0 <= (abs x) ;
  field_valued_separation : (abs eps0) = 0 /\ forall x : F, P x -> (abs x) = 0 -> eqF x eps0 ;
  field_valued_triangular_inequality : forall x y : F, P x -> P y -> abs (add x y) <= (abs x) + (abs y);
  field_valued_homogeneity : forall x y : F, P x -> P y -> abs (mult x y) = (abs x) * (abs y)
}.

Class Vector_Space (E : Type) (P : E -> Prop) (eqE : relation E) (F : Type) (Q : F -> Prop) (eqF : relation F)
                                 (v_add : operation E) (v_mult : scalar F E)
                                 (add : operation F) (mult : operation F)
                                 (v_null : E)
                                 (eps0 : F) (eps1 : F):= {
  vector_space_field :> Field_Commutative F Q eqF add mult eps0 eps1 ;
  vector_space_group_comm :> Group_Commutative E P eqE v_add v_null ;
  vector_space_eq_compat :> Morphism_arit_2 eqF eqE v_mult ;
  vector_space_distributive_r : forall a : F, forall x y : E, Q a -> P x -> P y -> eqE (v_mult a (v_add x y)) (v_add (v_mult a x) (v_mult a y)) ;
  vector_space_distributive_l : forall a b : F, forall x : E, Q a -> Q b -> P x -> eqE (v_mult (add a b) x) (v_add (v_mult a x) (v_mult b x)) ;
  vector_space_assoc : forall a b : F, forall x : E, Q a -> Q b -> P x -> eqE (v_mult (mult a b) x) (v_mult a (v_mult b x)) ;
  vector_space_iden_l : forall a : F, forall x : E, Q a -> P x -> eqE (v_mult eps1 x) x
}.

Class Vector_Space_Normed (E : Type) (P : E -> Prop) (eqE : relation E) (F : Type) (Q : F -> Prop) (eqF : relation F)
                                 (v_add : operation E) (v_mult : scalar F E)
                                 (add : operation F) (mult : operation F)
                                 (v_null : E)
                                 (eps0 : F) (eps1 : F)
                                 (norm: value E) (abs : value F) := {
  vector_space_normed_field_valued :> Field_Valued F Q eqF add mult eps0 eps1 abs ;
  vector_space_normed_vector_space :> Vector_Space E P eqE F Q eqF v_add v_mult add mult v_null eps0 eps1 ;
  vector_space_normed_separation : forall v : E, P v -> (norm v) = 0 -> eqE v v_null ;
  vector_space_normed_triangular_inequality : forall v w : E, P v -> P w -> norm (v_add v w) <= (norm v) + (norm w) ;
  vector_space_normed_homogeneity : forall x : F, forall v : E, Q x -> P v -> norm (v_mult x v) = (abs x) * (norm v)
}.
