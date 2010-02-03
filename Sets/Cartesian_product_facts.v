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

Require Export Cartesian_product.
Require Export My_Sets_facts.
Require Export Finite_sets_facts.
Require Export Arith.

Section Cartesian_product_facts.

Implicit Arguments Product [U V].
Implicit Arguments Union [U].
Implicit Arguments Add [U].
Implicit Arguments Singleton [U].
Implicit Arguments Finite [U].
Implicit Arguments cardinal [U].

Variable U V W: Type.

Lemma Product_set_empty_set_empty : forall X:Ensemble U, 
  Product X (Empty_set V)=Empty_set (U*V).
Proof.
intros.
apply Extensionality_Ensembles.
split.
intro; intros.
destruct x.
destruct H.
inversion H0.
intro; intros.
destruct x.
destruct H.
Qed.

Lemma Product_empty_set_set_empty : forall Y:Ensemble V, 
  Product (Empty_set U) Y=Empty_set (U*V).
Proof.
intros.
apply Extensionality_Ensembles.
split.
intro. intros.
destruct x.
destruct H.
inversion H.
intro. intros.
destruct x.
destruct H.
Qed.

Lemma Product_add_left : forall (X:Ensemble U) (Y:Ensemble V) (x:U),
  Product (Add X x) Y=Union (Product X Y) (Product (Singleton x) Y).
Proof.
intros.
apply Extensionality_Ensembles; split.
intro; intros.
destruct x0.
destruct H.
destruct H.
apply Union_introl.
split; trivial.
apply Union_intror.
destruct H.
split; trivial; constructor.

intro; intros.
destruct H.
destruct x0.
destruct H.
split; trivial.
apply Union_introl; trivial.
destruct x0.
destruct H.
split; trivial.
apply Union_intror; trivial.
Qed.

Lemma Product_add_right : forall (X:Ensemble U) (Y:Ensemble V) (y:V),
  Product X (Add Y y)=Union (Product X Y) (Product X (Singleton y)).
Proof.
intros.
apply Extensionality_Ensembles; split.
intro; intros.
destruct x.
destruct H.
destruct H0.
apply Union_introl.
split;trivial.
apply Union_intror.
destruct H0; constructor; auto; constructor.

intro. intros.
destruct H.
destruct x.
destruct H.
split; trivial.
apply Union_introl.
trivial.
destruct x.
destruct H.
split; trivial.
apply Union_intror; trivial.
Qed.

Lemma Product_singleton_add : forall (x:U) (Y:Ensemble V) (y:V),
  Product (Singleton x) (Add Y y)=Add (Product (Singleton x) Y) (x,y).
Proof.
intros.
apply Extensionality_Ensembles; split.
intro; intros.
destruct x0.
destruct H.
destruct H0.
apply Union_introl.
split;trivial.
apply Union_intror.
destruct H0.
destruct H.
constructor.

intro; intros.
destruct H.
destruct x0.
destruct H.
split; trivial.
apply Union_introl; trivial.
destruct x0.
split; inversion H; [ | apply Union_intror]; constructor.
Qed.

Lemma Product_add_singleton : forall (x:U) (X:Ensemble U) (y:V),
  Product (Add X x) (Singleton y)=Add (Product X (Singleton y)) (x,y).
Proof.
intros.
apply Extensionality_Ensembles; split.
intro; intros.
destruct x0. destruct H.
destruct H0. destruct H.
apply Union_introl.
split; auto; constructor.
destruct H.
apply Union_intror.
constructor.

intro. intros.
destruct H. destruct x0.
destruct H.
destruct H0.
split.
apply Union_introl. auto. constructor.
destruct H.
split.
apply Union_intror. constructor. constructor.
Qed.

Lemma Product_singleton_singleton_singleton : forall (x:U) (y:V),
  Product (Singleton x) (Singleton y)=Singleton (x,y).
Proof.
intros.
apply Extensionality_Ensembles; split.
intro; intros.
destruct x0.
destruct H.
destruct H.
destruct H0.
constructor.

intro; intros.
destruct x0.
destruct H.
split; constructor.
Qed.

Lemma Product_preserves_finite : forall X:Ensemble U, forall Y:Ensemble V,
  Finite X -> Finite Y -> Finite (Product X Y).
Proof.
induction 2; [rewrite Product_set_empty_set_empty; constructor |].
rewrite Product_add_right.
apply Union_preserves_Finite; auto.
induction H; [rewrite Product_empty_set_set_empty; constructor |].
rewrite Product_add_left.
apply Union_preserves_Finite.
 apply IHFinite0.
 rewrite Product_add_left in IHFinite.
 apply Finite_downward_closed with (Union (Product A0 A) (Product (Singleton x0) A)); intuition.
 
 rewrite Product_singleton_singleton_singleton.
 replace (Singleton (x0,x)) with (Add (Empty_set (U*V)) (x0,x)); intuition.
Qed.

Lemma Product_cardinal : forall X:Ensemble U, forall Y:Ensemble V, forall n m:nat,
  cardinal X n -> cardinal Y m -> cardinal (Product X Y) (n*m).
Proof.
cut (forall X:Ensemble U, forall n:nat, cardinal X n -> 
  forall Y:Ensemble V, forall m, cardinal Y m -> cardinal (Product X Y) (n*m)).
 intuition.
induction 1.
 intros; rewrite Product_empty_set_set_empty; intuition.
 
 induction 1.
 rewrite Product_set_empty_set_empty.
  rewrite mult_0_r; constructor.
  
  replace (S n*S n0) with (n*n0+n+n0+1) by ring.
  rewrite Product_add_left.
  repeat rewrite Product_add_right.
  rewrite Product_singleton_singleton_singleton.
  rewrite <- Union_assoc.
  apply cardinal_of_disjoint_union.
   replace (n*n0+n+n0) with (n*n0+n0+n) by ring.
   rewrite Union_assoc.
   replace (Union (Product A (Singleton x0)) (Product (Singleton x) A0)) with
     (Union (Product (Singleton x) A0) (Product A (Singleton x0))) by intuition.
   rewrite <- Union_assoc.
   apply cardinal_of_disjoint_union.
    rewrite <- Product_add_left.
    replace (n*n0+n0) with (S n*n0) by ring; auto.
    
    replace n with (n*1) by ring.
    apply IHcardinal.
    rewrite Singleton_is_add_empty; intuition.
    
    split; intros x1 H3;
    destruct H3; destruct H3; destruct x1;
      destruct H3; destruct H4; destruct H6; intuition.
  
  rewrite Singleton_is_add_empty; intuition.
  
  split; intros x1 H3;
  destruct H3; destruct H3; try destruct H3;
   destruct H4; destruct H3;  intuition.
Qed.

End Cartesian_product_facts.
