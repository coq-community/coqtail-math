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

Require Import Ensembles.
Require Import Topology.

Section Functions.

  Variable U V : Type.
  
  Inductive Image (X:Ensemble U) (f:U -> V) : Ensemble V :=
    Image_intro : forall x:U, In _ X x -> forall y:V, y = f x -> In _ (Image X f) y.
  
  Inductive Preimage (Y:Ensemble V) (f:U -> V) : Ensemble U :=
    Inverse_Image_intro : forall y, In _ Y y -> forall x, y = f x -> In _ (Preimage Y f) x.
  
  Definition function (A:Ensemble U) (B:Ensemble V) : (U->V)->Prop :=
    fun f:U->V => forall a:U, In U A a -> In V B (f a).
  
  Lemma Image_in_arrival_space : forall (A:Ensemble U) (B:Ensemble V) (f:U->V),
      function A B f -> Included _ (Image A f) B.
  Proof.
  intros A B f funf y.
  intros yIm. induction yIm.
  rewrite H0.
  apply (funf x H).
  Qed.
  
  (*Lemma Preimage_in_departure_space (A:Ensemble U) (B:Ensemble V) :
    forall f:U->V,
      function A B f -> Included _ (Preimage B f) A.
  Proof.
  intros A B f funf x.
  intros xIm; induction xIm.
  (*rewrite H0.
  apply (funf x H).*)
  Qed.*)
End Functions.
