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

Section Sets.
  Variable U : Type.

  Definition set := U -> Prop.
  
  Definition In (A:set) x : Prop := A x.
  
  Definition Set_included A B := forall x, In A x -> In B x.
  
  Inductive Set_inter (A B:set) : set :=
    Set_inter_intro : forall x, In A x -> In B x -> In (Set_inter A B) x.
  
  Inductive Set_union (A B:set) : set :=
    | Set_union_intro_l : forall x, In A x -> In (Set_union A B) x
    | Set_union_intro_r : forall x, In B x -> In (Set_union A B) x.
  
  Inductive Set_empty : set :=.
  
  Inductive Set_full : set :=
    | Set_full_intro : forall x, In Set_full x.
  
  Inductive Set_singleton (x:U) : set :=
    Set_singleton_intro : In (Set_singleton x) x.
  
  Inductive Set_couple (x y:U) : set :=
    | Set_couple_l : In (Set_couple x y) x
    | Set_couple_r : In (Set_couple x y) y.
  
  Inductive Set_triple (x y z:U) : set :=
    | Set_triple_l : In (Set_triple x y z) x
    | Set_triple_m : In (Set_triple x y z) y
    | Set_triple_r : In (Set_triple x y z) z.
  
  Definition Set_complement (A:set) : set := fun x:U => ~ In A x.
  
  Definition Set_minus (B C:set) : set := fun x:U => In B x /\ ~ In C x.
  
  Definition Set_subtract (B:set) (x:U) : set := Set_minus B (Set_singleton x).
  
  Inductive Set_disjoint (B C:set) : Prop :=
    Set_disjoint_intro : (forall x:U, ~ In (Set_inter B C) x) -> Set_disjoint B C.
  
  Inductive Set_inhabited (B:set) : Prop :=
    Inhabited_intro : forall x:U, In B x -> Set_inhabited B.
  
  Definition Set_strict_included (B C:set) : Prop := Set_included B C /\ B <> C.
  
  Definition Set_same (B C:set) : Prop := Set_included B C /\ Set_included C B.
  
  Axiom Set_Extensionality : forall A B:set, Set_same A B -> A = B.
End Sets.

Implicit Arguments set [U].
Implicit Arguments In [U].
Implicit Arguments Set_included [U].
Implicit Arguments Set_inter [U].
Implicit Arguments Set_union [U].
Implicit Arguments Set_empty [U].
Implicit Arguments Set_full [U].
Implicit Arguments Set_singleton [U].
Implicit Arguments Set_couple [U].
Implicit Arguments Set_triple [U].
Implicit Arguments Set_complement [U].
Implicit Arguments Set_minus [U].
Implicit Arguments Set_subtract [U].
Implicit Arguments Set_disjoint [U].
Implicit Arguments Set_inhabited [U].
Implicit Arguments Set_strict_included [U].
Implicit Arguments Set_same [U].
Implicit Arguments Set_Extensionality [U].
