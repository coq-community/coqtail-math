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

Require Import Vectors.
Require Import Reals.

Section Euclidean_Space.
  Variable (V:Type) (vO:V).
  Variable vadd : V->V->V.
  Variable smul : R->V->V.
  Variable v : vector_space R (1%R) Rplus Rmult V vO vadd smul.
  Variable inner : V->V->R.
  
  Record eucledian_space : Type := {
    euclidean_conjugate_symmetry : forall x y, inner x y = inner y x;
    euclidean_left_linearity_mult : forall a x y, inner (smul a x) y = Rmult a (inner x y);
    euclidean_left_linearity_plus : forall x y z, inner (vadd x y) z = inner (vadd x z) (vadd y z);
    euclidean_positiveness : forall x, (inner x x >= 0)%R;
    euclidean_definiteness : forall x, inner x x = 0%R -> x = vO
  }.
End Euclidean_Space.

(*

Todo : not just with a finite number of dimensions

*)
