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

Require Import Reals.
Require Import Rintegral.
Require Import Rintegral_usual.
(* TODO I modified a Rint_reverse into Rint_reverse_1.... check if there is a problem then erase*)
(* constructs a proof of the form Rint f a b ?x *)
Ltac Rint_constr f a b := match goal with
  | id : Rint f a b ?x |- _ => constr:(id)
  | id : Rint f b a ?x |- _ => constr:(Rint_reverse_1 f b a x)
  | _ => match constr:(f) with 
    | fct_cte ?c => constr:(Rint_constant c a b)
    | (?g + ?h)%F => let H1 := Rint_constr g a b in let H2 := Rint_constr h a b in
                     constr:(Rint_plus g h a b H1 H2)
    | (?g - ?h)%F => let H1 := Rint_constr g a b in let H2 := Rint_constr h a b in
                     constr:(Rint_minus g h a b H1 H2)
    | ((fct_cte ?c) * ?h)%F => let H := Rint_constr h a b in
                     constr:(Rint_scalar_mult_compat_l h a b H)
    | (?h * (fct_cte ?c))%F => let H := Rint_constr h a b in
                     constr:(Rint_scalar_mult_compat_r h a b H)
  end
(* singleton *)
end.


Ltac rint_tac := match goal with
  | id : Rint ?f ?a ?b ?x |- Rint ?f ?a ?b ?x => assumption
  | |- Rint ?f ?a ?a => apply Rint_singleton
  | |- Rint ?f ?a ?b ?x => let H := Rint_constr f a b in match type of H with
         Rint f a b ?y => replace x with y ; [apply H | subst; try reflexivity; try field; intuition] end
end.
