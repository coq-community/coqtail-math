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

Require Import Field_theory.

(** * Vector spaces *)

Section Vector_Spaces.
  Variable (R:Type)
    (rO:R) (rI:R)
    (radd rmul rsub : R -> R -> R)
    (ropp : R -> R)
    (rdiv : R -> R -> R)
    (rinv : R -> R)
    (req : R -> R -> Prop)
  .
  Variable Rfield : field_theory rO rI radd rmul rsub ropp rdiv rinv req.
  Variable (V:Type) (vO:V).
  Variable vadd : V->V->V.
  Variable smul : R->V->V.
  
  Record vector_space : Type := {
    vadd_comm := forall x y, vadd x y = vadd y x;
    vadd_assoc := forall x y z, vadd (vadd x y) z = vadd x (vadd y z);
    vadd_identity := forall x, vadd vO x = x;
    vadd_inverse := forall x, exists y, vadd x y = vO;
  
    smul_distr_vadd := forall a x y, smul a (vadd x y) = vadd (smul a x) (smul a y);
    smul_distr_radd := forall a b x, smul (radd a b) x = vadd (smul a x) (smul b x);
    smul_compat_rmul := forall a b x, smul a (smul b x) = smul (rmul a b) x;
    smul_identity := forall x, smul rI x = x
  }.
  
  Fixpoint finite_sum (n:nat) (v:nat->V) {struct n} := match n with
    | 0 => vO
    | S i => vadd (v n) (finite_sum i v)
  end.
  
  Record Basis (I:Type) (Xi:I->V) : Prop := {
    basis_spanning : forall x:V, exists n, exists vn : nat -> I,
      x = finite_sum n (fun n => Xi (vn n));
    basis_linear_independence : forall n (vn : nat->I) (an : nat->R),
      (forall i j , i<=n -> j<=n -> vn i = vn j -> i=j) ->
      finite_sum n (fun m => Xi (vn m)) = vO ->
      forall i, i<=n -> an i = rO
  }.
   
End Vector_Spaces.

















