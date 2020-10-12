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

(** Some usual integrals *)


Require Import Reals.
Require Import MyRfunctions.
Require Import Rintegral.
Require Import Lia.

Open Scope R_scope.

Lemma Rint_inv : forall a b, 
  0 < a <= b -> Rint (fun x => /x) a b (ln b - ln a).
intros a b Hab.
apply Rint_derive.
  intuition.
intros x Hx.
  apply derivable_pt_lim_ln.
  apply Rlt_le_trans with a; intuition.
  intros x Hx.
  apply continuity_pt_inv.
  apply derivable_continuous, derivable_id.
  assert( 0 < x).
  apply Rlt_le_trans with a; tauto.
  auto with *.
Qed.
Hint Resolve Rint_inv : Rint.

Lemma Rint_exp : forall a b, Rint exp a b (exp b - exp a).
Proof.
intros a b.
apply Rint_derive2.
intros; apply derivable_pt_lim_exp.
intros; apply derivable_continuous_pt, derivable_pt_exp.
Qed.
Hint Resolve Rint_exp : Rint.

Lemma Rint_pow_pos : forall n a b, 
  Rint (fun y : R => INR n * y ^ (pred n)) a b ((b ^ n - a ^ n)).
Proof.
intros n a b.
destruct n.
  replace (b ^ 0 - a ^ 0) with (0 * (b - a)) by ring.
  apply Rint_eq_compat with (fct_cte 0).
  unfold fct_cte; auto with *.
  apply Rint_constant.
apply Rint_derive2 with (f := fun x => x ^ (S n)); intros.
apply derivable_pt_lim_pow_pos; lia.
apply continuity_pt_mult.
apply continuity_pt_const; intros u v ; reflexivity.

  induction n.
  apply continuity_pt_const; intros u v ; reflexivity.
  simpl.
  apply continuity_pt_mult.

auto with Rcont.
auto with Rcont.
Qed.
Hint Resolve Rint_pow_pos : Rint.

Lemma Rint_cos : forall a b, 
  Rint cos a b (sin b - sin a).
Proof.
intros a b.
apply Rint_derive2.
intros; apply derivable_pt_lim_sin.
intros; apply continuity_cos.
Qed.
Hint Resolve Rint_cos : Rint.

Lemma Rint_sin : forall a b, 
  Rint sin a b (cos a - cos b).
intros a b.
replace (cos a - cos b) with (- cos b - -cos a) by ring.
apply Rint_derive2 with (f := (-cos)%F).
intros; replace (sin x) with (--sin x) by ring; 
  apply derivable_pt_lim_opp, derivable_pt_lim_cos.
intros; apply continuity_sin.
Qed.
Hint Resolve Rint_sin : Rint.

Lemma Rint_sqrt_inv : forall a b, 0 < a -> 0 < b ->
  Rint (fun x => /(sqrt x)) a b (2 *( sqrt b - sqrt a)).
Proof.
intros a b Ha Hb.
assert(Hneq : forall x, Rmin a b <= x <= Rmax a b -> 0 < sqrt x).
  intros; 
    apply sqrt_lt_R0.
    apply Rlt_le_trans with (Rmin a b).
    apply Rmin_pos; assumption.
    intuition.
apply Rint_eq_compat with (fun x => 2 * /(2 * sqrt x)).
  intros; field.
  auto with *.
apply Rint_scalar_mult_compat_l.
apply Rint_derive2.
intros; apply derivable_pt_lim_sqrt.
  apply Rlt_le_trans with (Rmin a b).
  apply Rmin_pos; assumption.
  intuition.
intros.
apply continuity_pt_inv.
  apply continuity_pt_mult.
  apply continuity_pt_constant.
  apply continuity_pt_sqrt.
  apply Rle_trans with (Rmin a b).
  apply Rmin_ge; intuition.
  intuition.
assert( 0 < 2 * sqrt x).
apply Rmult_lt_0_compat.
  auto with *.
  auto.
auto with *.
Qed.
Hint Resolve Rint_sqrt_inv : Rint.

(* cosh sinh  *)
