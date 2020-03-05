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

Require Import RIneq MyNeq.
Require Import Rfunctions.

Require Import Lra.

Open Scope R_scope.

Implicit Type r : R.

Require Setoid.

Add Parametric Relation : R Rle
reflexivity proved by Rle_refl
transitivity proved by Rle_trans as Rle.

Add Parametric Relation : R Rlt
transitivity proved by Rlt_trans as Rlt.

Lemma Rabs_opp1 : forall p, Rabs ((- 1) ^ p) = 1.
Proof.
apply pow_1_abs.
Qed.

Lemma Rdiv_eq_0_inv : forall a b, a / b = 0 -> b <> 0 -> a = 0.
Proof.
intros a b Hab Hb ; destruct (Rmult_integral _ _ Hab) as [Ha | Hb'].
 apply Ha.
 assert (Hb'' : / b <> 0) by (apply Rinv_neq_0_compat ; assumption).
 apply False_ind, Hb'', Hb'.
Qed.

Lemma Rabs_Rdiv : forall a b, b <> 0 -> Rabs a / Rabs b = Rabs (a / b).
Proof.
intros a b b_neq ; unfold Rdiv ; rewrite Rabs_mult, Rabs_Rinv.
 reflexivity.
 assumption.
Qed.

Lemma Rplus_pos_lt : forall x h, 0 < h -> x < x + h.
Proof.
intros ; lra.
Qed.

Lemma Rminus_pos_lt : forall x h, 0 < h -> x - h < x.
Proof.
intros ; lra.
Qed.

Lemma Rplus_pos_neq : forall x h, 0 < h -> x <> x + h.
Proof.
intros ; apply Rlt_not_eq, Rplus_pos_lt ; assumption.
Qed.


Lemma Rlt_minus_sort : forall a b c, a < c + b -> a - c < b.
Proof.
intros ; lra.
Qed.

Lemma Rlt_minus_sort2 : forall a b c, a - c < b -> - c < b - a.
Proof.
intros ; lra.
Qed.

Lemma Rminus_lt_compat_l : forall a b c, a < b + c -> a - b < c.
intros ; lra.
Qed.

Lemma Rminus_lt_compat_r : forall a b c, a + c < b -> a < b - c.
Proof.
intros ; lra.
Qed.

Lemma Rminus_lt_compat_l_rev : forall a b c, a - b < c -> a < b + c.
Proof.
intros ; lra.
Qed.

Lemma Rminus_le_compat_l : forall a b c, a <= b + c -> a - b <= c.
intros ; lra.
Qed.

Lemma Rminus_le_compat_r : forall a b c, a + c <= b -> a <= b - c.
Proof.
intros ; lra.
Qed.

Lemma Rminus_le_compat_l_rev : forall a b c, a - b <= c -> a <= b + c.
Proof.
intros ; lra.
Qed.

Lemma Rinv_lt_contravar_rev : forall x y, 0 < x -> 0 < y -> /x < /y -> y < x.
Proof.
intros x y x_pos y_pos Hxy ; rewrite <- (Rinv_involutive x), <- (Rinv_involutive y) ;
 try (apply Rgt_not_eq ; assumption).
 apply Rinv_lt_contravar ; [| assumption] ; apply Rmult_lt_0_compat ;
 apply Rinv_0_lt_compat ; assumption.
Qed.

Lemma Ropp_Rdiv_compat_l : forall a b, b <> 0 -> - a / b = - (a / b).
Proof.
intros ; field ; assumption.
Qed.

Lemma Rle_Rminus : forall a b, a <= b -> 0 <= b - a.
Proof.
intros ; lra.
Qed.

Lemma Rle_Rminus_rev : forall a b, 0 <= b - a -> a <= b.
Proof.
intros ; lra.
Qed.

Lemma Rlt_Rminus_rev : forall a b, 0 < b - a -> a < b.
Proof.
intros ; lra.
Qed.

Lemma Rmult_Rinv_lt_compat_r : forall a b c, 0 < a -> a * b < c -> b < c * / a.
Proof.
intros a b c a_pos Habc ; apply Rle_lt_trans with (a * b * / a).
 right ; field ; apply Rgt_not_eq ; assumption.
 apply Rmult_lt_compat_r ; [apply Rinv_0_lt_compat |] ; assumption.
Qed.

Lemma Rmult_Rinv_lt_compat_r_rev : forall a b c, 0 < a -> b < c * / a -> a * b < c.
Proof.
intros a b c a_pos Habc ; apply Rlt_le_trans with (a * (c * / a)).
 apply Rmult_lt_compat_l ; assumption.
 right ; field ; apply Rgt_not_eq ; assumption.
Qed.

Lemma Rmult_Rinv_lt_compat_l : forall a b c, 0 < c -> a < b * c -> a * / c < b.
Proof.
intros a b c a_pos Habc ; apply Rlt_le_trans with (b * c * / c).
 apply Rmult_lt_compat_r ; [apply Rinv_0_lt_compat |] ; assumption.
 right ; field ; apply Rgt_not_eq ; assumption.
Qed.

Lemma Rmult_Rinv_lt_compat_l_rev : forall a b c, 0 < c -> a * / c < b -> a < b * c.
Proof.
intros a b c a_pos Habc ; apply Rle_lt_trans with (a * / c * c).
 right ; field ; apply Rgt_not_eq ; assumption.
 apply Rmult_lt_compat_r ; assumption.
Qed.

Lemma Rlt_minus_swap: forall x y z, x - y < z -> x - z < y.
Proof.
intros ; lra.
Qed.

Lemma Rdiv_0_l: forall r, 0 / r = 0.
Proof.
intro r ; unfold Rdiv ; apply Rmult_0_l.
Qed.

Lemma Rmin_opp_opp_Rmax : forall r1 r2, Rmin (-r1) (-r2) = - (Rmax r1 r2).
Proof.
intros r1 r2 ; unfold Rmin, Rmax ; destruct (Rle_dec r1 r2) as [L1 | R1] ;
 destruct (Rle_dec (-r1) (-r2)) as [L2 | R2].
 assert (H := Ropp_le_cancel _ _ L2) ; apply Ropp_eq_compat ;
  apply Rle_antisym ; assumption.
 reflexivity.
 reflexivity.
 assert (H1 := Rnot_le_lt _ _ R1).
 assert (H2 := Ropp_lt_cancel _ _ (Rnot_le_lt _ _ R2)).
 apply False_ind ; apply Rlt_irrefl with r1 ; apply Rlt_trans with r2 ;
  assumption.
Qed.

Lemma Rmax_opp_opp_Rmin : forall r1 r2, Rmax (-r1) (-r2) = - (Rmin r1 r2).
Proof.
intros r1 r2.
replace (Rmin r1 r2) with (Rmin (--r1) (--r2)) by (rewrite Ropp_involutive ; intuition).
 rewrite Rmin_opp_opp_Rmax ; rewrite Ropp_involutive ; reflexivity.
Qed.

Lemma Rmin_diag : forall r, Rmin r r = r.
Proof.
intro r ; unfold Rmin ; destruct (Rle_dec r r) ; auto.
Qed.

Lemma Rmin_eq_l : forall r1 r2, r1 <= r2 -> Rmin r1 r2 = r1.
Proof.
intros r1 r2 r1_le_r2 ; unfold Rmin ; destruct (Rle_dec r1 r2).
 reflexivity.
 contradiction.
Qed.

Lemma Rmin_eq_r : forall r1 r2, r1 <= r2 -> Rmin r2 r1 = r1.
Proof.
intros r1 r2 r1_le_r2 ; rewrite Rmin_comm ;
 apply Rmin_eq_l ; assumption.
Qed.

Lemma Rmax_diag : forall r, Rmax r r = r.
Proof.
intro r ; unfold Rmax ; destruct (Rle_dec r r) ; auto.
Qed.

Lemma Rmax_eq_l : forall r1 r2, r2 <= r1 -> Rmax r1 r2 = r1.
Proof.
intros r1 r2 r1_le_r2 ; unfold Rmax ; destruct (Rle_dec r1 r2).
 destruct r.
 apply False_ind ; apply Rlt_irrefl with r2 ;
 apply Rle_lt_trans with r1 ; assumption.
 symmetry ; trivial.
 reflexivity.
Qed.

Lemma Rmax_eq_r : forall r1 r2, r2 <= r1 -> Rmax r2 r1 = r1.
Proof.
intros r1 r2 r1_le_r2 ; rewrite Rmax_comm ; apply Rmax_eq_l ;
 assumption.
Qed.

Lemma Rmin_pos : forall x y, 0 <= x -> 0 <= y -> 0 <= Rmin x y.
Proof.
intros x y x_pos y_pos ; unfold Rmin ;
 destruct (Rle_dec x y) ; assumption.
Qed.

Lemma Rmin_pos_lt : forall x y, 0 < x -> 0 < y -> 0 < Rmin x y.
Proof.
intros x y x_pos y_pos ; unfold Rmin ;
 destruct (Rle_dec x y) ; assumption.
Qed.

Lemma Rmax_pos_l : forall x y, 0 <= x -> 0 <= Rmax x y.
Proof.
intros x y x_pos ; unfold Rmax ; destruct (Rle_dec x y) ;
 [apply Rle_trans with x |] ; assumption.
Qed.

Lemma Rmax_pos_r : forall x y, 0 <= y -> 0 <= Rmax x y.
Proof.
intros ; rewrite Rmax_comm ; apply Rmax_pos_l ; auto.
(* U Mad? *)
Qed.

Lemma Rmax_pos_lt_l : forall x y, 0 < x -> 0 < Rmax x y.
Proof.
intros x y x_pos ; unfold Rmax ; destruct (Rle_dec x y) ;
 [apply Rlt_le_trans with x |] ; assumption.
Qed.

Lemma Rmax_pos_lt_r : forall x y, 0 < y -> 0 < Rmax x y.
Proof.
intros ; rewrite Rmax_comm ; apply Rmax_pos_lt_l ; auto.
(* U Mad? *)
Qed.

Lemma Rabs_eq_compat : forall r1 r2, r1 = r2 -> Rabs r1 = Rabs r2.
Proof.
intros ; subst ; reflexivity.
Qed.

Lemma Rabs_le : forall r, - Rabs r <= r.
Proof.
intros r ; unfold Rabs ; destruct (Rcase_abs r) ;
 [| apply Rle_trans with 0] ; intuition.
Qed.

Lemma Req_dec : forall r1 r2, {r1 = r2} + {r1 <> r2}.
Proof.
intros r1 r2.
destruct (total_order_T r1 r2) as [[Hlt|Heq]|Hgt].
right; intro Hn; apply (Rlt_irrefl r2);
  rewrite Hn in Hlt; assumption.
left; assumption.
right; intros Hn; apply (Rlt_irrefl r2);
  rewrite Hn in Hgt; assumption.
Qed.

Lemma Req_or_neq : forall r, {r = 0} + {r <> 0}.
Proof.
intros r; exact (Req_dec r 0).
Qed.

Lemma Rneq_le_lt: forall x y, x <> y -> x <= y -> x < y.
Proof.
intros x y Hneq [] ; intuition.
Qed.

Lemma Rneq_lt_or_gt: forall x y, x <> y -> {x < y} + {y < x}.
Proof.
intros x y x_neq_y.
 destruct (Rle_lt_dec x y).
  left ; apply Rneq_le_lt ; assumption.
  right ; assumption.
Qed.

Lemma Rminus_opp : forall x y, x - - y = x + y.
Proof.
intros ; unfold Rminus ; rewrite Ropp_involutive ;
 reflexivity.
Qed.

Lemma Rplus_eq_compat_r : forall r r1 r2, r1 = r2 -> r1 + r = r2 + r.
Proof.
intros ; subst ; reflexivity.
Qed.

Lemma Rplus_eq_compat : forall r1 r2 r3 r4, r1 = r3 -> r2 = r4 -> r1 + r2 = r3 + r4.
Proof.
intros ; subst ; reflexivity.
Qed.

Lemma Rmult_eq_compat_r : forall r1 r2 r, r1 = r2 -> r1 * r = r2 * r.
Proof.
intros ; subst ; reflexivity.
Qed.

Lemma Rminus_eq_compat : forall r1 r2 r3 r4, r1 = r3 -> r2 = r4 ->
  r1 - r2 = r3 - r4.
Proof.
intros ; subst ; reflexivity.
Qed.

Lemma Rmult_eq_compat : forall r1 r2 r3 r4, r1 = r3 -> r2 = r4 ->
  r1 * r2 = r3 * r4.
Proof.
intros ; subst ; reflexivity.
Qed.

Lemma Rpow_eq_compat : forall a b d, a = b -> a ^ d = b ^ d.
Proof.
intros ; subst ; reflexivity.
Qed.

Lemma Rdiv_eq_compat: forall x y z, x = y -> x / z = y / z.
Proof.
intros ; subst ; reflexivity.
Qed.

Lemma Rplus_lt_simpl_l : forall r1 r2, 0 < r2 -> r1 < r1 + r2.
Proof.
intros ; lra.
Qed.

Lemma Rplus_lt_simpl_r : forall r1 r2, 0 < r1 -> r2 < r1 + r2.
Proof.
intros ; lra.
Qed.

Lemma Rplus_le_simpl_l : forall r1 r2, 0 <= r2 -> r1 <= r1 + r2.
Proof.
intros ; lra.
Qed.

Lemma Rplus_le_simpl_r : forall r1 r2, 0 <= r1 -> r2 <= r1 + r2.
Proof.
intros ; lra.
Qed.

Lemma Rmax_lt_lt_lt : forall x y z, Rmax x y < z <-> x < z /\ y < z.
Proof.
intros x y z ; unfold Rmax ; destruct (Rle_dec x y) ; split ; intuition.
 apply Rle_lt_trans with y ; assumption.
 transitivity x ; [apply Rnot_le_lt |] ; assumption.
Qed.

Lemma Rmax_le_le_le : forall x y z, Rmax x y <= z <-> x <= z /\ y <= z.
Proof.
intros x y z ; unfold Rmax ; destruct (Rle_dec x y) ; split ; intuition.
 transitivity y ; assumption.
 transitivity x ; [left ; apply Rnot_le_lt |] ; assumption.
Qed.

Lemma Rmin_lt_lt_lt : forall x y z, z < Rmin x y <-> z < x /\ z < y.
Proof.
intros x y z ; unfold Rmin ; destruct (Rle_dec x y) ; split ; intuition.
 apply Rlt_le_trans with x ; assumption.
 transitivity y ; [| apply Rnot_le_lt] ; assumption.
Qed.

Lemma Rmin_le_le_le : forall x y z, z <= Rmin x y <-> z <= x /\ z <= y.
Proof.
intros x y z ; unfold Rmin ; destruct (Rle_dec x y) ; split ; intuition.
 transitivity x ; assumption.
 transitivity y ; [| left ; apply Rnot_le_lt] ; assumption.
Qed.

Lemma Rle_neq_lt : forall x y, x <= y -> x <> y -> x < y.
Proof.
intros m n Hyp1 Hyp2 ; case Hyp1.
 intuition.
 intro Hfalse ; apply False_ind ; apply Hyp2 ; exact Hfalse.
Qed.

Lemma Rlt_1_mult_inv : forall  x y, 0 < y ->
  y < x -> 1 < x * / y.
intros x y y_pos y_lb ; apply Rle_lt_trans with (y * / y).
 right ; symmetry ; apply Rinv_r ; apply Rgt_not_eq ; assumption.
 apply Rmult_lt_compat_r ; [apply Rinv_0_lt_compat |] ; assumption.
Qed.

Lemma Rabs_pos_lt_contravar : forall x, 0 < Rabs x -> x <> 0.
Proof.
intros x Hpos ; destruct (Req_or_neq x) as [Heq | Hneq].
 rewrite Heq, Rabs_R0 in Hpos ; destruct (Rlt_irrefl _ Hpos).
 assumption.
Qed.

Lemma Rmult_Rinv_le_compat : forall x y z, 0 < y ->
  x <= y * z -> x * / y <= z.
Proof.
intros x y z y_pos Hle.
 apply Rle_trans with (y * z * / y).
 apply Rmult_le_compat_r.
  left ; apply Rinv_0_lt_compat ; assumption.
  assumption.
 right ; field ; apply Rgt_not_eq ; assumption.
Qed.

Lemma Rmult_Rinv_le_compat_contravar : forall x y z, 0 < y ->
 x * / y <= z -> x <= y * z.
Proof.
intros x y z y_pos Hle.
 apply Rle_trans with (y * (x * / y)).
  right ; field ; apply Rgt_not_eq ; assumption.
  apply Rmult_le_compat_l ; [left |] ; assumption.
Qed.

Lemma Rmult_minus_distr_r: forall x y z,
  (x - y) * z = x * z - y * z.
Proof.
intros ; ring.
Qed.

Lemma Rneq_lt_gt_dec : forall a b, a <> b -> { a < b } + { b < a }.
Proof.
intros a b ab_neq ; destruct (Rlt_le_dec a b).
 left ; assumption.
 right ; apply Rle_neq_lt ; [| symmetry] ; assumption.
Qed.

Lemma Rminus_lt_compat_r_rev : forall a b c : R, a - c < b -> a < b + c.
intros ; lra.
Qed.

Lemma Rminus_lt_compat : forall a b c, a < b -> a - c < b - c.
Proof.
intros ; lra.
Qed.

Lemma Rminus_lt_compat_rev : forall a b c, a - c < b - c -> a < b.
Proof.
intros ; lra.
Qed.

Lemma Rmult_Rdiv_lt_compat_l_rev: forall a b c : R, 0 < c -> a < b / c -> c * a < b.
Proof.
intros ; apply Rlt_le_trans with (c * (b / c))%R.
 apply Rmult_lt_compat_l ; assumption.
 right ; field ; apply Rgt_not_eq ; assumption.
Qed.

Lemma Rlt_minus_sort3: forall a b c : R, a - b < - c -> a + c < b.
Proof.
intros ; lra.
Qed.

Lemma dist_2_pos : forall lb ub, lb < ub -> (0 < (ub - lb) / 2)%R.
Proof.
intros lb ub lt ; lra.
Qed.
