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

(** * Real riemannian integrals *)

Require Import Reals.
Require Import RiemannInt.
Require Import RIneq.
Require Import Lra.
Require Import R_sqr.
Require Import MyRfunctions.
Local Open Scope R_scope.

(* begin hide *)

Lemma Rmin_def : forall a b, a <= b -> Rmin a b = a.
Proof.
intros a b Hab.
unfold Rmin.
destruct (Rle_dec a b); tauto.
Qed.

Lemma Rmax_def : forall a b, a <= b -> Rmax a b = b.
Proof.
intros a b Hab.
unfold Rmax.
destruct (Rle_dec a b); tauto.
Qed.

Lemma Rmax_le : forall a b c, a <= c -> b <= c -> Rmax a b <= c.
intros a b c H1 H2.
unfold Rmax.
case (Rle_dec a b); intro H.
 apply H2.
apply H1.
Qed.

Lemma Rmax_lt : forall a b c, a < c -> b < c -> Rmax a b < c.
Proof.
intros a b c H1 H2.
unfold Rmax.
case (Rle_dec a b); intro H.
 apply H2.
apply H1.
Qed.

Lemma Rmin_ge : forall a b c, c <= a -> c <= b -> c <= Rmin a b.
intros a b c H1 H2.
unfold Rmin.
case (Rle_dec a b); intro H.
 apply H1.
apply H2.
Qed.

(* end hide *)

(** * Definition of the integral of f between a and b using Riemann_integrable *)

Definition Rint f a b I := {pr : Riemann_integrable f a b | RiemannInt pr = I}.

(** * Common results on integrals *)

Section Rint_facts.

(** The integral from a to b is the opposite of the integral from b to a *)

Lemma Rint_reverse_1 : forall f a b x, Rint f a b  (-x) -> Rint f b a x.
Proof.
 intros f a b x [pr H]. pose proof RiemannInt_P1 pr as pr2.
 exists pr2;
assert(RiemannInt pr2 = - RiemannInt pr) as Hrew;
  [ apply RiemannInt_P8 | rewrite Hrew];
rewrite H; intuition.
Qed.

Lemma Rint_reverse_2 : forall f a b x, Rint f a b  x -> Rint f b a (-x).
Proof.
intros f a b x [pr H]. 
pose proof RiemannInt_P1 pr as pr2;
exists pr2;
assert(RiemannInt pr2 = - RiemannInt pr) as Hrew;
  [ apply RiemannInt_P8 | rewrite Hrew];
rewrite H; intuition.
Qed.

Lemma Riemann_integrable_eq_compat : forall f g a b, 
  (forall x, Rmin a b <= x <= Rmax a b -> g x = f x) -> 
    Riemann_integrable f a b -> 
      Riemann_integrable g a b.
Proof.
intros f g a b Heq prf;
case(Rle_dec a b); intro Hab;
  [ | apply RiemannInt_P1 in prf;
     apply RiemannInt_P1];
  intro eps; destruct (prf eps) as [phi [psi Hpsi]];
  [ | rewrite Rmin_comm, Rmax_comm in Heq ];
  exists phi; exists psi.
  split; [
  intros t Ht; rewrite Heq; [ apply Hpsi | apply Ht] ;
    apply Ht |
    apply Hpsi ] .
  split; [
  intros t Ht; rewrite Heq; [ apply Hpsi | apply Ht] ;
    apply Ht |
    apply Hpsi ] .
Qed.

Lemma Rint_eq_compat : forall f g a b x,
  (forall x, Rmin a b <= x <= Rmax a b -> g x = f x) -> 
    Rint f a b x -> Rint g a b x.
Proof.
intros f g a b x Heq.
case(Rle_dec a b); intros Hab.
intros [prf Hf].
pose proof (Riemann_integrable_eq_compat f g a b Heq prf) as prg.
exists prg.
erewrite RiemannInt_P18.
  apply Hf.
 apply Hab.
 rewrite (Rmin_def _ _ Hab), (Rmax_def _ _ Hab) in Heq.
 intuition.
rewrite Rmin_comm, Rmax_comm in Heq.
intro RIf.
apply Rint_reverse_1.
apply Rint_reverse_2 in RIf.
destruct RIf as [prf Hf].
pose proof (Riemann_integrable_eq_compat f g b a Heq prf) as prg.
exists prg.
apply Rnot_le_lt, Rlt_le in Hab.
erewrite RiemannInt_P18.
  apply Hf.
  apply Hab.
 rewrite (Rmin_def _ _ Hab), (Rmax_def _ _ Hab) in Heq.
 intuition.
Qed.

Lemma Rint_RiemannInt_link : forall f a b (pr : Riemann_integrable f a b), 
  Rint f a b (RiemannInt pr).
Proof.
intros f a b pr.
exists pr.
reflexivity.
Qed.

(** * Continuous functions are integrable *)

Lemma Rint_continuity : forall f a b, 
  a <= b ->
    (forall x, a <= x <= b -> continuity_pt f x) ->
  {x : R & (Rint f a b x)}.
Proof.
intros f a b Hab f_cont.
exists(RiemannInt (continuity_implies_RiemannInt Hab f_cont)).
apply Rint_RiemannInt_link.
Qed.

(** * Chasles relation on integrals *)

Lemma Rint_Chasles : forall f a b c x y,  
  Rint f a b x -> Rint f b c y -> Rint f a c (x+y).
Proof.
intros f a b c x y [prab Hab] [prbc Hbc].
pose proof (RiemannInt_P24  prab prbc) as prac.
exists prac.
rewrite <- Hab, <- Hbc.
symmetry.
apply RiemannInt_P26.
Qed.

Lemma Rint_singleton : forall f a, Rint f a a 0.
Proof.
intros f a.
pose proof RiemannInt_P7 f a as pr.
exists pr.
apply RiemannInt_P9.
Qed.

Lemma Rint_constant : forall c a b, Rint (fct_cte c) a b (c*(b-a)).
Proof.
intros c a b.
pose proof RiemannInt_P14 a b c as pr.
exists pr.
apply RiemannInt_P15.
Qed.

(** The value of the integral is unique *)

Lemma Rint_uniqueness : forall f a b x y, Rint f a b x -> Rint f a b y -> x = y.
Proof.
intros f a b x y [pr1 H1] [pr2 H2].
rewrite <- H1, <- H2.
apply RiemannInt_P5.
Qed.

Lemma Rint_subinterval : forall f a b c x, (a <= b <= c) ->
  Rint f a c  x -> {y : R & Rint f a b y & Rint f b c (x-y)}.
Proof.
intros f a b c x Hb [prac Hf].
pose proof RiemannInt_P22 prac Hb as prab.
exists (RiemannInt prab).
  apply Rint_RiemannInt_link.
pose proof RiemannInt_P23 prac Hb as prbc.
exists prbc.
rewrite <- Hf.
rewrite <- RiemannInt_P26 with _ _ _ _ prab prbc prac.
ring.
Qed.

End Rint_facts.


(** * Compatibility of integrals with operations *)

Section Rint_operations.

Lemma Rint_eq : forall x y f a b, Rint f a b x -> x = y -> Rint f a b y.
Proof.
 intros x y f a b H Heq.
 subst. apply H.
Qed.

Lemma Rint_plus : forall f g a b x y, Rint f a b x -> Rint g a b y -> Rint (f + g)%F a b (x + y).
Proof.
intros f g a b x y [prf Hf] [prg Hg]; unfold plus_fct.
apply Rint_eq_compat with (fun u => f u + 1 * g u).
  intros; ring.
replace (x+y) with (x+1*y) by ring.
pose proof RiemannInt_P10 1 prf prg as prfg.
exists prfg.
rewrite RiemannInt_P13 with _ _ _ _ _ prf prg prfg.
rewrite Hf, Hg; reflexivity.
Qed.

Lemma Rint_minus : forall f g a b x y, Rint f a b x -> Rint g a b y -> Rint (f - g)%F a b (x - y).
Proof.
intros f g a b x y [prf Hf] [prg Hg]; unfold minus_fct.
apply Rint_eq_compat with (fun u => f u + (-1) * g u).
  intros; ring.
replace (x - y) with (x+(-1)*y) by ring.
pose proof RiemannInt_P10 (-1) prf prg as prfg.
exists prfg.
rewrite RiemannInt_P13 with _ _ _ _ _ prf prg prfg.
rewrite Hf, Hg; reflexivity.
Qed.

Lemma Rint_opp1 : forall f a b x, Rint f a b x -> Rint (- f)%F a b (- x).
Proof.
intros f a b x; intros [prf Hf]; unfold opp_fct.
  apply Rint_eq_compat with (fun u => fct_cte 0 u + (-1) * f u).
    unfold fct_cte; intros; ring.
  replace (- x) with (0 + (-1)* x) by ring.
  pose proof Rint_constant 0 a b as [prg Hg].
  pose proof RiemannInt_P10 (-1) prg prf as prfg.
  exists prfg.
  rewrite RiemannInt_P13 with _ _ _ _ _ prg prf prfg.
  rewrite Hf, Hg; ring.
Qed.

Lemma Rint_opp2 : forall f a b x, Rint (-f)%F a b (- x) -> Rint f a b x.
Proof.
intros f a b x; intros [prf Hf]; unfold opp_fct.
apply Rint_eq_compat with (fun u => fct_cte 0 u + (-1) *(- f)%F u).
  unfold fct_cte, opp_fct; intros; ring.
replace (x) with (0 + (-1)*(- x)) by ring.
pose proof Rint_constant 0 a b as [prg Hg].
pose proof RiemannInt_P10 (-1) prg prf as prfg.
exists prfg.
rewrite RiemannInt_P13 with _ _ _ _ _ prg prf prfg.
rewrite Hf, Hg; ring.
Qed.

Lemma Rint_scalar_mult_compat_l : forall f a b x C, Rint f a b x -> Rint (fct_cte C * f)%F a b (C*x).
Proof.
intros f a b x C [prf Hf].
apply Rint_eq_compat with (fun u => fct_cte 0 u + C * f u).
    unfold fct_cte, mult_fct; intros; ring.
  replace (C * x) with (0 + C* x) by ring.
  pose proof Rint_constant 0 a b as [prg Hg].
  pose proof RiemannInt_P10 C prg prf as prfg.
  exists prfg.
  rewrite RiemannInt_P13 with _ _ _ _ _ prg prf prfg.
  rewrite Hf, Hg; ring.
Qed.

Lemma Rint_scalar_mult_compat_r : forall f a b x C, Rint f a b x -> Rint (f * fct_cte C)%F a b (x * C).
Proof.
intros f a b x C [prf Hf].
apply Rint_eq_compat with (fun u => fct_cte 0 u + C * f u).
    unfold fct_cte, mult_fct; intros; ring.
  replace (C * x) with (0 + C* x) by ring.
  pose proof Rint_constant 0 a b as [prg Hg].
  pose proof RiemannInt_P10 C prg prf as prfg.
  exists prfg.
  rewrite RiemannInt_P13 with _ _ _ _ _ prg prf prfg.
  rewrite Hf, Hg; ring.
Qed.

End Rint_operations.



Create HintDb Rint.

Hint Resolve Rint_reverse_2 : Rint.
Hint Resolve Rint_RiemannInt_link : Rint.
Hint Resolve Rint_Chasles : Rint.
Hint Resolve Rint_constant : Rint.
Hint Resolve Rint_plus : Rint.
Hint Resolve Rint_minus : Rint.
Hint Resolve Rint_opp1 : Rint.
Hint Resolve Rint_scalar_mult_compat_l : Rint.
Hint Resolve Rint_scalar_mult_compat_r : Rint.
Hint Resolve Rint_uniqueness : Rint.
Hint Resolve RiemannInt_P6 : Rint.
Hint Resolve RiemannInt_P7 : Rint.
Hint Resolve RiemannInt_P10 : Rint.
Hint Resolve RiemannInt_P14 : Rint.
Hint Resolve RiemannInt_P16 : Rint.

Section Rint_props.

(** * Inequalities involving integrals *)

Lemma Rint_le_compat : forall f g a b x y, 
  a <= b -> (forall u, a < u < b -> f u <= g u) ->
      Rint f a b x -> Rint g a b y ->  x <= y.
Proof.
intros f g a b x y Hab Heq [prh Hf] [prg Hg].
rewrite <-  Hf, <- Hg.
apply RiemannInt_P19.
  apply Hab.
apply Heq.
Qed.

(** A positive function has positive growing integral *)

Lemma Rint_pos : forall f a b x, 
  a <= b -> (forall u, a <= u <= b -> 0 <= f u) -> Rint f a b x -> 0 <= x.
Proof.
intros f a b x Hab Hpos Hf.
destruct(Rint_constant 0 a b) as [pr0 H0].
ring_simplify in H0.
apply Rint_le_compat with (fct_cte 0) f a b.
  apply Hab.
  intros u Hu; apply Hpos; intuition.
  exists pr0.
  apply H0.
apply Hf.
Qed.


(** Inequality between integral of the absolute value and 
 absolute value of the integral *)

Lemma Rint_abs_le_int : forall f a b x, 
  a <= b -> Rint f a b x -> 
    {y : R & (Rint (fun u => Rabs (f u)) a b y) & (Rabs x <= y)}.
Proof.
intros f a b x Hab [prf Hf].
pose proof RiemannInt_P16 prf as prabs.
exists (RiemannInt prabs).
  exists prabs.
  reflexivity.
rewrite <- Hf.
apply RiemannInt_P17.
apply Hab.
Qed.

(** A non always null, non negative, continuous function on a non trivial segment has positive integral *)

Lemma Rint_continuous_gt_0 : forall f a b u X,
  a < b ->
    a <= u <= b ->
      (forall x, a <= x <= b -> continuity_pt f x) ->
        (forall x, a <= x <= b -> 0 <= f x) ->
          f u <> 0 -> Rint f a b X -> 0 < X.
Proof.
intros f a b u X Hab Haub Hcont Hpos Hu HX.
destruct (continuous_neq_0 f u (Hcont u Haub) Hu) as [eps Heps].
assert(exists c, exists d, a <= c <= b /\ a <= d <= b /\ c < d /\ forall x, c <= x <= d -> 0 < f x).
  exists (Rmax a (u -eps/2)).
  exists (Rmin b (u+ eps/2)).
  assert(Heps2 : 0 < eps/2) .
    apply Rlt_mult_inv_pos.
      apply cond_pos.
      auto with *.
  repeat split.
    apply RmaxLess1.

    apply Rmax_le.
      left; apply Hab.

    apply Rle_trans with u; [lra | intuition].
    
    apply Rmin_ge.
      left; apply Hab.
    apply Rle_trans with u;  [intuition | lra].
    
    apply Rmin_l.
    
    case(Rle_lt_or_eq_dec a u(proj1 Haub)); intro Hau.
      apply Rlt_le_trans with u.
        apply Rmax_lt; [intuition | lra].
    apply Rmin_ge; [intuition | lra].
    subst.
    apply Rle_lt_trans with u.
      apply Rmax_le; lra.
    apply Rmin_2; lra.
  intros x Hx.
  rewrite <- Rabs_pos_eq.
    apply Rabs_pos_lt.
    replace x with (u+ (x-u)) by ring.
    apply (Heps (x-u)).
    assert( u - eps <  x < u + eps) as [ Hu1 Hu2].
    split.
      apply Rlt_le_trans with (Rmax a (u - eps/2)).
        apply Rlt_le_trans with (u-eps/2).
          lra.
        apply RmaxLess2.
        apply Hx.
      apply Rle_lt_trans with (Rmin b (u + eps/2)).
        apply Hx.
      apply Rle_lt_trans with (u + eps/2).
        apply Rmin_r.
      lra.
    apply Rabs_def1; lra.        
  apply Hpos.
  split.
    eapply Rle_trans.
      apply RmaxLess1.
      apply (proj1 Hx).
    eapply Rle_trans.
      apply (proj2 Hx).
      apply Rmin_l.    
destruct H as [c [d [ Hacb [Hadb [Hcd Hstp]]]]].
destruct (Rint_subinterval _ _ _ _ _ Hacb HX) as [Y HY HZ'].
assert(c <= d<=b) as Hcdb by intuition.
destruct (Rint_subinterval _ _ _ _ _ Hcdb HZ') as [T HV HT'].
destruct (continuity_ab_min f c d) as [m Hm].
 apply Hcdb.

 intros x Hcxd.
 apply Hcont.
 split; eapply Rle_trans; [apply Hacb | apply Hcxd | apply Hcxd | apply Hadb].
apply Rlt_le_trans with ((f m) * (d - c)).
 apply Rmult_lt_0_compat; [apply Hstp; apply Hm | lra].
apply Rle_trans with T.
 apply Rint_le_compat with (fct_cte (f m)) f c d.
  apply Hcdb.

  intros; apply Hm; split; apply Rlt_le; apply H.

  apply Rint_constant.

  apply HV.
apply Rle_trans with (X - Y).
  assert(Hcbpos : forall x : R, c <= x <= b -> 0 <= f x).
    intros x [H1 H2]; apply Hpos; split;[apply Rle_trans with c| ]; intuition.
    pose proof (Rint_pos _ _ _ _ (proj2 Hacb) Hcbpos HZ') as H.
  assert(0 <= X - Y - T).
    assert(Hdbpos : forall x : R, d <= x <= b -> 0 <= f x).
      intros x [H1 H2]; apply Hpos; split;[apply Rle_trans with d| ]; intuition.
    apply (Rint_pos _ _ _ _ (proj2 Hadb) Hdbpos HT').
  lra.
assert(Hacpos : forall x : R, a <= x <= c -> 0 <= f x).
  intros x [H1 H2]; apply Hpos; split; [ | apply Rle_trans with c]; intuition.
pose proof (Rint_pos _ _ _ _ (proj1 Hacb) Hacpos HY) as H.
  assert(0 <= X - Y - T).
    assert(Hdbpos : forall x : R, d <= x <= b -> 0 <= f x).
      intros x [H1 H2]; apply Hpos; split;[apply Rle_trans with d| ]; intuition.
    apply (Rint_pos _ _ _ _ (proj2 Hadb) Hdbpos HT').
  lra.
Qed.

(** A non negative function with null integral in a non trivial segment is null on it *)

Lemma Rint_continuous_pos_eq_0 : forall f a b,
  a < b ->
    (forall x, a <= x <= b -> continuity_pt f x) ->
      (forall x, a <= x <= b -> 0 <= f x) ->
      Rint f a b 0 -> (forall x, a <= x <= b -> f x = 0).
Proof.
intros f a b Hab Hcont Hpos Hint x Hx.
case (Req_dec (f x) 0); intro Hcase.
  apply Hcase.
pose proof Rint_continuous_gt_0 _ _ _ _ 0 Hab Hx Hcont Hpos Hcase Hint as pr.
exact (False_ind _ (Rlt_irrefl 0 pr)).
Qed.

(* begin hide *)
Lemma Rsqr_eq_0_reg : forall a, a * a = 0 -> a = 0.
Proof.
intros a Haa.
destruct (total_order_T a 0) as [[|]|]; subst; trivial;
 (cut (0 < a * a); [intro; apply False_ind; apply (Rlt_not_eq _ _ H); auto|]);
 [replace (a * a) with (- a * - a) by ring|];
 apply Rmult_lt_0_compat; lra.
Qed.

(* end hide *)

(** Cauchy-Schwarz's theorem for integrals *)

Lemma Rint_Cauchy_Schwarz : forall f g a b x y z,
  a <= b -> 
    (forall x, a <= x <= b -> continuity_pt f x) ->
      (forall x, a <= x <= b -> continuity_pt g x) ->
      Rint (f * f)%F a b x -> Rint (g * g)%F a b y -> Rint (f * g)%F a b z ->
      z^2 <= x * y.
Proof.
intros f g a b x y z Hle Hfc Hgc Hf Hg Hfg.
assert (H0 : {y = 0} + {y <> 0}).
  destruct (total_order_T y 0) as [[H|H]|H].
    right; apply Rlt_not_eq; assumption.
    left; assumption.
    right; apply Rgt_not_eq; assumption.
destruct H0 as [H0|H0].
assert (Hz : z = 0).
 destruct (Rle_lt_or_eq_dec a b Hle); [|
   subst; apply (Rint_uniqueness (f * g)%F b b z 0 Hfg
     (Rint_singleton (f * g)%F b))].
 eapply Rint_uniqueness; [apply Hfg|].
 eapply Rint_eq_compat with (fun _ => 0).
  intros.
  unfold mult_fct.
  apply Rmult_eq_0_compat_l.
  apply Rsqr_eq_0_reg.
  replace (g x0 * g x0) with ((g * g)%F x0) by auto.
  replace (Rmin a b) with a in * by (symmetry; apply Rmin_def; apply Hle).
  replace (Rmax a b) with b in * by (symmetry; apply Rmax_def; apply Hle).
  apply Rint_continuous_pos_eq_0 with a b; auto.
   intros; apply continuity_pt_mult; apply Hgc; assumption.
   intros; apply Rle_0_sqr.
   subst; assumption.
  pose (fun _:R => 0) as null; fold null.
  replace 0 with (0 * (b - a)) by ring.
  apply Rint_constant.
subst y; subst z.
  repeat rewrite Rmult_0_r.
  rewrite pow_ne_zero; auto with *.
assert (Hy : 0 <= y).
  eapply Rint_pos with (f := (g * g)%F).
    eexact Hle.
    intros u Hu; apply Rle_0_sqr.
    assumption.
pose (F k x := (f x - k * g x)²).
assert (Hpos : forall k i, Rint (F k) a b i -> 0 <= i).
  intros k i H.
  eapply Rint_pos with (f := F k).
    eexact Hle.
    intros u Hu; apply Rle_0_sqr.
    assumption.
assert (Heq : forall k, Rint (F k) a b (x - 2 * k * z + k² * y)).
  intros k.
    apply Rint_eq_compat with (f := ((f * f) - (fct_cte (2 * k)) * (f * g) + (fct_cte k² )* (g * g))%F).
    intros; unfold fct_cte, F, plus_fct, mult_fct, minus_fct, Rsqr; ring.
    auto with Rint.
assert (Hcs : 0 <= x - z² / y).
  eapply Hpos.
  replace (x - z² / y) with (x - 2 * (z / y) * z + (z / y)² * y).
  apply Heq.
  unfold Rsqr; field; assumption.
apply Rle_ge in Hcs; apply Rminus_ge in Hcs; apply Rge_le in Hcs.
apply Rmult_le_compat_r with (r := y) in Hcs; [|assumption].
replace (z² / y * y) with z² in Hcs by (field; assumption).
unfold Rsqr in Hcs.
ring_simplify in Hcs.
apply Hcs.
Qed.

(** Fundamental theorem of real analysis *)

Lemma Rint_derive : forall f a b d, 
  a <= b -> 
  (forall x, a <= x <= b -> derivable_pt_abs f x (d x)) ->
  (forall x, a <= x <= b -> continuity_pt d x) ->
  Rint d a b (f b - f a).
Proof.
intros f a b d Hab Hder Hcont.
pose proof prolongement_C1_C1 f d a b Hab Hder Hcont as [g [Heq Hdeq]].
apply Rint_eq_compat with (derive g (diff0 g)).
  rewrite Rmin_def, Rmax_def; assumption.
exists (RiemannInt_P32 g a b).
rewrite RiemannInt_P33; intuition.
do 2 (rewrite Heq; intuition).
Qed.

Lemma Rint_derive2 : forall f a b d,
  (forall x, Rmin a b <= x <= Rmax a b -> derivable_pt_abs f x (d x)) ->
  (forall x, Rmin a b <= x <= Rmax a b -> continuity_pt d x) ->
  Rint d a b (f b - f a).
Proof.
intros f a b d Hder Hcont.
destruct (Rle_dec a b) as [n|n].
 rewrite Rmin_def, Rmax_def in *; try assumption.
apply Rint_derive; assumption.
apply Rnot_le_lt, Rlt_le in n.
  rewrite Rmin_comm, Rmax_comm, Rmin_def, Rmax_def  in *; try assumption.
apply Rint_reverse_1; replace (- (f b - f a)) with (f a - f b) by ring.
apply Rint_derive; assumption.
Qed.

(** Integration by parts *)

Lemma Rint_parts : forall f g a b f' g' Ifg' If'g,
a <= b ->
  (forall x : R, a <= x <= b -> derivable_pt_lim f x (f' x)) ->
  (forall x : R, a <= x <= b -> derivable_pt_lim g x (g' x)) ->
    (forall x : R, a <= x <= b -> continuity_pt f' x) ->
    (forall x : R, a <= x <= b -> continuity_pt g' x) ->
      Rint (f * g')%F a b Ifg' -> Rint (f' * g)%F a b If'g ->
        Ifg' = f b * g b - f a * g a - If'g.
Proof.
intros f g a b f' g' Ifg' If'g Hab Hderf Hderg Hcontf' Hcontg' Hfg' Hf'g.
assert (H : forall a b c, a + b = c -> a = c - b) by (intros; subst; ring);
apply H; clear H.
apply Rint_uniqueness with (f * g' + f' * g)%F a b.
  apply Rint_plus; assumption.
replace (f b * g b - f a * g a) with ((f * g)%F b - (f * g)%F a) by reflexivity.

apply Rint_derive.
  assumption.
  
  intros; unfold mult_fct, plus_fct; rewrite Rplus_comm;
  apply derivable_pt_lim_mult; intuition.

  intros; apply continuity_pt_plus;
  apply continuity_pt_mult; try intuition;
    apply derivable_continuous_pt.
    exists (f' x); apply Hderf; intuition.
    exists (g' x); apply Hderg; intuition.
Qed.

(** Variable change theorem *)

Lemma Rint_substitution : forall f g g' a b I,
  a <= b -> (forall x, a <= x <= b -> g a <= g x <= g b) ->
  (forall x, g a <= x <= g b -> continuity_pt f x) ->
  (forall x, a <= x <= b -> derivable_pt_lim g x (g' x)) ->
  (forall x, a <= x <= b -> continuity_pt g' x) ->
  Rint (fun x => f (g x) * g' x) a b I ->
  Rint f (g a) (g b) I.
Proof.
intros f g g' a b I Hab Habgab Hcontf Hder Hcontg' HI.
 destruct (Habgab a) as [_ Hgab]; auto with *.

assert (Hpr : forall x : R, g a <= x -> x <= g b -> Riemann_integrable f (g a) x).
 intros.
 apply continuity_implies_RiemannInt; trivial.
 intros; apply Hcontf; split.
 tauto.
 apply Rle_trans with x; intuition; trivial.

pose (primitive Hgab (FTC_P1 Hgab Hcontf)) as F.

assert(Hfab : Riemann_integrable f (g a) (g b)).
 apply Hpr; auto with *.

assert(HF := RiemannInt_P20 Hgab (FTC_P1 Hgab Hcontf) Hfab).

assert(Heq : Rint f (g a) (g b) (F(g b) - (F(g a)))).
 unfold F; rewrite <- HF.
 apply Rint_RiemannInt_link.
replace I with (comp F g b - comp F g a).
apply Heq.

symmetry.
eapply Rint_uniqueness.
 apply HI.

 apply Rint_derive.
  trivial.
  intros.
  apply derivable_pt_lim_comp.
   auto.
   apply RiemannInt_P28; auto.
 
 intros.
 apply continuity_pt_mult.
  apply continuity_pt_comp.
   apply derivable_continuous_pt.
   exists (g' x); apply Hder; apply H.

  auto.

auto.
Qed.

End Rint_props.
