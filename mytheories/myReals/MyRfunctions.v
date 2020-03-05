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
Require Import Lra.
Require Export Rfunctions.


Open Scope R_scope.

(** Power *)

Lemma Rpow_mult_distr : forall x y n, (x * y) ^ n = x ^ n * y ^ n.
Proof.
intros x y n; induction n; simpl.
 field.
 repeat (rewrite Rmult_assoc); apply Rmult_eq_compat_l.
 rewrite IHn; field.
Qed.

(** Distance *) 

Lemma R_dist_ge_l : forall x y z, R_dist x y <= z -> Rabs x <= Rabs y + z.
Proof.
unfold R_dist; unfold Rabs.
intros x y z H.
repeat destruct Rcase_abs; lra.
Qed.

Lemma R_dist_gt_l : forall x y z, R_dist x y < z -> Rabs x < Rabs y + z.
Proof.
unfold R_dist; unfold Rabs.
intros x y z H.
repeat destruct Rcase_abs; lra.
Qed.

Lemma R_dist_ge_r : forall x y z, R_dist x y <= z -> Rabs y - z <= Rabs x.
Proof.
unfold R_dist; unfold Rabs.
intros x y z H.
repeat destruct Rcase_abs; lra.
Qed.

Lemma R_dist_gt_r : forall x y z, R_dist x y < z -> Rabs y - z < Rabs x.
Proof. 
unfold R_dist; unfold Rabs.
intros x y z H.
repeat destruct Rcase_abs; lra.
Qed.

Lemma continuity_pt_constant : forall c x, continuity_pt (fct_cte c) x.
Proof.
intros c x ; apply continuity_const.
intros u y; reflexivity.
Qed.

Lemma continuity_constant : forall c, continuity (fct_cte c).
Proof.
intro c; apply continuity_const.
intros x y; reflexivity.
Qed.

(** C1 continuation of a C1 function on a segment *)
 
Section Rint_C1.

Definition C1_continuation f a b d:= 
fun x : R => 
 if Rlt_dec x a then d a * (x - a) + f a 
 else if Rle_dec x b then f x else d b * (x - b) + f b .

Definition C1_continuation_derive d a b : R -> R :=
fun x : R =>  
  if Rlt_dec x a then d a 
  else if Rle_dec x b then d x else d b.

Lemma C1_continuation_eq : forall f a b d x, 
  a <= x <= b -> C1_continuation f a b d x = f x.
Proof.
intros f a b d x Hx.
unfold C1_continuation.
destruct (Rlt_dec x a).
  apply False_ind; apply (Rlt_not_le _ _ r), (proj1 Hx).

  destruct (Rle_dec x b).
    reflexivity.
  
    apply False_ind, n0, (proj2 Hx).
Qed.

Lemma C1_continuation_derive_eq : forall a b d x, 
  a <= x <= b -> C1_continuation_derive d a b x = d x.
Proof.
intros a b d x Hx.
unfold C1_continuation_derive.
destruct (Rlt_dec x a).
  apply False_ind; apply (Rlt_not_le _ _ r), (proj1 Hx).

  destruct (Rle_dec x b).
    reflexivity.
  
    apply False_ind, n0, (proj2 Hx).
Qed.

Lemma prolongement_C1_derivable : forall (f d : R -> R) (a b : R),
  a <= b ->
  (forall c, a <= c <= b -> derivable_pt_abs f c (d c)) ->
  { derg | forall x, derive (C1_continuation f a b d) derg x =
               C1_continuation_derive d a b x}.
(*         (forall c : R, a <= c <= b -> g c = f c) /\ 
         (forall c : R, a <= c <= b -> derive g derg c = d c). *)
Proof.
intros f d a b Hab Hder.
assert (Hrew : forall c u v, v <> 0 -> (c * (u + v - u) + f u - f u) / v - d u = c - d u) 
  by ( intros; field; assumption).
        
assert (Hrew2 : forall u x h z, h <> 0 -> ((u * (x + h - z) + f z -(u * (x - z) + f z)) / h - u) = 0) by
    (intros; field; assumption).
assert(forall x, derivable_pt_abs (C1_continuation f a b d) x (C1_continuation_derive d a b x)).
  intro x.
  unfold C1_continuation, C1_continuation_derive, derivable_pt_abs, derivable_pt_lim.
  destruct (Rlt_dec x a) as [Hxa | Hax].
    (* x < a *)	
    destruct (Rle_dec x b) as [Hxb | Hxb].
    intros eps Heps.
    exists (mkposreal (a-x) (Rgt_minus _ _ Hxa)).
    intros h hneq Hcond.
    destruct(Rlt_dec (x+h) a) as [Hxha | Hxha].
    rewrite Hrew2, Rabs_R0; assumption; apply Heps.
    
    apply False_ind, Hxha.
    apply Rle_lt_trans with (x+ Rabs h).
      apply Rplus_le_compat_l.
      apply RRle_abs.
    replace a with (x + a + -x) by ring.
    rewrite Rplus_assoc; apply Rplus_lt_compat_l.
    apply Hcond.
    
    apply False_ind, Hxb.
    apply Rle_trans with a; intuition.
    destruct (Rle_dec x b) as [Hxb | Hxb].
      (* a <= x <= b *)	
      intros eps Heps.
      apply Rnot_lt_le in Hax.
      assert (Hx : a <= x <= b) by (split;assumption). 
      destruct (Hder x Hx eps Heps) as [delta Hdelta].
      destruct Hxb as [Hxb | Hxb]. 
        destruct Hax as [Hax |Hax]. (* a < x < b *)       
        assert (0 < Rmin delta (Rmin (b-x) (x - a))) as Hposreal.
          apply Rmin_pos.
            apply cond_pos.
            apply Rmin_pos; lra.
        exists (mkposreal _ Hposreal).
        intros h hneq Hcond.
      destruct(Rlt_dec (x+h) a) as [Hxha | Hxha].
      apply False_ind; apply (Rlt_not_le _ _ Hxha).
      assert(- h < x - a) as Hf.
        apply Rle_lt_trans with (Rabs h).
          rewrite <- Rabs_Ropp; apply RRle_abs.
    
          apply Rlt_le_trans with (Rmin (b - x) (x - a)).
            apply (proj2 ((Rmin_Rgt_l delta (Rmin (b - x) (x - a)) (Rabs h) Hcond))).
            apply Rmin_r.
          lra.
      destruct (Rle_dec (x+h) b) as [Hxhb | Hxhb].
        apply (Hdelta _ hneq).
        apply (proj1 (Rmin_Rgt_l delta _ _ Hcond)).

        apply False_ind, Hxhb.
        replace b with (x + (b - x)) by ring.
        apply Rplus_le_compat_l.
        apply Rle_trans with (Rabs h).
          apply RRle_abs.
          apply Rle_trans with (Rmin (b - x) (x - a)).
            left; apply (proj2 ((Rmin_Rgt_l delta _ (Rabs h) Hcond))).
            apply Rmin_l.
        
        subst x. (* x = a *)
        assert( Hposreal : 0 < Rmin delta (b-a)).
            apply Rmin_pos.
            apply cond_pos.
            lra.
        exists (mkposreal _ Hposreal).
        intros h hneq Hcond.
        destruct (Rlt_dec (a + h) a) as [Hah | Hah].
        rewrite Hrew.
        ring_simplify (d a - d a).
        rewrite Rabs_R0; apply Heps.
        apply hneq.
          destruct(Rle_dec (a+h) b) as [Hh | Hh].
            apply (Hdelta h hneq).
              apply Rlt_le_trans with (Rmin delta (b-a)).
                apply Hcond.
                apply Rmin_l.
            apply False_ind, Hh.
            replace b with (a + (b-a)) by ring.
            apply Rplus_le_compat_l.
            apply Rle_trans with (Rabs h).              
              apply RRle_abs.
              apply Rle_trans with (Rmin delta (b-a)).
                left; apply Hcond.
                apply Rmin_r.

        subst x. (* x = b *)
        destruct Hax as [Hax | Hax].
        assert( Hposreal : 0 < Rmin delta (b-a)).
            apply Rmin_pos.
            apply cond_pos.
            lra.
        exists (mkposreal _ Hposreal).
        intros h hneq Hcond.
        destruct (Rlt_dec (b + h) a) as [Hbh | Hbh].
        apply False_ind, (Rlt_not_le _ _ Hbh).
        assert(- h <= b - a) as Hf.
          apply Rle_trans with (Rabs h).
            rewrite <- Rabs_Ropp; apply RRle_abs.
            apply Rle_trans with (Rmin delta (b - a)).
              intuition. 
              apply Rmin_r.
        lra.
        
        destruct(Rle_dec (b+h) b) as [Hh | Hh].
          apply (Hdelta h hneq).
          apply Rlt_le_trans with (Rmin delta (b - a)).
          apply Hcond.
          apply Rmin_l.
          rewrite Hrew.
          ring_simplify ( d b - d b).
          rewrite Rabs_R0; apply Heps.
          apply hneq.
          
            subst b. (* a = x = b *)
            exists delta.
            intros h hneq Hcond.
            destruct(Rlt_dec (a+h) a).
            
            rewrite Hrew.
          ring_simplify ( d a - d a).
          rewrite Rabs_R0; apply Heps.
          apply hneq.
          
          destruct (Rle_dec (a+h) a) as [Hh | Hh].
            intuition.
            rewrite Hrew.
          ring_simplify ( d a - d a).
          rewrite Rabs_R0; apply Heps.
          apply hneq.
          
    (* b < x *)	
    destruct (Rle_dec x b).
    intros eps Heps.
    apply Rnot_le_lt in Hxb.
    exists (mkposreal (x - b) (Rgt_minus _ _ Hxb)).
    intros h hneq Hcond.
    destruct(Rlt_dec (x+h) a) as [Hxha | Hxha].
      apply False_ind, (RIneq.Rle_not_lt _ _ Hab).
      apply Rlt_le_trans with (x+h).
        assert(- h <= x - b) as Hf.
          apply Rle_trans with (Rabs h).
            rewrite <- Rabs_Ropp; apply RRle_abs.
              intuition.
        lra.
        intuition.      
        
    destruct (Rle_dec (x + h) b) as [Hh | Hh].
      apply False_ind, (RIneq.Rle_not_lt _ _ Hh).
        assert(- h <= x - b) as Hf.
          apply Rle_trans with (Rabs h).
            rewrite <- Rabs_Ropp; apply RRle_abs.
              intuition.
        lra.
        
        rewrite Hrew2, Rabs_R0; assumption; apply Heps.
  intros eps Heps.
  
  apply Rnot_le_lt in Hxb.
  exists (mkposreal (x - b) (Rgt_minus _ _ Hxb)).
  intros h hneq Hcond.
  destruct(Rlt_dec (x+h) a) as [Hxha | Hxha].
    apply False_ind, (RIneq.Rle_not_lt _ _ Hab).
    apply Rlt_le_trans with (x+h).
      assert(- h <= x - b) as Hf.
        apply Rle_trans with (Rabs h).
          rewrite <- Rabs_Ropp; apply RRle_abs.
          intuition.
        lra.
        intuition.      
        
    destruct (Rle_dec (x + h) b) as [Hh | Hh].
      apply False_ind, (RIneq.Rle_not_lt _ _ Hh).
        assert(- h < x - b) as Hf.
          apply Rle_lt_trans with (Rabs h).
            rewrite <- Rabs_Ropp; apply RRle_abs.
              intuition.
        lra.
  
  rewrite Hrew2, Rabs_R0; assumption.
assert(derivable (C1_continuation f a b d)) as der_c by
(intro x; exists (C1_continuation_derive d a b x); apply H).
exists der_c.
intro x.
unfold derive.
apply uniqueness_limite with (C1_continuation f a b d) x.
  eapply derive_pt_eq_1.
  reflexivity.

  apply H.
Qed.

Lemma C0_sticking_one_pt : forall f gl gr a, 
  continuity gl -> continuity gr ->
  (forall x, x <= a -> f x = gl x) ->
  (forall x, a <= x -> f x = gr x) ->
  continuity f.
Proof.
intros f gl gr a Hl Hr Hfl Hfr x.
destruct (Rtotal_order x a).

intros eps Heps.
destruct (Hl x eps); try assumption.
destruct H0.
destruct (Rlt_dec x0 (a - x)).
exists x0; split; try assumption.
intro.
destruct (Rlt_dec a x1).
intros.
assert False; try contradiction.
apply (Rgt_asym a x1); try assumption.
destruct H2; simpl in H3; unfold R_dist in H3.
assert ((x1 - x) <= Rabs (x1 - x)) by apply RRle_abs.
lra.
repeat rewrite Hfl.
apply (H1 x1). lra.
apply Rnot_lt_le; assumption.


apply Rnot_lt_le in n.
exists (a - x); split; try lra.
intro.
destruct (Rlt_dec a x1).
intros.
assert False; try contradiction.
apply (Rgt_asym a x1); try assumption.
destruct H2; simpl in H3; unfold R_dist in H3.
assert ((x1 - x) <= Rabs (x1 - x)) by apply RRle_abs.
lra.
assert (D_x no_cond x x1 /\ dist R_met x1 x < x0 ->
    dist R_met (gl x1) (gl x) < eps) by (exact (H1 x1)).
apply Rnot_lt_le in n0.
repeat rewrite Hfl; try lra.
intros; destruct H3.
apply H2.
split; try assumption.
lra.

destruct H.
intros eps Heps.
rewrite H in |-*; clear x H.
destruct (Hl a eps); try assumption.
destruct (Hr a eps); try assumption.
destruct H; destruct H0.
exists (Rmin x x0); split.
apply Rmin_pos; assumption.
intro x1; destruct (Rlt_dec x1 a).
repeat rewrite Hfl; try lra.
assert (D_x no_cond a x1 /\ dist R_met x1 a < x ->
    dist R_met (gl x1) (gl a) < eps) by (exact (H1 x1)).
intros; destruct H4.
apply H3.
split; try assumption.
assert (Rmin x x0 <= x) by exact (Rmin_l x x0).
lra.
apply Rnot_lt_le in n.
repeat rewrite Hfr; try lra.
assert (D_x no_cond a x1 /\ dist R_met x1 a < x0 ->
    dist R_met (gr x1) (gr a) < eps) by (exact (H2 x1)).
intros; destruct H4.
apply H3.
split; try assumption.
assert (Rmin x x0 <= x0) by exact (Rmin_r x x0).
lra.

intros eps Heps.
destruct (Hr x eps); try assumption.
destruct H0.
destruct (Rlt_dec x0 (x - a)).
exists x0; split; try assumption.
intro.
destruct (Rlt_dec x1 a).
intros.
assert False; try contradiction.
apply (Rgt_asym a x1); try assumption.
destruct H2; simpl in H3; unfold R_dist in H3.
assert (x - x1 <= Rabs (x1 - x)).
rewrite Rabs_minus_sym; apply RRle_abs.
lra.
repeat rewrite Hfr.
apply (H1 x1). lra.
apply Rnot_lt_le; assumption.

exists (x - a); split; try lra.
intro.
destruct (Rlt_dec x1 a).
intros.
assert False; try contradiction.
apply (Rgt_asym a x1); try assumption.
destruct H2; simpl in H3; unfold R_dist in H3.
assert (x - x1 <= Rabs (x1 - x)).
rewrite Rabs_minus_sym; apply RRle_abs.
lra.
apply Rnot_lt_le in n0.
repeat rewrite Hfr; try lra.
apply Rnot_lt_le in n.
assert (D_x no_cond x x1 /\ dist R_met x1 x < x0 ->
    dist R_met (gr x1) (gr x) < eps) by (exact (H1 x1)).
intros; destruct H3.
apply H2.
split; try assumption.
lra.
Qed.


Lemma C0_sticking_one_pt_strong : forall f gl gr a, 
  (forall x, x <= a -> continuity_pt gl x) ->
  (forall x, a <= x -> continuity_pt gr x) ->
  (forall x, x <= a -> f x = gl x) ->
  (forall x, a <= x -> f x = gr x) ->
  continuity f.
Proof.
intros f gl gr a Hl Hr Hfl Hfr x.
destruct (Rtotal_order x a) as [|[]].
 intros eps Heps.
 destruct (Hl x (Rlt_le _ _ H) eps); try assumption.
 destruct H0.
 destruct (Rlt_dec x0 (a - x)).
  exists x0; split; try assumption.
  intro.
  destruct (Rlt_dec a x1).
  intros.
  assert False; try contradiction.
  apply (Rgt_asym a x1); try assumption.
  destruct H2; simpl in H3; unfold R_dist in H3.
  assert ((x1 - x) <= Rabs (x1 - x)) by apply RRle_abs.
  lra.
  repeat rewrite Hfl.
  apply (H1 x1). lra.
  apply Rnot_lt_le; assumption.
  
  apply Rnot_lt_le in n.
  exists (a - x); split; try lra.
  intro.
  destruct (Rlt_dec a x1).
  intros.
  assert False; try contradiction.
  apply (Rgt_asym a x1); try assumption.
  destruct H2; simpl in H3; unfold R_dist in H3.
  assert ((x1 - x) <= Rabs (x1 - x)) by apply RRle_abs.
  lra.
  assert (D_x no_cond x x1 /\ dist R_met x1 x < x0 ->
    dist R_met (gl x1) (gl x) < eps) by (exact (H1 x1)).
  apply Rnot_lt_le in n0.
  repeat rewrite Hfl; try lra.
  intros; destruct H3.
  apply H2.
  split; try assumption.
  lra.
 
 intros eps Heps.
 rewrite H in |-*; clear H x.
 destruct (Hl a (Rle_refl a) eps); try assumption.
 destruct (Hr a (Rle_refl a) eps); try assumption.
 destruct H; destruct H0.
 exists (Rmin x x0); split.
 apply Rmin_pos; assumption.
 intro x1; destruct (Rlt_dec x1 a).
 repeat rewrite Hfl; try lra.
 assert (D_x no_cond a x1 /\ dist R_met x1 a < x ->
   dist R_met (gl x1) (gl a) < eps) by (exact (H1 x1)).
 intros; destruct H4.
 apply H3.
 split; try assumption.
 assert (Rmin x x0 <= x) by exact (Rmin_l x x0).
 lra.
 apply Rnot_lt_le in n.
 repeat rewrite Hfr; try lra.
 assert (D_x no_cond a x1 /\ dist R_met x1 a < x0 ->
   dist R_met (gr x1) (gr a) < eps) by (exact (H2 x1)).
 intros; destruct H4.
 apply H3.
 split; try assumption.
 assert (Rmin x x0 <= x0) by exact (Rmin_r x x0).
 lra.

 intros eps Heps.
 destruct (Hr x (Rlt_le _ _ H) eps); try assumption.
 destruct H0.
 destruct (Rlt_dec x0 (x - a)).
  exists x0; split; try assumption.
  intro.
  destruct (Rlt_dec x1 a).
  intros.
  assert False; try contradiction.
  apply (Rgt_asym a x1); try assumption.
  destruct H2; simpl in H3; unfold R_dist in H3.
  assert (x - x1 <= Rabs (x1 - x)).
  rewrite Rabs_minus_sym; apply RRle_abs.
  lra.
  repeat rewrite Hfr.
  apply (H1 x1). lra.
  apply Rnot_lt_le; assumption.
  
  exists (x - a); split; try lra.
  intro.
  destruct (Rlt_dec x1 a).
  intros.
  assert False; try contradiction.
  apply (Rgt_asym a x1); try assumption.
  destruct H2; simpl in H3; unfold R_dist in H3.
  assert (x - x1 <= Rabs (x1 - x)).
  rewrite Rabs_minus_sym; apply RRle_abs.
  lra.
  apply Rnot_lt_le in n0.
  repeat rewrite Hfr; try lra.
  apply Rnot_lt_le in n.
  assert (D_x no_cond x x1 /\ dist R_met x1 x < x0 ->
    dist R_met (gr x1) (gr x) < eps) by (exact (H1 x1)).
  intros; destruct H3.
  apply H2.
  split; auto.
  lra.
Qed.

Lemma C0_sticking_two_pt : forall f gl gc gr a b,
  a <= b  ->
  continuity gl ->
  (forall x, a <= x <= b -> continuity_pt gc x) ->
  continuity gr ->
  (forall x, x <= a -> f x = gl x) ->
  (forall x, a <= x <= b -> f x = gc x) ->
  (forall x, b <= x -> f x = gr x) ->
  continuity f.
Proof.
intros f gl gc gr a b Hab Hl Hc Hr Hfl Hfc Hfr x.
destruct ((Rle_lt_or_eq_dec a b) Hab).
destruct (Rtotal_order x a).

(* x < a *)
intros eps Heps.
destruct (Hl x eps); try assumption.
destruct H0.
exists (Rmin x0 (a-x)); split.
repeat (apply Rmin_pos); lra.
intro.
destruct (Rlt_dec a x1).
intros.
assert False; try contradiction.
apply (Rgt_asym a x1); try assumption.
destruct H2; simpl in H3; unfold R_dist in H3.
assert ((x1 - x) <= Rabs (x1 - x)) by apply RRle_abs.
assert (Rmin x0 (a - x) <= a - x) by exact (Rmin_r x0 (a - x)).
lra.
apply Rnot_lt_le in n.
repeat rewrite Hfl; try lra.
assert (D_x no_cond x x1 /\ dist R_met x1 x < x0 ->
    dist R_met (gl x1) (gl x) < eps) by (exact (H1 x1)).
intros; destruct H3.
apply H2.
split; try assumption.
assert (Rmin x0 (a - x) <= x0) by exact (Rmin_l x0 (a - x)).
lra.

(* x = a, x1 < a *)
destruct H.
rewrite H in |-*; clear x H.
intros eps Heps.
destruct (Hl a eps); try assumption.
destruct (Hc a (conj (Rle_refl a) (Rlt_le _ _ r)) eps); try assumption.
destruct H; destruct H0.
exists (Rmin x (Rmin x0 (b-a))); split.
repeat (apply Rmin_pos); lra.
intro x1; destruct (Rlt_dec x1 a).
repeat rewrite Hfl; try lra.
assert (D_x no_cond a x1 /\ dist R_met x1 a < x ->
    dist R_met (gl x1) (gl a) < eps) by (exact (H1 x1)).
intros; destruct H4.
apply H3.
split; try assumption.
assert (Rmin x (Rmin x0 (b-a)) <= x) by exact (Rmin_l x (Rmin x0 (b-a))).
lra.

(* x = a, x1 > a *)
apply Rnot_lt_le in n.
destruct (Rlt_dec b x1).
intros.
assert False; try contradiction.
apply (Rgt_asym b x1); try assumption.
destruct H3; simpl in H4; unfold R_dist in H4.
assert ((x1 - a) <= Rabs (x1 - a)) by apply RRle_abs.
assert (Rmin x (Rmin x0 (b-a)) <= (b-a)).
assert (Rmin x (Rmin x0 (b-a)) <= (Rmin x0 (b-a)))
     by exact (Rmin_r x (Rmin x0 (b-a))).
assert ((Rmin x0 (b-a)) <= (b-a)) by exact (Rmin_r  x0 (b-a)).
lra.
lra.
apply Rnot_lt_le in n0.
repeat rewrite Hfc; try split; try lra.
assert (D_x no_cond a x1 /\ dist R_met x1 a < x0 ->
    dist R_met (gc x1) (gc a) < eps) by (exact (H2 x1)).
intros; destruct H4.
apply H3.
split; try assumption.
assert (Rmin x (Rmin x0 (b-a)) <= x0).
assert (Rmin x (Rmin x0 (b-a)) <= (Rmin x0 (b-a)))
     by exact (Rmin_r x (Rmin x0 (b-a))).
assert ((Rmin x0 (b-a)) <= x0) by exact (Rmin_l  x0 (b-a)).
lra.
lra.

(* a < x < b *)
destruct (Rtotal_order x b).
intros eps Heps.
destruct (Hc x (conj (Rlt_le _ _ H) (Rlt_le _ _ H0)) eps); try assumption.
destruct H1.
exists (Rmin (Rmin (x-a) (b-x)) x0); split.
repeat (apply Rmin_pos); lra.
intro x1.
destruct (Rlt_dec x1 a).
intros.
assert False; try contradiction.
apply (Rgt_asym a x1); try assumption.
destruct H3; simpl in H4; unfold R_dist in H4.
assert (x - x1 <= Rabs (x1 - x)).
rewrite Rabs_minus_sym; apply RRle_abs.
assert ((Rmin (Rmin (x-a) (b-x)) x0) <= (x-a)).
assert ((Rmin (Rmin (x-a) (b-x)) x0) <= (Rmin (x-a) (b-x)))
     by exact (Rmin_l (Rmin (x-a) (b-x)) x0).
assert ((Rmin (x-a) (b-x)) <= x-a) by exact (Rmin_l  (x-a) (b-x)).
lra.
lra.
destruct (Rlt_dec b x1).
intros.
assert False; try contradiction.
apply (Rgt_asym x1 b); try assumption.
destruct H3; simpl in H4; unfold R_dist in H4.
assert (x1 - x <= Rabs (x1 - x)) by apply RRle_abs.
assert ((Rmin (Rmin (x-a) (b-x)) x0) <= (b-x)).
assert ((Rmin (Rmin (x-a) (b-x)) x0) <= (Rmin (x-a) (b-x)))
     by exact (Rmin_l (Rmin (x-a) (b-x)) x0).
assert ((Rmin (x-a) (b-x)) <= b-x) by exact (Rmin_r  (x-a) (b-x)).
lra.
lra.
apply Rnot_lt_le in n.
apply Rnot_lt_le in n0.
assert (D_x no_cond x x1 /\ dist R_met x1 x < x0 ->
    dist R_met (gc x1) (gc x) < eps) by (exact (H2 x1)).
repeat rewrite Hfc; try split; try lra.
intros; destruct H4.
apply H3.
split; try assumption.
assert ((Rmin (Rmin (x-a) (b-x)) x0) <= x0)
     by exact (Rmin_r (Rmin (x-a) (b-x)) x0).
lra.

(* x = b, x1 > b *)
destruct H0.
rewrite H0 in |-*; clear H x H0.
intros eps Heps.
destruct (Hc b (conj (Rlt_le _ _ r) (Rle_refl b)) eps); try assumption.
destruct (Hr b eps); try assumption.
destruct H; destruct H0.
exists (Rmin x (Rmin x0 (b-a))); split.
repeat (apply Rmin_pos); lra.
intro x1; destruct (Rlt_dec b x1).
repeat rewrite Hfr; try lra.
assert (D_x no_cond b x1 /\ dist R_met x1 b < x0 ->
    dist R_met (gr x1) (gr b) < eps) by (exact (H2 x1)).
intros; destruct H4.
apply H3.
split; try assumption.
assert (Rmin x (Rmin x0 (b-a)) <= x0).
assert (Rmin x (Rmin x0 (b-a)) <= (Rmin x0 (b-a)))
     by exact (Rmin_r x (Rmin x0 (b-a))).
assert ((Rmin x0 (b-a)) <= x0) by exact (Rmin_l  x0 (b-a)).
lra.
lra.

(* x = b, x1 < b *)
destruct (Rlt_dec x1 a).
intros.
assert False; try contradiction.
apply (Rgt_asym x1 a); try assumption.
destruct H3; simpl in H4; unfold R_dist in H4.
assert ((b - x1) <= Rabs (x1 - b)).
rewrite Rabs_minus_sym; apply RRle_abs.
assert (Rmin x (Rmin x0 (b-a)) <= (b-a)).
assert (Rmin x (Rmin x0 (b-a)) <= (Rmin x0 (b-a)))
     by exact (Rmin_r x (Rmin x0 (b-a))).
assert ((Rmin x0 (b-a)) <= (b-a)) by exact (Rmin_r  x0 (b-a)).
lra.
lra.
apply Rnot_lt_le in n.
apply Rnot_lt_le in n0.
repeat rewrite Hfc; try split; try lra.
assert (D_x no_cond b x1 /\ dist R_met x1 b < x ->
    dist R_met (gc x1) (gc b) < eps) by (exact (H1 x1)).
intros; destruct H4.
apply H3.
split; try assumption.
assert (Rmin x (Rmin x0 (b-a)) <= x) by exact (Rmin_l x (Rmin x0 (b-a))).
lra.

(* x > b *)
intros eps Heps.
destruct (Hr x eps); try assumption.
destruct H1.
exists (Rmin x0 (x - b)); split.
repeat (apply Rmin_pos); lra.
intro.
destruct (Rlt_dec x1 b).
intros.
assert False; try contradiction.
apply (Rgt_asym b x1); try assumption.
destruct H3; simpl in H4; unfold R_dist in H4.
assert ((x - x1) <= Rabs (x1 - x)).
rewrite Rabs_minus_sym; apply RRle_abs.
assert (Rmin x0 (x - b) <= x - b) by exact (Rmin_r x0 (x - b)).
lra.
apply Rnot_lt_le in n.
repeat rewrite Hfr; try lra.
assert (D_x no_cond x x1 /\ dist R_met x1 x < x0 ->
    dist R_met (gr x1) (gr x) < eps) by (exact (H2 x1)).
intros; destruct H4.
apply H3.
split; try assumption.
assert (Rmin x0 (x - b) <= x0) by exact (Rmin_l x0 (x - b)).
lra.

(* a = b *)
rewrite e in *|-.
apply (C0_sticking_one_pt f gl gr b); assumption.
Qed.

(*Lemma C0_sticking_two_pt f gl gc gr a b :
  a <= b  ->
  continuity gl ->
  (forall x, a <= x <= b -> continuity_pt gc x) ->
  continuity gr ->
  (forall x, x <= a -> f x = gl x) ->
  (forall x, a <= x <= b -> f x = gc x) ->
  (forall x, b <= x -> f x = gr x) ->
  continuity f.
Proof.
intros f gl gc gr a b Hab Cgl Cgc Cgr El Ec Er.
assert (Hgcr : {gcr |
  (forall x, x <= b -> gcr x = gc x) &
  (forall x, b <= x -> gcr x = gr x)}).
 exists (fun x => if Rle_lt_dec x b then gc x else gr x); 
   intros; destruct (Rle_lt_dec x b); auto.
  apply (False_ind _ (RIneq.Rle_not_lt _ _ H r)).
  transitivity (f x).
   symmetry; apply Ec; split; auto; apply Rle_trans with b; auto.
   apply Er; auto.
destruct Hgcr as [gcr Hcrc Hcrr].
apply (C0_sticking_one_pt_strong _ gl gcr a); auto.
 apply (C0_sticking_one_pt_constraint gcr gc gr a b Hab Cgc); auto.
 intros x Hx.
 destruct (Rle_lt_dec x b).
  transitivity (gc x); auto; symmetry; auto.
  transitivity (gr x).
   apply Er; apply Rlt_le; auto.
   symmetry; apply Hcrr; apply Rlt_le; auto.
Qed.*)
         
Lemma C1_continuation_derive_continuous : forall d a b, a <= b ->
(forall c, a <= c <= b -> continuity_pt d c) ->
  continuity (C1_continuation_derive d a b).
Proof.
intros d a b Hab Cd.
(*destruct (Rle_dec a b) as [Hab|Hab].*)
apply (C0_sticking_two_pt _ (fct_cte (d a)) d (fct_cte (d b)) a b Hab);
  try (apply continuity_constant); auto; intros;
  unfold C1_continuation_derive;
  destruct (Rlt_dec x a);
  destruct (Rle_dec x b); auto.
 
 assert (x = a) by (apply Rle_antisym; auto; apply Rnot_lt_le; auto).
 subst; trivial.
 
 pose proof Rle_antisym a x (Rnot_lt_le _ _ n) H; subst.
 apply (False_ind _ (n0 Hab)).
 
 apply (False_ind _ (RIneq.Rle_not_lt _ _ (proj1 H) r)).
 
 apply (False_ind _ (RIneq.Rle_not_lt _ _ (proj1 H) r)).
 
 apply (False_ind _ (n0 (proj2 H))).
 
 assert (x = b) by (apply Rle_antisym; auto; apply Rnot_lt_le; auto); subst.
 apply (False_ind _ (RIneq.Rle_not_lt _ _ Hab r)).
 
 apply False_ind; apply (RIneq.Rle_not_lt _ _ H).
 apply Rlt_le_trans with a; auto.
 
 assert (x = b) by (apply Rle_antisym; auto; apply Rnot_lt_le; auto); subst.
 trivial.
Qed.

Lemma prolongement_C1_C1 : forall (f d : R -> R) (a b : R),
  a <= b ->
  (forall c, a <= c <= b -> derivable_pt_abs f c (d c)) ->
  (forall c, a <= c <= b -> continuity_pt d c) ->
  {g : C1_fun |
  (forall c : R, a <= c <= b -> f c = g c) /\
  (forall c : R, a <= c <= b -> d c = derive g (diff0 g) c)}.
Proof.
intros f d a b Hab Hder Hcont.
pose proof (prolongement_C1_derivable f d a b Hab Hder) as [diff0 Heq].
pose proof (C1_continuation_derive_continuous d a b Hab Hcont) as cont.
assert(c1 : continuity (derive (C1_continuation f a b d) diff0)).
  intros x eps Heps.
  destruct (cont x eps Heps) as [alpha [Halpha1 Halpha2]].
  exists alpha.
  split.
  assumption.
  intros.
  do 2 rewrite Heq; intuition.
exists (mkC1 c1).
split.
  intros x Hx.
  rewrite <- (C1_continuation_eq f a b d x Hx);
  reflexivity.
  
  intros x Hx.
  rewrite <- (C1_continuation_derive_eq a b d x Hx), Heq;
  reflexivity.
Qed.

End Rint_C1.

Create HintDb Rcont.

Hint Resolve continuity_pt_plus : Rcont.
Hint Resolve continuity_pt_mult : Rcont.
Hint Resolve continuity_pt_minus : Rcont.
Hint Resolve continuity_pt_opp : Rcont.
Hint Resolve continuity_pt_const : Rcont.
Hint Resolve continuity_pt_inv : Rcont.
Hint Resolve continuity_pt_div : Rcont.
Hint Resolve continuity_pt_comp : Rcont.
Hint Resolve continuity_pt_sqrt : Rcont.
Hint Resolve continuity_pt_constant : Rcont.
Hint Resolve derivable_continuous_pt : Rcont.

Hint Resolve continuity_plus : Rcont.
Hint Resolve continuity_mult : Rcont.
Hint Resolve continuity_minus : Rcont.
Hint Resolve continuity_opp : Rcont.
Hint Resolve continuity_const : Rcont.
Hint Resolve continuity_inv : Rcont.
Hint Resolve continuity_div : Rcont.
Hint Resolve continuity_constant : Rcont.
Hint Resolve continuity_comp : Rcont.
Hint Resolve derivable_continuous : Rcont.

Hint Resolve derivable_pt_plus : Rcont.
Hint Resolve derivable_pt_mult : Rcont.
Hint Resolve derivable_pt_minus: Rcont.
Hint Resolve derivable_pt_opp : Rcont.
Hint Resolve derivable_pt_const : Rcont.
Hint Resolve derivable_pt_inv : Rcont.
Hint Resolve derivable_pt_div : Rcont.
Hint Resolve derivable_pt_comp : Rcont.
Hint Resolve derivable_pt_sqrt : Rcont.
Hint Resolve derivable_pt_exp : Rcont.
Hint Resolve derivable_pt_id : Rcont.
Hint Resolve derivable_pt_pow : Rcont.
Hint Resolve derivable_pt_cosh : Rcont.

Hint Resolve derivable_plus : Rcont.
Hint Resolve derivable_mult : Rcont.
Hint Resolve derivable_minus : Rcont.
Hint Resolve derivable_opp : Rcont.
Hint Resolve derivable_const : Rcont.
Hint Resolve derivable_inv : Rcont.
Hint Resolve derivable_div : Rcont.
Hint Resolve derivable_comp : Rcont.
Hint Resolve derivable_continuous : Rcont.
Hint Resolve derivable_cos : Rcont.
Hint Resolve derivable_sin : Rcont.
Hint Resolve derivable_exp : Rcont.
Hint Resolve derivable_id : Rcont.
Hint Resolve derivable_id : Rcont.
Hint Resolve derivable_pow : Rcont.
Hint Resolve derivable_cosh : Rcont.

Hint Resolve derivable_pt_lim_sin : Rcont.
Hint Resolve derivable_pt_lim_cos : Rcont.
Hint Resolve derivable_pt_lim_sqrt : Rcont.
Hint Resolve derivable_pt_lim_ln : Rcont.
Hint Resolve derivable_pt_lim_exp : Rcont.
Hint Resolve derivable_pt_lim_plus: Rcont.
Hint Resolve derivable_pt_lim_mult: Rcont.
Hint Resolve derivable_pt_lim_minus : Rcont.
Hint Resolve derivable_pt_lim_opp : Rcont.
Hint Resolve derivable_pt_lim_const : Rcont.
Hint Resolve derivable_pt_lim_id : Rcont.
Hint Resolve derivable_pt_lim_div : Rcont.
Hint Resolve derivable_pt_lim_comp : Rcont.
Hint Resolve derivable_pt_lim_pow : Rcont.
Hint Resolve derivable_pt_lim_power : Rcont.
Hint Resolve derivable_pt_lim_id : Rcont.
Hint Resolve derivable_pt_lim_cosh : Rcont.
