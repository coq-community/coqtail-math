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

(** Properties of real series *)

Require Export Reals.
Require Export Rsequence.
Require Export Rseries_def Rseries_base_facts Rseries_pos_facts.
Require Export Rseries_remainder_facts Rseries_cv_facts Rseries_usual.
Require Import Lra.
Require Import Max.
Require Import Rtactic MyRIneq.

Local Open Scope R_scope.
(** printing ~	~ *)

(** Finite facts *)

Lemma sum_minus: forall Un n n2, 
- sum_f_R0 Un n + sum_f_R0 Un (S (n2 + n)) =
sum_f_R0 (fun k : nat => Un (S n + k)%nat) n2.
Proof.
intros Un n n2.
induction n2.
 simpl. ring_simplify. rewrite plus_0_r. reflexivity.
 
 repeat rewrite tech5. rewrite <- IHn2. 
 rewrite <- plus_n_Sm. do 2 rewrite plus_Sn_m.
 rewrite plus_comm.
 ring.
Qed.

Lemma sum_reorder_0 : forall Un n N, (n <= N)%nat -> 
  sum_f_R0 (fun k0 : nat => Un (k0 - N)%nat) n =
    INR (S n) * Un O.
Proof.
intros Un n N HnN.
induction n.
 simpl ; ring.

 rewrite tech5. rewrite IHn ; intuition.
 do 3 rewrite S_INR.
 inversion HnN.
  rewrite minus_diag. ring.
   
  rewrite not_le_minus_0. 
   ring.
   intuition.
Qed.   

Open Scope Rseq_scope.


(** * Convergence and comparisons between sequences*)

Section Rser_pos_comp.

(** Big-O and bound *)

Lemma Rser_big_O_maj : forall (Un Vn: Rseq), 
  (forall n : nat, 0 <= Vn n) -> Un = O (Vn) ->
  exists K, exists SN, 0 <= K /\
  forall n : nat, Rseq_sum (|Un|) n <= K* (Rseq_sum Vn n) + SN.
Proof.
intros Un Vn Vn_pos [K [HK [N HN]]] ; apply Rge_le in HK ;
exists K ; exists (Rseq_sum (| Un |) N) ; split ; [assumption |].
intro n ; destruct (le_lt_dec n N) as [HnN | HNn].
 transitivity (Rseq_sum (| Un |) N).
 destruct (eq_nat_dec n N) as [Heq | Hneq].
  subst ; reflexivity.
  unfold Rseq_sum ; rewrite tech2 with (| Un |) n N ; [| lia] ;
  apply Rplus_le_simpl_l, Rseq_sum_pos ; intros ; apply Rabs_pos.
  apply Rplus_le_simpl_r, Rmult_le_pos, Rseq_sum_pos ; assumption.
  unfold Rseq_sum ; rewrite tech2 with (|Un|) N n, Rplus_comm.
  apply Rplus_le_compat_r ; rewrite tech2 with Vn N n, Rmult_plus_distr_l.
  transitivity ((K * Rseq_sum (Rseq_shifts Vn (S N)))%Rseq (n - S N)%nat).
  rewrite <- Rseq_sum_scal_compat_l ; apply Rseq_sum_le_compat ;
  unfold Rseq_shifts, Rseq_abs, Rseq_mult, Rseq_constant ; intros ;
  rewrite <- (Rabs_right (Vn _)), HN.
   reflexivity.
   lia.
   apply Rle_ge ; apply Vn_pos.
  apply Rplus_le_simpl_r, Rmult_le_pos, Rseq_sum_pos, Vn_pos.
  assumption.
  assumption.
  assumption.
Qed.


(** Convergence and big-O *)

Lemma Rser_big_O_cv_weak : forall (Un Vn : nat -> R), 
    (forall n : nat, 0 <= Un n) -> (forall n : nat, 0 <= Vn n) ->
        Un = O(Vn) -> {lv | Rser_cv Vn lv} -> {lu | Rser_cv Un lu}.
Proof.
intros Un Vn Un_pos Vn_pos HO Hlv; destruct Hlv as [lv Hlv].
assert ({M | Rser_bound_max Un M}) as HM.
assert ({M : R | is_lub (EUn (sum_f_R0 Un))M})as HMub.
apply ub_to_lub.
destruct (Rser_big_O_maj Un Vn  Vn_pos HO) as [K [SN [K_pos Hmaj]]].
exists (K*lv+SN)%R.
intros x Hx; destruct Hx as [n Hn]; rewrite Hn.
apply Rle_trans with (K * sum_f_R0 Vn n + SN)%R.
rewrite (sum_eq Un (fun k => Rabs (Un k))).
apply Hmaj.
intros i Hi; rewrite Rabs_pos_eq; [reflexivity | apply Un_pos].
apply Rplus_le_compat_r.
apply Rmult_le_compat_l.
apply K_pos.
apply growing_ineq.
apply Rser_pos_growing; apply Vn_pos.
apply Hlv.
destruct HMub as [M [HM _]]; exists M.
intro n; apply HM.
exists n; reflexivity.
destruct HM as [M HM].
apply Rser_pos_bound_cv with M.
apply Un_pos.
apply HM.
Qed.

Lemma Rser_big_O_cv : forall (Un Vn : nat -> R), 
  Un = O(Vn) -> {lv | Rser_abs_cv Vn lv} -> {lu | Rser_abs_cv Un lu}.
Proof.
intros Un Vn HO Hlv.
apply Rser_big_O_cv_weak with (|Vn|); intros; apply Rabs_pos || auto.
destruct HO as [M [HM [N HN]]]; exists M.
split; auto.
exists N; intros.
unfold Rseq_abs; rewrite Rabs_Rabsolu; auto.
rewrite Rabs_Rabsolu; apply HN; assumption.
Qed.

(** Little-O and bound *)

Lemma Rser_little_O_maj : forall (Un Vn : nat -> R),
    (forall n : nat, 0 <= Vn n) -> Un = o (Vn) ->
        forall eps, 0< eps -> exists SN,
            forall n : nat, sum_f_R0 (|Un|) n <= eps* (sum_f_R0 Vn n) + SN.
Proof.
intros Un Vn Vn_pos HO eps Heps.
assert (0<= eps) as Heps_pos.
apply Rlt_le; apply Heps.
destruct (HO eps Heps) as [N HN].
exists (sum_f_R0 (|Un|) N).
intro n; case (le_lt_dec n N); intro Hn.
apply Rle_trans with (sum_f_R0 (|Un|) N).
assert (n = N \/ n < N)%nat.
lia.
case H ; intro HnN.
rewrite HnN; apply Rle_refl.
rewrite tech2 with (|Un|) n N.
apply Rplus_le_simpl_l.
apply cond_pos_sum.
intro k; apply Rabs_pos.
apply HnN.
apply Rplus_le_simpl_r.
apply Rmult_le_pos; [apply Heps_pos | apply cond_pos_sum; apply Vn_pos].
rewrite tech2 with (|Un|) N n.
rewrite Rplus_comm.
apply Rplus_le_compat_r.
rewrite tech2 with Vn N n.
rewrite Rmult_plus_distr_l.
apply Rle_trans with (eps * sum_f_R0 (fun i : nat => Vn (S N + i)%nat) (n- (S N)))%R.
rewrite scal_sum.
apply sum_Rle.
intros n0 Hn0.
rewrite <- Rabs_pos_eq.
rewrite Rmult_comm; rewrite Rabs_mult.
rewrite Rabs_pos_eq with eps.
apply HN; lia.
apply Heps_pos.
apply Rmult_le_pos; [apply Vn_pos | apply Heps_pos].
apply Rplus_le_simpl_r.
apply Rmult_le_pos; [apply Heps_pos | apply cond_pos_sum; apply Vn_pos].
apply Hn.
apply Hn.
Qed.

(** Convergence and little-O*)

Lemma Rser_little_O_cv : forall (Un Vn : nat -> R), 
  Un = o(Vn) -> {lv | Rser_abs_cv Vn lv} -> {lu | Rser_abs_cv Un lu}.
Proof.
intros Un Vn Ho Hcv.
apply (Rser_big_O_cv Un Vn); [|assumption].
apply Rseq_little_O_big_O_incl; assumption.
Qed.

(** Convergence and equivalence *)

Lemma Rser_equiv_cv : forall (Un Vn : nat -> R), 
    (forall n : nat, 0 <= Un n) -> (forall n : nat, 0 <= Vn n) ->
        Un ~ Vn -> {lv | Rser_cv Vn lv} -> {lu | Rser_cv Un lu}.
Proof.
intros Un Vn Un_pos Vn_pos Heq Hlv.
apply Rseq_equiv_sym in Heq.
assert  ({luv | Rser_cv (fun n => Rabs (Vn n - Un n)) luv}) as Hluv.
apply Rser_little_O_cv with Vn.
unfold Rseq_little_O.
intros eps Heps.
destruct (Heq eps Heps) as [N HN]; exists N.
intro n; apply HN.
destruct Hlv as [lv Hlv].
exists lv; apply Rser_cv_ext with Vn.
  intros n; unfold Rseq_abs; rewrite Rabs_right; auto with real.
assumption.
destruct Hlv as [lv Hlv].
destruct Hluv as [luv Hluv].
apply Rser_pos_bound_cv with (lv + luv)%R.
apply Un_pos.
intro n.
apply Rle_trans with (sum_f_R0 Vn n + sum_f_R0 (fun n : nat => Rabs (Vn n - Un n)) n)%R.
apply Rle_trans with (sum_f_R0 (fun n0 : nat => Vn n0 + Rabs (Vn n0 - Un n0)) n)%R.
apply sum_Rle.
intros n0 Hn0.
rewrite <- ( Rabs_pos_eq)  with (Vn n0).
rewrite Rabs_pos_eq at 2.
rewrite <- Rabs_pos_eq  with (Un n0).
rewrite  Rabs_pos_eq  at 2.
rewrite <-  Rabs_Ropp.
rewrite <-  Rabs_Ropp with (Vn n0).
replace (- Un n0)%R with  (- Vn n0 + (Vn n0 - Un n0))%R by ring.
apply Rabs_triang.
apply Un_pos .
apply Un_pos.
apply Vn_pos.
apply Vn_pos.
rewrite plus_sum.
apply Rplus_le_compat_l.
apply Rle_refl.
apply Rplus_le_compat; [ | ]; apply growing_ineq.
apply Rser_pos_growing.
apply Vn_pos.
apply Hlv.
apply Rser_pos_growing.
intro k; apply Rabs_pos.
apply Hluv.
Qed.

(** classical is needed? *)
Hypothesis NNPP : forall p : Prop, ~ ~ p -> p.
Hypothesis classic: forall P : Prop, P \/ ~ P.


Lemma Rser_equiv_cv_infty : forall (Un Vn : nat -> R),
    (forall n : nat, 0 <= Un n) -> (forall n : nat, 0 <= Vn n) ->
        Un ~ Vn -> Rser_cv_pos_infty Vn -> Rser_cv_pos_infty Un.
Proof.
intros Un Vn Un_pos Vn_pos Heq Hv.
case (Rser_pos_cv_dec Un Un_pos NNPP classic); intro Hcase.
apply Rseq_growing_constructive_limit in Hcase.
apply (Rser_equiv_cv Vn Un) in Hcase.
assert ((exists l, Rser_cv Vn l)/\ Rser_cv_pos_infty Vn).
split.
destruct Hcase as [ l Hl].
exists l; apply Hl.
apply Hv.
elim Rseq_cv_not_infty with (sum_f_R0 Vn).
apply H.
apply Vn_pos.
apply Un_pos.
apply Rseq_equiv_sym.
apply Heq.
apply Rser_pos_growing.
apply Un_pos.
apply Hcase.
Qed.

End Rser_pos_comp.

(** * Summing Landau's relations when the series go to infinity*)

Section Rser_landau_infty.

Variables Vn : nat -> R.
Hypothesis Vn_pos : (forall n : nat, 0 <= Vn n).
Hypothesis Vn_infty : Rser_cv_pos_infty Vn.

Lemma Rser_partial_big_O_compat : forall (Un : nat -> R), 
    Un = O(Vn) -> sum_f_R0 Un = O(sum_f_R0 Vn).
Proof.
intros Un HO.
assert (forall n, 0<= Rabs(Un n)) as RUn_pos.
intro n; apply Rabs_pos.
destruct (Rser_big_O_maj Un Vn Vn_pos HO) as [K [SN [K_pos Hmaj]]].
destruct (Vn_infty SN) as [N HN].
exists (K+1)%R.
split.
auto with *.
exists N; intros n Hn.
apply Rle_trans with (K * sum_f_R0 Vn n + SN)%R.
apply Rle_trans with (sum_f_R0 (fun k : nat => Rabs (Un k)) n).
apply sum_f_R0_triangle.
apply Hmaj.
rewrite Rmult_plus_distr_r.
rewrite Rabs_pos_eq.
ring_simplify.
apply Rplus_le_compat_l.
apply Rlt_le; apply HN; apply Hn.
apply (cond_pos_sum _ _ Vn_pos).
Qed.

Lemma Rser_partial_little_O_compat : forall (Un : nat -> R),
    Un = o(Vn) -> sum_f_R0 Un = o(sum_f_R0 Vn).
Proof.
intros Un Ho eps Heps.
assert (0<eps/2) as Heps2; [lra|].
destruct (Rser_little_O_maj _ _ Vn_pos Ho (eps /2)) as [C HC].
apply Heps2.
destruct (Vn_infty (C/(eps/2))%R) as [N HN].
exists N.
intros n Hn.
rewrite Rabs_pos_eq with (sum_f_R0 Vn n).
apply Rle_trans with (sum_f_R0 (fun k : nat => Rabs (Un k)) n).
apply sum_f_R0_triangle.
apply Rle_trans with ((eps / 2) * sum_f_R0 Vn n + C)%R.
apply HC.
rewrite double_var with eps .
rewrite <- double_var at 1.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat_l.
assert (C = (eps/2)*(/(eps/2))*C)%R as HCr.
field.
intro Hf; apply Rlt_irrefl with 0; rewrite Hf in Heps; apply Heps.
rewrite HCr.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le; apply Heps2.
rewrite Rmult_comm.
apply Rlt_le.
apply HN; apply Hn.
apply (cond_pos_sum Vn n Vn_pos).
Qed.

Lemma Rser_partial_equiv_compat : forall (Un : nat -> R), 
    Un ~ Vn -> (sum_f_R0 Un) ~ (sum_f_R0 Vn).
Proof.
intros Un Heq.
apply Rseq_equiv_sym.
apply Rseq_equiv_sym in Heq.
assert((sum_f_R0 (Vn -Un)) = o(sum_f_R0 Vn)).
apply (Rser_partial_little_O_compat (Vn - Un) Heq ).
intros eps Heps.
destruct (H eps Heps) as [N HN].
exists N; intros n Hn.
unfold Rseq_minus.
rewrite <- minus_sum.
apply HN; apply Hn.
Qed.

End Rser_landau_infty.

(** Properties of remainder *)
Section Rser_rem.







End Rser_rem.




(** * Summing Landau's relations when the series converge*)
Section Rser_landau_cv.

Variables Un Vn : nat-> R.
Hypothesis Vn_pos : (forall n : nat, 0 <= Vn n).
Variable lu lv : R.
Hypothesis Hlv : Rser_cv Vn lv.
Hypothesis Hlu : Rser_cv Un lu.


Lemma Rser_rem_big_O_compat :
    Un = O(Vn) -> (Rser_rem Un lu Hlu) = O(Rser_rem Vn lv Hlv).
Proof.
intro HO.
destruct HO as [K [K_pos [N HN]]].
exists K.
split.
apply K_pos.
exists N.
intros n Hn.
rewrite <- Rabs_pos_eq with K.
rewrite <- Rabs_mult.
apply Rle_cv_lim with (fun p : nat => Rabs (sum_f_R0 (fun k => (Un (S n+k))) p))%R
                                    (fun p : nat => Rabs (sum_f_R0 (fun k => (Vn (S n+k))*K) p))%R.
intro p.
apply Rle_trans with (sum_f_R0 (fun k : nat =>(Rabs (Un (S n + k)))) p)%R.
apply Rabs_triang_gen.
rewrite Rabs_pos_eq.
apply sum_Rle.
intros k Hk.
 rewrite <- Rabs_pos_eq with (Vn (S n + k)).
rewrite Rmult_comm.
apply HN; lia.
apply Vn_pos.
apply cond_pos_sum; intro.
apply Rge_le in K_pos.
rewrite Rmult_comm.
apply Rmult_le_pos; [apply K_pos | apply Vn_pos].
apply Rseq_cv_abs_compat; apply Rser_rem_cv.
apply Rseq_cv_abs_compat.
apply Rseq_cv_eq_compat with (fun p : nat => K * sum_f_R0 (fun k : nat => ( Vn (S n + k))) p)%R.
intro; rewrite (scal_sum _ _ K); reflexivity.
apply CV_mult.
apply Rseq_constant_cv.
apply Rser_rem_cv.
apply Rge_le.
apply K_pos; apply K_pos.
Qed.

Lemma Rser_rem_little_O_compat :
    Un = o(Vn) -> (Rser_rem Un lu Hlu) = o(Rser_rem Vn lv Hlv).
Proof.
intros Ho eps Heps.
destruct (Ho eps Heps) as  [N HN].
exists N.
intros n Hn.
assert (0<= eps) as eps_pos.
apply Rlt_le; apply Heps.
rewrite <- Rabs_pos_eq with eps.
rewrite <- Rabs_mult.
apply Rle_cv_lim with (fun p : nat => Rabs (sum_f_R0 (fun k => (Un (S n+k))) p))%R
                                    (fun p : nat => Rabs (sum_f_R0 (fun k => (Vn (S n+k))*eps) p))%R.
intro p.
apply Rle_trans with (sum_f_R0 (fun k : nat =>(Rabs (Un (S n + k)))) p)%R.
apply Rabs_triang_gen.
rewrite Rabs_pos_eq.
apply sum_Rle.
intros k Hk.
 rewrite <- Rabs_pos_eq with (Vn (S n + k)).
rewrite Rmult_comm.
apply HN; lia.
apply Vn_pos.
apply cond_pos_sum; intro.
apply Rmult_le_pos; [ apply Vn_pos| apply eps_pos].
apply Rseq_cv_abs_compat; apply Rser_rem_cv.
apply Rseq_cv_abs_compat.
apply Rseq_cv_eq_compat with (fun p : nat => eps * sum_f_R0 (fun k : nat => ( Vn (S n + k))) p)%R.
intro; rewrite (scal_sum _ _ eps); reflexivity.
apply CV_mult.
apply Rseq_constant_cv.
apply Rser_rem_cv.
apply eps_pos.
Qed.

End Rser_landau_cv.

Section Rser_equiv_cv.

Variables Un Vn : nat-> R.
Hypothesis Vn_pos : (forall n : nat, 0 <= Vn n).
Variable lu lv : R.
Hypothesis Hlv : Rser_cv Vn lv.
Hypothesis Hlu : Rser_cv Un lu.


Lemma Rser_rem_equiv_compat :
    Un ~ Vn -> (Rser_rem Un lu Hlu) ~ (Rser_rem Vn lv Hlv).
Proof.
intro Heq.
apply Rseq_equiv_sym.
apply Rseq_equiv_sym in Heq.
unfold Rseq_equiv in *.
assert(Hrew : (Rser_rem Vn lv Hlv - Rser_rem Un lu Hlu)== Rser_rem (Vn-Un) (lv-lu) (Rser_cv_minus_compat Vn Un lv lu Hlv Hlu)).
apply Rser_rem_minus_compat.
intros eps Heps.
destruct(Rser_rem_little_O_compat (Vn -Un) Vn Vn_pos (lv-lu) lv Hlv (Rser_cv_minus_compat Vn Un lv lu Hlv Hlu) Heq eps Heps) as [N HN].
exists N.
intro n.
rewrite Hrew.
apply HN.
Qed.

End Rser_equiv_cv.


(* begin hide *)
Open Scope R_scope.
(* end hide *)



Require Import Rsequence.


Lemma Rser_rem_lt_le : forall Un lu lv (n : nat) Vn 
  (Hlu : Rser_cv Un lu) (Hlv : Rser_cv Vn lv),
   (forall k, (k > n)%nat -> Un k <= Vn k) ->
    {k | (k > n)%nat /\ Un k < Vn k} ->
     Rser_rem Un lu Hlu n < Rser_rem Vn lv Hlv n.
Proof.
intros Un lu lv n Vn Hlu Hlv Hle Hlt.
assert (Rser_cv (Vn - Un)%Rseq (lv - lu)).
 apply Rser_cv_minus_compat ; assumption.

assert (Hpos : (forall k, (k > n)%nat -> Vn k - Un k >= 0)). 
 intros. apply Rge_minus. apply Rle_ge. apply Hle. assumption.

apply Rminus_gt. generalize (Rser_rem_minus_compat Vn Un lv lu Hlv Hlu H n).
intros Hrewrite. unfold Rseq_minus in Hrewrite. rewrite Hrewrite.
apply Rser_rem_pos. 
 apply Hpos. 

 destruct Hlt as [k [Hkn Hlt]].
exists k. 
split. 
 apply Hkn.

 apply Rgt_minus. apply Hlt.
Qed.

(* begin hide *)
Lemma seq_exist_subproof :  forall Un Vn n, 
  (forall k, (k > n)%nat -> Vn k <= Un (k - S n)%nat) ->
    {k | (k > n)%nat /\ Vn k < Un (k - S n)%nat} ->
      {Wn : (nat -> R)&{k | (forall k1, Vn k1 + Wn k1 = Un (k1 - S n)%nat /\ 
        ((k1 > n)%nat -> Wn k1 >= 0)) /\
          (k > n)%nat /\ Wn k > 0}}.
Proof.
intros Un Vn n Hle Hlt.
pose (Un1 := fun k => Un (k - S n)%nat).
pose (Wn := (Un1 - Vn)%Rseq).
destruct Hlt as [k [Hnk Hlt]].
exists Wn. exists k.
split. 
 unfold Wn. unfold Rseq_minus, Un1; intuition.
 apply Rge_minus. apply Rle_ge. apply Hle. assumption.

 split ; [assumption|unfold Wn, Rseq_minus, Un1].
 apply Rgt_minus. assumption.
Qed.

Lemma Rser_cv_reorder : forall n Un l, 
  Rser_cv Un l ->
    Rser_cv (fun k => Un (k - S n)%nat) (l + INR (S n) * (Un O)).
Proof.
intros n Un l Uncv.
intros eps Heps.
destruct (Uncv eps Heps) as (N, Hn).
exists (S n + N)%nat.
intros k Hk.
assert (HkN : (k >= N)%nat) by intuition.
generalize (Hn k HkN) ; intros Hcv.
unfold R_dist in *.
assert (forall k n, (k >= S n)%nat -> sum_f_R0 (fun k0 : nat => Un (k0 - S n)%nat) k =
  sum_f_R0 Un (k - S n) + INR (S n) * Un O).
 intros m n0 Hmn0.
 induction Hmn0.
  induction n0.
   simpl. ring.
   
   rewrite sum_reorder_0. repeat rewrite S_INR.
    rewrite <- minus_diag_reverse.
    simpl. ring.
    
    intuition.
   rewrite tech5. rewrite IHHmn0. rewrite <- minus_Sn_m.
    rewrite tech5. ring.

    intuition.
  rewrite H. ring_simplify (sum_f_R0 Un (k - S n) + INR (S n) * Un 0%nat - (l + INR (S n) * Un 0%nat)).
   assert (k - S n >= N)%nat by intuition. 
   generalize (Hn (k - S n)%nat H0). intuition.
   
   intuition.
Qed.
(* end hide *)

Lemma Rser_Rser_rem_lt_le : forall Un Vn x l (H : Rser_cv Vn l) n,
  (forall k, (k > n)%nat -> Vn k <= Un (k - S n)%nat) ->
   {k | (k > n)%nat /\ Vn k < Un (k - S n)%nat} ->
    Rser_cv Un x -> Rser_rem Vn l H n < x.
Proof.
intros Un Vn x l Hv n Hle Hlt Hu.
destruct (seq_exist_subproof Un Vn n Hle Hlt) as (Wn, [k2 [Hwn11 [Hwn2 Hwn3]]]).
assert (Hwn :  Rser_cv Wn (x + INR (S n) * (Un O) - l)).
 assert (H1 : Rser_cv (fun k => Un (k - S n)%nat) (x + INR (S n) * (Un O))).
  apply Rser_cv_reorder. assumption.
 
 apply Rser_cv_ext with ((fun k => Un (k - S n)%nat) - Vn)%Rseq.
  intros k. generalize (Hwn11 k) ; intros Hwn1. destruct Hwn1 as (Hwn1, _).
  unfold Rseq_minus. rewrite <- Hwn1. ring.

  apply Rser_cv_minus_compat ; intuition.
pose (l1 := x + INR (S n) * Un 0%nat - l).
assert (H1 : Rser_cv (Vn + Wn)%Rseq (l + l1)).
 apply Rser_cv_plus_compat ; assumption.

rewrite (Rser_Rser_rem_equiv Un (Vn + Wn)%Rseq x (l + l1) H1 n).
 apply Rser_rem_lt_le. 
  unfold Rseq_plus. intuition.
  replace (Vn k) with (Vn k + 0) by intuition.
  apply Rplus_le_compat.
   intuition. 

   destruct (Hwn11 k) as (_, Hwn1). destruct (Hwn1 H) ; intuition.

  destruct Hlt as (k, H2). exists k ; intuition.
  destruct (Hwn11 k) as (Hwn1, Hwn5). unfold Rseq_plus. rewrite Hwn1. intuition.

 intros k.
 destruct (Hwn11 (S n + k)%nat) as (Hwn1, Hwn5).
 unfold Rseq_shifts, Rseq_plus. rewrite Hwn1. intuition.

 assumption.
Qed.
