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

(** Properties involving series and integrals *)
Require Import Reals.
Require Import Rseries_def.
Require Import Rseries_facts.
Require Import RiemannInt.
Require Import Lra.
Require Import Rsequence_facts.
Require Import Rsequence_subsequence.
Require Import Riemann_integrable.
Require Import Rintegral.

Local Open Scope R_scope.
(** printing ~	~ *)
Section Rseries_RiemannInt.

Local Coercion INR : nat >-> R.

(* begin hide *)
Lemma Rle_minus' : forall a b, b <= a -> 0 <= a - b. intros; lra. Qed.
Lemma Rminus_le_compat_r: forall r r1 r2 : R, r2 <= r1 -> r - r1 <= r - r2. intros; lra. Qed.
(* end hide *)

Lemma Telescoping_series : forall a n, sum_f_R0 (fun i => a (S i) - a i) n = a (S n) - a O.
Proof.
intros a n.
rewrite tech11 with (fun i => a (S i) - a i) (fun i => a (S i)) a _; [|reflexivity].
destruct n; [reflexivity|].
rewrite tech2 with a O (S n); [|intuition].
rewrite tech5.
simpl (sum_f_R0 a 0).
replace (S n - 1)%nat with n by (simpl; apply minus_n_O).
assert (REW : forall S S' A B, S = S' -> S + A - (B + S') = A - B) by (intros; subst; ring).
apply REW.
reflexivity.
Qed.

Lemma Telescoping_series_opp : forall a n, sum_f_R0 (fun i => a i - a (S i)) n = a O - a (S n).
Proof.
intros a n.
rewrite tech11 with (fun i => a i - a (S i)) a (fun i => a (S i)) _; [|reflexivity].
destruct n; [reflexivity|].
rewrite tech2 with a O (S n); [|intuition].
rewrite tech5.
simpl (sum_f_R0 a 0).
replace (S n - 1)%nat with n by (simpl; apply minus_n_O).
assert (REW : forall S S' A B, S = S' -> A + S - (S' + B) = A - B) by (intros; subst; ring).
apply REW.
reflexivity.
Qed.


(** * Generalized Chasles relation *)
Lemma Rint_generalized_Chasles : forall f An, 
  (forall n : nat, Rint f n (S n) (An n)) -> 
    forall n : nat, Rint f 0 (S n) (sum_f_R0 An n).
Proof.
intros f An H.
induction n.
  apply (H O).
apply Rint_Chasles with (S n).
  apply IHn.
apply H.
Qed.

Section Rser_RiemannInt_link.

Variable f : R -> R.
Hypothesis Hcont : forall x, 0 <= x -> continuity_pt f x.
Hypothesis Hpos : forall x, 0 <= x -> 0 <= f x.
Hypothesis Hdec : forall x y : R, 0 <= x <= y -> f y <= f x.

Lemma Riemann_integrable_f_n_Sn : forall (n : nat), Riemann_integrable f (INR n) (INR (S n)).
Proof.
intro n.
apply continuity_implies_RiemannInt.
  apply le_INR; do 2 constructor.
intros x [Hnx HxSn]; apply Hcont.
apply (Rle_trans 0 (INR n) x (le_INR _ _ (le_O_n n)) Hnx).
Qed.

Lemma Rser_RiemannInt_link_general_term_integrable : forall (n : nat), 
  Riemann_integrable (fun x => fct_cte (f (INR n)) x - f x) (INR n) (INR (S n)).
Proof.
intros n.
apply RiemannInt_integrable_minus.
 apply RiemannInt_P6.
  auto with *.
  intros x Hx.
  apply continuity_const.
  intros y z; reflexivity.
  
  apply (Riemann_integrable_f_n_Sn n).
Qed.

Lemma Rser_RiemannInt_link_general_term_bound (n : nat) : 
  RiemannInt (Rser_RiemannInt_link_general_term_integrable n) <= f (INR n) - f (INR (S n)).
Proof.
intros.
rewrite <- Rmult_1_r.
replace 1 with (INR (S n) - (INR n)).
 assert (pr:Riemann_integrable (fct_cte (f (INR n) - f (INR (S n)))) (INR n) (INR (S n))) by apply RiemannInt_P14.
 rewrite <- RiemannInt_P15 with _ _ _ pr.
 apply RiemannInt_P19; [intuition|].
 unfold fct_cte.
 intros x [xn xsn].
 apply Rminus_le_compat_r.
 apply Hdec.
 split. 
 apply Rle_trans with (INR n).
 auto with *.
 left; apply xn. 
 apply (Rlt_le _ _ xsn).
 
 rewrite <- minus_INR by intuition.
 replace (S n - n)%nat with 1%nat by intuition.
 reflexivity.
Qed.

(**  * Link between series and integral *)
Lemma Rser_RiemannInt_link : { l | Rser_cv (fun n => f (INR n) - RiemannInt (Riemann_integrable_f_n_Sn n) ) l}.
Proof.
apply Rser_pos_bound_cv with (f 0).
 intro n.
 destruct (Rint_constant (f n) n (S n)) as [ pr int]. 
 replace (f n * (S n -n)) with (f n) in int by (rewrite S_INR; ring).
 rewrite <- int.
 apply Rle_minus'.
 apply RiemannInt_P19; [intuition|].
 intros x [xn snx].
 assert(Hcond : 0 <= (INR n) <= x).
   split.
     auto with *.
     
     left; apply xn.
   apply (Hdec _ _ Hcond).
 
 intro n.
 apply Rle_trans with (sum_f_R0 (fun n => f (INR n) - f (INR (S n))) n).
 apply sum_Rle.
  intros i ni.
  destruct (Rint_constant (f i) i (S i)) as [ pr int]. 
   replace (f i * (S i -i)) with (f i) in int by (rewrite S_INR; ring).
  rewrite <- int.
  rewrite <- RiemannInt_minus with _ _ _ _ _ _ (Rser_RiemannInt_link_general_term_integrable i); [|intuition].
  rewrite RiemannInt_P15.
  replace (INR (S i) - INR i) with 1.
   rewrite Rmult_1_r.
   apply (Rser_RiemannInt_link_general_term_bound i).
   
   rewrite <- minus_INR by intuition.
   replace (S i - i)%nat with 1%nat by intuition.
   reflexivity.
  
  rewrite Telescoping_series_opp.
  rewrite <- Rminus_0_r.
  apply Rminus_le_compat_r.
  apply Hpos.
auto with *.
Qed.

Lemma Rser_RiemannInt_cv_pos_infty : 
    exists pr : forall (n : nat), Riemann_integrable f 0 (INR n), 
    Rseq_cv_pos_infty (fun n => RiemannInt (pr (S n))) ->
        (sum_f_R0 (fun n => f (INR n))) ~ (fun n => RiemannInt (pr (S n))).
Proof.
assert (pr : forall n : nat, Riemann_integrable f 0 n).
  intro n.
  apply continuity_implies_RiemannInt.
  intuition.
  intros x [Hx _]; apply (Hcont x Hx).
exists pr.
intro Hdiv.
destruct Rser_RiemannInt_link as [ l Hl].
apply Rseq_equiv_sym.
unfold Rseq_equiv, Rseq_minus.
apply Rseq_cv_little_O_cv_pos_infty with (-l).
  apply Rseq_cv_eq_compat with
      (sum_f_R0 (fun n : nat =>- (f (INR n) - RiemannInt (Riemann_integrable_f_n_Sn n)))).
    intro n.
    destruct (Rint_generalized_Chasles f 
                  (fun n =>RiemannInt (Riemann_integrable_f_n_Sn n))
                  (fun n => Rint_RiemannInt_link f n (S n) (Riemann_integrable_f_n_Sn n)) n) as [prn H].
    rewrite RiemannInt_P5 with _ _ _ (pr (S n)) prn.
    rewrite H.
    rewrite <- minus_sum.
    apply sum_eq; intros p Hp.
    unfold Rminus.
    ring.
  unfold Rser_cv in Hl.
  apply Rser_cv_opp_compat; apply Hl.
apply Hdiv.
Qed.

End Rser_RiemannInt_link.

Section Applications.

Definition ln1 := comp ln (fun x => x+1).

Lemma Rint_inv1 : forall a b, 
  -1 < a <= b -> Rint (/(id + fct_cte 1))%F a b (ln (b + 1) - ln (a + 1)).
Proof.
intros a b Hab.
replace (ln (b + 1)) with (comp ln (id + fct_cte 1) b) by reflexivity.
replace (ln (a + 1)) with (comp ln (id + fct_cte 1) a) by reflexivity.
apply Rint_derive.
intuition.
intros x Hx.
  replace ((/ (id + fct_cte 1))%F x) with ((/ (id + fct_cte 1))%F x * (1+0)) by ring.
  apply derivable_pt_lim_comp.
    apply derivable_pt_lim_plus.
      apply derivable_pt_lim_id.
      apply derivable_pt_lim_const.
      apply derivable_pt_lim_ln.

     unfold plus_fct, fct_cte, id.
     intuition.
     apply Rlt_le_trans with (a + 1); lra.
  intros x Hx.
  apply continuity_pt_inv.
  apply continuity_pt_plus.
  apply derivable_continuous, derivable_id.
  apply continuity_pt_const.
  unfold fct_cte; intros u v; reflexivity.
  unfold fct_cte, id, plus_fct.
  assert(0 < x + 1).
  apply Rlt_le_trans with (a + 1).
  replace 0 with (- 1 + 1) by ring.
  apply Rplus_lt_compat_r; intuition.
  apply Rplus_le_compat_r; intuition.
auto with *.
Qed.   
      
(** Equivalent of the harmonic series *)
Lemma harmonic_series_equiv : (sum_f_R0 (fun n => / (S n))) ~ (fun n => ln (S (S n))).
Proof.
destruct (Rser_RiemannInt_cv_pos_infty (/(id + fct_cte 1))%F) as [int_f_0_n Hi];
unfold plus_fct, fct_cte, id, inv_fct.
  intros x Hx.
    apply continuity_pt_inv.
    apply (continuity_pt_plus _ _ _ 
      (derivable_continuous id derivable_id x) 
      (derivable_continuous _ (derivable_const 1) x)).
    auto with *.

  auto with *.

  intros x y [Hxpos Hxy].
  apply Rle_Rinv; lra.
  assert (Heq2 : (fun n : nat => ln (INR (S (S n)))) ==
          (fun n : nat => RiemannInt (int_f_0_n (S n)))).
    intro n.
    replace (ln (S (S n))) with ((ln (S n + 1)%R - ln (O + 1))).
    destruct (Rint_inv1 0%nat (S n)) as [Hint Heq].
    change (INR O) with 0.
    auto with *.
    rewrite <- Heq.
    apply RiemannInt_P18.
    auto with *.
    reflexivity.
    replace (INR (S n) + 1) with (INR (S (S n))) by trivial.
    replace (INR 0 + 1) with 1 by (simpl; ring).
    rewrite ln_1.
    ring.
  assert(Rseq_cv_pos_infty (fun n : nat => RiemannInt (int_f_0_n (S n)))) as Hdiv.
    apply Rseq_cv_pos_infty_eq_compat with (fun n : nat => ln (S (S n))).
    apply Heq2.
    apply Rseq_subseq_cv_pos_infty_compat with (fun n => ln n).
    assert (Hex : is_extractor (fun n => (S (S n)))).
      constructor.
    exists (exist _ _ Hex).
    trivial.
  apply Rseq_ln_cv.
  assert(Heq1 : (sum_f_R0 (fun n : nat => (/ (id + fct_cte 1))%F (INR n))) ==
                 (sum_f_R0 (fun n : nat => / INR (S n)))).
    intro n; apply sum_eq; intros k Hk.

    unfold inv_fct, id, plus_fct, fct_cte.
    rewrite S_INR.
    reflexivity.
    apply Rseq_eq_sym in Heq2.
  apply (Rseq_equiv_eq_compat
  _ _ _ _  Heq1 Heq2 (Hi Hdiv)).
Qed.


End Applications.

End Rseries_RiemannInt.
