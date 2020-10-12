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
Require Import Rsequence_facts.
Require Export Rseries.
Require Import Rsequence_subsequence.
Require Import Rtactic.
Require Import Lia.

Open Scope R_scope.

(* begin hide *)
Ltac solve_with_eq a b := let H := fresh in 
 assert (H : a = b); [ | rewrite H; try reflexivity].

Ltac inject := match goal with |- ?a = ?b => recinject (a = b) end
with recinject t := match t with
  | ?a = ?a => idtac
  | ?a ?b = ?a ?c => recinject (b = c)
  | ?b ?a = ?c ?a => recinject (b = c)
  | ?b = ?c => solve_with_eq b c
end.
(* end hide *)

(* Better S_INR *)
Lemma plus_1_S : forall a, INR (S a) = 1 + (INR a).
Proof.
intros.
INR_solve.
Qed.

(** * Convergence of the 1/n² series *)

Definition Rseq_square_inv n := / (INR n) ^ 2.
Definition Rseq_square_inv_s n := / (INR (S n)) ^ 2.

(** * Splitting series in odd and even terms *)

Definition odds Un : Rseq := fun n => Un (S (2 * n)).
Definition evens Un : Rseq := fun n => Un (mult 2 n).

(** Convergence of splitting *)
Lemma Rser_cv_pair_compat : forall Un l, Rser_cv Un l -> Rser_cv (fun n => Un (mult 2 n) + Un (S (mult 2 n))) l.
Proof.
intros Un l Ucv.
intros e epos.
destruct (Ucv e epos) as [N Hu].
exists N; intros n nN.
replace (Rseq_sum (fun n0 : nat => Un (2 * n0)%nat + Un (S (2 * n0))) n)
 with (Rseq_sum Un (S (2 * n))).
 intros; apply Hu; lia.
 
 clear nN.
 induction n.
  intros; simpl; ring.
  
  simpl Rseq_sum.
  replace (n + S (n + 0))%nat with (S (2 * n)) by ring.
  rewrite IHn.
  ring_simplify.
  assert (SIMPL : forall a b c d, a = c -> a + b + d = b + d + c) by (intros; subst; ring).
  apply SIMPL.
  apply Rseq_sum_ext; intro.
  simpl; trivial.
Qed.

(** Finite sum splitting *)

Lemma sum_odd_even_split : forall an n, sum_f_R0 (odds an) n =
  sum_f_R0 an (S (2 * n)) - sum_f_R0 (evens an) n.
Proof.
intros an n.
induction n.
 simpl; unfold odds, evens; simpl; ring.
 
 simpl.
 rewrite IHn.
 replace (n + S (n + 0))%nat with (S (2 * n)) by ring.
 unfold odds, evens.
 simpl.
 replace (S (S (n + S (n + 0)))) with (S (2 * S n)) by ring.
 replace (S (S (n + (n + 0)))) with (2 * S n)%nat by ring.
 replace (S (n + S (n + 0))) with (2 * S n)%nat by ring.
 ring.
Qed.

(** Substracting odd terms *)

Lemma remove_odds : forall Un l, {lu | Rser_cv Un lu} ->
  Rser_cv (evens Un) l -> Rser_cv (Un - (odds Un)) l.
Proof.
intros Un lo [lu Hu] Ho.
replace lo with (lu - (lu - lo)) by ring.
apply Rser_cv_minus_compat; try assumption.
apply Rseq_cv_eq_compat with ((fun n => sum_f_R0 Un (S (2 * n))) - sum_f_R0 (evens Un))%Rseq.
 intro n; rewrite (sum_odd_even_split); trivial.
 apply Rseq_cv_minus_compat.

 eapply Rseq_subseq_cv_compat; [|apply Hu].
  assert (Hex : is_extractor (fun i => S (2 * i))).
    intros n; lia.
  exists (exist _ _ Hex).
  reflexivity.
  assumption.
Qed.

(** Substracting even terms *)

Lemma remove_evens : forall Un l, {lu | Rser_cv Un lu} ->
  Rser_cv (odds Un) l -> Rser_cv (Un - evens Un) l.
Proof.
intros Un lo [lu Hu] Ho.
replace lo with (lu - (lu - lo)) by ring.
apply Rser_cv_minus_compat; try assumption.
apply Rseq_cv_eq_compat with ((fun n => sum_f_R0 Un (S (2 * n))) - sum_f_R0 (odds Un))%Rseq.
 intro n. symmetry.
 assert (REW : forall a b c, a - b = c -> a - c = b) by (intros; subst; ring); apply REW.
 rewrite (sum_odd_even_split); trivial.
 
 apply Rseq_cv_minus_compat.
  eapply Rseq_subseq_cv_compat; [|apply Hu].
   assert (Hex : is_extractor (fun i => S (2 * i))).
     intros n; lia.
   exists (exist _ _ Hex).
   
   reflexivity.
  
  assumption.
Qed.

(** * Introduction of pi *)

Definition antg : nat -> R := fun n => (- 1)^n / (2 * (INR n) + 1).
Definition antg_neg : nat -> R := fun n => (- 1)^n / (- 2 * (INR n) + 1).

Lemma PI_tg_PI : Rseq_cv (sum_f_R0 (tg_alt PI_tg)) (PI / 4).
Proof.
  generalize PI_ineq, exist_PI.
  generalize (sum_f_R0 (tg_alt PI_tg)) as u.
  generalize (PI / 4) as x.
  intros x u Hu [y Hy].
  rewrite <-Rseq_cv_Un_cv_equiv in Hy.
  change (fun N : nat => u N) with u in Hy.
  pose proof Rseq_sandwich_theorem.
  assert (uy : Rseq_cv (fun N : nat => u (2 * N)%nat) y).
  { eapply Rseq_subseq_cv_compat; eauto.
    apply subsequence_helper with (mult 2). lia. reflexivity. }
  assert (uy' : Rseq_cv (fun N : nat => u (S (2 * N))%nat) y).
  { eapply Rseq_subseq_cv_compat; [ | apply Hy].
    apply subsequence_helper with (fun n => S (2 * n)). lia. reflexivity. }
  pose proof Rseq_sandwich_theorem _ _ _ y uy' uy Hu as xy.
  pose proof Rseq_constant_cv x as xx.
  pose proof Rseq_cv_unique _ _ _ xx xy.
  now subst.
Qed.

Lemma Sum_antg : Rser_cv antg (PI / 4).
Proof.
  unfold Rser_cv.
  eapply Rseq_cv_eq_compat with (sum_f_R0 (tg_alt PI_tg)). 2: apply PI_tg_PI.
  apply Rseq_sum_ext.
  intros n.
  unfold tg_alt, PI_tg, antg.
  INR_group (2 * INR n + 1).
  field.
  INR_solve.
Qed.

Lemma antg_shift_neg_compat : Rseq_shift antg_neg == antg.
Proof.
intro n.
unfold Rseq_shift.
unfold antg.
unfold antg_neg.
rewrite S_INR.
simpl pow.
field; split;
 replace (-2) with (-(2%R)) by reflexivity;
 replace 2 with (INR 2) by reflexivity;
 replace 1 with (INR 1) by reflexivity.
 INR_solve.

 intro Hinv.
 rewrite Ropp_mult_distr_l_reverse in Hinv.
 pose proof (Rplus_opp_r_uniq _ _ Hinv) as H.
 rewrite Ropp_involutive in H.
 rewrite <- plus_INR in H.
 rewrite <- mult_INR in H.
 generalize dependent H.
 apply not_INR.
 lia.
Qed.

Lemma Sum_antg_neg : Rser_cv antg_neg (PI / 4 + 1).
Proof.
 apply Rser_cv_shift_rev2.
 eapply Rser_cv_ext.
 apply antg_shift_neg_compat.
 replace (PI / 4 + 1 - antg_neg 0) with (PI / 4) by (compute; field).
 apply Sum_antg.
Qed.

Definition bntg n := / (2 * (INR n) + 1) ^ 2.
Definition bntg_neg n := / (- 2 * (INR n) + 1) ^ 2.

Lemma bntg_pos : forall n, 0 < bntg n.
Proof.
intro n.
unfold bntg.
INR_solve.
Qed.

Lemma odd_not_zero : forall n, 2 * (INR n) + 1 <> 0.
Proof.
intros.
INR_solve.
Qed.

Lemma neg_odd_not_zero : forall n, 2 * (INR n) - 1 <> 0.
Proof.
intros.
destruct n.
 simpl.
 replace (2 * 0 - 1) with (- 1) by field.
  apply Ropp_neq_0_compat; apply R1_neq_R0.
  INR_solve.
Qed.

Lemma bntg_neg_simpl : forall n, 
  1 / (- 2 * (INR n) + 1) ^ 2 = 1 / (2 * (INR n) - 1) ^ 2.
Proof.
intros; field.
split.
 apply neg_odd_not_zero.
 replace (-2 * INR n + 1) with (- (2 * (INR n) - 1)) by field.
 apply Ropp_neq_0_compat; apply neg_odd_not_zero.
Qed.

Definition pi_tg2 (n : nat) := 2 / ((4 * (INR n) + 1) * (4 * (INR n) + 3)).

Lemma pi_tg2_corresp : forall n, 
  pi_tg2 n = tg_alt PI_tg (2 * n) + tg_alt PI_tg (S (2 * n)).
Proof.
intros.
unfold tg_alt, PI_tg, pi_tg2.
rewrite pow_1_odd.
rewrite pow_1_even.
assert (R1 : INR ((2 * (2 * n) + 1)%nat) = 2 * (2 * (INR n)) + 1) by INR_solve.
assert (R2 : INR ((2 * S (2 * n) + 1)%nat) = 2 * (1 + (2 * (INR n))) + 1) by INR_solve.
rewrite R1.
rewrite R2.
field.
split;
 [replace (1 + 2 * (INR n)) with (INR (1 + 2 * n)); [apply (odd_not_zero) | rewrite plus_INR]
 |replace (2 * (INR n)) with (INR (2 * n)); [apply odd_not_zero | ]];
 rewrite mult_INR; trivial.
Qed.

Lemma pi_tg2_cv : { l | Rser_cv pi_tg2 l }.
Proof.
destruct (exist_PI) as [PI_4 Hc].
exists PI_4.
apply Rser_cv_ext with (fun n => tg_alt PI_tg (2 * n) + tg_alt PI_tg (S (2 * n))).
 intro n; apply pi_tg2_corresp.
 
 apply Rser_cv_pair_compat.
 intros eps epspos.
 
 destruct (Hc eps epspos) as [N H].
 exists N.
 intros n nN.
 apply (H n nN).
Qed.

Lemma Rser_cv_bntg : {l | Rser_cv bntg l}.
Proof.
eapply Rser_pos_maj_cv.
 intro; apply Rlt_le; apply bntg_pos.
 
 3: apply Rser_cv_square_inv.
 
 intro; apply Rlt_le; apply Rinv_0_lt_compat; apply pow_lt; INR_solve.
 
 intro n; apply Rle_Rinv; unfold Rseq_shift ; try (apply pow_lt; INR_solve).
 unfold pow; INR_solve; try (apply mult_le_compat; lia).
Qed.

(** * Sums indexed by relative integers (from -N to N) *)

Require Import ZArith.

Fixpoint bisum (f : Z -> R) (N : nat) := match N with
  | O => f Z0
  | S n => (bisum f n) + f (Z_of_nat N) + f (- Z_of_nat N)%Z
end.

(** - 1 to a relative integer Z *)

Definition pow1_P p := match p with xO _ => 1 | _ => -1 end.

Definition pow1 z := match z with
  | Z0 => 1
  | Zpos n | Zneg n => pow1_P n
end.

Lemma pow1_P_ind : forall p, pow1_P (Pos.succ (Pos.succ p)) = pow1_P p.
Proof.
destruct p; trivial.
Qed.

Lemma nat_ind2 : forall (P : nat -> Prop), 
  P O -> P (S O) -> (forall m, P m -> P (S (S m))) -> forall n, P n. 
Proof.
intros P H0 H1 H n.
assert (P n /\ P (S n)).
 induction n; split; try assumption; [ | apply H]; apply IHn.
 apply H2.
Qed.

Lemma pow1_nat : forall n, pow1 (Z_of_nat n) = (- 1) ^ n.
Proof.
intros n.
destruct n.
 trivial.
 unfold Z_of_nat.
 simpl pow1.
 generalize dependent n; apply nat_ind2; try (simpl; trivial; ring).
 intros n H; simpl.
 rewrite pow1_P_ind.
 rewrite H.
 simpl pow; field.
Qed.

Lemma pow1_nat_neg : forall n, pow1 (- Z_of_nat n) = (- 1) ^ n.
Proof.
intros n.
destruct n.
 trivial.
 unfold Z_of_nat.
 simpl pow1.
 generalize dependent n; apply nat_ind2; try (simpl; trivial; ring).
 intros n H; simpl.
 rewrite pow1_P_ind.
 rewrite H.
 simpl pow; field.
Qed.

Lemma pow1_squared : forall z, (pow1 z) ^ 2 = 1.
Proof.
destruct z; [simpl; ring | | ]; unfold pow1;
  destruct p;
    simpl; ring.
Qed.

Lemma pow1_Rabs : forall z, Rabs (pow1 z) = 1.
Proof.
destruct z; try destruct p; simpl; change (-1) with (-(1%R)); try rewrite Rabs_Ropp; apply Rabs_R1.
Qed.

Lemma pow1_P_plus : forall a b, pow1_P (a + b) = pow1_P a * pow1_P b.
Proof.
intros a b.
destruct a; destruct b; simpl; ring.
Qed.

Lemma pow1_succ : forall z, pow1 (Z.succ z) = - pow1 z.
Proof.
destruct z; trivial;
 destruct p; simpl; try ring;
 destruct p; simpl; ring.
Qed.

Lemma pow1_plus_nat : forall a b, pow1 (a + Z_of_nat b) = (pow1 a) * (-1) ^ b.
Proof.
intros.
induction b.
 simpl; ring_simplify; inject; lia.
 
 rewrite inj_S; rewrite <- Zplus_succ_r_reverse; rewrite pow1_succ.
 rewrite IHb.
 simpl; ring.
Qed.

(** Operations on bisums *)

Definition zr (op : R -> R) (f : Z -> R) z := op (f z).
Definition zr2 (op : R -> R -> R) (f g : Z -> R) z := op (f z) (g z).
Definition zr22 (op : R -> R -> R) (f g : Z -> Z -> R) x y := op (f x y) (g x y).

Lemma bisum_eq_compat : forall f g n, (forall z, f z = g z) -> bisum f n = bisum g n.
Proof.
intros.
induction n.
 simpl; apply H.
 
 simpl; do 2 rewrite H.
 rewrite IHn; trivial.
Qed.

Lemma bisum_plus : forall f g n, bisum (zr2 Rplus f g) n = bisum f n + bisum g n.
Proof.
induction n.
 trivial.
 
 simpl bisum; rewrite IHn.
 unfold zr2; ring.
Qed.

Lemma bisum_minus : forall f g n, bisum (zr2 Rminus f g) n = bisum f n - bisum g n.
Proof.
induction n.
 trivial.
 
 simpl bisum; rewrite IHn.
 unfold zr2; ring.
Qed.

Lemma bisum_scal_mult : forall f a n, bisum (zr (Rmult a) f) n = a * (bisum f n).
Proof.
induction n.
 trivial.
 
 simpl bisum; rewrite IHn.
 unfold zr; ring.
Qed.

Lemma bisum_mult : forall f g n m, (bisum f n) * (bisum g m) = 
  bisum (fun i => bisum (fun j => f i * g j) m) n.
Proof.
induction n.
 simpl; intro.
 replace (fun j : Z => f 0%Z * g j) with (zr (Rmult (f 0%Z)) g) by trivial.
 rewrite bisum_scal_mult; trivial.
 
 intros m.
 simpl bisum.
 repeat rewrite Rmult_plus_distr_r.
 rewrite IHn.
 replace (fun j : Z => f (Zpos (P_of_succ_nat n)) * g j) with (zr (Rmult (f (Zpos (P_of_succ_nat n)))) g) by trivial.
 replace (fun j : Z => f (Zneg (P_of_succ_nat n)) * g j) with (zr (Rmult (f (Zneg (P_of_succ_nat n)))) g) by trivial.
 repeat rewrite bisum_scal_mult.
 trivial.
Qed.

(** Reversing terms *)

Lemma bisum_reverse : forall f n, bisum f n = bisum (fun i => f (- i)%Z) n.
Proof.
induction n.
 trivial.
 
 simpl.
 rewrite IHn.
 ring.
Qed.

(** Rewriting a bisum as sums *)

Lemma sum_bisum : forall n f, bisum f (S n) =
  sum_f_R0 (fun i => f (Z_of_nat i)) (S n) + sum_f_R0 (fun i => f (- Z_of_nat (S i))%Z) n.
Proof.
intros.
induction n.
 trivial.
 
 replace (bisum f (S (S n))) with (bisum f (S n) + f (Zpos (Pos.succ (P_of_succ_nat n))) + 
   f (Zneg (Pos.succ (P_of_succ_nat n)))) by trivial.
 rewrite IHn.
 simpl.
 ring.
Qed.

(** * Introducing pi to bisums *)

Definition anz z := (pow1 z) / (2 * (IZR z) + 1).
Definition bnz z := / (2 * (IZR z) + 1) ^ 2.
Definition An := bisum anz.
Definition Bn := bisum bnz.

Lemma anz_antg : forall n, antg n = anz (Z_of_nat n).
Proof.
intro n.
unfold antg, anz.
destruct n.
 simpl; field.
 
 rewrite pow1_nat.
 rewrite <- INR_IZR_INZ.
 trivial.
Qed.

Lemma anz_antg_neg : forall n, antg_neg n = anz (- Z_of_nat n).
Proof.
intro n.
unfold antg_neg, anz.
destruct n.
 simpl; field.
 
 rewrite pow1_nat_neg.
 rewrite Ropp_Ropp_IZR.
 rewrite <- INR_IZR_INZ.
 field.
 rewrite plus_1_S.
 replace (2 * - (1 + INR n) + 1) with (- (1 + 2 * INR n)) by ring.
 apply Ropp_neq_0_compat.
 repeat INR_solve.
Qed.

Lemma bisum_anz_antg : (sum_f_R0 antg + (sum_f_R0 antg_neg - 1))%Rseq == bisum anz.
Proof.
intro n.
induction n.
 compute; field.
 
 simpl bisum.
 rewrite <- IHn.
 unfold Rseq_minus.
 unfold Rseq_plus.
 unfold Rseq_constant.
 repeat rewrite tech5.
 repeat rewrite anz_antg_neg.
 repeat rewrite anz_antg.
 replace (Zneg (P_of_succ_nat n)) with (- Z_of_nat (S n))%Z by trivial.
 replace (Zpos (P_of_succ_nat n)) with (Z_of_nat (S n))%Z by trivial.
 ring.
Qed.

Lemma An_cv : Rseq_cv An (PI / 2).
Proof.
replace (PI / 2) with (PI / 4 + (PI / 4 + 1 - 1)) by field.
eapply Rseq_cv_eq_compat.
 2: apply Rseq_cv_plus_compat.
 2: apply Sum_antg.
 
 2: eapply Rseq_cv_eq_compat.
  3: apply Rseq_cv_minus_compat.
   3: apply Sum_antg_neg.
   3: apply Rseq_constant_cv.
 symmetry. apply bisum_anz_antg.
 intro; trivial.
Qed.

Lemma An_squared_cv : Rseq_cv (An * An) (PI ^ 2 / 4).
Proof.
replace (PI ^ 2 / 4) with ((PI / 2) * (PI / 2)) by field.
apply Rseq_cv_mult_compat; apply An_cv.
Qed.

(** * Double sums *)

Definition bisumsum f N := bisum (fun i => (bisum (f i) N)) N.

(** Double sum minus its diagonal *)

Definition bisum_strip f j N := bisum f N - (f j).
Definition bisumsum_strip_diag f N := bisumsum f N - bisum (fun i => (f i i)) N.

(** Double sum in which its diagonal terms are null *)

Definition bisum_strip' f j N := bisum (fun i => if Z.eq_dec i j then 0 else f i) N.
Definition bisumsum_strip_diag' f N := bisumsum (fun i j => if Z.eq_dec i j then 0 else f i j) N.

(** Weak extensional equality *)

Lemma bisumsum_eq_compat : forall f g n, (forall x y, f x y = g x y) ->
  bisumsum f n = bisumsum g n.
Proof.
intros; apply bisum_eq_compat.
intros; apply bisum_eq_compat.
apply H.
Qed.

(** Bounded extensional equality *)

Lemma bisum_eq_compat_bounded : forall f g n, (forall z, ((-Z_of_nat n) <= z <= Z_of_nat n)%Z -> f z = g z) ->
  bisum f n = bisum g n.
Proof.
intros.
induction n.
 simpl; apply H; simpl; lia.
 
 simpl.
 rewrite H; [ | simpl; split; [apply Zle_neg_pos | lia]].
 rewrite H; [ | simpl; split; [lia | apply Zle_neg_pos]].
 rewrite IHn.
  trivial.
  
  intros z [H1 H2].
  apply H; split; eapply Z.le_trans; [ | apply H1 | apply H2 | ]; rewrite inj_S; lia.
Qed.

(** Double sum distributivity *)

Lemma bisumsum_square : forall f n, bisumsum (fun i j => f i * f j) n = bisum f n * bisum f n.
Proof.
intros.
rewrite bisum_mult.
trivial.
Qed.

(** Inequalities *)

Lemma Psucc_lt : forall p, (Zpos p < Zpos (Pos.succ p))%Z.
Proof.
intros.
replace (Zpos (Pos.succ p)) with (1 + Zpos p)%Z.
 lia.
 induction p; trivial.
Qed.

Lemma Psucc_lt_neg : forall p, (Zneg (Pos.succ p) < Zneg p)%Z.
Proof.
intros.
replace (Zneg (Pos.succ p)) with (- 1 + Zneg p)%Z.
 lia.
 induction p; trivial.
Qed.

(** A special term outside the bounds can be ignored *)

Lemma bisum_not_in : forall f g j n, (j < (- Z_of_nat n) \/ Z_of_nat n < j)%Z -> 
  bisum (fun i : Z => if Z.eq_dec i j then g j else f i) n = bisum f n.
Proof.
intros.
apply bisum_eq_compat_bounded; intros.
destruct H.
 destruct (Z.eq_dec z (- Z_of_nat (S n))).
  subst;  destruct H0; rewrite inj_S in * |-; apply False_ind; lia.
  destruct (Z.eq_dec z j).
   subst; apply False_ind; lia.
   trivial.
 destruct (Z.eq_dec z (Z_of_nat (S n))).
  subst;  destruct H0; rewrite inj_S in * |-; apply False_ind; lia.
  destruct (Z.eq_dec z j).
   subst; apply False_ind; lia.
   trivial.
Qed.

(** A special term between the bounds can be extracted *)

Lemma bisum_in : forall f g j n, (- Z_of_nat n <= j <= Z_of_nat n)%Z -> 
  bisum (fun i : Z => if Z.eq_dec i j then g j else f i) n = bisum f n - f j + g j.
Proof.
intros.
induction n.
 assert (j = Z0) by (replace (Z_of_nat O) with Z0 in H by trivial; lia); subst; trivial.
 simpl; ring.
 
 set (h := fun i => if Z.eq_dec i j then g j else f i).
 simpl bisum; unfold h in *.
 destruct (Z.eq_dec (Zpos (P_of_succ_nat n)) j) as [e|e];
 destruct (Z.eq_dec (Zneg (P_of_succ_nat n)) j) as [e'|e']; subst; try inversion e'.
  rewrite bisum_not_in.
   ring.
   right; destruct n; simpl.
    lia.
    apply Psucc_lt.
  
  rewrite bisum_not_in.
   ring.
   left; destruct n; simpl.
    lia.
    apply Psucc_lt_neg.
  
  rewrite IHn.
   ring.
   split; rewrite inj_S in H.
    destruct (Z_le_gt_dec (- Z_of_nat n) j); trivial.
    replace (Zneg (P_of_succ_nat n)) with (- Z_of_nat (S n))%Z in e' by trivial.
    rewrite inj_S in *.
    lia.
    
    destruct (Z_le_gt_dec j (Z_of_nat n)); trivial.
    replace (Zpos (P_of_succ_nat n)) with (Z_of_nat (S n))%Z in e by trivial.
    rewrite inj_S in *.
    lia.
Qed.

(** Stripping terms *)

Definition Zzero : Z -> R := fun _ => 0.

Lemma bisum_strip_equiv : forall f n j, ((- Z_of_nat n) <= j <= Z_of_nat n)%Z -> 
  bisum_strip f j n = bisum_strip' f j n.
Proof.
intros.
unfold bisum_strip, bisum_strip'.

replace
  (bisum (fun i : Z => if Z.eq_dec i j then 0 else f i) n) with
  (bisum (fun i : Z => if Z.eq_dec i j then Zzero j else f i) n).
 
 rewrite bisum_in.
  unfold Zzero; ring.
  apply H.
 
 unfold Zzero; trivial.
Qed.

Lemma bisum_strip_nothing : forall f n j, ((- Z_of_nat (S n)) = j \/ j = Z_of_nat (S n))%Z -> 
  bisum_strip' f j n = bisum f n.
Proof.
intros.
unfold bisum_strip'.
apply bisum_eq_compat_bounded; intros.
destruct H; subst.
 destruct (Z.eq_dec z (- Z_of_nat (S n))).
  subst; destruct H0; rewrite inj_S in * |- ; apply False_ind; lia.
  trivial.
 destruct (Z.eq_dec z (Z_of_nat (S n))).
  subst; destruct H0; rewrite inj_S in * |- ; apply False_ind; lia.
  trivial.
Qed.

(** Steps of calculus in bisums *)

Lemma bisum_one_step : forall f n, bisum f (S n) = bisum f n + f (Z_of_nat (S n)) + f (- Z_of_nat (S n))%Z.
Proof.
trivial.
Qed.

Lemma bisumsum_one_step : forall f n m, 
  bisum (fun i => bisum (f i) (S n)) m =
  bisum (fun i => bisum (f i) n) m + 
  bisum (fun i =>        f i (Z_of_nat (S n))    ) m +
  bisum (fun i =>        f i (- Z_of_nat (S n))%Z ) m.
intros.
simpl.
repeat rewrite <- bisum_plus.
apply bisum_eq_compat; intros.
trivial.
Qed.

(** Switching indices *)

Lemma bisum_eq_sym : forall f z n,
  bisum (fun i : Z => if Z.eq_dec i z then 0 else f z i) n =
  bisum (fun j : Z => if Z.eq_dec z j then 0 else f z j) n.
Proof.
intros; apply bisum_eq_compat; intros.
destruct (Z.eq_dec z0 z); destruct (Z.eq_dec z z0); try trivial; subst; 
  apply False_ind; apply n0; trivial.
Qed.

(** Substracting the diagonal terms sum makes them null in the main double sum *)

Lemma strip_diag : forall f n, bisumsum_strip_diag' f n = bisumsum_strip_diag f n.
Proof.
intros.
induction n.
 unfold bisumsum_strip_diag', bisumsum_strip_diag, bisumsum.
 simpl; ring.
 
 unfold bisumsum_strip_diag', bisumsum_strip_diag, bisumsum.
 rewrite bisumsum_one_step.
 rewrite bisum_one_step.
 unfold bisumsum_strip_diag', bisumsum_strip_diag, bisumsum in IHn.
 rewrite IHn.
 rewrite (bisum_one_step (fun i : Z => f i i)).
 repeat rewrite bisum_one_step.
 destruct (Z.eq_dec (Z_of_nat (S n)) (Z_of_nat (S n))); [ | apply False_ind; lia]; clear e.
 destruct (Z.eq_dec (Z_of_nat (S n)) (- Z_of_nat (S n))); [ apply False_ind; inversion e | ]; clear n0.
 destruct (Z.eq_dec (- Z_of_nat (S n)) (Z_of_nat (S n))); [ apply False_ind; inversion e | ]; clear n0.
 destruct (Z.eq_dec (- Z_of_nat (S n)) (- Z_of_nat (S n))); [ | apply False_ind; lia]; clear e.
 ring_simplify.
 assert (H : forall BII FNP FPN A B C D BIJ BIJS BPJS BNJS,
  BIJ + A + B + C + D = BIJS + BPJS + BNJS ->
  BIJ - BII + A + B + C + FNP + D + FPN = - BII + FNP + FPN + BIJS + BPJS + BNJS)
 by (intros; assert (H' : BIJ = - (A + B + C + D) + (BIJS + BPJS + BNJS)) by (rewrite <- H; ring); rewrite H'; ring).
 erewrite H; [reflexivity | ].
 replace (bisum (fun j : Z => if Z.eq_dec (Z_of_nat (S n)) j then 0 else f (Z_of_nat (S n)) j) n)
   with (bisum_strip' (f (Z_of_nat (S n))) (Z_of_nat (S n)) n) by apply bisum_eq_sym.
 replace (bisum (fun j : Z => if Z.eq_dec (- Z_of_nat (S n)) j then 0 else f (- Z_of_nat (S n))%Z j) n)
   with (bisum_strip' (f (- Z_of_nat (S n)))%Z (- Z_of_nat (S n)) n)%Z by apply bisum_eq_sym.
 replace (bisum (fun i : Z => if Z.eq_dec i (- Z_of_nat (S n)) then 0 else f i (- Z_of_nat (S n))%Z) n)
   with (bisum_strip' (fun i => f i (- Z_of_nat (S n)))%Z (- Z_of_nat (S n)) n)%Z by trivial.
 replace (bisum (fun i : Z => if Z.eq_dec i (Z_of_nat (S n)) then 0 else f i (Z_of_nat (S n))) n)
   with (bisum_strip' (fun i => f i (Z_of_nat (S n)))%Z (Z_of_nat (S n)) n)%Z by trivial.
 repeat rewrite bisum_strip_nothing; [ | left | right | left | right ]; trivial.
 rewrite bisumsum_one_step.
 ring.
Qed.

(** * Rewriting double sums *)

(** Switching indices in a double sum *)

Lemma bisumsum_switch_index : forall f n, bisumsum (fun i j => f j i) n = bisumsum f n.
Proof.
intros.
induction n.
 trivial.
 
 unfold bisumsum in *.
 rewrite bisumsum_one_step.
 rewrite bisumsum_one_step.
 simpl.
 rewrite IHn.
 replace (bisum (f (Zneg (P_of_succ_nat n))) n) with (bisum (fun i => f (Zneg (P_of_succ_nat n)) i) n) by (apply bisum_eq_compat; trivial).
 replace (bisum (f (Zpos (P_of_succ_nat n))) n) with (bisum (fun i => f (Zpos (P_of_succ_nat n)) i) n) by (apply bisum_eq_compat; trivial).
 ring.
Qed.

(** Switching indices in a double sum (where diagonal terms are null) *)

Lemma bisumsum_strip_diag'_switch_index : forall f n,
  bisumsum_strip_diag' (fun i j => f j i) n =
  bisumsum_strip_diag' f n.
Proof.
intros.
unfold bisumsum_strip_diag'.
rewrite bisumsum_switch_index.
apply bisumsum_eq_compat; intros.
destruct (Z.eq_dec y x); destruct (Z.eq_dec x y); try trivial;
  subst; apply False_ind; apply n0; trivial.
Qed.

(** Adding double sums *)

Lemma bisumsum_strip_diag'_plus : forall f g n,
  bisumsum_strip_diag' (fun i j => f i j + g i j) n =
  bisumsum_strip_diag' f n +
  bisumsum_strip_diag' g n.
Proof.
intros.
unfold bisumsum_strip_diag'.
unfold bisumsum.
rewrite <- bisum_plus.
apply bisum_eq_compat; intros.
unfold zr2.
rewrite <- bisum_plus.
apply bisum_eq_compat; intros.
unfold zr2.
destruct (Z.eq_dec z z0); ring.
Qed.

(** Switching indices of only one term in a sum in a double sum *)

Lemma bisumsum_plus_switch : forall f g n,
  bisumsum_strip_diag' (fun i j => f i j + g i j) n =
  bisumsum_strip_diag' (fun i j => f i j + g j i) n.
Proof.
intros.
rewrite bisumsum_strip_diag'_plus.
rewrite <- bisumsum_strip_diag'_switch_index with g n.
rewrite <- bisumsum_strip_diag'_plus.
trivial.
Qed.

(** Extensional equality but on the diagonal terms *)

Lemma bisumsum_strip_diag'_eq_but_diag_compat : forall f g n,
  (forall i j, i <> j -> f i j = g i j) ->
  bisumsum_strip_diag' f n = bisumsum_strip_diag' g n.
Proof.
intros.
apply bisum_eq_compat; intros.
apply bisum_eq_compat; intros.
destruct (Z.eq_dec z z0).
 trivial.
 apply (H _ _ n0).
Qed.

(** Shifting a sequence (with an integer) *)
Fixpoint sum1 u n := match n with
  | O => 0
  | S n' => (sum1 u n') + u (Z_of_nat n)
end.

Lemma sum_f_R0_sum1 : forall u n, sum1 u (S n) = 
  sum_f_R0 (fun i => u (Z_of_nat (S i))) n.
Proof.
intros.
induction n.
 compute; ring.
 
 simpl in *.
 rewrite IHn.
 trivial.
Qed.

Definition shiftp (u:Z->R) (p:nat) (i:Z) := u (i + (Z_of_nat p))%Z.

Lemma bisum_shifting_S : forall u a b, 
  bisum (shiftp u (S b)) (S a) = 
  bisum (shiftp u b) a +
  u (Z_of_nat (S (a + b))) +
  u (Z_of_nat (S (S (a + b))))
.
Proof.
intros.
induction a.
 unfold bisum, shiftp.
 assert (AP : forall a b c a' b' c', a = a' -> b = b' -> c = c' ->
   a + b + c = c' + a' + b') by (intros; subst; ring);
   apply AP; clear AP;
   inject;
   simpl (0 + b)%nat; simpl (Z_of_nat 1); repeat rewrite inj_S; lia.
 rewrite bisum_one_step.
 rewrite IHa; clear IHa.
 rewrite bisum_one_step.
 repeat rewrite Rplus_assoc.
 inject.
 unfold shiftp.
 repeat rewrite <- Rplus_assoc.
 assert (AP : forall a b c d a' b' c' d', a = a' -> b = b' -> c = c' -> d = d' ->
   a + b + c + d = a' + d' + b' + c') by (intros; subst; ring);
   apply AP; clear AP;
   inject;
   try (simpl (0 + b)%nat; simpl (Z_of_nat 1); repeat rewrite inj_S; lia);
   repeat rewrite inj_S; rewrite inj_plus; repeat rewrite inj_S; lia.
Qed.

Lemma bisum_shifting : forall u n p, 
  bisum (shiftp u p) (n + p) = 
  bisum u n + sum1 (shiftp u n) (2 * p)
.
Proof.
intros.
induction p.
 rewrite bisum_eq_compat with _ u _; 
   [| intro; unfold shiftp; inject; simpl Z_of_nat; lia].
 simpl.
 ring_simplify; inject; lia.
 
 rewrite <- plus_n_Sm.
 replace (mult 2 (S p)) with (S (S (2 * p))) by lia.
 replace (sum1 (shiftp u n) (S (S (2 * p))))
   with (sum1 (shiftp u n) (2 * p) + 
     (shiftp u n) (Z_of_nat (S (2 * p))) + 
     (shiftp u n) (Z_of_nat (S (S (2 * p)))))
   by trivial.
 repeat rewrite <- Rplus_assoc.
 rewrite <- IHp; clear IHp.
 replace (bisum (shiftp u (S p)) (S (n + p)))
   with (bisum (shiftp u p) (n + p) + 
     (shiftp u n) (Z_of_nat (S (2 * p))) +
     (shiftp u n) (Z_of_nat (S (S (2 * p)))))
     ; [trivial | ].
 rewrite bisum_shifting_S.
 unfold shiftp.
 replace (mult 2 p) with (plus p p) by lia.
 assert (AP : forall a b c a' b' c', a = a' -> b = b' -> c = c' ->
   a + b + c = a' + b' + c') by (intros; subst; ring);
   apply AP; clear AP; trivial;
   inject;
   repeat (repeat rewrite inj_S; repeat rewrite inj_plus); lia.
Qed.

(** * Rewriting An * An - Bn *)

Definition d x := 2 * x + 1.
Definition d' z := d (IZR z).

Lemma splitmn : forall n m, d n <> 0 -> d m <> 0 -> m <> n -> 
  / ((d n) * (d m)) = / (2 * (m - n)) * (/ (d n) - / (d m)).
Proof.
intros.
unfold d in *.
field.
split; [|split].
 assumption.
 assumption.
 apply Rminus_eq_contra; assumption.
Qed.

Lemma d_not_null : forall z, d' z <> 0.
Proof.
intros.
unfold d', d.
discrR; lia.
Qed.

Lemma calc1 : forall N, (An N) * (An N) - Bn N =
  bisumsum_strip_diag' (fun n m =>
    (pow1 m * pow1 n) * / (2 * (IZR (m - n))) * (/ (d' n) - / (d' m))
  ) N.
Proof.
assert (forall z, 2 * IZR z + 1 <> 0) by (intro; discrR; lia).
intros N.
unfold An.
rewrite <- bisumsum_square.
replace (Bn N) with (bisum (fun i => anz i * anz i) N).
 rewrite bisumsum_strip_diag'_eq_but_diag_compat with _ (fun i j => anz i * anz j) _.
  rewrite strip_diag.
  unfold bisumsum_strip_diag.
  trivial.
  
  intros.
  unfold anz.
  replace (pow1 i / (2 * IZR i + 1) * (pow1 j / (2 * IZR j + 1)))
    with (pow1 i * pow1 j * (/ ((2 * IZR i + 1) * (2 * IZR j + 1)))).
   2:field_simplify; [ trivial | split | split ]; try apply d_not_null.
   
   replace (2 * IZR i + 1) with (d (IZR i)) by trivial.
   replace (2 * IZR j + 1) with (d (IZR j)) by trivial.
   rewrite splitmn; try apply d_not_null; try (discrR; lia).
    unfold d'.
    rewrite Z_R_minus.
    field; repeat split; try apply d_not_null; discrR; lia.
 
 apply bisum_eq_compat.
 intro.
 unfold bnz, anz; field_simplify; try apply H.
 rewrite pow1_squared; field.
 unfold pow.
 discrR; lia.
Qed.

Lemma calc2 : forall N, (An N) * (An N) - Bn N = bisumsum_strip_diag'  (fun n m =>
    (pow1 m * pow1 n) * / ((IZR (m - n)) * (d' n))
  ) N.
Proof.
intros.
rewrite calc1.
rewrite bisumsum_strip_diag'_eq_but_diag_compat with _
  (fun n m : Z => pow1 m * pow1 n / (2 * IZR (m - n)) * (  / d' n) +
                  pow1 m * pow1 n / (2 * IZR (m - n)) * (- / d' m)) _.
 rewrite bisumsum_strip_diag'_plus.
 rewrite bisumsum_strip_diag'_switch_index.
 rewrite <- bisumsum_strip_diag'_plus.
 rewrite bisumsum_strip_diag'_switch_index.
 apply bisumsum_strip_diag'_eq_but_diag_compat.
 intros.
 replace (IZR (i - j)) with (- IZR (j - i)).
  field; split.
   apply d_not_null.
   discrR; lia.
  repeat rewrite <- Z_R_minus; ring.
 intros.
 field; repeat split.
  apply d_not_null.
  discrR; lia.
  apply d_not_null.
Qed.

Definition cn n N := bisum (fun m => if Z.eq_dec n m then 0 else pow1 m / (IZR (m - n))) N.

Lemma calc3 : forall N, (An N) * (An N) - Bn N = bisum (fun n => pow1 n / (d' n) * (cn n N)) N.
Proof.
intros.
rewrite calc2.
apply bisum_eq_compat; intros.
unfold cn.
rewrite <- bisum_scal_mult.
apply bisum_eq_compat; intros.
unfold zr.
destruct (Z.eq_dec z z0); field; [ | split ]; try apply d_not_null.
discrR; lia.
Qed.

Lemma cn_odd : forall n N, cn (- n)%Z N = - (cn n N).
Proof.
intros.
replace (- cn n N) with (-1 * cn n N) by ring.
unfold cn.
rewrite bisum_reverse.
rewrite <- bisum_scal_mult.
apply bisum_eq_compat; intros.
unfold zr.
destruct (Z.eq_dec (- n) (- z)); destruct (Z.eq_dec n z); subst; try ring.
 assert (n = z) by lia; subst; apply False_ind; apply n0; trivial.
 apply False_ind; apply n0; trivial.
 replace (- z - - n)%Z with (n - z)%Z by lia.
 replace (pow1 (- z)) with (pow1 z).
  replace (IZR (n - z)) with (- IZR (z - n)).
   field.
   discrR; lia.
  rewrite <- Ropp_Ropp_IZR; apply IZR_eq; lia.
  induction z; trivial.
Qed.

Lemma cn_zero_zero : forall N, cn 0 N = 0.
Proof.
intros.
cut (2 * cn 0 N = 0).
 intro H.
 apply Rmult_integral in H.
 destruct H.
  lra.
  assumption.
 rewrite double.
 replace (cn 0 N + cn 0 N) with (cn 0 N + cn (- 0) N) by (inject; ring).
 rewrite cn_odd.
 ring.
Qed.

(** * Bounding *)

Lemma cn_pos : forall n N, (S n <= N)%nat ->
  cn (Zpos (P_of_succ_nat n)) N = 
  (pow (-1) (S (S n))) * 
  (sum_f_R0 (fun j => pow (-1) (j + N - n) * / (INR (j + N - n)))) (S (2 * n))
.
Proof.
intros.
assert (odd' : forall a b, cn a b = - (cn (- a) b))
  by (intros; rewrite cn_odd; ring).
rewrite odd'.
pose (N - S n)%nat as k.
replace N with (k + S n)%nat by (unfold k; lia).
unfold cn.

replace
  (bisum
   (fun m : Z => if Z.eq_dec (- Zpos (P_of_succ_nat n)) m then 0
    else pow1 m / IZR (m - - Zpos (P_of_succ_nat n))) (k + S n))
  with
  (bisum
   (shiftp (fun j : Z => - (-1) ^ n * if Z.eq_dec 0 j then 0 else pow1 j / IZR j) (S n))
   (k + S n)).
 
 rewrite bisum_shifting.
 
 assert (bisum (fun j : Z => - (-1) ^ n * (if Z.eq_dec 0 j then 0 else pow1 j / IZR j)) k = 0).
  induction k.
   simpl; ring.
   rewrite bisum_one_step.
   rewrite IHk.
   change (Z.eq_dec 0) with (Z.eq_dec (Z_of_nat O)).
   destruct (Z.eq_dec (Z_of_nat 0) (Z_of_nat (S k))).
    apply inj_eq_rev in e.
    inversion e.
   replace (Z.eq_dec (Z_of_nat O)) with (Z.eq_dec (- Z_of_nat O)%Z) by trivial.
   destruct (Z.eq_dec (- Z_of_nat O)%Z (- Z_of_nat (S k))).
    apply Z.opp_inj in e.
    apply inj_eq_rev in e.
    inversion e.
   
   ring_simplify.
   rewrite pow1_nat_neg.
   rewrite pow1_nat.
   rewrite Ropp_Ropp_IZR.
   field; discrR.
  
  rewrite H0; clear H0.
  rewrite Rplus_0_l.
  replace (mult 2 (S n)) with (S (S (2 * n))) by lia.
  rewrite sum_f_R0_sum1.
  assert (RE : forall x, - x = -1 * x) by (intro; ring);
    rewrite RE; clear RE.
  do 2 rewrite scal_sum.
  apply Rseq_sum_ext; intro i.
  unfold shiftp.
  replace (Z_of_nat (S i) + Z_of_nat k)%Z
    with (Z_of_nat (S i + k)).
  
   replace 0%Z with (Z_of_nat O) by trivial.
   destruct (Z.eq_dec (Z_of_nat O) (Z_of_nat (S i + k))).
    apply inj_eq_rev in e.
    inversion e.  
   
   rewrite pow1_nat.
   rewrite <- INR_IZR_INZ.
   replace (i + (k + S n) - n)%nat with (S i + k)%nat by lia.
   simpl pow.
   field; INR_solve.
  
  simpl (S i + k)%nat.
  do 2 rewrite inj_S.
  rewrite Zplus_succ_l.
  inject.
  induction i.
   trivial.
   simpl (S i + k)%nat.
   do 2 rewrite inj_S.
   rewrite IHi.
   lia.
 
 apply bisum_eq_compat; intro.
 unfold shiftp.
 destruct (Z.eq_dec 0 (z + Z_of_nat (S n)));
 destruct (Z.eq_dec (- Zpos (P_of_succ_nat n)) z).
  auto with *.
  
  assert (z = - Z_of_nat (S n))%Z by lia.
  assert (- Zpos (P_of_succ_nat n) = (- Z_of_nat (S n)))%Z by trivial.
  subst; tauto.
  
  subst.
  assert (- Zpos (P_of_succ_nat n) = (- Z_of_nat (S n)))%Z by trivial.
  apply False_ind; lia.
  
  repeat rewrite <- Rmult_assoc.
  assert (AP : forall a b a' a'' b', a = a' * a'' -> b = b' -> (b' <> 0)%Z ->
    a' * (a'' / IZR b') = a / IZR b) by (intros; subst; field; discrR; auto);
    apply AP; clear AP;
    auto.
   rewrite pow1_plus_nat.
   ring_simplify.
   assert ((-1) ^ n * (-1) ^ S n = -1).
    rewrite <- Rdef_pow_add.
    replace (n + S n)%nat with (S (2 * n)) by lia.
    apply pow_1_odd.
   
   rewrite Rmult_assoc.
   rewrite H0.
   ring.
Qed.

Lemma alt_bounding : 
  forall u : nat -> R,
  Un_decreasing u ->
  (forall n, 0 <= u n) ->
  forall n, 0 <= sum_f_R0 (tg_alt u) n <= u O.
Proof.
intros Un dec pos n.
pose (sum_f_R0 (tg_alt Un)) as Sn; fold Sn.

assert (Heu : forall p, Sn (2 * p)%nat <= Un O).
induction p.
 compute; intuition.
 eapply Rle_trans.
  apply CV_ALT_step1; assumption.
  assumption.

assert (Ho0 : forall p, 0 <= Sn (S (2 * p))).
induction p.
 unfold Sn; simpl; unfold tg_alt, pow; ring_simplify.
 assert (Un 1%nat <= Un O) by auto; lra.
 eapply Rle_trans.
  apply IHp.
  apply CV_ALT_step0; assumption.

destruct (even_odd_cor n) as [p [he|ho]]; subst; split.
 destruct p.
 unfold Sn; simpl; unfold tg_alt, pow; ring_simplify; apply pos.
 replace (2 * S p)%nat with (S (S (2 * p))) by lia.
 unfold Sn; rewrite tech5; fold Sn.
 apply Rplus_le_le_0_compat.
  apply Ho0.
  replace (S (S (2 * p))) with (2 * S p)%nat by lia.
  unfold tg_alt.
  rewrite pow_1_even.
  rewrite Rmult_1_l.
  apply pos.

 apply Heu.
 
 apply Ho0.
 
 unfold Sn; rewrite tech5; fold Sn.
 unfold tg_alt.
 rewrite pow_1_odd.
 assert (AP : forall a b c, a <= c -> 0 <= b -> a + -1 * b <= c)
   by (intros; lra); apply AP; clear AP.
  apply Heu.
  apply pos.
Qed.

Lemma cn_maj : forall n N, (n <= N)%nat -> Rabs (cn (Z_of_nat n) N) <= / (INR (N - n + 1)).
Proof.
intros.
destruct n.
 simpl; rewrite cn_zero_zero.
 unfold Rabs.
 destruct (Rcase_abs 0); left;
  replace (- 0) with 0 by ring;
  apply Rinv_0_lt_compat;
  INR_solve.
 
 unfold Z_of_nat.
 rewrite cn_pos with n N; [|assumption].
 rewrite Rabs_mult; rewrite pow_1_abs; rewrite Rmult_1_l.
 replace (sum_f_R0 (fun j : nat => (-1) ^ (j + N - n) * / INR (j + N - n)) (S (2 * n)))
   with ((-1) ^ (N - n) * sum_f_R0 (fun j : nat => (-1) ^ j * / INR (j + N - n)) (S (2 * n))).
  2:rewrite scal_sum.
  2:apply Rseq_sum_ext; intro.
  2:replace (n0 + N - n)%nat with (n0 + (N - n))%nat by lia.
  2:rewrite Rdef_pow_add; ring.
  
 rewrite Rabs_mult; rewrite pow_1_abs; rewrite Rmult_1_l.
 cut (forall i, Rabs (sum_f_R0 (fun j : nat => (-1) ^ j * / INR (j + N - n)) i) <= / INR (N - S n + 1))
   ;[intuition | ].
 replace (N - S n + 1)%nat with (N - n)%nat by lia.
 
 pose (N - n)%nat as k; fold k.
 assert (kpos : (0 < k)%nat) by (unfold k; lia).
 pose (fun j => / INR (j + k)) as Un.
 
 intro i;
 replace (sum_f_R0 (fun j => (-1) ^ j * / INR (j + N - n)) i)
   with (sum_f_R0 (fun j => (-1) ^ j * / INR (j + k)) i)
   by (apply Rseq_sum_ext; intro; trivial; inject; unfold k; lia).
 replace (sum_f_R0 (fun j => (-1) ^ j * / INR (j + k)) i)
   with (sum_f_R0 (tg_alt Un) i)
   by (apply Rseq_sum_ext; intro; trivial).
 replace (/ INR k) with (Un O) by trivial.
 
 edestruct (alt_bounding Un).
  intro; unfold Un. apply Rle_Rinv; INR_solve.
  intro; unfold Un; apply Rlt_le; apply Rinv_0_lt_compat; INR_solve.
 
 assert (0 <= sum_f_R0 (tg_alt Un) i) by apply H0.
 rewrite Rabs_pos_eq by apply H2.
 apply H1.
Qed.

Lemma abound_eq : forall n N, (O <= n)%nat -> (S n <= N)%nat ->
  / (INR (N - n)) * (/ (INR (2 * n + 1)) + / (INR (2 * n + 3))) =
  / (INR (2 * N + 1)) * (2 / (INR (2 * n + 1)) + / (INR (N - n))) +
  / (INR (2 * N + 3)) * (2 / (INR (2 * n + 3)) + / (INR (N - n))).
Proof.
intros.
rewrite minus_INR.
repeat rewrite plus_INR.
repeat rewrite mult_INR.
replace (INR 1) with 1 by trivial.
replace (INR 2) with 2 by trivial.
field; INR_solve.
eapply le_trans.
 constructor 2; constructor.
 assumption.
Qed.

Definition abound N := sum_f_R0 (fun n => / (INR (N - (S n) + 1)) * 
    (/ (INR (2 * n + 1)) + / (INR (2 * n + 3)))
  ) (pred N).

Definition bound1 N :=  / (INR (2 * N + 1)) * 
  sum_f_R0 (fun n => 
    2 / (INR (2 * n + 1)) + / (INR (N - (S n) + 1))
  ) (pred N).

Definition bound2 N :=  / (INR (2 * N + 3)) * 
  sum_f_R0 (fun n => 
    2 / (INR (2 * n + 3)) + / (INR (N - (S n) + 1))
  ) (pred N).

Definition bound1' N :=  / INR (2 * N + 1) * sum_f_R0 (fun n =>  2 / INR (2 * n + 1)) (pred N).
Definition bound2' N :=  / INR (2 * N + 3) * sum_f_R0 (fun n =>  2 / INR (2 * n + 3)) (pred N).
Definition bound1c N :=  / INR (2 * N + 1) * sum_f_R0 (fun n => / INR (N - (S n) + 1)) (pred N).
Definition bound2c N :=  / INR (2 * N + 3) * sum_f_R0 (fun n => / INR (N - (S n) + 1)) (pred N).

Lemma An_squared_Bn_maj : forall N, (1 <= N)%nat -> Rabs (An N * An N - Bn N) <= abound N.
Proof.
intros N H.
destruct N.
 inversion H.
 
 rewrite calc3.
 rewrite sum_bisum.
 eapply Rle_trans; [apply Rabs_triang | ].
 unfold abound.
 assert (REWdiv : forall a b, pow1 a / b = pow1 a * / b) by reflexivity.
 replace (sum_f_R0 (fun n : nat =>
   / INR (S N - S n + 1) * (/ INR (2 * n + 1) + / INR (2 * n + 3)))
   (pred (S N)))
   with
   (sum_f_R0 (fun n : nat => / INR (S N - S n + 1) * / INR (2 * n + 3)) (pred (S N)) +
   sum_f_R0  (fun n : nat => / INR (S N - S n + 1) * / INR (2 * n + 1)) (pred (S N)))
 by (
   rewrite <- plus_sum; simpl pred;
   apply Rseq_sum_ext; intro n;
   field; INR_solve
 ).
 rewrite decomp_sum by lia; simpl pred; simpl (Z_of_nat 0);
   rewrite cn_zero_zero; rewrite Rmult_0_r; rewrite Rplus_0_l.
 
 apply Rplus_le_compat.
  eapply Rle_trans; [apply Rsum_abs | ].
  replace (pred (S (S N))) with (S N) by trivial.
  apply sum_Rle; intros n nSN.
  rewrite REWdiv.
  repeat rewrite Rabs_mult.
  rewrite pow1_Rabs; rewrite Rmult_1_l.
  rewrite Rmult_comm.
  apply Rmult_le_compat; try apply Rabs_pos.
   apply (cn_maj (S n) (S N)); lia.
   unfold d', d; rewrite <- INR_IZR_INZ.
   rewrite Rabs_pos_eq; try apply Rle_Rinv;
     try (apply Rlt_le; apply Rinv_0_lt_compat);
     INR_solve.
  
  eapply Rle_trans; [apply Rsum_abs | ].
  replace (pred (S (S N))) with (S N) by trivial.  
  apply sum_Rle; intros n nSN.
  rewrite REWdiv.
  repeat rewrite Rabs_mult.
  rewrite pow1_Rabs; rewrite Rmult_1_l.
  rewrite Rmult_comm.
  apply Rmult_le_compat; try apply Rabs_pos.
   eapply Rle_trans.
    rewrite cn_odd; rewrite Rabs_Ropp.
    apply (cn_maj (S n) (S N)); lia.
    apply Rle_Rinv; INR_solve.
   unfold d', d; rewrite Ropp_Ropp_IZR; rewrite <- INR_IZR_INZ.
   rewrite <- Rabs_Ropp; rewrite Ropp_inv_permute.
   replace (- (2 * - INR (S n) + 1)) with ((2 * INR n + 1)) by (rewrite plus_1_S; ring).
   rewrite Rabs_pos_eq; try apply Rle_Rinv;
     try (apply Rlt_le; apply Rinv_0_lt_compat);
     INR_solve.
   rewrite INR_IZR_INZ; discrR.
Qed.

Lemma bound_eq : forall N, abound (S N) = bound1 (S N) + bound2 (S N).
Proof.
intros.
unfold abound, bound1, bound2.
simpl (pred (S N)).
do 2 rewrite scal_sum.
erewrite sum_eq.
 apply sum_plus.
 
 intros n H.
 replace (S N - S n + 1)%nat with (S N - n)%nat by lia.
 rewrite abound_eq; try lia.
 replace (S N - S n + 1)%nat with (S N - n)%nat by lia.
 field; INR_solve.
Qed.

(** Convergence of the bounds *)

Definition inverse_mean n := sum_f_R0 (fun i => / INR (S i)) n / INR (S n).

Lemma inverse_cv_0 : Rseq_cv (fun i => / INR (S i)) 0.
Proof.
apply Rseq_cv_pos_infty_inv_compat.
assert (H01 : (1 > 0)%nat) by lia.
pose proof (Rseq_poly_cv 1 H01).
unfold Rseq_poly in H; simpl in H.
eapply Rseq_cv_pos_infty_eq_compat in H; [ | intro; apply Rmult_1_r].
intro M.
destruct (H M) as [N Hcv].
exists N.
intros.
eapply Rlt_le_trans.
 apply Hcv.
 apply H0.
 INR_solve.
Qed.

Lemma inverse_mean_cv_0 : Rseq_cv inverse_mean 0.
Proof.
unfold inverse_mean.
eapply Rseq_cv_eq_compat.
 2:eapply Rseq_cv_shift_compat_reciprocal.
 2:apply (Cesaro_1 (fun i => / INR (S i))).
 intro n; unfold Rseq_shift; simpl pred; reflexivity.
 
 apply inverse_cv_0.
Qed.

Lemma Rseq_cv_0_pos_maj_compat : forall Un Vn, (forall n, 0 <= Un n) -> (forall n, Un n <= Vn n) ->
  Rseq_cv Vn 0 -> Rseq_cv Un 0.
Proof.
intros Un Vn Unpos Unmaj Vncv e epos.
destruct (Vncv e epos) as [N H].
exists N; intros n nN.
unfold R_dist; rewrite Rminus_0_r; rewrite Rabs_pos_eq; [|apply Unpos].
eapply Rle_lt_trans.
 apply Unmaj.
 pose proof H n nN as J.
 unfold R_dist in J; rewrite Rminus_0_r in J; rewrite Rabs_pos_eq in J.
  apply J.
  eapply Rle_trans; [apply Unpos | apply Unmaj].
Qed.

Lemma half_mean_0 : forall Un k m, 0 <= k -> (1 <= m)%nat -> (forall n, 0 <= Un n) -> (forall n, Un n <= k / INR (S n)) ->
  Rseq_cv (fun N => / INR (2 * N + m) * sum_f_R0 Un (pred N)) 0.
Proof.
intros Un k m kpos mpos Unpos Unbound.
apply Rseq_cv_shift_compat; unfold Rseq_shift; simpl pred.
eapply Rseq_cv_0_pos_maj_compat.
 intro.
 rewrite Rmult_comm; apply Rle_mult_inv_pos.
  apply cond_pos_sum; assumption.
  INR_solve.
 
 intro.
 eapply Rle_trans.
  apply Rmult_le_compat.
   apply Rlt_le; apply Rinv_0_lt_compat; INR_solve.
   apply cond_pos_sum; assumption.
   apply Rlt_le; apply (Rinv_lt_contravar (INR (S n))); INR_solve.
  apply (sum_growing _ (fun n => k / INR (S n))); apply Unbound.
  
  replace (sum_f_R0 (fun n0 : nat => k / INR (S n0)) n)
    with (sum_f_R0 (fun n0 : nat => / INR (S n0) * k) n)
    by (apply Rseq_sum_ext; intro; field; INR_solve).
  rewrite <- scal_sum.
  rewrite <- Rmult_assoc; rewrite Rmult_comm with _ k; rewrite Rmult_assoc.
 
 2: replace 0 with (k * 0) by ring.
 2: apply Rseq_cv_mult_compat.
  2: apply Rseq_constant_cv.
  2: apply inverse_mean_cv_0.
 
 unfold Rseq_mult, Rseq_constant.
 apply (Rmult_le_compat_l k _ _ kpos).
 unfold inverse_mean, Rdiv.
 rewrite Rmult_comm.
 intuition.
Qed.

Lemma bound1'_cv : Rseq_cv bound1' 0.
Proof.
apply Rseq_cv_shift_compat.
unfold bound1', Rseq_shift.
assert (Rseq_cv
      (fun N : nat =>
       / INR (2 * N + 1) *
       sum_f_R0 (fun n0 : nat => 2 / INR (2 * n0 + 1)) (pred N)) 0).
 apply (half_mean_0 _ 2).
  lra.
  
  lia.
  
  intro; unfold Rdiv; apply Rle_mult_inv_pos; [lra | INR_solve].
  
  intro; unfold Rdiv.
  apply Rmult_le_compat_l; [lra | ].
  apply Rle_Rinv; INR_solve.
 
 intros e epos; destruct (H e epos) as [N J]; exists N; intros n nN.
 simpl pred.
 apply J; lia.
Qed.

Lemma bound2'_cv : Rseq_cv bound2' 0.
Proof.
apply Rseq_cv_shift_compat.
unfold bound1', Rseq_shift.
assert (Rseq_cv
      (fun N : nat =>
       / INR (2 * N + 3) *
       sum_f_R0 (fun n0 : nat => 2 / INR (2 * n0 + 3)) (pred N)) 0).
 apply (half_mean_0 _ 2).
  lra.
  
  lia.
  
  intro; unfold Rdiv; apply Rle_mult_inv_pos; [lra | INR_solve].
  
  intro; unfold Rdiv.
  apply Rmult_le_compat_l; [lra | ].
  apply Rle_Rinv; INR_solve.
 
 intros e epos; destruct (H e epos) as [N J]; exists N; intros n nN.
 simpl pred.
 apply J; lia.
Qed.

Lemma Rsum_switch_index : forall Un N, sum_f_R0 (fun n => Un (N - n)%nat) N = sum_f_R0 Un N.
Proof.
intros Un N.
induction N.
 trivial.
 
 rewrite decomp_sum by lia; simpl.
 rewrite IHN.
 ring.
Qed.

Lemma bound1c_cv : Rseq_cv bound1c 0.
Proof.
apply Rseq_cv_shift_compat.
unfold bound1', Rseq_shift.
assert (Rseq_cv
      (fun N : nat =>
       / INR (2 * N + 1) *
       sum_f_R0 (fun n0 : nat => / INR (S n0)) (pred N)) 0).
 apply (half_mean_0 _ 1).
  lra.
  
  lia.
  
  intro; apply Rlt_le; apply Rinv_0_lt_compat; INR_solve.
  
  intro; unfold Rdiv; rewrite Rmult_1_l; auto with *.
 
 intros e epos; destruct (H e epos) as [N J]; exists N; intros n nN.
 simpl pred.
 unfold bound1c.
 replace (sum_f_R0 (fun n0 : nat => / INR (S n - S n0 + 1)) (pred (S n)))
   with (sum_f_R0 (fun n0 : nat => / INR (S n0)) (pred (S n)))
   by (rewrite <- Rsum_switch_index; apply Rseq_sum_ext; intro; inject; lia).
 apply J; lia.
Qed.

Lemma bound2c_cv : Rseq_cv bound2c 0.
Proof.
apply Rseq_cv_shift_compat.
unfold bound1', Rseq_shift.
assert (Rseq_cv
      (fun N : nat =>
       / INR (2 * N + 3) *
       sum_f_R0 (fun n0 : nat => / INR (S n0)) (pred N)) 0).
 apply (half_mean_0 _ 1).
  lra.
  
  lia.
  
  intro; apply Rlt_le; apply Rinv_0_lt_compat; INR_solve.
  
  intro; unfold Rdiv; rewrite Rmult_1_l; apply Rle_Rinv; INR_solve.
 
 intros e epos; destruct (H e epos) as [N J]; exists N; intros n nN.
 simpl pred.
 unfold bound2c.
 replace (sum_f_R0 (fun n0 : nat => / INR (S n - S n0 + 1)) (pred (S n)))
   with (sum_f_R0 (fun n0 : nat => / INR (S n0)) (pred (S n)))
   by (rewrite <- Rsum_switch_index; apply Rseq_sum_ext; intro; inject; lia).
 apply J; lia.
Qed.

Lemma bound1_cv : Rseq_cv bound1 0.
Proof.
replace 0 with (0 + 0) by ring.
eapply Rseq_cv_eq_compat.
 2:apply Rseq_cv_plus_compat; [apply bound1'_cv | apply bound1c_cv].
 intro; unfold Rseq_plus, bound1', bound1c, bound1.
 rewrite <- Rmult_plus_distr_l.
 inject.
 rewrite <- sum_plus.
 apply Rseq_sum_ext; intro; trivial.
Qed.

Lemma bound2_cv : Rseq_cv bound2 0.
Proof.
replace 0 with (0 + 0) by ring.
eapply Rseq_cv_eq_compat.
 2:apply Rseq_cv_plus_compat; [apply bound2'_cv | apply bound2c_cv].
 intro; unfold Rseq_plus, bound2', bound2c, bound2.
 rewrite <- Rmult_plus_distr_l.
 inject.
 rewrite <- sum_plus.
 apply Rseq_sum_ext; intro; trivial.
Qed.

Lemma abound_cv : Rseq_cv abound 0.
Proof.
replace 0 with (0 + 0) by ring.
eapply Rseq_cv_asymptotic_eq_compat.
 2:apply Rseq_cv_plus_compat; [apply bound1_cv | apply bound2_cv].
 exists (S O).
 intros n Hb.
  assert (H : exists n', n = S n').
   exists (pred n); apply S_pred with O; apply Hb.
  destruct H; subst.
  unfold Rseq_plus.
  symmetry; apply bound_eq.
Qed.

(** Final result about sums *)

Lemma An_squared_Bn_cv : Rseq_cv (An * An - Bn) 0.
Proof.
intros e epos.
destruct (abound_cv e epos) as [N H].
exists (S N); intros n nN.
unfold R_dist; rewrite Rminus_0_r.
unfold Rseq_minus, Rseq_mult, Rseq_abs.
eapply Rle_lt_trans.
 apply An_squared_Bn_maj.
 lia.
 assert (nN' : (n >= N)%nat) by lia.
 pose proof (H n nN') as T.
 unfold R_dist in T; rewrite Rminus_0_r in T.
 eapply Rle_lt_trans.
  2: apply T.
  apply RRle_abs.
Qed.

(** * Bn converges to pi²/4 *)

Lemma Bn_cv : Rseq_cv Bn (PI ^ 2 / 4).
Proof.
replace (PI ^ 2 / 4) with (PI ^ 2 / 4 - 0) by field.
apply Rseq_cv_eq_compat with (An * An - (An * An - Bn))%Rseq.
 intro; unfold Rseq_minus, Rseq_mult; ring.
 
 apply Rseq_cv_minus_compat.
  apply An_squared_cv.
  apply An_squared_Bn_cv.
Qed.

(** * Linking sums on nat and sums on Z *)

Lemma bnz_bntg : forall n, bntg n = bnz (Z_of_nat n).
Proof.
intro n.
unfold bntg, bnz.
destruct n.
 simpl; field.
 
 rewrite <- INR_IZR_INZ.
 field.
 INR_solve.
Qed.

Lemma bnz_bntg_neg : forall n, bntg_neg n = bnz (- Z_of_nat n).
Proof.
intro n.
unfold bntg_neg, bnz.
destruct n.
 simpl; field.
 
 rewrite Ropp_Ropp_IZR.
 rewrite <- INR_IZR_INZ.
 field.
 rewrite plus_1_S.
 replace (2 * - (1 + INR n) + 1) with (- (1 + 2 * INR n)) by ring.
 apply Ropp_neq_0_compat.
 repeat INR_solve.
Qed.

Lemma bisum_bnz_bntg : (sum_f_R0 bntg + (sum_f_R0 bntg_neg - 1))%Rseq == bisum bnz.
Proof.
intro n.
induction n.
 compute; field.
 
 simpl bisum.
 rewrite <- IHn.
 unfold Rseq_minus.
 unfold Rseq_plus.
 unfold Rseq_constant.
 repeat rewrite tech5.
 repeat rewrite bnz_bntg_neg.
 repeat rewrite bnz_bntg.
 replace (Zneg (P_of_succ_nat n)) with (- Z_of_nat (S n))%Z by trivial.
 replace (Zpos (P_of_succ_nat n)) with (Z_of_nat (S n))%Z by trivial.
 ring.
Qed.

Definition sumbntg := let (l, _) := Rser_cv_bntg in l.

Lemma Sum_bntg : Rser_cv bntg sumbntg.
Proof.
unfold sumbntg.
destruct Rser_cv_bntg; assumption.
Qed.

Lemma bntg_shift_neg_compat : Rseq_shift bntg_neg == bntg.
intro n.
unfold Rseq_shift.
unfold bntg.
unfold bntg_neg.
rewrite S_INR.
simpl pow.
field; split.
 INR_solve.
 replace (-2 * (INR n + 1) + 1) with (- (2 * (INR n) + 1)) by field.
 apply Ropp_neq_0_compat.
 INR_solve.
Qed.

Lemma Sum_bntg_neg : Rser_cv bntg_neg (sumbntg + 1).
Proof.
apply Rser_cv_shift_rev2.
eapply Rser_cv_ext.
 apply bntg_shift_neg_compat.
 replace (sumbntg + 1 - bntg_neg 0) with sumbntg by (compute; field).
 apply Sum_bntg.
Qed.

Lemma Sum_bnz : Rseq_cv Bn (2 * sumbntg).
Proof.
eapply Rseq_cv_eq_compat; [symmetry; apply bisum_bnz_bntg | ].
replace (2 * sumbntg) with (sumbntg + ((sumbntg + 1) - 1)) by field.
apply Rseq_cv_plus_compat; [apply Sum_bntg | ].
apply Rseq_cv_minus_compat; [ | apply Rseq_constant_cv].
apply Sum_bntg_neg.
Qed.

Lemma sumbntg_val : sumbntg = PI ^ 2 / 8.
Proof.
apply Rmult_eq_reg_l with 2.
 replace (2 * (PI ^ 2 / 8)) with (PI ^ 2 / 4) by field.
 apply (Rseq_cv_unique _ _ _ Sum_bnz Bn_cv).
 assert(0 < 2) by lra; auto with *.
Qed.

Lemma odd_zeta : Rser_cv bntg (PI ^ 2 / 8).
Proof.
rewrite <- sumbntg_val.
apply Sum_bntg.
Qed.

(** * Linking even terms of the 1/n² series to the series itself *)

Lemma odd_zeta_evens : Rser_cv (evens (Rseq_shift Rseq_square_inv)) (PI ^ 2 / 8).
apply Rser_cv_ext with bntg.
 intro n.
 unfold Rseq_shift, evens, Rseq_square_inv, bntg.
 replace (INR (S (2 * n))) with (2 * INR n + 1); [reflexivity | ].
 replace (S n) with (1 + n)%nat by reflexivity.
 INR_solve.
 do 2 (try rewrite <- plus_INR; try rewrite <- mult_INR).
 inject; lia.
 
 apply odd_zeta.
Qed.

Definition zeta2 := let (l, _) := Rser_cv_square_inv in l.

Lemma zeta2_half : Rser_cv (odds (Rseq_shift (Rseq_square_inv))) (zeta2 / 4).
Proof.
replace (zeta2 / 4) with (/4 * zeta2) by field.
assert (REW : forall a, (/4 * (4 * a))%Rseq == a).
 intros a n; unfold Rseq_mult, Rseq_inv; field.
 unfold Rseq_constant.
 apply Rgt_not_eq ; lra.
 
 eapply Rser_cv_ext.
  symmetry ; apply REW.
  
  apply (Rser_cv_scal_compat_l _ _ (/ 4)).
  eapply Rser_cv_ext.
   2:unfold zeta2.
   2:destruct Rser_cv_square_inv as [l H].
   2:apply H.
   
   intro n.
   unfold Rseq_mult, odds, Rseq_shift, Rseq_square_inv, Rseq_constant.
   replace (S (S (2 * n))) with (mult 2 (S n)) by lia.
   replace (INR (2 * (S n))) with (2 * INR (S n)) by (rewrite mult_INR; trivial).
   unfold Rseq_square_inv_s.
   field.
   apply not_0_INR; lia.
Qed.

(** Final result with free variables *)

Lemma zeta2_val : zeta2 = PI ^ 2 / 6.
Proof.
apply Rmult_eq_reg_l with (3 / 4);
 [ | intro H; apply (Rmult_eq_compat_l 4) in H; field_simplify in H; lra].
replace (3 / 4 * zeta2) with (zeta2 - zeta2 / 4) by field.
replace (3 / 4 * (PI ^ 2 / 6)) with (PI ^ 2 / 8) by field.
eapply Rser_cv_unique.
 apply Rser_cv_minus_compat.
  unfold zeta2.
  destruct Rser_cv_square_inv as [x H].
  apply H.
  
  2:apply remove_odds.
   apply zeta2_half.
   
   apply Rser_cv_square_inv.
 
 apply odd_zeta_evens.
Qed.

Coercion INR : nat >-> R.

(** * Final theorem *)

Theorem zeta2_pi_2_6 : Rser_cv (fun n => 1 / (n + 1) ^ 2) (PI ^ 2 / 6).
Proof.
rewrite <- zeta2_val.
unfold zeta2.
eapply Rser_cv_ext.
 2:destruct Rser_cv_square_inv as [l H].
 2:apply H.
 
 intro n; unfold Rseq_shift, Rseq_square_inv_s.
 rewrite plus_1_S.
 field.
 INR_solve.
Qed.
