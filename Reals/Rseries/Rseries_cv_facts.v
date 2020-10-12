Require Import Rsequence.
Require Import Rseries_def Rseries_base_facts Rseries_pos_facts.
Require Import MyNat MyRIneq.

Require Import Max.
Require Import Lra Rtactic.

Local Open Scope R_scope.

(** * Convergence facts *)
(** For basic convergence lemmas (e.g. compatibility with common operations), see Rseries_base_facts *)


(** Even / odd partition *)

Lemma Rser_even_odd_split : forall An le lo, 
  Rser_cv (fun n => An (2*n)%nat) le ->
  Rser_cv (fun n => An (S(2*n))%nat) lo ->
  Rser_cv An (le + lo).
Proof.
intros An le lo Hle Hlo ; apply Rseq_cv_even_odd_compat.
 apply Rseq_cv_shift_compat ; unfold Rseq_shift ; apply Rseq_cv_eq_compat
  with (Rseq_plus (Rseq_shift (Rseq_sum (fun i => An (2 * i)%nat)))
       (Rseq_sum (fun i => An (S (2 * i))))).
  intro n ; rewrite <- Rseq_sum_even_odd_split' ; unfold Rseq_shift, Rseq_plus ;
  reflexivity.
  apply Rseq_cv_plus_compat ; [apply Rseq_cv_shift_compat_reciprocal |] ; assumption.
 apply Rseq_cv_eq_compat with (Rseq_plus (Rseq_sum (fun i => An (2 * i)%nat))
       (Rseq_sum (fun i => An (S (2 * i))))).
  intro n ; symmetry ; apply Rseq_sum_even_odd_split.
  apply Rseq_cv_plus_compat ; assumption.
Qed.

(** A gt-positive series bounded by a converging one is converging. *)

Lemma Rser_pos_maj_cv : forall (An Bn : nat -> R), 
  (forall n : nat, 0 <= An n) -> (forall n : nat, 0 <= Bn n) ->
  Rseq_le An Bn ->  {l | Rser_cv Bn l } -> {l | Rser_cv An l}.
Proof.
intros An Bn An_pos Bn_pos AnBn [lb Hlb] ; apply Rser_pos_bound_cv with lb.
 assumption.
 intro n ; transitivity (Rseq_sum Bn n).
  apply Rseq_sum_le_compat ; assumption.
  apply growing_ineq ; [apply Rser_pos_growing |] ; assumption.
Qed.

(** * Mertens' theorem *)

Lemma Rseq_prod_rewrite: forall An Bn,
 Rseq_sum (An # Bn) == (Rseq_sum Bn) # An.
Proof.
intros An Bn n ; induction n.
 apply Rmult_comm.
 rewrite Rseq_sum_simpl, IHn.
  transitivity (Rseq_sum (An * (fun i => Rseq_sum Bn (n - i)%nat))%Rseq n
   + (An # Bn) (S n)).
   apply Rplus_eq_compat_r ; rewrite Rseq_sum_reindex_compat ;
   apply Rseq_sum_ext_strong ; intros p p_lb ; unfold Rseq_mult ;
   replace (n - (n - p))%nat with p by lia ; apply Rmult_comm.
  transitivity (Rseq_sum (An * (fun i => Rseq_sum Bn (S n - i)))%Rseq (S n)).
   unfold Rseq_prod ; do 2 rewrite Rseq_sum_simpl ; rewrite <- Rplus_assoc.
   apply Rplus_eq_compat.
   rewrite (Rseq_sum_ext_strong (An * (fun i => Rseq_sum Bn (S n - i)))%Rseq
   ((An * (fun i => Rseq_sum Bn (n - i))) + (An * (fun i => Bn (S n - i)%nat)))%Rseq).
   symmetry ; apply Rseq_sum_plus_compat.
    intros p p_ub ; unfold Rseq_mult, Rseq_plus ;
    replace (S n - p)%nat with (S (n - p)) by lia ; simpl ; ring.
    unfold Rseq_mult ; rewrite minus_diag ; reflexivity.
   rewrite Rseq_sum_reindex_compat ; apply Rseq_sum_ext_strong ; intros p Hp ;
    unfold Rseq_mult ; replace (S n - (S n - p))%nat with p by lia ;
    apply Rmult_comm.
Qed.

Lemma Rplus_minus_assoc: forall x y z,
  x + y - z = x + (y - z).
Proof.
intros ; ring.
Qed.

Lemma Rser_cv_prod_compat : forall An Bn la lb lna,
 Rser_cv An la -> Rser_cv Bn lb -> 
 Rser_abs_cv An lna -> Rser_cv (An # Bn) (la * lb).
Proof.
intros An Bn la lb lna Hla Hlb Hlna eps eps_pos.
 pose (eps2 := eps / 4 / (lna + 1)).
 assert (lna_pos: 0 < lna + 1).
  apply Rle_lt_0_plus_1 ; transitivity (Rabs (An O)).
   apply Rabs_pos.
(** TODO: remove sum_incr from std_lib *)
   eapply (sum_incr (| An |) O).
    trivial.
    intro ; apply Rabs_pos.
 assert (eps2_pos : 0 < eps2) by (apply Rlt_mult_inv_pos; auto; lra).
 destruct (Hlb _ eps2_pos) as [N1 HN1].
 destruct (Rseq_cv_bound (Rseq_sum Bn) _ Hlb) as [MBn [MBn_pos HMBn]].
 pose (MB := MBn + Rabs lb).
 assert (MB_pos: 0 < MB).
  apply Rplus_lt_le_0_compat ; [trivial | apply Rabs_pos].
 assert (HMB: forall n, Rabs (Rseq_sum Bn n - lb) <= MB).
  intro n ; transitivity (Rabs (Rseq_sum Bn n) + Rabs lb).
   rewrite <- (Rabs_Ropp lb) ; apply Rabs_triang.
   apply Rplus_le_compat ; [trivial | reflexivity].
 pose (eps3 := eps / 8 / INR (S N1) / (MB + 1)).
 assert (eps3_pos: 0 < eps3).
  repeat apply Rlt_mult_inv_pos ; intuition ; lra.
 destruct (Rser_cv_zero An _ Hla _ eps3_pos) as [N2 HN2t].
 assert (HN2: forall n : nat, (n >= N2)%nat -> Rabs (An n) < eps3).
  intros p p_lb ; rewrite <- (Rminus_0_r (An p)) ; apply HN2t ; assumption.
 clear HN2t.
 pose (eps4 := eps / 2 / (Rabs lb + 1)). 
 assert (eps4_pos: 0 < eps4).
  repeat apply Rlt_mult_inv_pos ; intuition.
  apply Rle_lt_0_plus_1, Rabs_pos.
 destruct (Hla _ eps4_pos) as [N3 HN3].
 pose (N := max (max (S N1) (N1 + N2)) N3) ; exists N ; intros n n_lb.
 rewrite Rseq_prod_rewrite.
 replace ((Rseq_sum Bn # An) n) with
  (Rseq_sum ((Rseq_sum Bn - lb) * (fun i => An (n - i)%nat)
  + (fun i => An (n - i)%nat) * lb)%Rseq n).
 rewrite Rseq_sum_plus_compat ; unfold Rseq_plus.
 rewrite Rseq_sum_scal_compat_r ; unfold Rseq_mult.
 rewrite <- Rseq_sum_reindex_compat ; unfold Rseq_constant.
 unfold R_dist ; rewrite Rplus_minus_assoc, <- Rmult_minus_distr_r.
 eapply Rle_lt_trans ; [apply Rabs_triang |].
 replace eps with (eps / 4 + eps / 4 + eps / 2) by field.
 apply Rplus_lt_compat.
  eapply Rle_lt_trans; [apply Rseq_sum_triang |].
  fold (Rseq_constant lb) (Rseq_mult (Rseq_sum Bn - lb) (fun i => An (n - i)%nat)).
 pose (Un := | (Rseq_sum Bn - lb) * (fun i => An (n - i)%nat) |) ; fold Un.
 apply Rle_lt_trans with (Rseq_shifts (Rseq_sum Un) (S N1) (n - S N1)).
 right ; unfold Rseq_shifts.
 assert (HNn: (S N1 <= n)%nat).
  transitivity (max (S N1) (N1 + N2)) ; [| transitivity N ;
  [| assumption]] ; apply le_max_l.
 replace (S N1 + (n - S N1))%nat with n by lia ; reflexivity.
 apply Rle_lt_trans with (Rseq_sum Un N1 + Rseq_sum (Rseq_shifts Un (S N1)) (n - S N1)).
 rewrite Rseq_sum_shifts_compat ; right ; ring.
 apply Rplus_lt_compat.
 apply Rlt_le_trans with (eps3 * 2 * INR (S N1) * (MB + 1)).
 apply Rle_lt_trans with (Rseq_sum (MB * |(fun i => An (n - i)%nat)|)%Rseq N1).
 apply Rseq_sum_le_compat ; unfold Un, Rseq_abs, Rseq_mult ; intro p ;
 rewrite Rabs_mult ; apply Rmult_le_compat_r.
  apply Rabs_pos.
  transitivity (Rabs (Rseq_sum Bn p) + Rabs lb) ; unfold Rseq_constant.
  unfold Rseq_minus ; rewrite <- (Rabs_Ropp lb) ; apply Rabs_triang.
  apply Rplus_le_compat ; [trivial | reflexivity].
 rewrite Rseq_sum_scal_compat_l, Rmult_comm.
 apply Rmult_le_0_lt_compat.
  unfold Rseq_constant ; left ; trivial.
  apply Rseq_sum_pos ; intro p ; apply Rabs_pos.
  apply Rlt_plus_1.
 transitivity (eps3 * 1 * INR (S N1)).
 rewrite Rmult_1_r ; apply Rlt_le_trans with (Rseq_sum eps3 N1).
 apply Rseq_sum_lt_compat_strong ; intros p p_lb.
  assert ((N1 + N2 <= n)%nat).
   transitivity (max (S N1) (N1 + N2)) ; [apply le_max_r |
   transitivity N ; [apply le_max_l | assumption]].
 unfold Rseq_abs ; apply HN2 ; lia.
 right ; rewrite Rmult_comm ; apply Rseq_sum_constant_compat.
 apply Rmult_lt_compat_r ; [| apply Rmult_lt_compat_l].
  apply lt_0_INR ; lia.
  assumption.
  lra.
 right ; unfold eps3 ; field ; split.
 replace 0 with (INR O) by auto ; apply not_INR ; auto.
 apply Rgt_not_eq ; apply Rle_lt_0_plus_1 ; left ; assumption.
 apply Rlt_le_trans with (eps2 * (lna + 1)).
 apply Rle_lt_trans with (Rseq_sum (eps2 * (| Rseq_shifts (fun i => An (n - i)%nat)
  (S N1)|))%Rseq (n - S N1)).
 unfold Un ; apply Rseq_sum_le_compat_strong.
  intros p p_lb ; unfold Rseq_shifts, Rseq_mult, Rseq_abs, Rseq_minus, Rseq_constant ;
  rewrite Rabs_mult ; apply Rmult_le_compat_r ; [apply Rabs_pos |].
  left ; apply HN1 ; lia.
 rewrite Rseq_sum_scal_compat_l ; unfold Rseq_mult, Rseq_constant ;
  apply Rmult_lt_compat_l ; [assumption |].
 eapply Rle_lt_trans; [|apply Rlt_plus_1].
 transitivity (Rseq_sum (fun i => Rabs (An ((n - S N1) - i)%nat)) (n - S N1)).
 right ; apply Rseq_sum_ext_strong ; intros p p_lb ; unfold Rseq_abs, Rseq_shifts.
 replace (n - (S N1 + p))%nat with ((n - S N1) - p)%nat by lia ; reflexivity.
 rewrite <- (Rseq_sum_reindex_compat (fun i => Rabs (An i))).
(* TODO: remove growing_ineq from std_lib *)
 apply growing_ineq.
 intro p ; rewrite Rseq_sum_simpl ; assert (H := Rabs_pos (An (S p))) ; lra.
 apply Hlna.
 right ; unfold eps2 ; field ; apply Rgt_not_eq ; assumption.
 rewrite Rabs_mult ; apply Rle_lt_trans with (eps4 * Rabs lb).
 apply Rmult_le_compat_r ; [apply Rabs_pos |].
 left ; apply HN3, le_trans with N ; [apply le_max_r | assumption].
 replace eps with (eps4 * 2 * (Rabs lb + 1)) by (unfold eps4 ; field ;
  apply Rgt_not_eq ; apply Rle_lt_0_plus_1, Rabs_pos).
 field_simplify ; unfold Rdiv ; lra || (apply Rmult_lt_compat_r ; [rewrite Rinv_1 |] ; lra).
 unfold Rseq_prod ; apply Rseq_sum_ext ; intro p ; unfold Rseq_mult, Rseq_minus,
  Rseq_constant, Rseq_plus ; ring.
Qed.


(** * Extensionnal equality compatibility *)

Lemma Rsum_eq_compat : forall Un Vn, Un == Vn -> sum_f_R0 Un == sum_f_R0 Vn.
Proof.
intros Un Vn H n.
induction n; simpl; rewrite (H _); [|rewrite IHn]; reflexivity.
Qed.

Lemma Rser_cv_eq_compat : forall Un Vn l, Un == Vn -> Rser_cv Un l -> Rser_cv Vn l.
Proof.
intros Un Vn l H n.
apply Rseq_cv_eq_compat with (sum_f_R0 Un); [apply Rsum_eq_compat ; symmetry | ] ; assumption.
Qed.

Lemma Rsum_shift : forall Un, sum_f_R0 (Rseq_shift Un) == ((Rseq_shift (sum_f_R0 Un)) - (Un O))%Rseq.
Proof.
intros Un n.
assert (REW : forall a b c, c + a = b -> a = b - c) by (intros; subst; field).
apply REW.
induction n.
 compute; field.
 
 unfold Rseq_shift in *.
 do 2 rewrite tech5.
 rewrite <- IHn.
 unfold Rseq_constant.
 field.
Qed.


Lemma Rser_cv_shift_reciprocal : forall Un l, Rser_cv (Rseq_shift Un) (l - (Un O)) -> Rser_cv Un l.
Proof.
intros Un l H.
assert (EC : forall (a:Rseq) (b x:R), Rseq_cv (a - b)%Rseq (x - b) -> Rseq_cv a x).
 intros; apply Rseq_cv_eq_compat with (a - b + b)%Rseq.
  intro; compute; field.
  replace x with (x - b + b) by field.
  apply Rseq_cv_plus_compat.
   assumption.
   apply Rseq_constant_cv.
 
 eapply EC with (Un O).
 apply Rseq_cv_shift_compat.
 apply Rseq_cv_eq_compat with (sum_f_R0 (Rseq_shift Un)).
 symmetry ; apply Rsum_shift.
 apply H.
Qed.

Lemma Rser_cv_sig_shift_reciprocal_compat : forall Un, {l | Rser_cv (Rseq_shift Un) l} -> {l | Rser_cv Un l}.
Proof.
intros Un [l H].
exists (l + (Un O)).
apply Rser_cv_shift_reciprocal.
replace (l + Un 0%nat - Un 0%nat) with l by ring; assumption.
Qed.

Lemma Rser_pos_maj_cv_shift : forall Un Vn : nat -> R,
  (forall n, 0 <= Un (S n) <= Vn n) -> {lv : R | Rser_cv Vn lv} -> {lu : R | Rser_cv Un lu}.
Proof.
intros Un Vn uposmaj Vncv.
apply Rser_cv_sig_shift_reciprocal_compat.
eapply Rser_pos_maj_cv.
 intro; unfold Rseq_shift; apply (uposmaj n).
 intro; eapply Rle_trans; apply (uposmaj n).
 intro; apply (uposmaj n).
 assumption.
Qed.
