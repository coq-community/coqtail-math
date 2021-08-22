Require Import Reals MyRIneq Fourier Lia Lra.
Require Import Rsequence_usual_facts.

Local Open Scope R_scope.

Lemma pow_lt_compat : forall x y, 0 <= x -> x < y ->
  forall n, (1 <= n)%nat -> x ^ n < y ^ n.
Proof.
intros x y x_pos x_lt_y n n_lb.
 induction n.
 apply False_ind ; intuition; try lia.
 destruct n.
 simpl ; repeat (rewrite Rmult_1_r) ; assumption.
 assert (Hrew : forall a n, a ^ S (S n) = a * a ^ S n).
  intros a m ; simpl ; reflexivity.
 destruct x_pos as [x_pos | x_null].
 do 2 rewrite Hrew.
  repeat (rewrite Hrew) ; apply Rmult_gt_0_lt_compat ; [apply pow_lt | | | apply IHn] ; intuition.
  apply Rlt_gt ; transitivity x ; assumption.
 rewrite Hrew, <- x_null, Rmult_0_l ; apply pow_lt ;
  apply Rle_lt_trans with x ; [right |] ; auto.
Qed.

Lemma pow_le_compat : forall x y, 0 <= x -> x <= y ->
 forall n, x ^ n <= y ^ n.
Proof.
intros x y x_pos x_lt_y n.
induction n.
simpl ; apply Req_le ; reflexivity.
simpl ; apply Rmult_le_compat ; [| apply pow_le | |] ; assumption.
Qed.


Lemma pow2_sqr : forall r, r² = r ^ 2.
Proof.
intros ; rewrite <- (mult_1_r 2), pow_Rsqr, pow_1 ; reflexivity.
Qed.

Lemma pow2_pos : forall r, 0 <= r ^ 2.
Proof.
intro r ; rewrite <- pow2_sqr ; apply Rle_0_sqr.
Qed.

Lemma Rsqrt_sqr : forall x (y : nonnegreal),
  0 <= x -> (x ^ 2 = y)%R -> Rsqrt y = x.
Proof.
intros x y x_pos Heq ; unfold Rsqrt.
 destruct (Rsqrt_exists y (cond_nonneg y)) as [z [z_pos Hz]].
 apply Rsqr_inj ; try assumption.
 symmetry ; rewrite pow2_sqr, Heq ; apply Hz.
Qed.

Lemma Rsqr_Rsqrt : forall x, Rsqrt x ^ 2 = x.
Proof.
intro ; simpl ; rewrite <- Rmult_assoc, Rsqrt_Rsqrt ; apply Rmult_1_r.
Qed.

Lemma Rsqrt_mult_distr : forall (x y z : nonnegreal), x * y = z ->
  Rsqrt z = Rsqrt x * Rsqrt y.
Proof.
intros x y z Heq ; apply Rsqr_inj.
 apply Rsqrt_positivity.
 apply Rmult_le_pos ; apply Rsqrt_positivity.
 rewrite Rsqr_mult.
 unfold Rsqr ; do 3 rewrite Rsqrt_Rsqrt ; auto.
Qed.

Lemma Rsqrt_pow_even : forall r n, Rsqrt r ^ (2 * n) = r ^ n.
Proof.
intros r n ; rewrite pow_sqr, Rsqrt_Rsqrt ; reflexivity.
Qed.

Lemma sum_pow : forall (q : R) (m k : nat),
  q <> 1 ->
  sum_f_R0 (fun i : nat => q ^ (m + i)) k = q^m * (1 - q ^ S k) / (1 - q).
Proof.
intros q m k q_neq_1.
 induction m.
  assert (H := tech3 q k q_neq_1) ; rewrite Rmult_1_l ; rewrite <- H ; unfold pow ; simpl ;
  apply sum_eq ; intros i i_ub ; intuition.
 replace (sum_f_R0 (fun i : nat => pow q (S m + i)) k) with (q * (sum_f_R0 (fun i : nat => pow q (m + i)) k)).
 rewrite IHm ; simpl ; unfold Rdiv ; repeat (rewrite Rmult_assoc) ; repeat (apply Rmult_eq_compat_l) ;
 reflexivity.
 clear ; induction k.
 simpl ; intuition.
 simpl ; rewrite Rmult_plus_distr_l ; rewrite IHk ; apply Rplus_eq_compat_l ; apply Rmult_eq_compat_l.
 unfold pow ; replace (k + S m)%nat with (S (k + m))%nat by intuition ; simpl ; reflexivity.
Qed.

Lemma Rpser_cv_speed_pow_id : forall x : R, Rabs x < 1 ->
     Un_cv (fun n : nat => INR (S n) *  x ^ S n) 0.
Proof.
intros x x_bd eps eps_pos.
 case (Req_or_neq x) ; intro Hx.
  exists 0%nat ; intros ; unfold R_dist ; rewrite Rminus_0_r ;
  rewrite Hx ; rewrite pow_i ; [| intuition] ; rewrite Rmult_0_r ; rewrite Rabs_R0 ;
  assumption.
 assert (H : Un_cv (fun n => /INR (S n)) 0).
  apply cv_infty_cv_R0.
  intros n Hf ; replace 0 with (INR 0) in Hf by intuition.
  discriminate (INR_eq _ _ Hf).
  intro B ; assert (0 <= IZR (up (Rabs B))).
  apply Rle_trans with (Rabs B) ; [apply Rabs_pos |] ;
  apply Rge_le ; left ; apply (proj1 (archimed (Rabs B))).
  assert (H1 : (0 <= up (Rabs B))%Z).
  apply le_IZR ; assumption.
  destruct (IZN (up (Rabs B)) H1) as (N, HN) ; exists N ;
  intros n n_lb ; apply Rlt_le_trans with (INR (S N)).
  apply Rlt_trans with (IZR (up (Rabs B))).
  apply Rle_lt_trans with (Rabs B) ; [apply RRle_abs |] ;
  apply (proj1 (archimed (Rabs B))).
  rewrite HN.
  rewrite <- INR_IZR_INZ.
  intuition.
  intuition.
  assert (Rinv_r_pos : 0 < (1 + 1 / Rabs x) / 2 - 1).
   apply Rlt_Rminus ; apply Rle_lt_trans with ((1 + 1)/2).
   right ; field.
   unfold Rdiv ; apply Rmult_lt_compat_r.
   apply Rinv_0_lt_compat ; intuition.
   apply Rplus_lt_compat_l ; rewrite Rmult_1_l ; rewrite <- Rinv_1 ;
   apply Rinv_lt_contravar.
   rewrite Rmult_1_r ; apply Rabs_pos_lt ; assumption. 
   assumption.
   pose (k := (1 + Rabs x) / 2).
   assert (k_pos : 0 <= k).
    unfold k ; replace 0 with (0/2) by field ; unfold Rdiv ; apply Rmult_le_compat_r.
    left ; apply Rinv_0_lt_compat ; intuition.
    apply Rle_zero_pos_plus1 ; apply Rabs_pos.
 assert (k_lt_1 : ((1 + Rabs x) / 2) < 1).
  apply Rlt_le_trans with ((1 + 1) /2).
  unfold Rdiv ; apply Rmult_lt_compat_r.
  apply Rinv_0_lt_compat ; intuition.
  apply Rplus_lt_compat_l ; assumption.
  right ; field.
  assert (Main : forall M eps, 0 < eps -> 0 < M -> exists N, forall n, (n >= N)%nat ->
             M * ((1 + Rabs x) / 2) ^ n < eps).
   clear -k_lt_1 k_pos ; intros M eps eps_pos M_pos ;
   assert (r_bd : 0 <= (1 + Rabs x) / 2 < 1) by intuition ;
   destruct (Rseq_pow_lt_1_cv ((1 + Rabs x) / 2) r_bd (eps / M)) as (N, HN).
   unfold Rdiv ; apply Rmult_lt_0_compat ; [| apply Rinv_0_lt_compat] ; assumption.
   exists N ; intros n n_lb.
   apply Rlt_le_trans with (M * (eps / M)).
   apply Rmult_lt_compat_l.
   assumption.
   replace (((1 + Rabs x) / 2) ^ n) with (Rabs (((1 + Rabs x) / 2) ^ n - 0)).
   apply HN ; assumption.
   rewrite Rminus_0_r ; apply Rabs_right.
   apply Rle_ge ; apply pow_le ; assumption.
   right ; field ; apply Rgt_not_eq ; assumption.
   destruct (H ((1 + 1 / Rabs x) / 2 - 1) Rinv_r_pos) as (N, HN).
assert (Temp : forall M i : nat, (M >= S N)%nat -> Rabs (INR (i + S M) * x ^ (i + S M)) <
        (1 + Rabs x) / 2 * Rabs (INR (i + M) * x ^ (i + M))).
 intros M i M_lb.
 apply Rle_lt_trans with (Rabs ((INR (i + S M) / (INR (i + M))) * ((INR (i + M)) * x ^ (i + S M)))).
 right ; apply Rabs_eq_compat ; field ; apply Rgt_not_eq ; apply lt_0_INR; lia.
 replace (i + S M)%nat with (S (i + M))%nat by intuition lia.
 rewrite <- tech_pow_Rmult.
 repeat (rewrite Rabs_mult ; rewrite <- Rmult_assoc).
 apply Rmult_lt_compat_r.
 apply Rabs_pos_lt ; apply pow_nonzero ; assumption.
 rewrite Rmult_comm, <- Rmult_assoc.
 apply Rmult_lt_compat_r.
 apply Rabs_pos_lt ; apply Rgt_not_eq ; apply lt_0_INR; lia.
 replace (INR (S (i + M)) / INR (i + M)) with (1 + / INR (i + M)).
 apply Rlt_le_trans with (Rabs x * (1 + 1 / Rabs x) / 2).
 unfold Rdiv ; rewrite Rmult_assoc ; apply Rmult_lt_compat_l.
 apply Rabs_pos_lt ; assumption.
 rewrite Rabs_right.
 assert (Temp : forall a b c, b < c - a -> a + b < c).
  clear ; intros ; lra.
 apply Temp.
 replace (/INR (i + M)) with (R_dist (/INR (S (i + pred M))) 0).
 apply HN ; intuition lia.
 unfold R_dist ; rewrite Rminus_0_r ; replace (S (i + pred M))%nat with (i + M)%nat.
 apply Rabs_right ; left ; apply Rinv_0_lt_compat ; apply lt_0_INR; lia.
 intuition lia.
 apply Rle_ge ; apply Rle_zero_pos_plus1.
 left ; apply Rinv_0_lt_compat; apply lt_0_INR; lia.
 right ; field.
 apply Rgt_not_eq ; apply Rabs_pos_lt ; assumption.
 replace (INR (S (i + M))) with (1 + INR (i + M)).
 field ; apply Rgt_not_eq ; apply lt_0_INR; lia.
 replace (S (i + M)) with (1 + (i + M))%nat by intuition ; rewrite S_O_plus_INR.
 intuition.
 pose (An_0 := Rabs (INR (S N))).
 assert (An_0_pos : 0 < An_0 * Rabs x ^ (S N)). 
  apply Rmult_lt_0_compat.
  unfold An_0 ; apply Rabs_pos_lt ; apply Rgt_not_eq ; intuition.
  apply pow_lt ; apply Rabs_pos_lt ; assumption.
 destruct (Main (An_0 * Rabs x ^ (S N)) eps eps_pos An_0_pos) as (N2, HN2).
 exists (N2 + S N)%nat ; intros n n_lb.
 fold k in Temp.
 assert (Temp2 : forall i : nat,
      (fun i0 : nat => Rabs (INR (i0 + S N) * x ^ (i0 + S N))) (S i) <
      k * (fun i0 : nat => Rabs (INR (i0 + S N) * x ^ (i0 + S N))) i).
 intro i.
 replace (S i + S N)%nat with (i + S (S N))%nat by ring.
 apply Temp ; intuition.
 clear Temp.
 unfold R_dist, Rminus ; rewrite Ropp_0 ; rewrite Rplus_0_r.
 assert (Temp : forall m n, (m >= n)%nat -> {p | (m = n + p)%nat}).
   clear ; intros m n ; induction n ; intro H.
   exists m ; intuition lia.
   case (le_lt_eq_dec _ _ H) ; clear H ; intro H.
   assert (H' : (m >= n)%nat) by intuition lia.
   destruct (IHn H') as (p, Hp) ; destruct p.
   exists 0%nat ; apply False_ind ; intuition lia.
   exists p ; intuition lia.
   exists 0%nat ; intuition lia.
  destruct (Temp n (N2 + S N)%nat n_lb) as (p,Hp).
  rewrite Hp. replace (S (N2 + S N + p))%nat with ((S N2 + p) + S N)%nat by intuition lia.
 assert (H' := tech4 (fun i : nat => Rabs (INR (i + S N) * x ^ (i + S N))) k
             (S N2 + p) k_pos Temp2).
 apply Rle_lt_trans with (Rabs (INR (0 + S N) * x ^ (0 + S N)) * k ^ (S N2 + p)).
 apply H'.
 simpl (0 + S N)%nat ; rewrite Rabs_mult ; fold An_0 ; unfold k ; rewrite <- RPow_abs ;
 apply HN2.
 intuition.
Qed.
