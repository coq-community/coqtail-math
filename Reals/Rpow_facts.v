Require Import Reals.

Open Local Scope R_scope.

Lemma pow_lt_compat : forall x y, 0 < x -> x < y ->
  forall n, (1 <= n)%nat -> x ^ n < y ^ n.
Proof.
intros x y x_pos x_lt_y n n_lb.
 induction n.
 apply False_ind ; intuition.
 destruct n.
 simpl ; repeat (rewrite Rmult_1_r) ; assumption.
 assert (Hrew : forall a n, a ^ S (S n) = a * a ^ S n).
  intros a m ; simpl ; reflexivity.
 repeat (rewrite Hrew) ; apply Rmult_gt_0_lt_compat ; [apply pow_lt | | | apply IHn] ; intuition.
 apply Rlt_trans with x ; assumption.
Qed.

Lemma pow_le_compat : forall x y, 0 <= x -> x <= y ->
 forall n, x ^ n <= y ^ n.
Proof.
intros x y x_pos x_lt_y n.
induction n.
simpl ; apply Req_le ; reflexivity.
simpl ; apply Rmult_le_compat ; [| apply pow_le | |] ; assumption.
Qed.