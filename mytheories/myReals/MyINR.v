Require Import Reals.

Local Open Scope R_scope.

Lemma INR_1 : INR 1 = 1.
Proof.
simpl ; reflexivity.
Qed.

Lemma Rabs_INR : forall n, Rabs (INR n) = INR n.
Proof.
intros ; apply Rabs_pos_eq ; apply pos_INR.
Qed.