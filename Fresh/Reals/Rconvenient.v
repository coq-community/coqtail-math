Require Import SetoidClass.
Require Import Raxiom.

Module Rconvenient (T : CReals).
Import T.

Open Scope R_scope.

(** * Useful and basics results on <, ==, # *)

Lemma Req_sym : forall x y, Req x y -> Req y x.
Proof.
compute; intuition.
Qed.

Lemma Req_refl : forall r, Req r r.
Proof.
intros r [H|H]; apply (Rlt_asym r r); apply H.
Qed.

Lemma Rlt_irrefl : forall r, r < r -> False.
Proof.
pose Rlt_asym; eauto.
Qed.

Lemma Rdiscr_irrefl : forall r, r # r -> False.
Proof.
intros ? [|]; apply Rlt_irrefl.
Qed.

Lemma Req_trans : forall r1 r2 r3 : R, Req r1 r2 -> Req r2 r3 -> Req r1 r3.
Proof.
intros r1 r2 r3 Hl Hr [H|H].
 eapply Req_lt_compat_l in H; [|eexact Hl].
 eapply Req_lt_compat_l in H; [|eexact Hr].
 apply (Rlt_irrefl _ H).
 
 eapply Req_lt_compat_l in H; [|apply Req_sym; eexact Hr].
 eapply Req_lt_compat_l in H; [|apply Req_sym; eexact Hl].
 apply (Rlt_irrefl _ H).
Qed.



(** * Setoid **)

Instance Equivalence_Req : Equivalence Req.
Proof.
split.
 intros x [H|H]; eapply Rlt_asym; apply H.
 compute; intuition.
 intros x y z Hxy Hyz [Hc|Hc].
  apply (Rlt_asym z z);
    eapply (Req_lt_compat_l y); eauto;
      eapply (Req_lt_compat_l _); eauto.
  apply (Rlt_asym z z);
    eapply (Req_lt_compat_r y); eauto;
      eapply (Req_lt_compat_r _); eauto.
Qed.

Lemma Radd_0_r : forall x, Req (x + R0) x.
Proof.
intros x.
eapply Req_trans.
 apply Radd_comm.
 apply Radd_0_l.
Qed.

Lemma Radd_eq_compat_l : forall (x y1 y2 : R), Req y1 y2 -> Req (x + y1) (x + y2).
Proof.
intros x y1 y2 Hy [H1|H2].
 apply Rlt_irrefl with y2.
 eapply Req_lt_compat_l; [ apply Hy | ]; clear Hy.
 eapply Req_lt_compat_l; [ apply Radd_0_l | ].
 eapply Req_lt_compat_r; [ apply Radd_0_l | ].
 pose proof Req_lt_compat_l _ _ _ (Req_sym _ _ (Radd_assoc _ _ _)) (Radd_lt_compat_l (-x) _ _ H1) as H1'.
 pose proof Req_lt_compat_r _ _ _ (Req_sym _ _ (Radd_assoc _ _ _)) H1'.
 (*what do? Is it provable? *)
Admitted.

Lemma Radd_eq_compat_r : forall (x1 x2 y : R), Req x1 x2 -> Req (x1 + y) (x2 + y).
Proof.
intros x1 x2 y Hx.
eapply Req_trans; [ apply Radd_comm | ].
eapply Req_trans; [ | apply Radd_comm ].
apply Radd_eq_compat_l; assumption.
Qed.

Lemma Radd_lt_compat_r : forall x1 x2 y : R, x1 < x2 -> x1 + y < x2 + y.
Proof.
intros.
eapply Req_lt_compat_l; [ apply Radd_comm | ].
eapply Req_lt_compat_r; [ apply Radd_comm | ].
apply Radd_lt_compat_l; auto.
Qed.

Lemma Rlt_opp_1_0 : - R1 < R0.
Proof.
eapply Req_lt_compat_l; [ apply Radd_0_l | ].
eapply Req_lt_compat_r; [ apply Radd_opp_r | ].
apply Radd_lt_compat_r.
apply Rlt_0_1.
Qed.

Instance Proper_Req_add : Proper (Req ==> Req ==> Req) Radd.
Proof.
intros x x' Hx y y' Hy.
eapply Req_trans.
 eapply Radd_eq_compat_l; eassumption.
 eapply Radd_eq_compat_r; eassumption.
Qed.

(*
Lemma Rmul_opp_l : forall a b, Req (- a * b) (- (a * b)).
Admitted.
*)

Lemma Rmul_0_l : forall r:R, Req (R0 * r) R0.
Admitted.

Lemma Rmul_0_r : forall r:R, Req (r * R0) R0.
Proof.
intros r.
eapply Req_trans; [ apply Rmul_comm | ].
apply Rmul_0_l.
Qed.


End Rconvenient.