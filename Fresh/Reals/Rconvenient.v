Require Import SetoidClass.
Require Import Raxiom.

Module Rconvenient (Import T : CReals).

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
split; red.
  apply Req_refl.
  apply Req_sym.
  apply Req_trans.
Qed.

Instance Setoid_R : Setoid R := { equiv := Req }.

Lemma Radd_eq_compat_r : forall (x1 x2 y : R), Req x1 x2 -> Req (x1 + y) (x2 + y).
Proof.
intros x1 x2 y Hx.
eapply Req_trans; [ apply Radd_comm | ].
eapply Req_trans; [ | apply Radd_comm ].
apply Radd_eq_compat_l; assumption.
Qed.

Lemma Rmul_eq_compat_r : forall x1 x2 y, Req x1 x2 -> Req (x1 * y) (x2 * y).
Proof.
intros x1 x2 y Hx.
eapply Req_trans; [ apply Rmul_comm | ].
eapply Req_trans; [ | apply Rmul_comm ].
apply Rmul_eq_compat_l; assumption.
Qed.

Lemma Rmul_add_distr_r : forall x y z : R, Req ((x + y) * z) (x * z + y * z).
Proof.
intros x y z.
etransitivity; [apply Rmul_comm|].
etransitivity; [|apply Radd_eq_compat_l; apply Rmul_comm].
etransitivity; [|apply Radd_eq_compat_r; apply Rmul_comm].
apply Rmul_add_distr_l.
Qed.

Instance Proper_Req_add : Proper (Req ==> Req ==> Req) Radd.
Proof.
intros x x' Hx y y' Hy.
eapply Req_trans.
 eapply Radd_eq_compat_l; eassumption.
 eapply Radd_eq_compat_r; eassumption.
Qed.

Instance Proper_Req_mul : Proper (Req ==> Req ==> Req) Rmul.
Proof.
intros x x' Hx y y' Hy.
eapply Req_trans.
  eapply Rmul_eq_compat_l; eassumption.
  eapply Rmul_eq_compat_r; eassumption.
Qed.

Instance Proper_Req_opp : Proper (Req ==> Req) Ropp.
Proof.
intros x x' Hx.
Admitted.

Definition R_ring : ring_theory R0 R1 Radd Rmul Rsub Ropp Req.
Proof.
split.
  apply Radd_0_l.
  apply Radd_comm.
  intros; apply Req_sym, Radd_assoc.
  apply Rmul_1_l.
  apply Rmul_comm.
  intros; apply Req_sym, Rmul_assoc.
  apply Rmul_add_distr_r.
  reflexivity.
  apply Radd_opp_r.
Qed.

Add Ring R_ring : R_ring.

Lemma Radd_0_r : forall x, Req (x + R0) x.
Proof.
intros; ring.
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

Lemma Rmul_0_l : forall r:R, Req (R0 * r) R0.
Proof.
intros; ring.
Qed.

Lemma Rmul_0_r : forall r:R, Req (r * R0) R0.
Proof.
intros; ring.
Qed.

End Rconvenient.
