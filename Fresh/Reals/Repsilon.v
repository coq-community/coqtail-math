Require Import Raxiom Rconvenient IZR.

Module Repsilon (Import T : CReals).

Module Rconvenient := Rconvenient T. Import Rconvenient.
Module IZR := IZR T. Import IZR.

Lemma Rlt_pos_0 : forall x, (forall e, R0 < e -> (- e < x) * (x < e)) -> x == R0.
Proof.
 intros x Hx [ L | G ]; apply (Rlt_irrefl x).
  specialize (Hx (- x)).
  eapply Req_lt_compat_l; [ apply Ropp_involutive | ].
  apply Hx.
  apply Rlt_0_opp; auto.
  
  specialize (Hx x G); intuition.
Qed.

Lemma Rsub_0_eq : forall a b, a - b == R0 -> a == b.
Proof.
 intros a b Zab.
 apply (Radd_eq_cancel_r _ _ (- b)).
 transitivity R0; auto.
 symmetry; apply Radd_opp_r.
Qed.

Lemma Rsub_lt_pos_eq : forall a b, (forall e, R0 < e -> (a - b < e) * (b - a < e)) -> a == b.
Proof.
 intros a b Lab.
 apply Rsub_0_eq.
 apply Rlt_pos_0.
 intros e epos; destruct (Lab e epos) as (ab, ba).
 split; [ | now intuition ].
 apply Ropp_lt_contravar_reciprocal.
 eapply Req_lt_compat; [ .. | apply ba ]; ring_simplify; reflexivity.
Qed.

Lemma Rmul_2 : forall x, x + x == IPR 2 * x.
Proof.
 intros x.
 unfold IPR.
 ring.
Qed.

Lemma halfpos : forall e, R0 < e -> sigT (fun e' => prod (R0 < e') (e == e' + e')).
 intros e epos.
 exists (Rdiv e (IPR 2) (Rdiscr_IPR_0 2)); split.
  apply Rmul_lt_cancel_l with (IPR 2).
   apply Rpos_IPR.
   apply (Req_lt_compat R0 e); auto.
     ring_simplify; reflexivity (* TODO ring bug again *).
     symmetry; apply Rdiv_mul_l.
  rewrite Rmul_2.
  symmetry; apply Rdiv_mul_l.
Qed.

End Repsilon.