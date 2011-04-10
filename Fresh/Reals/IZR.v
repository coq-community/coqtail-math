Require Import Raxiom Rconvenient.

Module IZR (Import T : CReals).

Module Rconvenient := Rconvenient T.
Import Rconvenient.

Open Scope R_scope.

Definition INR := fix f n := match n with O => R0 | S n' => R1 + f n' end.

Lemma INR_add : forall a b, INR (a + b) == INR a + INR b.
Proof.
  intros a b; induction a.
    simpl; symmetry; apply Radd_0_l.
    simpl; rewrite IHa; ring.
Qed.

Lemma INR_S : forall n, INR (S n) == R1 + INR n.
Proof.
  intros; reflexivity.
Qed.

Lemma INR_mul : forall a b, INR (a * b) == INR a * INR b.
Proof.
  intros a b; induction a.
    simpl; symmetry; apply Rmul_0_l.
    simpl; rewrite INR_add, IHa; ring.
Qed.

Lemma INR_IPR : forall p, INR (nat_of_P p) == IPR p.
Proof.
  intros p.
  induction p.
    rewrite nat_of_P_xI, INR_S, INR_mul, IHp; simpl; ring.
    rewrite nat_of_P_xO, INR_mul, IHp; simpl; ring.
    simpl; ring.
Qed.

Lemma IZR_Zopp : forall z, IZR (- z) == - IZR z.
Proof.
  intros z; induction z.
    simpl; symmetry; apply Ropp_0.
    reflexivity.
    symmetry; apply Ropp_involutive.
Qed.

Lemma IZR_INR : forall n, IZR (Z_of_nat n) == INR n.
Proof.
  intros n.
  destruct n.
  reflexivity.
  
  rewrite
    <- nat_of_P_o_P_of_succ_nat_eq_succ,
    <- Zpos_eq_Z_of_nat_o_nat_of_P,
    INR_IPR.
  reflexivity.
Qed.

Lemma INR_sub : forall a b, le b a -> INR (a - b) == INR a - INR b.
Proof.
  intros a b ab.
  rewrite (le_plus_minus b a ab) at 2.
  unfold Rsub.
  rewrite INR_add.
  rewrite Radd_comm, <- Radd_assoc, (Radd_comm (- INR b)), Radd_opp_r, Radd_0_l.
  reflexivity.
Qed.


Lemma Zopp_swap : forall a b, Zopp a = b -> a = Zopp b.
Proof.
  intros a b H; rewrite <- H; ring.
Qed.

Lemma Zuminus : forall a b, (a + - b = a - b)%Z.
Proof.
  intros; ring.
Qed.

Lemma IZR_add : forall x y, IZR (x + y) == IZR x + IZR y.
Proof.
  intros a b.
  destruct (Z_le_gt_dec 0 a) as [Ha|Ha];
  [ destruct (Z_of_nat_complete_inf a Ha) as (na, Hna)
  | assert (Ha' : (0 <= -a)%Z) by omega; destruct (Z_of_nat_complete_inf _ Ha') as (na, Hna) ];
  (destruct (Z_le_gt_dec 0 b) as [Hb|Hb];
  [ destruct (Z_of_nat_complete_inf b Hb) as (nb, Hnb)
  | assert (Hb' : (0 <= -b)%Z) by omega; destruct (Z_of_nat_complete_inf _ Hb') as (nb, Hnb) ]).
  
  subst.
  rewrite <- inj_plus.
  do 3 rewrite IZR_INR; apply INR_add.
  
  apply Zopp_swap in Hnb.
  subst.
  rewrite Zuminus.
  destruct (le_dec na nb) as [ab|ab].
    assert (Hr : forall a b, (a - b = - (b - a))%Z) by (intros; ring); rewrite Hr; clear Hr.
    rewrite <- (inj_minus1 _ _ ab).
    repeat rewrite IZR_Zopp.
    repeat rewrite IZR_INR.
    rewrite INR_sub; auto.
    apply Ropp_sub.
    
    rewrite <- inj_minus1; [ | omega ].
    rewrite IZR_Zopp.
    repeat rewrite IZR_INR.
    rewrite INR_sub; [ | omega ].
    reflexivity.
  
  apply Zopp_swap in Hna.
  subst.
  destruct (le_dec na nb) as [ab|ab].
    assert (Hr : forall a b, (- a + b = b - a)%Z) by (intros; ring); rewrite Hr; clear Hr.
    rewrite <- (inj_minus1 _ _ ab).
    repeat rewrite IZR_Zopp.
    repeat rewrite IZR_INR.
    rewrite INR_sub; auto.
    rewrite Radd_comm.
    reflexivity.
    
    assert (Hr : forall a b, (- a + b = - (a - b))%Z) by (intros; ring); rewrite Hr; clear Hr.
    rewrite <- inj_minus1; [ | omega ].
    repeat rewrite IZR_Zopp.
    repeat rewrite IZR_INR.
    rewrite INR_sub; [ | omega ].
    rewrite Ropp_sub, Radd_comm; reflexivity.
  
  apply Zopp_swap in Hna.
  apply Zopp_swap in Hnb.
  subst.
  rewrite <- Zopp_plus_distr.
  repeat rewrite IZR_Zopp.
  rewrite <- inj_plus.
  repeat rewrite IZR_INR.
  rewrite INR_add.
  apply Ropp_add.
Qed.

Lemma IZR_sub : forall x y, IZR (x - y) == IZR x - IZR y.
Proof.
  intros a b. unfold Zminus. unfold Rsub. rewrite IZR_add. rewrite IZR_Zopp. ring.
Qed.

Lemma Rpos_IPR : forall p, R0 < IPR p.
Proof.
intros p; induction p; simpl.
  apply Rlt_trans with (R0 + R1).
  apply Req_lt_compat_r with R1; [ symmetry; apply Radd_0_l | apply Rlt_0_1 ].
  
  apply Radd_lt_compat_r.
  eapply Req_lt_compat_l; [ apply Rmul_0_r | ].
  apply Rmul_lt_compat_l.
    apply Rlt_0_2.
    apply IHp.
  
  eapply Req_lt_compat_l; [ apply Rmul_0_r | ].
  apply Rmul_lt_compat_l.
    apply Rlt_0_2.
    apply IHp.
  
  apply Rlt_0_1.
Qed.

Lemma Rdiscr_IPR_0 : forall p, IPR p ## R0.
Proof.
intros p; right; apply Rpos_IPR.
Qed.

Lemma IZR_lt : forall x y, (x < y)%Z -> IZR x < IZR y.
Proof.
  intros x y xy.
  apply Radd_lt_cancel_l with (-IZR x).
  eapply Req_lt_compat_l; [ apply Radd_comm | ].
  eapply Req_lt_compat_l; [ symmetry; apply Radd_opp_r | ].
  eapply Req_lt_compat_r; [ apply Radd_comm | ].
  eapply Req_lt_compat_r.
    rewrite <- IZR_Zopp, <- IZR_add; reflexivity.
    
    remember (y + - x)%Z as d.
    assert (dp : (0 < d)%Z) by omega.
    destruct d; try inversion dp.
    simpl.
    apply Rpos_IPR.
Qed.

Lemma IZR_le : forall x y, (x <= y)%Z -> IZR x <= IZR y.
Proof.
  intros x y xy.
  destruct (Z_le_lt_eq_dec _ _ xy).
  left; apply IZR_lt; auto.
  right; subst; apply Req_refl.
Qed.

Lemma IZR_opp : forall a, IZR (- a) == - IZR a.
Proof.
  intros [ | p | p ]; simpl; symmetry.
    apply Ropp_0.
    reflexivity.
    apply Ropp_involutive.
Qed.

Lemma IPR_mul : forall a b, IPR (a * b) == IPR a * IPR b.
Proof.
  intros a b.
  repeat rewrite <- INR_IPR.
  rewrite <- INR_mul, nat_of_P_mult_morphism.
  reflexivity.
Qed.

Lemma IZR_mul : forall a b, IZR (a * b) == IZR a * IZR b.
Proof.
  intros [ | p | p ] [ | q | q ]; simpl; try rewrite IPR_mul; ring.
Qed.

Lemma IZR_eq : forall a b, a = b -> IZR a == IZR b.
Proof.
  intros; subst; reflexivity.
Qed.

Ltac IZRify :=
  replace R1 with (IZR 1) by reflexivity;
  replace R0 with (IZR 0) by reflexivity;
  repeat
    (rewrite <- IZR_add ||
    rewrite <- IZR_sub ||
    rewrite <- IZR_mul ||
    rewrite <- IZR_opp);
  apply IZR_eq || apply IZR_lt || apply IZR_le || idtac.

Ltac eq_lt_compat_r_tac t := eapply Req_lt_compat_r; [ t; reflexivity | ].
Ltac eq_lt_compat_l_tac t := eapply Req_lt_compat_l; [ t; reflexivity | ].
Ltac eq_le_compat_r_tac t := eapply Req_le_compat_r; [ t; reflexivity | ].
Ltac eq_le_compat_l_tac t := eapply Req_le_compat_l; [ t; reflexivity | ].
Ltac eq_eq_compat_l_tac t := eapply Req_trans; [ symmetry; t; reflexivity | ].
Ltac eq_eq_compat_r_tac t := symmetry; eapply Req_trans; [ symmetry; t; reflexivity | ]; symmetry.

Ltac eq_compat_l_tac t := match goal with
  | |- _ == _ => eq_eq_compat_l_tac t
  | |- _ <  _ => eq_lt_compat_l_tac t
  | |- _ <= _ => eq_le_compat_l_tac t end.

Ltac eq_compat_r_tac t := match goal with
  | |- _ == _ => eq_eq_compat_r_tac t
  | |- _ <  _ => eq_lt_compat_r_tac t
  | |- _ <= _ => eq_le_compat_r_tac t end.

Ltac IZRrel :=
  eq_compat_r_tac IZRify;
  eq_compat_l_tac IZRify;
  match goal with
  | |- _ == _ => try apply IZR_eq
  | |- _ <= _ => try apply IZR_le
  | |- _ <  _ => try apply IZR_lt
  end; try omega.

End IZR.
