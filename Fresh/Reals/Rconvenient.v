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

Lemma Rdiscr_irrefl : forall r, r ## r -> False.
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

Lemma Rlt_le_trans : forall x y z, Rlt x y -> Rle y z -> Rlt x z.
Proof.
intros ? ? ? ? [|?].
 apply Rlt_trans; auto.
 eapply Req_lt_compat_r; eauto.
Qed.

Lemma Rle_lt_trans : forall x y z, Rle x y -> Rlt y z -> Rlt x z.
Proof.
intros ? ? ? [?|].
 apply Rlt_trans; auto.
 intros; eapply Req_lt_compat_l.
  apply Req_sym; eauto.
  auto.
Qed.

Lemma Rle_trans : forall x y z, Rle x y -> Rle y z -> Rle x z.
Proof.
intros x y z [xy|xy] [yz|yz].
 left; eapply Rlt_trans; eauto.
 left; eapply Req_lt_compat_r; eauto.
 left; eapply Req_lt_compat_l; eauto; apply Req_sym, xy.
 right; eapply Req_trans; eauto.
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

Lemma Radd_0_r : forall x, x + R0 == x.
Proof.
intro.
rewrite Radd_comm.
apply Radd_0_l.
Qed.

Lemma Radd_lt_compat_r : forall x y1 y2 : R, y1 < y2 -> y1 + x < y2 + x.
Proof.
intros x a b ab.
eapply Req_lt_compat_l; try apply Radd_comm.
eapply Req_lt_compat_r; try apply Radd_comm.
apply Radd_lt_compat_l; auto.
Qed.

Lemma Rlt_0_2 : R0 < R1 + R1.
Proof.
apply Req_lt_compat_l with (R0 + R0); try apply Radd_0_l.
apply Rlt_trans with (R0 + R1).
 eapply Radd_lt_compat_l; apply Rlt_0_1.
 eapply Radd_lt_compat_r; apply Rlt_0_1.
Qed.

Lemma Radd_eq_cancel_r : forall x x' y, x + y == x' + y -> x == x'.
intros x x' y Hxy.
rewrite <- (Radd_0_r x), <- (Radd_0_r x').
rewrite <- (Radd_opp_r y).
repeat rewrite <- Radd_assoc.
rewrite <- Hxy.
apply Radd_eq_compat_l.
reflexivity.
Qed.

Instance Proper_Req_opp : Proper (Req ==> Req) Ropp.
Proof.
intros x x' Hx.
apply (Radd_eq_cancel_r _ _ x).
rewrite Hx at 3.
do 2 rewrite Radd_comm, Radd_opp_r; reflexivity.
Qed.

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

Lemma Radd_lt_cancel_l : forall x1 x2 y : R, y + x1 < y + x2 -> x1 < x2.
Proof.
intros x1 x2 y Hx.
eapply Req_lt_compat_l; [ rewrite <- Radd_0_l, <- (Radd_opp_r y), (Radd_comm y), Radd_assoc; reflexivity | ].
eapply Req_lt_compat_r; [ rewrite <- Radd_0_l, <- (Radd_opp_r y), (Radd_comm y), Radd_assoc; reflexivity | ].
apply Radd_lt_compat_l, Hx.
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

Definition Ppow2 := fix f n := match n with O => xH | S n' => xO (f n') end.
Definition Rpow2 n := IPR (Ppow2 n).

Lemma Rpos_pow2 : forall n, Rlt R0 (Rpow2 n).
Proof.
 intros n; induction n.
 apply Rlt_0_1.
 apply (Req_lt_compat_l _ _ _ (Radd_0_l R0)).
 apply Rlt_trans with (R0 + Rpow2 n).
  apply Radd_lt_compat_l; auto.
  
  simpl.
  unfold Rpow2; simpl.
  eapply Req_lt_compat_r; [ rewrite Rmul_add_distr_r; reflexivity | ].
  eapply Req_lt_compat_r; [ repeat rewrite Rmul_1_l; reflexivity | ].
  apply Radd_lt_compat_r; auto.
Qed.

Lemma Rnn_pow2 : forall n, Rpow2 n ## R0.
Proof.
 intros n; right; apply Rpos_pow2.
Qed.

Lemma Ropp_0 : - R0 == R0.
Proof.
  rewrite <- Radd_0_l.
  apply Radd_opp_r.
Qed.

Lemma Rmul_lt_cancel_l : forall x y1 y2 : R, R0 < x -> x * y1 < x * y2 -> y1 < y2.
Proof.
 intros r a b rpos Hab.
 assert (Hir := Rinv_0_lt_compat r rpos (inr rpos)).
 remember (Rinv r (inr rpos)) as ir.
 eapply Req_lt_compat_l; [ rewrite <- Rmul_1_l, <- (Rinv_l r (inr rpos)), Rmul_assoc; reflexivity | ].
 eapply Req_lt_compat_r; [ rewrite <- Rmul_1_l, <- (Rinv_l r (inr rpos)), Rmul_assoc; reflexivity | ].
 apply Rmul_lt_compat_l; subst; auto.
Qed.

Lemma Rmul_lt_compat_r : forall x y1 y2 : R, R0 < x -> y1 < y2 -> y1 * x < y2 * x.
Proof.
 intros x; intros.
 apply (Req_lt_compat_l _ _ _ (Rmul_comm x _)).
 apply (Req_lt_compat_r _ _ _ (Rmul_comm x _)).
 apply Rmul_lt_compat_l; auto.
Qed.

Lemma Ropp_involutive : forall x, - - x == x.
Proof.
intros x.
eapply Radd_eq_cancel_r with (- x).
rewrite Radd_opp_r.
rewrite Radd_comm, Radd_opp_r.
reflexivity.
Qed.

Lemma Zopp_Zpos : forall p, Zopp (Zpos p) = Zneg p.
Proof.
intros p.
simpl; auto.
Qed.

Lemma Ropp_add : forall a b, - (a + b) == - a - b.
Proof.
intros a b.
apply Radd_eq_cancel_r with (a + b).
rewrite Radd_comm, Radd_opp_r.
unfold Rsub.
rewrite <- Radd_assoc, Radd_comm, (Radd_comm (- a)).
rewrite Radd_assoc, (Radd_comm  _ a), Radd_opp_r.
rewrite Radd_0_r, Radd_opp_r.
reflexivity.
Qed.

Lemma Ropp_sub : forall a b, - (a - b) == b - a.
Proof.
intros a b.
unfold Rsub.
rewrite Ropp_add.
unfold Rsub.
rewrite Ropp_involutive.
apply Radd_comm.
Qed.

Section IZR_results.
  
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
  
End IZR_results.

Lemma Rlt_id_pow2 : forall n, IZR (Z_of_nat n) < Rpow2 n.
Proof.
intros n.
replace (Rpow2 n) with (IZR (Zpos (Ppow2 n))) by reflexivity.
apply IZR_lt.
destruct n.
 compute; auto.
 simpl.
 induction n.
  compute; auto.
  
  simpl.
  rewrite Zpos_succ_morphism.
  unfold Zsucc.
  remember (Zpos (P_of_succ_nat n)) as Zn.
  rewrite Zpos_xO in *.
  rewrite (Zpos_xO (Ppow2 n)).
  remember (Zpos (Ppow2 n)) as Zpn.
  ring_simplify.
  assert (0 < Zn)%Z.
   rewrite HeqZn; compute; reflexivity.
   omega.
Qed.

Lemma Rlt_0_opp : forall x, R0 < x -> - x < R0.
Proof.
intros x xpos.
apply Radd_lt_cancel_l with x.
eapply Req_lt_compat_r.
 symmetry; apply Radd_0_r.
 eapply Req_lt_compat_l.
  symmetry; apply Radd_opp_r.
  apply xpos.
Qed.

Lemma Rinv_pow_2_cv_0 : Rseq_cv (fun n => Rinv (Rpow2 n) (Rnn_pow2 n)) R0.
Proof.
 intros e epos.
 assert (Hie := Rinv_0_lt_compat e epos (inr epos)).
 remember (Rinv e (inr epos)) as ie.
 pose (nie := Zmax 1%Z (Rup (R1 + ie))).
 remember (Rup (R1 + ie)) as uie.
 destruct (Z_of_nat_complete_inf nie) as (N, HN).
  eapply Zle_trans; [ apply Zle_0_1 | unfold nie; apply Zle_max_l ].
  
  exists N.
  intros n Hn.
  split.
   eapply Req_lt_compat_l; [ unfold Rdist, Rsub; rewrite Ropp_0, Radd_0_r; reflexivity | ].
   apply (Rmul_lt_cancel_l (Rpow2 n) _ _ (Rpos_pow2 n)); eapply Req_lt_compat_l; [ rewrite Rmul_comm; symmetry; apply Rinv_l | ].
   
   cut (ie < Rpow2 n).
    intros Hien.
    apply Req_lt_compat_l with (ie * e); [ subst; apply Rinv_l | ].
    apply Rmul_lt_compat_r; auto.
    
    apply Rlt_le_trans with (IZR uie).
     destruct (Rup_spec (R1 + ie)) as (BA, _).
     rewrite <- Hequie in BA.
     assert (BAA := Radd_lt_compat_r (IZR uie - R1) _ _ BA).
     eapply Req_lt_compat_r; [ | eapply Req_lt_compat_l ] ; [ | | apply BAA ].
      ring.
      ring.
     
     eapply Rle_trans; [ | left; apply Rlt_id_pow2 ].
     apply IZR_le.
     apply Zle_trans with nie.
      apply Zle_max_r.
      rewrite HN; apply inj_le; auto.
   
   eapply Req_lt_compat_r; [ unfold Rdist, Rsub; rewrite Ropp_0, Radd_0_r; reflexivity | ].
   apply Rlt_trans with R0.
    apply Rlt_0_opp; auto.
    
    apply Rinv_0_lt_compat.
    apply Rpos_pow2.
Qed.

End Rconvenient.
