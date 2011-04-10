Require Import SetoidClass.
Require Import Raxiom.

Module Rconvenient (Import T : CReals).

Open Scope R_scope.

Section Req.

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

Global Instance Equivalence_Req : Equivalence Req.
Proof.
split; red.
  apply Req_refl.
  apply Req_sym.
  apply Req_trans.
Qed.

Global Instance Setoid_R : Setoid R := { equiv := Req }.

End Req.

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


Lemma Radd_lt_compat : forall x1 x2 y1 y2 : R, x1 < x2 -> y1 < y2 -> x1 + y1 < x2 + y2.
Proof.
intros.
eapply Rlt_trans.
 eapply Radd_lt_compat_l; eauto.
 eapply Radd_lt_compat_r; eauto.
Qed.

Lemma Radd_le_compat_l : forall x y1 y2 : R, y1 <= y2 -> x + y1 <= x + y2.
Proof.
  intros x y1 y2 H. destruct H.
   left. apply Radd_lt_compat_l. now assumption.
   
   right. apply Radd_eq_compat_l. assumption.
Qed.

Lemma Radd_le_compat_r : forall x y1 y2 : R, y1 <= y2 -> y1 + x <= y2 + x.
Proof.
  intros x y1 y2 H. destruct H.
   left. apply Radd_lt_compat_r. now assumption.
   
   right. apply Radd_eq_compat_r. assumption.
Qed.

Lemma Radd_lt_le_compat : forall x1 x2 y1 y2 : R, x1 < x2 -> y1 <= y2 -> x1 + y1 < x2 + y2.
Proof.
  intros x1 x2 y1 y2 H1 H2. apply Rlt_le_trans with (x2 + y1).
   apply Radd_lt_compat_r. now apply H1.
   
   apply Radd_le_compat_l. apply H2.
Qed.

Lemma Radd_le_lt_compat : forall x1 x2 y1 y2 : R, x1 <= x2 -> y1 < y2 -> x1 + y1 < x2 + y2.
Proof.
  intros x1 x2 y1 y2 H1 H2. apply Rle_lt_trans with (x2 + y1).
   apply Radd_le_compat_r. now apply H1.
   
   apply Radd_lt_compat_l. apply H2.
Qed.

Lemma Radd_le_compat : forall x1 x2 y1 y2 : R, x1 <= x2 -> y1 <= y2 -> x1 + y1 <= x2 + y2.
Proof.
  intros x1 x2 y1 y2 H1 H2. apply Rle_trans with (x1 + y2).
   apply Radd_le_compat_l. now apply H2.
   
   apply Radd_le_compat_r. apply H1.
Qed.

Lemma Rlt_0_2 : R0 < R1 + R1.
Proof.
apply Req_lt_compat_l with (R0 + R0); try apply Radd_0_l.
apply Rlt_trans with (R0 + R1).
 eapply Radd_lt_compat_l; apply Rlt_0_1.
 eapply Radd_lt_compat_r; apply Rlt_0_1.
Qed.

Lemma Radd_eq_cancel_r : forall x x' y, x + y == x' + y -> x == x'.
Proof.
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

Lemma Rmul_1_r : forall x, x * R1 == x.
Proof.
intros; rewrite Rmul_comm; apply Rmul_1_l.
Qed.

Lemma Rinv_r : forall x (pr : x ## R0), x * Rinv x pr == R1.
Proof.
intros x pr; rewrite Rmul_comm; apply Rinv_l.
Qed.

Lemma Rmul_eq_cancel_r : forall x x' y, y ## R0 -> x * y == x' * y -> x == x'.
Proof.
intros x x' y Hy Hxy.
rewrite <- (Rmul_1_r x), <- (Rmul_1_r x'), <- (Rinv_r y Hy).
repeat rewrite <- Rmul_assoc; rewrite <- Hxy.
apply Rmul_eq_compat_l; reflexivity.
Qed.

Instance Proper_Req_inv : Proper
  (fun f g : forall x, x ## R0 -> R => forall x x' H H', x == x' -> f x H == f x' H') Rinv.
Proof.
intros x x' Hx Hx' Heq.
apply (Rmul_eq_cancel_r _ _ x Hx).
rewrite Heq at 3.
do 2 rewrite Rmul_comm, Rinv_r; reflexivity.
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

Lemma Req_lt_compat : forall x y x' y', x == x' -> y == y' -> x < y -> x' < y'.
Proof.
intros.
eapply Req_lt_compat_l; eauto.
eapply Req_lt_compat_r; eauto.
Qed.

Lemma Req_le_compat : forall x y x' y', x == x' -> y == y' -> x <= y -> x' <= y'.
Proof.
  intros x y x' y' H1 H2 H3. destruct H3.
   left. now apply Req_lt_compat with x y; assumption.
   
   right. apply Req_trans with x.
    symmetry. now apply H1.
    
    apply Req_trans with y.
     now assumption.
     
     assumption.
Qed.

Lemma Radd_lt_cancel_l : forall x1 x2 y : R, y + x1 < y + x2 -> x1 < x2.
Proof.
intros x1 x2 y Hx.
cut (- y + (y + x1) < - y + (y + x2)).
  apply Req_lt_compat; try (ring_simplify; reflexivity).
  apply Radd_lt_compat_l, Hx.
Qed.
 
Lemma Radd_le_cancel_l : forall x1 x2 y : R, y + x1 <= y + x2 -> x1 <= x2.
Proof.
  intros x1 x2 y Hx. destruct Hx.
   left. apply Radd_lt_cancel_l with y. now assumption.
   
   right. assert (- y + ( y + x1) == - y + (y + x2)).
    apply Radd_eq_compat_l. now assumption.
    
    do 2 rewrite <- Radd_assoc in H. ring_simplify in H. apply H.
Qed.

Lemma Rlt_opp_1_0 : - R1 < R0.
Proof.
eapply Req_lt_compat_l; [ apply Radd_0_l | ].
eapply Req_lt_compat_r; [ apply Radd_opp_r | ].
apply Radd_lt_compat_r.
apply Rlt_0_1.
Qed.

Lemma Radd_lt_cancel_r : forall x1 x2 y : R, x1 + y < x2 + y -> x1 < x2.
Proof.
intros x1 x2 y H.
apply (Radd_lt_compat_l (- y)) in H.
eapply (Req_lt_compat_l _ x1) in H; [ | ring ].
eapply (Req_lt_compat_r _ x2) in H; [ auto | ring ].
Qed.

Lemma Radd_eq_cancel_l : forall x y1 y2, (x + y1 == x + y2) -> (y1 == y2).
Proof.
  intros x y1 y2 H1. apply (Radd_eq_compat_l (-x)) in H1. ring_simplify in H1. apply H1.
Qed.

Lemma Radd_le_cancel_r : forall x1 x2 y : R, x1 + y <= x2 + y -> x1 <= x2.
Proof.
  intros x1 x2 y H. destruct H.
   left. apply Radd_lt_cancel_r with y. now assumption.
   
   right. apply (Radd_eq_compat_r _ _ (-y)) in r. ring_simplify in r. apply r.
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

Lemma Rmul_le_cancel_l : forall x y1 y2 : R, R0 < x -> x * y1 <= x * y2 -> y1 <= y2.
Proof.
  intros x y1 y2 H1 H2. destruct H2.
   left. now apply Rmul_lt_cancel_l with x; assumption.
   
   right. assert (H0: x ## R0).
    right. now assumption.
    
    apply (Rmul_eq_compat_l (Rinv x H0)) in r. do 2 rewrite <- Rmul_assoc in r. rewrite Rinv_l in r.
    ring_simplify in r. apply r.
Qed.

Lemma Rmul_lt_cancel_r : forall x1 x2 y : R, R0 < y -> x1 * y < x2 * y -> x1 < x2.
Proof.
intros x1 x2 y Hpos H.
eapply Req_lt_compat_l in H; [|apply Rmul_comm].
eapply Req_lt_compat_r in H; [|apply Rmul_comm].
apply Rmul_lt_cancel_l in H; auto.
Qed.

Lemma Rmul_le_cancel_r : forall x1 x2 y : R, R0 < y -> x1 * y <= x2 * y -> x1 <= x2.
Proof.
  intros x1 x2 y H1 H2. destruct H2.
   left. now apply Rmul_lt_cancel_r with y; assumption.
   
   right. assert (H0: y ## R0).
    right. now assumption.
    
    apply (Rmul_eq_compat_r _ _ (Rinv y H0)) in r. do 2 rewrite Rmul_assoc in r. rewrite Rinv_r in r.
    ring_simplify in r. apply r.
Qed.

Lemma Rmul_lt_compat_r : forall x y1 y2 : R, R0 < x -> y1 < y2 -> y1 * x < y2 * x.
Proof.
 intros x; intros.
 apply (Req_lt_compat_l _ _ _ (Rmul_comm x _)).
 apply (Req_lt_compat_r _ _ _ (Rmul_comm x _)).
 apply Rmul_lt_compat_l; auto.
Qed.

Lemma Rmul_le_compat_r : forall x y1 y2 : R, R0 <= x -> y1 <= y2 -> y1 * x <= y2 * x.
Proof.
  intros x y1 y2 H1 H2. destruct H1.
   destruct H2.
    left. now apply Rmul_lt_compat_r; assumption.
    
    right. rewrite r0. now ring.
  
  right. rewrite <- r. ring.
Qed.

Lemma Ropp_involutive : forall x, - - x == x.
Proof.
  intros x. eapply Radd_eq_cancel_r with (- x). rewrite Radd_opp_r. rewrite Radd_comm, Radd_opp_r.
  reflexivity.
Qed.

Lemma Ropp_lt_contravar : forall x y, x < y -> - y < - x.
Proof.
 intros x y Lxy.
 apply (Radd_lt_cancel_r _ _ (x + y)).
 eapply Req_lt_compat_l; [ | eapply Req_lt_compat_r; [ | apply Lxy ] ].
   (* ; ring : Error: Tactic failure: anomaly: Find_at (level 97). *)
   ring.
   ring.
Qed.

Lemma Ropp_le_contravar : forall x y, x <= y -> - y <= - x.
Proof.
  intros x y H1. destruct H1.
   left. apply Ropp_lt_contravar. now apply r.
   
   right. rewrite r. ring.
Qed.

Lemma Ropp_lt_contravar_reciprocal : forall x y, - y < - x -> x < y.
Proof.
 intros x y Lxy.
 apply (Req_lt_compat (- - x) (- - y)); try (ring_simplify; reflexivity).
    (* Again, we could use ring but we get a strange error *)
 apply Ropp_lt_contravar; auto.
Qed.

Lemma Ropp_le_contravar_reciprocal : forall x y, - y <= - x -> x <= y.
Proof.
  intros x y H. destruct H.
   left. apply Ropp_lt_contravar_reciprocal. now assumption.
   
   right. rewrite <- Ropp_involutive. rewrite <- (Ropp_involutive y). rewrite r. reflexivity.
Qed.

Lemma Rlt_opp_0 : forall x, R0 < x -> - x < R0.
Proof.
 intros x xpos.
 eapply Req_lt_compat_r; [ apply Ropp_0 | ].
 apply Ropp_lt_contravar; auto.
Qed.

Lemma Rle_opp_0 : forall x, R0 <= x -> - x <= R0.
Proof.
  intros x H. destruct H.
   left. apply Rlt_opp_0. now assumption.
   
   right. rewrite <- r. ring.
Qed.

Lemma Rlt_0_opp : forall x, x < R0 -> R0 < - x.
Proof.
 intros x xpos.
 eapply Req_lt_compat_l; [ apply Ropp_0 | ].
 apply Ropp_lt_contravar; auto.  
Qed.

Lemma Rle_0_opp : forall x, x <= R0 -> R0 <= - x.
Proof.
  intros x H. destruct H.
   left. apply Rlt_0_opp. now assumption.
   
   right. rewrite r. ring.
Qed.

Lemma Rmul_lt_compat_neg_l : forall x y1 y2 : R, x < R0 -> y1 < y2 -> x * y2 < x * y1.
Proof.
 intros x; intros.
 apply Ropp_lt_contravar_reciprocal.
 apply (Req_lt_compat (- x * y1) (- x * y2)); try (ring_simplify; reflexivity).
 apply Rmul_lt_compat_l; try apply Rlt_0_opp; auto.
Qed.

Lemma Rmul_le_compat_neg_l : forall x y1 y2 : R, x <= R0 -> y1 <= y2 -> x * y2 <= x * y1.
Proof.
  intros x y1 y2 H1 H2. destruct H1.
   destruct H2.
    left. now apply Rmul_lt_compat_neg_l; assumption.
    
    right. rewrite r0. now reflexivity.
  
  right. rewrite r. ring.
Qed.

Lemma Rmul_lt_compat_neg_r : forall x y1 y2 : R, x < R0 -> y1 < y2 -> y2 * x < y1 * x.
Proof.
 intros x; intros.
 apply (Req_lt_compat_l _ _ _ (Rmul_comm x _)).
 apply (Req_lt_compat_r _ _ _ (Rmul_comm x _)).
 apply Rmul_lt_compat_neg_l; auto.
Qed.

Lemma Rmul_le_compat_neg_r : forall x y1 y2 : R, x <= R0 -> y1 <= y2 -> y2 * x <= y1 * x.
Proof.
  intros x y1 y2 H1 H2. destruct H1.
   destruct H2.
    left. now apply Rmul_lt_compat_neg_r; assumption.
    
    right. rewrite r0. now reflexivity.
  
  right. rewrite r. ring.
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

Lemma Rdiv_mul_r : forall a b (bpos : b ## R0), Rdiv a b bpos * b == a.
Proof.
intros a b bpos.
unfold Rdiv.
rewrite Rmul_assoc, Rinv_l, Rmul_1_r; reflexivity.
Qed.

Lemma Rdiv_mul_l : forall a b (bpos : b ## R0), b * Rdiv a b bpos == a.
Proof.
intros; rewrite Rmul_comm; apply Rdiv_mul_r.
Qed.

Lemma Rinv_pos_compat : forall x (p : R0 < x) (p' : x ## R0), R0 < Rinv x p'.
Proof.
intros x xp xd.
apply Rmul_lt_cancel_l with x.
 auto.
 apply (Req_lt_compat R0 R1).
  ring_simplify; reflexivity.
  rewrite Rinv_r; reflexivity.
  apply Rlt_0_1.
Qed.

Lemma Req_le_compat_l : forall x1 x2 y : R, x1 == x2 -> x1 <= y -> x2 <= y.
Proof.
  intros x1 x2 y H1 H2. destruct H2.
   left. apply Rle_lt_trans with x1.
    right. symmetry. now apply H1.
    
    now assumption.
  
  right. rewrite <- H1. assumption.
Qed.

Lemma Req_le_compat_r : forall x1 x2 y : R, x1 == x2 -> y <= x1 -> y <= x2.
Proof.
  intros x1 x2 y H1 H2. destruct H2.
   left. apply Rlt_le_trans with x1.
    now assumption.
    
    right. now apply H1.
  
  right. rewrite <- H1. assumption.
Qed.

Lemma Rmul_le_compat_l : forall x y1 y2 : R, R0 <= x -> y1 <= y2 -> x * y1 <= x * y2.
Proof.
  intros x y1 y2 H1 H2. destruct H1.
   destruct H2.
    left. now apply Rmul_lt_compat_l; assumption.
    
    right. rewrite r0. now reflexivity.
  
  right. rewrite <- r. ring.
Qed.

Lemma Radd_pos_compat : forall x y, R0 < x -> R0 < y -> R0 < x + y.
Proof.
  intros. apply Rle_lt_trans with (R0 + R0).
   right. now ring.
   
   apply Rlt_trans with (x + R0).
    apply Radd_lt_compat_r. now assumption.
    
    apply Radd_lt_compat_l. assumption.
Qed.

Lemma Rpos_lt : forall x y, R0 < y - x -> x < y.
Proof.
  intros x y pxy.
  apply Radd_lt_cancel_r with (- x).
  eapply Req_lt_compat_l; [ | eauto ]; symmetry; apply Radd_opp_r.
Qed.

Lemma Rlt_pos : forall x y, x < y -> R0 < y - x.
Proof.
  intros x y pxy.
  apply Radd_lt_cancel_r with x.
  eapply Req_lt_compat with x y; auto; symmetry.
    apply Radd_0_l.
    ring_simplify; reflexivity.
Qed.

End Rconvenient.
