Require Import Raxiom Rconvenient IZR Repsilon Rapprox.
Require Import Arith.

Module Rorder (Import T : CReals).
  Module Rconvenient := Rconvenient T. Import Rconvenient.
  Module IZR := IZR T. Import IZR.
  Module Repsilon := Repsilon T. Import Repsilon.
  Module Rapprox := Rapprox T. Import Rapprox.
  
  Definition Rlt_Prop : R -> R -> Prop := fun x y => inhabited (Rlt x y).
  
  Lemma Rlt_prop : forall x y, Rlt x y -> Rlt_Prop x y.
  Proof.
    intros; constructor; assumption.
  Qed.
  
  Section weak_constructive_eps.
    Inductive exT {A : Set} (P : A -> Type) : Prop :=
      exT_intro : forall a, P a -> exT P.
    
    Variable P : nat -> Type.
    Hypothesis P_weak_decidable : forall n : nat, P (S n) + (P n -> False).
    
    Let R (x y : nat) : Prop := x = S (S y) /\ (P y -> False).
    
    Lemma P_Acc : forall n, P n -> Acc R n.
    Proof.
      intros; constructor.
      intros [] []; tauto.
    Qed.
    
    Lemma P_later_Acc : forall n x, P (n + x) -> Acc R x.
    Proof.
      intros n; induction n.
        apply P_Acc.
        
        intros x Pnx; constructor; intros y (exy, npx).
        apply IHn; subst.
        do 2 rewrite <- plus_n_Sm.
        
        destruct (P_weak_decidable (S (n + x))); [ auto | ].
        tauto.
    Qed.
    
    Corollary exT_Acc_0 : exT P -> Acc R 0.
    Proof.
      intros (n, Hn).
      apply (P_later_Acc n).
      rewrite <- plus_n_O; assumption.
    Qed.
    
    Lemma Acc_0_sigT : Acc R 0 -> sigT P.
    Proof.
      intros HO.
      pattern 0.
      apply (@Fix_F _ R); auto.
      clear HO; intros x IHx.
      destruct (P_weak_decidable x) as [ px | npx ].
        exists (S x); auto.
        assert (Rx : R (S (S x)) x); unfold R; eauto.
    Qed.
    
    Lemma exT_sigT : exT P -> sigT P.
    Proof.
      intros exP; apply Acc_0_sigT, exT_Acc_0; auto.
    Qed.
  
  End weak_constructive_eps.
  
  Section DiscretePos.
    Variable x : R.
    Hypotheses xpos : Rlt_Prop R0 x.
    Definition pos_nat : nat -> Type := fun n => R1 < x * po n.
    
    Lemma pos_nat_weak_decidable : forall n, (pos_nat (S n)) + (pos_nat n -> False).
    Proof.
      intros n.
      unfold pos_nat.
      pose (xn := x * po (S (S n))); fold xn.
      pose proof Rup_spec xn as Hzn.
      set (zn := Rup xn); fold zn in Hzn.
      destruct Hzn as (uxn, lxn).
      destruct (Z_dec zn 3%Z) as [ [ lzn | gzn ] | ezn ].
        right.
        apply Rlt_asym.
        apply Rmul_lt_cancel_r with ((R1 + R1) + (R1 + R1)).
          do 2 apply Radd_pos_compat; apply Rlt_0_1.
          
          apply (Req_lt_compat xn (IZR 4)); simpl.
            unfold xn, po; simpl; ring.
            ring.
            apply Rlt_trans with (R1 + IZR zn).
              apply (Radd_lt_compat_r (IZR zn)) in uxn. 
              apply Rle_lt_trans with (xn - IZR zn + IZR zn).
              right. ring. apply uxn.
              
              change (IZR 1 + IZR zn < IZR 4).
              eapply Req_lt_compat_l; [ apply IZR_add | ].
              apply IZR_lt; omega.
        
        left.
        apply Rmul_lt_cancel_r with (R1 + R1).
          apply Radd_pos_compat; apply Rlt_0_1.
          
          apply (Req_lt_compat (IZR 2) xn); simpl.
            apply Rmul_comm.
            unfold xn, po; simpl; ring.
            apply Rlt_trans with (IZR zn - R1).
              change (IZR 2 < IZR zn - IZR 1).
              eapply Req_lt_compat_r; [ apply IZR_sub | ].
              apply IZR_lt; omega.
              
              apply (Radd_lt_compat_l (IZR zn)) in lxn. 
              apply Rlt_le_trans with (IZR zn + (xn - IZR zn)). 
              apply lxn. right. ring.
        
        (* both right and left? *)
        subst.
        rewrite ezn in *.
        left.
        apply Rmul_lt_cancel_r with (R1 + R1).
          apply Radd_pos_compat; apply Rlt_0_1.
          
          apply (Req_lt_compat (IZR 2) xn); simpl.
            apply Rmul_comm.
            unfold xn, po; simpl; ring.
            apply Radd_lt_cancel_r with (- IZR 3).
            eapply Req_lt_compat; [ | | apply lxn ]; simpl.
              ring.
              
              ring_simplify.
              apply Radd_eq_compat_l.
               unfold IZR, IPR. ring.
    Qed.
    
    Lemma sigT_pos_nat : sigT pos_nat.
    Proof.
     
      apply exT_sigT.
        apply pos_nat_weak_decidable.
        
        destruct xpos as [ xposT ].
        destruct (Rpos_witness _ xposT) as (n, Hn).
        exists n; specialize (Hn n (le_n _)).
        apply (Rmul_lt_compat_r (po n) _ _ (Rpos_IPR _)) in Hn.
        unfold pos_nat.
        eapply Req_lt_compat; [ | | apply Hn ]; simpl.
          apply Rinv_l.
          reflexivity.
    Qed.
    
    Lemma Rlt_0_x : Rlt R0 x.
    Proof.
      destruct sigT_pos_nat as (n, Hn); unfold pos_nat in *.
      apply Rmul_lt_cancel_r with (po n).
        apply Rpos_IPR.
        
        apply Rlt_trans with R1.
          eapply Req_lt_compat_l; [ | apply Rlt_0_1 ]; symmetry; apply Rmul_0_l.
          auto.
    Qed.
    
  End DiscretePos.
  
End Rorder.
