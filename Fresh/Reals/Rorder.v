Require Import Raxiom Rconvenient IZR Repsilon.
Require Import Arith.

Module Rorder (Import T : CReals).
  Module Rconvenient := Rconvenient T. Import Rconvenient.
  Module IZR := IZR T. Import IZR.
  Module Repsilon := Repsilon T. Import Repsilon.
  
  Inductive Rlt_Prop : R -> R -> Prop :=
    Rlt_Prop_inhabits : forall x y, Rlt x y -> Rlt_Prop x y.
  
  Lemma Rlt_prop : forall x y, Rlt x y -> Rlt_Prop x y.
  Proof.
    intros; constructor; assumption.
  Qed.
  
  Lemma Rlt_algebraic : forall x y, Rlt_Prop x y -> Rlt x y.
  Admitted.
  
  Section weak_constructive_eps.
    Variable P : nat -> Prop.
    Hypothesis P_upwards_closed : forall n : nat, P n -> P (S n).
    Hypothesis P_weak_decidable : forall n : nat, {P (S n)} + {~ P n}.
    
    Let R (x y : nat) : Prop := x = S (S y) /\ ~ P y.
    
    Notation Local acc x := (Acc R x).
    
    Lemma P_acc : forall n, P n -> acc n.
    Proof.
      intros; constructor.
      intros [] []; tauto.
    Qed.
    
    Lemma P_later_acc : forall n x, P (n + x) -> acc x.
    Proof.
      intros n; induction n.
        apply P_acc.
        
        intros x Pnx; constructor; intros y (exy, npx).
        apply IHn; subst.
        do 2 rewrite <- plus_n_Sm.
        apply P_upwards_closed.
        assumption.
    Qed.
    
    Corollary ex_acc_0 : ex P -> acc 0.
    Proof.
      intros (n, Hn).
      apply (P_later_acc n).
      rewrite <- plus_n_O; assumption.
    Qed.
    
    Lemma acc_0_sig : acc 0 -> sig P.
    Proof.
      intros HO.
      pattern 0.
      apply (@Fix_F _ R); auto.
      clear HO; intros x IHx.
      destruct (P_weak_decidable x) as [ px | npx ].
        exists (S x); auto.
        assert (Rx : R (S (S x)) x); unfold R; eauto.
    Qed.
    
    Lemma ex_sig : ex P -> sig P.
    Proof.
      intros exP; apply acc_0_sig, ex_acc_0; auto.
    Qed.
  
  End weak_constructive_eps.
  
End Rorder.
