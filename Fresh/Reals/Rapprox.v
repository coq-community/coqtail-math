Require Import Raxiom Rconvenient Repsilon Rseq IZR.
Require Import ZArith.

Module Rapprox (Import T : CReals).
  Module Rconvenient := (Rconvenient T). Import Rconvenient.
  Module Repsilon := (Repsilon T). Import Repsilon.
  Module Rsequence := (Rsequence T). Import Rsequence.
  Module IZR := IZR. Import IZR.
  Open Scope R_scope.
  
  Definition po n := IPR (Ppow2 n).
  Definition pop n : (po n ## R0) := Rdiscr_IPR_0 _.
  Definition Zapprox x n := Rup (x * po n).
  
  Definition Rseq_approx : R -> Rseq := fun x n => ((IZR (Zapprox x n)) / po n) (pop n).
  
  
  Lemma Ppow2_double : forall x, (Zpos (Ppow2 (S x)) = 2 * Zpos (Ppow2 x))%Z.
  Proof.
    reflexivity.
  Qed.
  
  Lemma Zle_S_Ppow2 : forall p, (Zpos (p + 1) <= Zpos (Ppow2 (Zabs_nat (Zpos p))))%Z.
  Proof.
    intros.
    rewrite Zpos_plus_distr.
    replace (Zpos p + 1)%Z with ((Z_of_nat (nat_of_P p)) + 1)%Z.
      simpl.
      induction (nat_of_P p).
        simpl. intuition.
        rewrite Ppow2_double. apply Zle_trans with (2* (Z_of_nat n + 1))%Z; zify; omega.
        rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P. reflexivity.
  Qed.
  
  Lemma Zpos_Ppow2_increasing : forall n m, (n <= m)%nat -> (Zpos (Ppow2 n) <= Zpos (Ppow2 m))%Z.
  Proof.
    intros n m Hnm.
    induction Hnm. omega.
    eapply Zle_trans; [apply IHHnm | ].
    simpl. zify; omega.
  Qed.

  Lemma extract_eps : forall e, R0 < e -> sigT (fun N => forall n, le N n -> Rinv (po n) (pop n) < e).
  Proof.
    intros e epos.
    assert (de : e ## R0) by (right; auto).
    pose (e' := Rinv e de).
    pose (N := Zabs_nat (Rup e')).
    exists N; intros n Hn.
    
    apply Rmul_lt_cancel_l with (po n).
      apply Rpos_IPR.
      
      eapply Req_lt_compat_l; [ symmetry; apply Rinv_r | ].
      apply Rmul_lt_cancel_r with e'.
        apply Rinv_pos_compat; auto.
        
        apply (Req_lt_compat e' (po n)).
          ring_simplify; reflexivity.
          
          unfold e'; rewrite Rmul_assoc, Rinv_r.
          ring_simplify; reflexivity.
          
          destruct (Rup_spec e') as (le', _).
          apply Rlt_le_trans with (IZR (Rup e') + R1).
            apply Radd_lt_cancel_r with (- IZR (Rup e')).
            apply Req_lt_compat_r with R1.
              ring.
              apply le'.
            
            apply Rle_trans with (po N).
              change (IZR (Rup e') + IZR 1 <= po N).
              eapply Req_le_compat_l; [ apply IZR_add | ].
              change (IZR (Rup e' + 1) <= IZR (Zpos (Ppow2 N))); apply IZR_le.
              unfold N; pose (r := Rup e'); fold r.
              clearbody r; clear.
              destruct r as [ | p | p ].
                simpl; now auto with *.
                
                apply Zle_S_Ppow2.
                
                apply Zle_trans with 1%Z; zify; omega.
              
              change (IZR (Zpos (Ppow2 N)) <= IZR (Zpos (Ppow2 n))); apply IZR_le.
              clearbody N e'; clear -Hn.
              apply Zpos_Ppow2_increasing. apply Hn.
  Qed.
  
  Lemma Rseq_cv_approx : forall x, Rseq_cv (Rseq_approx x) x.
  Proof.
    intros x e epos.
    destruct (extract_eps e epos) as (N, HN).
    exists N; intros n Hn.
    unfold Rdist, Rseq_approx, Zapprox.
    destruct (Rup_spec (x * po n)) as (re, er).
    split.
      apply Rmul_lt_cancel_r with (po n).
        apply Rpos_IPR.
        
        eapply Req_lt_compat_l; [ symmetry; apply Rmul_add_distr_r | ].
        eapply Req_lt_compat_l; [ eapply Radd_eq_compat_r; symmetry; apply Rdiv_mul_r | ].
        apply Rlt_trans with R1.
          apply Ropp_lt_contravar_reciprocal.
          eapply Req_lt_compat_r; [ rewrite Ropp_add | apply er ].
          ring.
          
          apply Rmul_lt_cancel_r with (Rinv (po n) (pop n)).
            apply Rinv_0_lt_compat, Rpos_IPR.
            apply (Req_lt_compat (Rinv (po n) (pop n)) e).
              ring_simplify; reflexivity.
              rewrite Rmul_assoc, (Rmul_comm e), Rinv_r, Rmul_1_l; reflexivity.
              auto.
      
      apply Rmul_lt_cancel_r with (po n).
        apply Rpos_IPR.
        apply Rlt_trans with (- R1).
          apply Rmul_lt_cancel_r with (Rinv (po n) (pop n)).
            apply Rinv_pos_compat, Rpos_IPR.
            apply (Req_lt_compat (- e) (- Rinv (po n) (pop n))).
              rewrite Rmul_assoc, Rinv_r, Rmul_1_r; reflexivity.
              ring_simplify; reflexivity.
              apply Ropp_lt_contravar; auto.
          
          eapply Req_lt_compat_r; [ symmetry; apply Rmul_add_distr_r | ].
          apply Ropp_lt_contravar_reciprocal.
          eapply Req_lt_compat_r; [ symmetry; apply Ropp_involutive | ].
          apply (Req_lt_compat (x * po n - IZR (Rup (x * po n))) R1).
            rewrite Rdiv_mul_r.
            ring_simplify; reflexivity.
            
            reflexivity.
            
            auto.
  Qed.
  
End Rapprox.