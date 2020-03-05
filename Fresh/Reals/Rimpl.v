Require Reals.
Require Raxiom.
Require Import ZArith.

(* Realisation of Raxioms thanks to the standard library of Coq *)

Module RD := Coq.Reals.Rdefinitions.
Module RA := Coq.Reals.Raxioms.
Module RI := Coq.Reals.RIneq.

Module Rimpl <: Raxiom.CReals.
  
  Definition R := RD.R.
  Definition R0 := RD.R0.
  Definition R1 := RD.R1.
  Definition Radd := RD.Rplus.
  Definition Rmul := RD.Rmult.
  Definition Ropp := RD.Ropp.
  Definition Rsub := RD.Rminus.
  Definition Rlt := RD.Rlt.
  
  Definition Rgt (r1 r2 : R) := Rlt r2 r1.
  Definition Rdiscr (r1 r2 : R) := sum (Rlt r1 r2) (Rlt r2 r1).
  Definition Req (r1 r2 : R) := Rdiscr r1 r2 -> False.
  Definition Rle (r1 r2 : R) := sumor (Rlt r1 r2) (Req r1 r2).
  Definition Rge (r1 r2 : R) := Rle r2 r1.
  
  Definition Rdiv x y (_ : Rdiscr y R0) := RD.Rdiv x y.
  
  Definition Rinv (x : R) (_ : Rdiscr x R0) := RD.Rinv x.
  
  Definition Rlt_trans := Coq.Reals.Raxioms.Rlt_trans.
  Definition Rlt_asym : forall r1 r2 : R, Rlt r1 r2 -> Rlt r2 r1 -> False.
  Proof.
    intros a b Hab Hba.
    apply (RIneq.Rlt_not_le a b Hba).
    apply (RIneq.Rlt_le _ _ Hab).
  Defined.
  
  Lemma Req_refl : forall x, Req x x.
  Proof.
    intros x [H|H]; eapply (Rlt_asym _ _); apply H.
  Qed. 
  
  Lemma eq_Req : forall {a b}, eq a b -> Req a b.
  Proof.
    intros a b Hab; subst; apply Req_refl.
  Qed.
  
  Lemma Req_eq : forall {a b}, Req a b -> eq a b.
  Proof.
    intros a b Hab.
    apply RIneq.Rle_antisym; apply RIneq.Rnot_lt_le;
      intro; destruct Hab; compute; intuition.
  Qed.
  
  Lemma Rdiscr_neq : forall {a b}, Rdiscr a b -> a <> b.
  Proof.
    intros a b [Lab|Lba]; apply RI.Rlt_dichotomy_converse; eauto.
  Qed.
  
  Lemma neq_Rdiscr : forall {a b}, a <> b -> Rdiscr a b.
  Proof.
    intros a b Nab.
    destruct (RA.total_order_T a b) as [[|]|].
     left; assumption.
     elimtype False; auto.
     right; auto.
  Qed.
  
  Ltac fold_Req := repeat (match goal with H : Req ?a ?b |- _ => apply Req_eq in H end).
  
  (** Congruences **)
  Definition Req_lt_compat_l : forall x1 x2 y : R, Req x1 x2 -> Rlt x1 y -> Rlt x2 y.
  Proof.
    intros; fold_Req.
    fold_Req.
    subst; auto.
  Qed.
  
  Definition Req_lt_compat_r : forall x1 x2 y : R, Req x1 x2 -> Rlt y x1 -> Rlt y x2.
  Proof.
    intros; fold_Req.
    subst; auto.
  Qed.
  
  Definition Radd_lt_compat_l := RA.Rplus_lt_compat_l.
  
  Definition Radd_eq_compat_l : forall x y1 y2, Req y1 y2 -> Req (Radd x y1) (Radd x y2).
  Proof.
    intros; fold_Req.
    subst.
    intros [H|H]; eapply (Rlt_asym _ _); apply H.
  Qed.
  
  Definition Rmul_lt_compat_l := RA.Rmult_lt_compat_l.
  
  Definition Rmul_eq_compat_l : forall x y1 y2, Req y1 y2 -> Req (Rmul x y1) (Rmul x y2).
  Proof.
    intros; fold_Req.
    subst.
    intros [H|H]; eapply (Rlt_asym _ _); apply H.
  Qed.
  
  Definition Rinv_0_lt_compat : forall (x : R) (pr : Rlt R0 x) (pr' : Rdiscr x R0), Rlt R0 (Rinv x pr').
  Proof.
    unfold Rinv, Rlt.
    intros.
    apply RI.Rinv_0_lt_compat.
    auto.
  Qed.
    
  (** Ring operations **)
  Definition Radd_comm : forall a b, Req (Radd a b) (Radd b a).
  Proof.
    intros; apply eq_Req, RA.Rplus_comm.
  Qed.
  
  Definition Radd_assoc : forall x y z, Req (Radd (Radd x y) z) (Radd x (Radd y z)).
  Proof.
    intros; apply eq_Req, RA.Rplus_assoc.
  Qed.
  
  Definition Radd_opp_r : forall x, Req (Radd x (Ropp x)) R0.
  Proof.
    intros; apply eq_Req, RA.Rplus_opp_r.
  Qed.
  
  Definition Radd_0_l : forall x, Req (Radd R0 x) x.
  Proof.
    intros; apply eq_Req, RA.Rplus_0_l.
  Qed.
  
  Definition Rmul_add_distr_l a b c : Req (Rmul a (Radd b c)) (Radd (Rmul a b) (Rmul a c)).
  Proof.
    intros; apply eq_Req, RA.Rmult_plus_distr_l.
  Qed.
  
  Definition Rmul_comm : forall a b, Req (Rmul a b) (Rmul b a).
  Proof.
    intros; apply eq_Req, RA.Rmult_comm.
  Qed.
  
  Definition Rmul_assoc : forall x y z, Req (Rmul (Rmul x y) z) (Rmul x (Rmul y z)).
  Proof.
    intros; apply eq_Req, RA.Rmult_assoc.
  Qed.
  
  Definition Rmul_1_l : forall x, Req (Rmul R1 x) x.
  Proof.
    intros; apply eq_Req, RA.Rmult_1_l.
  Qed.
  
  (** Constructive field operation **)
  Definition Rinv_l : forall (x : R) (pr : Rdiscr x R0), Req (Rmul (Rinv x pr) x) R1.
  Proof.
    intros.
    apply eq_Req.
    apply RA.Rinv_l.
    apply Rdiscr_neq.
    apply pr.
  Qed.
  
  (** Ordered Field **)
  Definition Rlt_0_1 : Rlt R0 R1.
  Proof.
    apply RI.Rlt_0_1.
  Qed.
  
  (** * Archimedean **)
  
  (** Injection from Z to R **)
  Fixpoint IPR (p : positive) : R :=
    match p with
      | xI p => Radd (Rmul (Radd R1 R1) (IPR p)) R1
      | xO p => Rmul (Radd R1 R1) (IPR p)
      | xH => R1
    end.
  
  Definition IZR (z : Z) : R :=
    match z with
      | Z0 => R0
      | Zpos p => IPR p
      | Zneg p => Ropp (IPR p)
    end.
  
  Definition Rdist x y d : Type := prod (Rlt (Rsub x y) d) (Rlt (Ropp d) (Rsub x y)).
  
  (** Getting back to Z **)
  
  Definition Rup : R -> Z.
  Proof.
    exact Coq.Reals.R_Ifp.Int_part.
  Defined.
  
  Lemma IPR_2_same : forall p, RD.IPR_2 p = Rmul (Radd R1 R1) (IPR p).
  Proof.
    induction 0; simpl.
      rewrite IHp, (RA.Rplus_comm RD.R1 (RD.Rmult _ _)); auto.
      rewrite IHp; auto.
      rewrite <-RI.Rmult_1_r at 1; auto.
  Qed.

  Lemma IPR_same : forall p, RD.IPR p = IPR p.
  Proof.
    destruct 0; auto.
      change (RD.Rplus RD.R1 (RD.IPR_2 p) = IPR p~1). rewrite IPR_2_same, RA.Rplus_comm. auto.
      change (RD.IPR_2 p = IPR p~0). rewrite IPR_2_same. auto.
  Qed.

  Lemma IZR_same : forall z, RD.IZR z = IZR z.
  Proof.
    destruct z; auto.
      apply IPR_same.
      change (RD.Ropp (RD.IPR p) = Ropp (IPR p)). rewrite IPR_same. auto.
  Qed.

  Lemma Rup_spec : forall r : R, Rdist r (IZR (Rup r)) R1.
  Proof.
    intros r.
    destruct (Coq.Reals.R_Ifp.base_Int_part r) as (Ir, Ur).
    rewrite IZR_same in *.
    unfold Rup, Rdist, Rsub, R1, Rlt.
    remember (R_Ifp.Int_part r) as z.
    split; [clear Ir|clear Ur].
     apply RI.Ropp_lt_cancel, RI.Rgt_lt.
     refine (RI.Rlt_eq_compat _ _ _ _ _ Ur _).
      reflexivity.
      rewrite RI.Ropp_minus_distr; auto.
     apply RI.Rlt_le_trans with RD.R0.
      apply RI.Ropp_lt_gt_0_contravar, Rlt_0_1.
      eapply RI.Rle_trans.
       apply RI.Req_le.
       symmetry.
       apply (RA.Rplus_opp_r (IZR z)).
       
       apply (RI.Rplus_le_compat_r (RD.Ropp (IZR z)) _ _ Ir).
  Qed.
  
  (** * Completeness **)
  
  Definition Rseq_Cauchy (Un : nat -> R) : Type := forall eps, Rlt R0 eps ->
    {N : nat & forall p q, (N <= p)%nat -> (N <= q)%nat -> Rdist (Un p) (Un q) eps}.
  
  Definition Rseq_cv (Un : nat -> R) (l : R) : Type := forall eps, Rlt R0 eps ->
    {N : nat & forall n, (N <= n)%nat -> Rdist (Un n) l eps}.
  
  Lemma R_dist : forall a b x, RD.Rlt (Rfunctions.R_dist a b) x -> Rdist a b x.
  Proof.
  intros.
  unfold Rdist. unfold Rfunctions.R_dist in H. 
  destruct (RA.total_order_T (Rdefinitions.Rminus a b) R0) as [[H1 | H1] | H1]. 
  rewrite Rbasic_fun.Rabs_left in H; try assumption.
  split. unfold Rsub. 
  destruct (RA.total_order_T x R0) as [[H2 | H2] | H2]; intuition.
  apply RA.Rlt_trans with (Rdefinitions.Ropp (Rdefinitions.Rminus a b)).
  apply RA.Rlt_trans with R0. apply H1.
  intuition.
  apply H.
  rewrite H2. apply H1.
  apply RA.Rlt_trans with R0; intuition.
  rewrite <- RI.Ropp_involutive. apply RI.Ropp_lt_contravar. 
  assumption.
  unfold Rsub. rewrite H1 in *. unfold R0 in H.
  change RD.R0 with (RD.IZR Z0) in H. rewrite Rbasic_fun.Rabs_R0 in H.
  split. apply H. apply RI.Ropp_lt_gt_0_contravar. intuition.
  
  rewrite Rbasic_fun.Rabs_right in H; intuition.
  destruct (RA.total_order_T x R0) as [[H2 | H2] | H2]. 
  assert (RD.Rlt x x). apply RA.Rlt_trans with ((Rdefinitions.Rminus a b)).
  apply RA.Rlt_trans with R0; intuition.
  intuition.
  apply RI.Rlt_irrefl in H0. destruct H0.
  subst. unfold R0. unfold Ropp.
  change RD.R0 with (RD.IZR Z0). rewrite RI.Ropp_0. assumption.

  apply RA.Rlt_trans with R0. intuition.
  intuition.
  Qed.

  Lemma Rcomplete : forall Un, Rseq_Cauchy Un -> {l : R & Rseq_cv Un l}.
  Proof.
    intros u Hu.
    destruct (Coq.Reals.Rcomplete.R_complete u) as (l, Hl).
    intros eps Heps. specialize (Hu eps Heps).
    destruct Hu as (N, Hu). exists N.
    intros. specialize (Hu n m H H0). destruct Hu as (Hu1, Hu2).
    unfold Rfunctions.R_dist. unfold Rbasic_fun.Rabs.
    destruct (Rbasic_fun.Rcase_abs (Rdefinitions.Rminus (u n) (u m))).
    rewrite <- (RI.Ropp_involutive eps). apply RI.Ropp_gt_lt_contravar. 
    apply Hu2.
    apply Hu1.
     (* montrer que le critère ci-dessus implique celui de la stdlib (proof ci dessus) *)

(* TODO preuve = disjonction sur le total_order puis preuve directe ou preuve de False *)     
     exists l.
     intros eps Heps.
     assert (Heps2 : Rlt R0 (RD.Rdiv eps (Radd R1 R1) )).
     unfold Rlt. apply RI.Rmult_lt_0_compat. apply Heps.
     apply RI.Rinv_0_lt_compat. intuition.
     specialize (Hu (RD.Rdiv eps (Radd R1 R1)) Heps2).
     destruct Hu as (N, Hu).
     exists N. intros. specialize (Hl (RD.Rdiv eps (Radd R1 R1)) Heps2). 
     destruct (RA.total_order_T eps (Rbasic_fun.Rabs (Rsub (u n) l))) as [H3 | H3]. 
     assert (H4 : RD.Rle eps (Rbasic_fun.Rabs (Rsub (u n) l))).
     destruct H3. intuition.
     rewrite <- e. intuition.
     assert False. destruct Hl as (N0, Hl0).
     pose (n_spe := (Max.max N N0)).
     assert (n_spe_t : n_spe >= N0). apply Max.le_max_r.
     specialize (Hl0 n_spe n_spe_t).
     assert (Rlt eps eps).
     apply RI.Rle_lt_trans with (Rbasic_fun.Rabs (Rsub (u n) l)).
     apply H4.
     replace (Rsub (u n) l) with (Radd (Rsub (u n) (u n_spe)) (Rsub (u n_spe) l)).

     apply RI.Rle_lt_trans with (Radd (Rbasic_fun.Rabs (Rsub (u n) (u n_spe))) (Rbasic_fun.Rabs (Rsub (u n_spe) l))).
     apply Rbasic_fun.Rabs_triang.
     replace eps with (Radd (RD.Rdiv eps (Radd R1 R1)) (RD.Rdiv eps (Radd R1 R1))).
     unfold Radd. apply RI.Rplus_lt_compat.
     assert (n_spe_r : n_spe >= N). apply Max.le_max_l.
     specialize (Hu n n_spe H n_spe_r). unfold Rdist in Hu.
     destruct Hu as (Hu1, Hu2).
     unfold Rlt in Hu1, Hu2.
     unfold Rbasic_fun.Rabs. destruct (Rbasic_fun.Rcase_abs (Rsub (u n) (u n_spe))).
     rewrite <- RI.Ropp_involutive. apply RI.Ropp_gt_lt_contravar. apply Hu2.
     apply Hu1.
     apply Hl0. 
     
     unfold Radd, Rsub. unfold RD.Rdiv. rewrite <- RA.Rmult_plus_distr_l.
     replace (Rdefinitions.Rplus (RD.Rinv (RD.Rplus R1 R1)) (RD.Rinv (RD.Rplus R1 R1))) with
     (RD.Rmult (RD.Rplus R1 R1) (RD.Rinv (RD.Rplus R1 R1))).  
     rewrite (RA.Rmult_comm (RD.Rplus _ _) _). rewrite RA.Rinv_l. intuition.
     assert (RD.Rlt R0 2). change R0 with (RD.IZR Z0). intuition. intro. unfold R0 in *.
     change RD.R0 with (RD.IZR Z0)in H0. rewrite <- H1 in H0. apply RI.Rlt_irrefl in H0. 
     destruct H0.
     apply RI.double.
    
     unfold Radd, Rsub. unfold RD.Rminus. rewrite RA.Rplus_assoc.
     replace (Rdefinitions.Rplus (RD.Ropp (u n_spe)) (RD.Rplus (u n_spe) (RD.Ropp l))) with (RD.Ropp l).
     reflexivity.
     rewrite <- RA.Rplus_assoc. rewrite RI.Rplus_opp_l. intuition.
     apply RI.Rlt_irrefl in H0. apply H0.
     destruct H0.
     apply R_dist. apply H3.
  Qed.
  
End Rimpl.
