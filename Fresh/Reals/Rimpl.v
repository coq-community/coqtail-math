Require Reals.
Require Raxiom.
Require Import ZArith.

(* Realisation of Raxioms thanks to the standard library of Coq *)

Module RD := Coq.Reals.Rdefinitions.
Module RA := Coq.Reals.Raxioms.
Module RI := Coq.Reals.RIneq.

Module Rimpl : Raxiom.CReals.
  
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
  Arguments Scope IPR [positive_scope].
  
  Definition IZR (z : Z) : R :=
    match z with
      | Z0 => R0
      | Zpos p => IPR p
      | Zneg p => Ropp (IPR p)
    end.
  Arguments Scope IZR [Z_scope].
  
  Definition Rdist x y d : Type := prod (Rlt (Rsub x y) d) (Rlt (Ropp d) (Rsub x y)).
  
  (** Getting back to Z **)
  
  Definition Rup : R -> Z.
  Proof.
    exact Coq.Reals.R_Ifp.Int_part.
  Defined.
  
  Lemma IZR_same : forall z, Raxioms.IZR z = IZR z.
  Proof.
    cut (forall p : positive, Raxioms.INR (nat_of_P p) = IPR p).
     intros H []; simpl; auto.
     intros p; rewrite H; auto.
   induction 0; auto.
    rewrite nat_of_P_xI, RI.S_INR, RI.mult_INR, IHp; auto.
    rewrite nat_of_P_xO, RI.mult_INR, IHp; auto.
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
  
  Lemma Rcomplete : forall Un, Rseq_Cauchy Un -> {l : R & Rseq_cv Un l}.
  Proof.
    intros u Hu.
    destruct (Coq.Reals.Rcomplete.R_complete u) as (l, Hl).
     (* montrer que le critère ci-dessus implique celui de la stdlib *)
     admit.
     
     exists l.
     (* montrer que la notion de convergence est impliquée par celle de la stdlib *)
     (* attention à la destruction d'hypothèses dans Prop *)
     admit.
  Qed.
  
End Rimpl.
