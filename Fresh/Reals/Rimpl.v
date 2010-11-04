(* Require Reals.
Require Raxiom.

Module Rimpl : Raxiom.CReals.
  
  Definition R := Coq.Reals.Rdefinitions.R.
  Definition R0 := Coq.Reals.Rdefinitions.R0.
  Definition R1 := Coq.Reals.Rdefinitions.R1.
  Definition Rplus := Coq.Reals.Rdefinitions.Rplus.
  Definition Rmult := Coq.Reals.Rdefinitions.Rmult.
  Definition Ropp := Coq.Reals.Rdefinitions.Ropp.
  Definition Rlt := Coq.Reals.Rdefinitions.Rlt.
  Definition Rup := Coq.Reals.Rdefinitions.up.

Infix "+" := Rplus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Infix "<" := Rlt : R_scope.

Definition Rgt (r1 r2 : R) := Rlt r2 r1.
Definition Rdiscr (r1 r2 : R) := sum (Rlt r1 r2) (Rlt r2 r1).
Definition Req (r1 r2 : R) := Rdiscr r1 r2 -> False.
Definition Rle (r1 r2 : R) := sumor (Rlt r1 r2) (Req r1 r2).
Definition Rge (r1 r2 : R) := Rle r2 r1.

  Definition Rinv (x : R) (_ : Rdiscr x R0) :=
    Coq.Reals.Rdefinitions.Rinv x.
  
  Definition Rlt_trans := Coq.Reals.Raxioms.Rlt_trans.
  Definition Rlt_asym : forall r1 r2 : R, Rlt r1 r2 -> Rlt r2 r1 -> False.
  Proof.
    intros a b Hab Hba.
    apply (RIneq.Rlt_not_le a b Hba).
    apply (RIneq.Rlt_le _ _ Hab).
  Defined.
  
  Lemma folding_Req_eq : forall a b, Req a b -> eq a b.
  Proof.
    intros a b Hab.
    apply RIneq.Rle_antisym; apply RIneq.Rnot_lt_le;
      intro; destruct Hab; compute; intuition.
  Qed.
  
End Rimpl.
*)