Require Raxiom.
Require Import ZArith.

Module Rrealize : Raxiom.CReals.
  Definition R : Type.
  Admitted. (* TODO *)
  
  Definition R0 : R.
  Admitted. (* TODO *)
  
  Definition R1 : R.
  Admitted. (* TODO *)
  
  Definition Radd : R -> R -> R.
  Admitted. (* TODO *)
  
  Definition Rmul (x y : R) : R.
  Admitted. (* TODO *)
  
  Definition Ropp (x : R) : R.
  Admitted. (* TODO *)
  
  Definition Rsub (x y : R) := Radd x (Ropp y).
  
  Definition Rlt (x y : R) : Type.
  Admitted. (* TODO *)
  
  Definition Rgt (r1 r2 : R) := Rlt r2 r1.
  Definition Rdiscr (r1 r2 : R) := sum (Rlt r1 r2) (Rlt r2 r1).
  Definition Req (r1 r2 : R) := Rdiscr r1 r2 -> False.
  Definition Rle (r1 r2 : R) := sumor (Rlt r1 r2) (Req r1 r2).
  Definition Rge (r1 r2 : R) := Rle r2 r1.
  
  Definition Rinv (x : R) (_ : Rdiscr x R0) := x. (* TODO *)
  
  Definition Rdiv (x y : R) (p : Rdiscr y R0) := Rmul x (Rinv y p).
  
  Lemma Rlt_trans : forall x y z, Rlt x y -> Rlt y z -> Rlt x z.
  Admitted. (* TODO *)
  
  Lemma Rlt_asym : forall x y : R, Rlt x y -> Rlt y x -> False.
  Admitted. (* TODO *)
  
  Lemma Req_lt_compat_l : forall x1 x2 y : R, Req x1 x2 -> Rlt x1 y -> Rlt x2 y.
  Admitted. (* TODO *)
  
  Lemma Req_lt_compat_r : forall x1 x2 y : R, Req x1 x2 -> Rlt y x1 -> Rlt y x2.
  Admitted. (* TODO *)
  
  Lemma Radd_lt_compat_l : forall x y1 y2 : R, Rlt y1 y2 -> Rlt (Radd x y1) (Radd x y2).
  Admitted. (* TODO *)
  
  Lemma Radd_eq_compat_l : forall x y1 y2, Req y1 y2 -> Req (Radd x y1) (Radd x y2).
  Admitted. (* TODO *)
  
  Lemma Rmul_lt_compat_l : forall x y1 y2 : R, Rlt R0 x -> Rlt y1 y2 -> Rlt (Rmul x y1) (Rmul x y2).
  Admitted. (* TODO *)
  
  Lemma Rmul_eq_compat_l : forall x y1 y2, Req y1 y2 -> Req (Rmul x y1) (Rmul x y2).
  Admitted. (* TODO *)
  
  Lemma Rinv_0_lt_compat : forall (x : R) (pr : Rlt R0 x) (pr' : Rdiscr x R0), Rlt R0 (Rinv x pr').
  Admitted. (* TODO *)
  
  Lemma Radd_comm : forall a b, Req (Radd a b) (Radd b a).
  Admitted. (* TODO *)
  
  Lemma Radd_assoc : forall x y z, Req (Radd (Radd x y) z) (Radd x (Radd y z)).
  Admitted. (* TODO *)
  
  Lemma Radd_opp_r : forall x, Req (Radd x (Ropp x)) R0.
  Admitted. (* TODO *)
  
  Lemma Radd_0_l : forall x, Req (Radd R0 x) x.
  Admitted. (* TODO *)
  
  Lemma Rmul_add_distr_l a b c : Req (Rmul a (Radd b c)) (Radd (Rmul a b) (Rmul a c)).
  Admitted. (* TODO *)
  
  Lemma Rmul_comm : forall a b, Req (Rmul a b) (Rmul b a).
  Admitted. (* TODO *)
  
  Lemma Rmul_assoc : forall x y z, Req (Rmul (Rmul x y) z) (Rmul x (Rmul y z)).
  Admitted. (* TODO *)
  
  Lemma Rmul_1_l : forall x, Req (Rmul R1 x) x.
  Admitted. (* TODO *)
  
  Lemma Rinv_l : forall (x : R) (pr : Rdiscr x R0), Req (Rmul (Rinv x pr) x) R1.
  Admitted. (* TODO *)
  
  Lemma Rlt_0_1 : Rlt R0 R1.
  Admitted. (* TODO *)
  
  Fixpoint IPR (p : positive) : R :=
    match p with
      | xI p => Radd (Rmul (Radd R1 R1) (IPR p)) R1
      | xO p => Rmul (Radd R1 R1) (IPR p)
      | xH => R1
    end.
  
  Definition IZR (z : BinInt.Z) : R :=
    match z with
      | Z0 => R0
      | Zpos p => IPR p
      | Zneg p => Ropp (IPR p)
    end.
  
  Definition Rdist x y d : Type := prod (Rlt (Rsub x y) d) (Rlt (Ropp d) (Rsub x y)).
  
  Definition Rup : R -> Z.
  Admitted. (* TODO *)
  
  Lemma Rup_spec : forall r : R, Rdist r (IZR (Rup r)) R1.
  Admitted. (* TODO *)
  
  Definition Rseq_Cauchy (Un : nat -> R) : Type := forall eps, Rlt R0 eps ->
    {N : nat & forall p q, (N <= p)%nat -> (N <= q)%nat -> Rdist (Un p) (Un q) eps}.
  
  Definition Rseq_cv (Un : nat -> R) (l : R) : Type := forall eps, Rlt R0 eps ->
    {N : nat & forall n, (N <= n)%nat -> Rdist (Un n) l eps}.
  
  Lemma Rcomplete : forall Un, Rseq_Cauchy Un -> {l : R & Rseq_cv Un l}.
  Admitted. (* TODO *)
  
End Rrealize.
