Module Type CReals.

Require Import ZArith.

(** * Constructive ordered field *)

Parameter R : Type.

Delimit Scope R_scope with R.
Bind Scope R_scope with R.
Open Local Scope R_scope.

(** R ring objects **)
Parameter R0 : R.
Parameter R1 : R.
Parameter Radd : R -> R -> R.
Parameter Rmul : R -> R -> R.
Parameter Ropp : R -> R.

(** Ordering **)
Parameter Rlt : R -> R -> Type.
Infix "<" := Rlt : R_scope.

Definition Rgt (r1 r2 : R) := r2 < r1.
Definition Rdiscr (r1 r2 : R) := sum (r1 < r2) (r2 < r1).
Definition Req (r1 r2 : R) := Rdiscr r1 r2 -> False.
Definition Rle (r1 r2 : R) := sumor (r1 < r2) (Req r1 r2).
Definition Rge (r1 r2 : R) := Rle r2 r1.

Infix "+" := Radd : R_scope.
Infix "*" := Rmul : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Infix "==" := Req (at level 70, no associativity) : R_scope.
Infix "#" := Rdiscr (at level 70, no associativity) : R_scope.
Infix "<=" := Rle : R_scope.
Infix ">=" := Rge : R_scope.
Infix ">"  := Rgt : R_scope.

(** Constructive order properties **)
Axiom Rlt_trans : forall x y z : R, x < y -> y < z -> x < z.
Axiom Rlt_asym : forall x y : R, x < y -> y < x -> False.

(** Constructive inverse *)
Axiom Rinv : forall x, Rdiscr x R0 -> R.

(** Convenient operations **)
Definition Rsub (x y : R) : R := Radd x (Ropp y).
Definition Rdiv (x y : R) (pr : y # R0) : R := x * Rinv y pr.

(** Congruences **)
Axiom Req_lt_compat_l : forall x1 x2 y : R, x1 == x2 -> x1 < y -> x2 < y.
Axiom Req_lt_compat_r : forall x1 x2 y : R, x1 == x2 -> y < x1 -> y < x2.
Axiom Req_inv_compat : forall (x : R) (pr : R0 < x) (pr' : x # R0), R0 < Rinv x pr'.
Axiom Radd_lt_compat_l : forall x y1 y2 : R, y1 < y2 -> x + y1 < x + y2.
Axiom Rmul_lt_compat_l : forall x y1 y2 : R, R0 < x -> y1 < y2 -> x * y1 < x * y2.

Infix "-" := Rsub : R_scope.
Infix "/" := Rdiv : R_scope.

(** Ring operations **)
Axiom Radd_comm : forall x y : R, x + y == y + x.
Axiom Radd_assoc : forall x y z : R, (x + y) + z == x + (y + z).
Axiom Radd_opp_r : forall x : R, x + - x == R0.
Axiom Radd_0_l : forall x : R, R0 + x == x.

Axiom Rmul_add_distr_l : forall x y z : R, Req (x * (y + z)) (x * y + x * z).

Axiom Rmul_comm : forall x y : R, x * y == y * x.
Axiom Rmul_assoc : forall x y z : R, (x * y) * z == x * (y * z).
Axiom Rmul_1_l : forall r : R, R1 * r == r.

(** Constructive field operation **)
Axiom Rinv_l : forall (x : R) (pr : x # R0), Rinv x pr * x == R1.

(** Ordered Field **)
Axiom Rlt_0_1 : R0 < R1.

(** * Archimedean **)

(** Injection from Z to R **)
Fixpoint IPR (p : positive) : R :=
  match p with
    | xI p => (R1 + R1) * (IPR p) + R1
    | xO p => (R1 + R1) * (IPR p)
    | xH => R1
  end.
Arguments Scope IPR [positive_scope].

Definition IZR (z : Z) : R :=
  match z with
    | Z0 => R0
    | Zpos p => IPR p
    | Zneg p => - IPR p
  end.
Arguments Scope IZR [Z_scope].

Definition Rsqr r : R := r * r.

(** Getting back to Z **)

Parameter Rup : R -> Z.
Axiom Rup_spec : forall r : R, Rsqr (r - IZR (Rup r)) < R1.

(** * Completeness **)

Lemma Rdiscr_0_2 : Rdiscr (R1 + R1) R0.
Proof.
right.
apply (Req_lt_compat_l _ _ _ (Radd_0_l _)).
apply Rlt_trans with (R0 + R1).
 apply Radd_lt_compat_l, Rlt_0_1.
 apply (Req_lt_compat_l _ _ _ (Radd_comm _ _)); apply Radd_lt_compat_l, Rlt_0_1.
Qed.

Definition Rinv_2 := Rinv (R1 + R1) Rdiscr_0_2.

Fixpoint Rpow_nat (x : R) (n : nat) : R := match n with
  | O => R1
  | S n => x * Rpow_nat x n
end.

Definition Rseq_Cauchy (Un : nat -> R) : Type := forall k,
  {N : nat & forall p q, (N <= p)%nat -> (N <= q)%nat -> Rsqr (Un p - Un q) < Rpow_nat Rinv_2 k}.

Definition Rseq_cv (Un : nat -> R) (l : R) : Type := forall k,
  {N : nat & forall n, (N <= n)%nat -> Rsqr (Un n - l) < Rpow_nat Rinv_2 k}.

Axiom Rcomplete : forall Un, Rseq_Cauchy Un -> {l : R & Rseq_cv Un l}.

End CReals.