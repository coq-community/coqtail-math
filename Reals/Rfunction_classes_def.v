Require Import Rbase.
Require Import Ranalysis.

Local Open Scope R_scope.

(** * Being of Class D_n *)

Inductive DClass (f : R -> R) : nat -> Type :=
  | D_0 : DClass f 0
  | D_S : forall n (pr : derivable f), DClass (derive f pr) n -> DClass f (S n).

Definition D n f := DClass f n.

(** Being D_infty *)

Definition D_infty (f : R -> R) := forall n, D n f.

Definition Dn (n : nat) := sigT (D n).
Definition Dinfty := sigT D_infty.

(** * Being of Class C_n *)

Inductive CClass (f : R -> R) : nat -> Type :=
  | C_0 : continuity f -> CClass f 0
  | C_S : forall n (pr : derivable f), CClass (derive f pr) n -> CClass f (S n).

Definition C n f := (CClass f n).

(** Being C_infty *)

Definition C_infty (f : R -> R) := forall n, C n f.

Definition Cn (n : nat) : Type := sigT (C n).
Definition Cinfty : Type := sigT C_infty.