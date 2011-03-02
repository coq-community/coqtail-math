Require Import Rbase.
Require Import Ranalysis.

Local Open Scope R_scope.

(** * Being of Class C_n *)

Inductive Class (f : R -> R) : nat -> Type :=
  | C_0 : continuity f -> Class f 0
  | C_Sn : forall n (pr : derivable f), Class (derive f pr) n -> Class f (S n).

Definition C n f := (Class f n).

(** Being C_infty *)

Definition C_infty (f : R -> R) := forall n, C n f.

Definition Cn (n : nat) : Type := sigT (C n).
Definition Cinfty : Type := sigT C_infty.