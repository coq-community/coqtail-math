Require Import Rbase.
Require Import Ranalysis.

Require Import Rinterval Ranalysis_def.

Local Open Scope R_scope.

(** * Being of Class D_n. *)

Inductive DClass (f : R -> R) : nat -> Type :=
  | D_0 : DClass f 0
  | D_S : forall n (pr : derivable f), DClass (derive f pr) n -> DClass f (S n).

Definition D n f := DClass f n.

(** Restriction to a specific Rball. *)

Inductive DClass_Rball (c r : R) (f : R -> R) : nat -> Type :=
  | Db_0 : DClass_Rball c r f 0
  | Db_S : forall n (pr : derivable_Rball c r f),
           DClass_Rball c r (derive_Rball c r f pr) n ->
           DClass_Rball c r f (S n).

Definition D_Rball c r n f := DClass_Rball c r f n.

(** Being D_infty *)

Definition D_infty (f : R -> R) := forall n, D n f.
Definition D_Rball_infty c r f := forall n, D_Rball c r n f.

Definition Dn (n : nat) := sigT (D n).
Definition Dn_Rball c r n := sigT (D_Rball c r n).

Definition Dinfty := sigT D_infty.

(** * Being of Class C_n *)

Inductive CClass (f : R -> R) : nat -> Type :=
  | C_0 : continuity f -> CClass f 0
  | C_S : forall n (pr : derivable f), CClass (derive f pr) n -> CClass f (S n).

Definition C n f := (CClass f n).

(** Restriction to a specific Rball. *)

Inductive CClass_Rball (c r : R) (f : R -> R) : nat -> Type :=
  | Cb_0 : continuity_Rball c r f -> CClass_Rball c r f 0
  | Cb_S : forall n (pr : derivable_Rball c r f),
           CClass_Rball c r (derive_Rball c r f pr) n ->
           CClass_Rball c r f (S n).

Definition C_Rball c r n f := CClass_Rball c r f n.

(** Being C_infty *)

Definition C_infty (f : R -> R) := forall n, C n f.
Definition C_Rball_infty c r f := forall n, C_Rball c r n f.

Definition Cn (n : nat) : Type := sigT (C n).
Definition Cn_Rball c r n := sigT (C_Rball c r n).

Definition Cinfty : Type := sigT C_infty.