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

Inductive DClass_Rball (f : R -> R) (c r : R) (r_pos : 0 <= r) : nat -> Type :=
  | Db_0 : DClass_Rball f c r r_pos 0
  | Db_S : forall n (pr : derivable_Rball f c r r_pos),
           DClass_Rball (derive_Rball f c r r_pos pr) c r r_pos n ->
           DClass_Rball f c r r_pos (S n).

Definition D_Rball c r r_pos n f := DClass_Rball f c r r_pos n.

(** Being D_infty *)

Definition D_infty (f : R -> R) := forall n, D n f.
Definition D_Rball_infty c r r_pos f := forall n, D_Rball c r r_pos n f.

Definition Dn (n : nat) := sigT (D n).
Definition Dn_Rball c r r_pos n := sigT (D_Rball c r r_pos n).

Definition Dinfty := sigT D_infty.

(** * Being of Class C_n *)

Inductive CClass (f : R -> R) : nat -> Type :=
  | C_0 : continuity f -> CClass f 0
  | C_S : forall n (pr : derivable f), CClass (derive f pr) n -> CClass f (S n).

Definition C n f := (CClass f n).

(** Restriction to a specific Rball. *)

Inductive CClass_Rball (f : R -> R) (c r : R) (r_pos : 0 <= r) : nat -> Type :=
  | Cb_0 : continuity_Rball f c r r_pos -> CClass_Rball f c r r_pos 0
  | Cb_S : forall n (pr : derivable_Rball f c r r_pos),
           CClass_Rball (derive_Rball f c r r_pos pr) c r r_pos n ->
           CClass_Rball f c r r_pos (S n).

Definition C_Rball c r r_pos n f := CClass_Rball f c r r_pos n.

(** Being C_infty *)

Definition C_infty (f : R -> R) := forall n, C n f.
Definition C_Rball_infty c r r_pos f := forall n, C_Rball c r r_pos n f.

Definition Cn (n : nat) : Type := sigT (C n).
Definition Cn_Rball c r r_pos n := sigT (C_Rball c r r_pos n).

Definition Cinfty : Type := sigT C_infty.