Require Import Reals.
Require Import Rfunction_classes.
Require Import Ranalysis_def Ranalysis_facts.

Local Open Scope R_scope.

(** * Definition of the nth derivative *)

Program Fixpoint nth_derive {n : nat} (f : R -> R) (pr : D n f) : R -> R := match n with
   | O   => f
   | S m => @nth_derive m (derive f _) _
end.
Next Obligation.
inversion pr ; assumption.
Qed.
Next Obligation.
apply D_derive ; assumption.
Qed.

Program Fixpoint nth_derive_Rball {n : nat} c r f (pr: D_Rball c r n f): R -> R :=
match n with
  | 0   => f
  | S m => @nth_derive_Rball m c r (derive_Rball c r f _) _
end.
Next Obligation.
inversion pr ; assumption.
Qed.
Next Obligation.
apply D_Rball_derive ; assumption.
Qed.

Definition nth_derive' {m : nat} (n : nat) f (pr : D m f) (nlem : (n <= m)%nat) : R -> R :=
  nth_derive f (D_le _ _ _ nlem pr).

Definition nth_derive_Rball' {m : nat} c r n f (pr: D_Rball c r m f)
  (nlem: (n <= m)%nat) : R -> R :=
  nth_derive_Rball c r f (D_Rball_le _ _ _ _ _ nlem pr).