Require Import Reals.
Require Import Rfunction_classes.
Require Import Ranalysis_def Ranalysis_facts.

Open Local Scope R_scope.

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

Program Fixpoint nth_derive_Rball {n : nat} c r r_pos f (pr: D_Rball c r r_pos n f): R -> R :=
match n with
  | 0   => f
  | S m => @nth_derive_Rball m c r r_pos (derive_Rball f c r r_pos _) _
end.
Next Obligation.
inversion pr ; assumption.
Qed.
Next Obligation.
apply D_Rball_derive ; assumption.
Qed.

Definition nth_derive' {m : nat} (n : nat) (f : R -> R) (pr : D m f)
  (nlem : (n <= m)%nat) : R -> R.
Proof.
intros ; eapply nth_derive ;
 [eapply D_le |] ; eassumption.
Defined.

Definition nth_derive_Rball_n' {m : nat} c r r_pos n f (pr: D_Rball c r r_pos m f)
  (nlem: (n <= m)%nat) : R -> R.
Proof.
intros ; eapply nth_derive_Rball ; [eapply D_Rball_le |] ; eassumption.
Defined.