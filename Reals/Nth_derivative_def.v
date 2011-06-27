Require Import Reals.
Require Import Rfunction_classes.

Open Local Scope R_scope.

(** * Definition of the nth derivative *)

Program Fixpoint nth_derive {n : nat} (f : R -> R) (pr : D n f) : R -> R := match n with
   | O   => f
   | S n' => @nth_derive n' (derive f _) _
end.
Next Obligation.
inversion pr ; assumption.
Qed.
Next Obligation.
apply D_derive ; assumption.
Qed.

Definition nth_derive' {m : nat} (n : nat) (f : R -> R) (pr : D m f)
  (nlem : (n <= m)%nat) : R -> R.
Proof.
intros ; eapply nth_derive ;
 [eapply D_le |] ; eassumption.
Defined.