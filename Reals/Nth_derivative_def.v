Require Import Reals.
Require Import C_n_def C_n_facts.

Open Local Scope R_scope.

(** * Definition of the nth derivative *)

Program Fixpoint nth_derive {n : nat} (f : R -> R) (pr : C n f) : R -> R := match n with
   | O   => f
   | S n' => @nth_derive n' (derive f _) _
end.
Next Obligation.
inversion pr ; assumption.
Qed.
Next Obligation.
apply C_derive ; assumption.
Qed.

Definition nth_derive' {m : nat} (n : nat) (f : R -> R) (pr : C m f)
  (nlem : (n <= m)%nat) : R -> R.
Proof.
intros ; eapply nth_derive ;
 [eapply C_le |] ; eassumption.
Defined.