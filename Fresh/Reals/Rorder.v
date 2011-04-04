Require Import Raxiom Rconvenient IZR Repsilon.

Module Rorder (Import T : CReals).
  Module Rconvenient := Rconvenient T. Import Rconvenient.
  Module IZR := IZR T. Import IZR.
  Module Repsilon := Repsilon T. Import Repsilon.
  
  Inductive Rlt_Prop : R -> R -> Prop :=
    Rlt_Prop_inhabits : forall x y, Rlt x y -> Rlt_Prop x y.
  
  Lemma Rlt_prop : forall x y, Rlt x y -> Rlt_Prop x y.
  Proof.
    intros; constructor; assumption.
  Qed.
  
  Lemma Rlt_algebraic : forall x y, Rlt_Prop x y -> Rlt x y.
  Admitted.
  
End Rorder.
