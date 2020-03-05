Require Import Raxiom Rconvenient IZR Repsilon Rapprox Rseq.
Require Import Arith.

Module Rabs (Import T : CReals).
  Module Rconvenient := Rconvenient T. Import Rconvenient.
  Module IZR := IZR T. Import IZR.
  Module Repsilon := Repsilon T. Import Repsilon.
  Module Rsequence := Rsequence T. Import Rsequence.
  Module Rapprox := Rapprox T. Import Rapprox.
  
  Definition Rseq_abs : R -> Rseq := fun x n => (IZR (Z.abs (Rup (x * po n))) / po n) (pop n).
  
  Lemma Rseq_cauchy_abs : forall x, Rseq_Cauchy (Rseq_abs x).
  Admitted.
  
  Definition Rabs (x : R) : R := projT1 (Rcomplete (Rseq_abs x) (Rseq_cauchy_abs x)).
  
  Lemma Rabs_pos : forall x, R0 ## x -> R0 < Rabs x.
  Admitted.
  
  Lemma Rabs_eq_compat : forall x y, x == y -> Rabs x == Rabs y.
  Admitted.
  
  Lemma Rabs_0 : Rabs R0 == R0.
  Admitted.
  
  (* TODO : dire que ~~A→A est plus faible que ~A\/A *)
  (* TODO : formuler la décision de l'égalité *)
  (* TODO : dire que (WEAK Rle → Rle) → Décision de l'égalité *)
  
End Rabs.