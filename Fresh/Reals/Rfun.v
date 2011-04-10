Require Import Raxiom Rconvenient IZR Repsilon Rapprox Rseq.
Require Import Arith.

Module Rfunction (Import T : CReals).
  Module Rconvenient := Rconvenient T. Import Rconvenient.
  Module IZR := IZR T. Import IZR.
  Module Repsilon := Repsilon T. Import Repsilon.
  Module Rsequence := Rsequence T. Import Rsequence.
  Module Rapprox := Rapprox T. Import Rapprox.
  
  Definition Rcont_pt (f : R -> R) (x : R) : Type :=
    forall e, R0 < e ->
      sigT (fun d =>
        prod
          (R0 < d)
          (forall x', Rdist x x' d -> Rdist (f x) (f x') e)).
  
  Definition Rcont (f : R -> R) : Type := forall x, Rcont_pt f x.
  
  Definition Rcont_op (op : R -> R -> R) : Type :=
    prod
      (forall a, Rcont (op a))
      (forall a, Rcont (fun x => op x a)).
  
  Lemma Rcont_add : Rcont_op Radd.
  Admitted.
  
  Lemma Rcont_mul : Rcont_op Rmul.
  Admitted.
  
  Lemma Rcont_sub : Rcont_op Rsub.
  Admitted.
  
  Lemma Rcont_opp : Rcont Ropp.
  Admitted.
  
  Lemma Rcont_compose : forall f g, Rcont f -> Rcont g -> Rcont (fun x => f (g x)).
  Proof.
    intros f g cf cg x e epos.
    destruct (cf (g x) e epos) as (d, (dpos, hd)).
    destruct (cg x d dpos) as (c, (cpos, hc)).
    eauto.
  Qed.
  
  (* TODO : dire que ~~A→A est plus faible que ~A\/A *)
  (* TODO : formuler la décision de l'égalité *)
  (* TODO : dire que (WEAK Rle → Rle) → Décision de l'égalité *)
  
End Rfunction.