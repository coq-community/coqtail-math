Require Import Reals.

Inductive C : nat -> (R -> R) -> Prop :=
  | C_0 : forall f, continuity f -> C 0 f
  | C_Sn : forall f n (pr : derivable f), { f' : R -> R | (forall x, derive_pt f x (pr x) = (f' x)) /\ C n f' } -> C (S n) f.

Definition C_infty (f : R -> R) : Prop := forall n, C n f.

Lemma id_C_infty : C_infty id.
Proof.
 intro n ; destruct n.
  constructor ; apply derivable_continuous ; apply derivable_id.
  apply C_Sn with derivable_id.
  exists (fct_cte 1); split.
   intro; reg.
   destruct n.
    constructor; reg.
    
    apply C_Sn with (derivable_const 1).
    exists (fct_cte R0).
    split.
     intro; reg.
     induction n.
      constructor; reg.
      
      apply C_Sn with (derivable_const 0).
      exists (fct_cte 0); split.
       intro; reg.
       apply IHn.
Qed.
