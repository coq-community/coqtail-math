Require Import Evect.

Section Vectorial_Cauchy.
Variable V : Type.
Variable N : V -> R.
Variable (vO:V).
Variable vadd : V->V->V.
Variable smul : R->V->V.
Variable dim : nat.
Variable base : nat -> V.
Variable p : nat -> V -> R.

Hypothesis vect_space : R_vector_space N vO vadd smul dim base p.

(* Cauchy Lipschtz for an autonomous patacouffin TODO *)
Lemma Cauchy_autonomous : forall (f : V -> V) (I : R -> Prop) (K : V -> Prop) (open : Open_space vect_space K) 
  (t0 : R) (x0 : V), 
  K x0 -> VVcontinuity f open -> lipschitz f open -> 
  {x : R -> V & {C : VC vect_space 1 I x | forall (t : R), I t -> (K (x t)) /\ (Vderive (VC_derivable C)) t = f (x t) /\ x t0 = x0}}.
Proof.
intros f I K openK t0 x0 Hx0K Hfcont lipschitzf.
Abort.

End Vectorial_Cauchy.
