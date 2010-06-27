Require Import Reals.

Inductive C : nat -> (R -> R) -> Prop :=
  | C_0 : forall f, continuity f -> C 0 f
  | C_Sn : forall f n (pr : derivable f), { f' : R -> R | (forall x, derive_pt f x (pr x) = (f' x)) /\ C n f' } -> C (S n) f.

Definition C_infty (f : R -> R) : Prop := forall n, C n f.

Lemma id_C_infty : C_infty id.
Proof.
 intro n ; destruct n.
  constructor ; apply derivable_continuous ; apply derivable_id.
  induction n.
   apply C_Sn with derivable_id.
   exists (fun x => R1) ; split ; [intro x | constructor] ; reg.
   