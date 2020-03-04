Require Export Reals.


Set Implicit Arguments.

Open Scope R_scope.

Section R_normed_vector_space.

Variable V : Type.
Variable N : V -> R.
Variable (vO:V).
Variable vadd : V->V->V.
Variable smul : R->V->V.
(* finite dimension *)
Variable dim : nat.
Variable base : nat -> V.

Variable p : nat -> V -> R. (* projection sur une base *)

Fixpoint finite_sum (n:nat) (v:nat->V) {struct n} := match n with
  | 0 => vO
  | S i => vadd (v n) (finite_sum i v)
end.
 
Record R_vector_space : Type := {
    vadd_comm : forall x y, vadd x y = vadd y x;
    vadd_assoc : forall x y z, vadd (vadd x y) z = vadd x (vadd y z);
    vadd_identity : forall x, vadd vO x = x;
    vadd_inverse : forall x, {y | vadd x y = vO} ;
  
    smul_distr_vadd : forall a x y, smul a (vadd x y) = vadd (smul a x) (smul a y);
    smul_distr_radd : forall a b x, smul (a + b) x = vadd (smul a x) (smul b x);
    smul_compat_rmul : forall a b x, smul a (smul b x) = smul (a * b) x;
    smul_identity : forall x, smul R1 x = x;
    
    Nzero : forall x, N x = 0 -> x = vO;
    Nmul : forall lambda x, N (smul lambda x) = Rabs (lambda) * N x;
    Ntriang : forall x y, N (vadd x y) <= N x + N y;

    basis : forall (v : V), v = finite_sum dim (fun n => smul (p n v) (base n))
  }.

End R_normed_vector_space.

Require Import integrales.

Module integral_vector (Import I : Integrals).

Parameter V : Type.
Parameter N : V -> R.
Parameter (vO:V).
Parameter vadd : V->V->V.
Parameter smul : R->V->V.
Parameter dim : nat.
Parameter base : nat -> V.
Parameter p : nat -> V -> R.

Parameter vect_space : R_vector_space N vO vadd smul dim base p.

Definition vect_Riemann_integrable (f : R -> V) (a b : R) := forall n, Riemann_integrable (fun x => p n (f x)) a b.

Definition vect_RiemannInt (f : R -> V) (a b : R) (pr : vect_Riemann_integrable f a b) : V := 
  finite_sum vO vadd dim
  (fun n => (smul (RiemannInt (pr n)) (base n))).

End integral_vector.

Section Useful_definitions.

Variable V : Type.
Variable N : V -> R.
Variable (vO:V).
Variable vadd : V->V->V.
Variable smul : R->V->V.
Variable dim : nat.
Variable base : nat -> V.
Variable p : nat -> V -> R.

Hypothesis vect_space : R_vector_space N vO vadd smul dim base p.

Definition vsub : V -> V -> V.
Proof.
intros.
destruct vect_space.
destruct (vadd_inverse0 X0).
apply (vadd X x).
Qed.

(* y is in the open ball of center x and of radius r *)
Definition being_in_ball (x : V) (r : R) (y : V) := N (vsub x y) < r.

(* Property : I is an open space.*)
Definition Open_space (I : V -> Prop) := forall x, I x -> {r : R | r > 0 /\ (forall y, being_in_ball x r y -> I y)}.


(* f is defined on I in the following*)

(* Continuity for a function f (I -> V)*)
Definition Vcontinuity_pt (f : R -> V) (I : R -> Prop) (x : R) := I x -> forall eps : R, eps > 0 -> 
  {alp : R | alp > 0 /\ (forall y, I y -> (Rabs (x - y) <= alp -> N (vsub (f y) (f x)) <= eps))}.

Definition Vcontinuity (f : R -> V) (I : R -> Prop) := forall x : R, Vcontinuity_pt f I x.

(* Derivability of a function f (I -> V)*)

Definition Vderivable_pt_lim (f : R -> V) (I : R -> Prop) (x : R) (l : V) := I x -> forall eps : R,
0 < eps ->
 {delta : R | delta > 0 /\  (forall h : R,
  h <> 0 -> Rabs h < delta -> I (x + h) -> (N (vsub (smul (/h) (vsub (f (x + h)) (f x) )) l )) < eps)}.

Definition Vderivable_pt_abs (f : R -> V) (I : R -> Prop) (x : R) (l : V) := Vderivable_pt_lim f I x l.

Definition Vderivable_pt (f : R -> V) (I : R -> Prop) (x : R) := {l : V & (Vderivable_pt_abs f I x l)}.

Definition Vderivable (f : R -> V) (I : R -> Prop) := forall x : R, Vderivable_pt f I x.

Definition Vderive_pt (f : R -> V) (I : R -> Prop) (x : R) (pr : Vderivable_pt f I x) := 
  projT1 pr.

Definition Vderive (f : R -> V) (I : R -> Prop) (pr : Vderivable f I) (x : R) := Vderive_pt (pr x).

(*Cn vectorial functions*)

Inductive VClass (f : R -> V) (I : R -> Prop) : nat -> Type :=
  | C_0 : Vcontinuity f I -> VClass f I 0
  | C_Sn : forall n (pr : Vderivable f I), VClass (Vderive pr) I n -> VClass f I (S n).

Definition VC n (I : R -> Prop) (f : R -> V) := (VClass f I n).

(** Being C_infty *)

Definition VC_infty (I : R -> Prop) (f : R -> V) := forall n, VC n I f.

Definition VCn (n : nat) (I : R -> Prop) := sigT (VC n I).
Definition VCinfty (I : R -> Prop) := sigT (VC_infty I).

Lemma VC_derivable : forall (f : R -> V) (I : R -> Prop), VC 1 I f -> Vderivable f I.
Proof.
intros.
inversion X.
apply pr.
Qed.


(* Continuity of f (K -> V) *)
Definition VVcontinuity_pt (f : V -> V) (K : V -> Prop) (open : Open_space K) (x : V) := K x -> forall eps : R, eps > 0 -> 
  {alp : R | alp > 0 /\ (forall y, K y -> N (vsub x y) <= alp -> N (vsub (f y) (f x)) <= eps)}.

Definition VVcontinuity (f : V -> V) (K : V -> Prop) (open : Open_space K) := forall (x : V), VVcontinuity_pt f open x.

(* Being locally "lipschitzienne" for f : K -> V *)
Definition lipschitz (f : V -> V) (K : V -> Prop) (open : Open_space K) := {k | k > 0 /\ forall (x x' : V), K x -> K x' -> N (vsub x x') < k * N (vsub (f x) (f x'))}.

End Useful_definitions.

