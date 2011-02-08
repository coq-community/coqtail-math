(*

Require Import Reals.
Require Import C_n_def C_n.
Require Import Functions.
Require Import Vec_def VecDep_def.
Require Import Program.
Require Import Max.

Inductive side_equa (n : nat) : Set :=
    | const : R -> side_equa n
    | y : forall (p : nat) (k : nat) (plen : p < n), side_equa n
    | opp : forall (s1 : side_equa n), side_equa n
    | plus : forall (s1 s2 : side_equa n), side_equa n
    | mult : forall (s1 s2 : side_equa n), side_equa n.

Definition minus {n : nat} (s1 s2 : side_equa n) := plus n s1 (opp n s2).

Definition diff_equa (n : nat) : Set := prod (side_equa n) (side_equa n).

Fixpoint max_se {n : nat} (s : side_equa n) (m : nat) (mltn : m < n) : nat :=
match s with
  | const _    => O
  | y p k _    => let b := eq_nat_dec m p in if b then k else O
  | opp s      => max_se s m mltn
  | plus s1 s2 => max (max_se s1 m mltn) (max_se s2 m mltn)
  | mult s1 s2 => max (max_se s1 m mltn) (max_se s2 m mltn)
end.

Fixpoint max_de {n : nat} (e : diff_equa n) (m : nat) (mltn : m < n) : nat :=
let (s1 , s2) := e in max (max_se s1 m mltn) (max_se s2 m mltn).

Definition Con {n : nat} (e : diff_equa n) : Vec Type n.
eapply Vmap.
 apply Cn.
 eapply Vmap ; [| eapply genVec].
 intro m ; eapply max_de.
  eexact e.
  
 Vmap Cn (Vmap (fun m => max_de e m _) (genVec n)).


Fixpoint interp_equa {n : nat} (s : side_equa n) (rho :) : R -> R := match s with
    | const x    => fun _ => x
    | y p k      => let (f , Cf) := rho p in nth_derive f (Cf k)
    | opp s1     => opp_fct  (interp_equa s1 rho)
    | plus s1 s2 => plus_fct (interp_equa s1 rho) (interp_equa s2 rho)
    | mult s1 s2 => mult_fct (interp_equa s1 rho) (interp_equa s2 rho)
end.

Fixpoint interp (e : diff_equa) (rho : nat -> Cinfty) : Prop := match e with
    | eq s1 s2 => forall x, (interp_equa s1 rho) x = (interp_equa s2 rho) x
end.

Delimit Scope de_scope with de.

Notation "`c k" := (const k) (at level 40) : de_scope.
Notation "- y" := (opp y) : de_scope.
Infix "+" := plus : de_scope.
Infix "-" := minus : de_scope.
Infix "*" := mult : de_scope.
Infix "=" := eq : de_scope.

Fixpoint list_to_fun {A : Type} (l : list A) (default : A) (n : nat) := match l with
    | nil     => default
    | h :: tl => match n with
        | O   => h
        | S m => list_to_fun tl default m
    end
end.

Notation "[| e |] rho" := (interp e%de (list_to_fun rho (zero_infty))) (at level 69).
*)