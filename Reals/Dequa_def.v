Require Import Reals.
Require Import C_n_def C_n.
Require Import Functions.
Require Import List.
Require Import Program.

Inductive side_equa : Set :=
    | const : R -> side_equa
    | y : forall (p : nat) (k : nat), side_equa
    | opp : forall (s1 : side_equa), side_equa
    | plus : forall (s1 s2 : side_equa), side_equa
    | mult : forall (s1 s2 : side_equa), side_equa.

Definition minus s1 s2 := plus s1 (opp s2).

Inductive diff_equa : Set :=
    | eq : forall (s1 s2 : side_equa), diff_equa.

Fixpoint interp_equa (s : side_equa) (rho : nat -> Cinfty) : R -> R := match s with
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