Require Import Reals.
Require Import C_n_def C_n.
Require Import Functions.
Require Import List.
Require Import Destruct.


Fixpoint Lget {A : Type} (L : list A) (n : nat) : option A :=
match L with
  | nil     => None
  | a :: L' =>
  match n with
    | O    => Some a
    | S n' => Lget L' n'
  end
end.


(* This file defines the differential equations and their
 interpretation as propositions. *)

Inductive side_equa : Set :=
    | cst  : R -> side_equa
    | y    : forall (p : nat) (k : nat), side_equa
    | opp  : forall (s1 : side_equa), side_equa
    | plus : forall (s1 s2 : side_equa), side_equa
    | mult : forall (s1 s2 : side_equa), side_equa.

Definition minus (s1 s2 : side_equa) := plus s1 (opp s2).

Definition diff_equa : Set := prod (side_equa) (side_equa).

Fixpoint interp_side_equa (s : side_equa)
 (rho : list (sigT Cn)) : option (R -> R).
destruct_eq s.
 exact (Some (fun _ => r)).
 destruct (Lget rho p) as [[l [f Clf]] |].
  destruct (le_lt_dec k l) as [klel | _].
   exact (Some (nth_derive' k f Clf klel)).
   exact None.
  exact None.
 destruct (interp_side_equa b rho) as [f |] ;
  [apply Some ; apply opp_fct ; exact f |
  exact None].
 destruct (interp_side_equa b1 rho) as [f |] ;
  [destruct (interp_side_equa b2 rho) as [g |] ;
  [apply Some ; apply plus_fct ; [exact f | exact g] |] |] ;
  exact None.
 destruct (interp_side_equa b1 rho) as [f |] ;
  [destruct (interp_side_equa b2 rho) as [g |] ;
  [apply Some ; apply mult_fct ; [exact f | exact g] |] |] ;
  exact None.
Defined.

Definition Invalid_context := False.

Definition interp (e : diff_equa)
 (rho : list (sigT Cn)) : Prop :=
let (s1, s2) := e in
match (interp_side_equa s1 rho), (interp_side_equa s2 rho) with
  | Some f1, Some f2 => forall (x : R), f1 x = f2 x
  | _, _ => Invalid_context
end.


Delimit Scope de_scope with de.

(* Automatically open scope C_scope for arguments of type C *)
Bind Scope de_scope with diff_equa.

Open Scope de_scope.

Notation "`c k" := (cst k) (at level 40) : de_scope.
Notation "- y" := (opp y) : de_scope.
Infix "+" := plus : de_scope.
Infix "-" := minus : de_scope.
Infix "*" := mult : de_scope.

Notation "[| e |]" := (interp e%de) (at level 69).