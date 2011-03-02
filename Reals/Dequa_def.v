Require Import Reals.
Require Import C_n_def C_n_facts.
Require Import Functions.
Require Import Rsequence.
Require Import List.
Require Import Destruct.

Local Open Scope R_scope.

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

Fixpoint interp_side_equa_in_R (s : side_equa)
 (rho : list (sigT Cn)) : option (R -> R).
destruct_eq s.
 exact (Some (fun _ => r)).
 destruct (nth_error rho p) as [[l [f Clf]] |].
  destruct (le_lt_dec k l) as [klel | _].
   exact (Some (nth_derive' k f Clf klel)).
   exact None.
  exact None.
 destruct (interp_side_equa_in_R b rho) as [f |] ;
  [apply Some ; apply opp_fct ; exact f |
  exact None].
 destruct (interp_side_equa_in_R b1 rho) as [f |] ;
  [destruct (interp_side_equa_in_R b2 rho) as [g |] ;
  [apply Some ; apply plus_fct ; [exact f | exact g] |] |] ;
  exact None.
 destruct (interp_side_equa_in_R b1 rho) as [f |] ;
  [destruct (interp_side_equa_in_R b2 rho) as [g |] ;
  [apply Some ; apply mult_fct ; [exact f | exact g] |] |] ;
  exact None.
Defined.

Fixpoint interp_side_equa_in_R2 (s : side_equa)
 (rho : list Cinfty) : option (R -> R).
destruct_eq s.
 exact (Some (fun _ => r)).
 destruct (nth_error rho p) as [[f Cf] |].
  exact (Some (nth_derive' k f (Cf _) (le_refl _))).
  exact None.
 destruct (interp_side_equa_in_R2 b rho) as [f |] ;
  [apply Some ; apply opp_fct ; exact f |
  exact None].
 destruct (interp_side_equa_in_R2 b1 rho) as [f |] ;
  [destruct (interp_side_equa_in_R2 b2 rho) as [g |] ;
  [apply Some ; apply plus_fct ; [exact f | exact g] |] |] ;
  exact None.
 destruct (interp_side_equa_in_R2 b1 rho) as [f |] ;
  [destruct (interp_side_equa_in_R2 b2 rho) as [g |] ;
  [apply Some ; apply mult_fct ; [exact f | exact g] |] |] ;
  exact None.
Defined.

Fixpoint interp_side_equa_in_N (s : side_equa)
 (rho : list Rseq) : option (nat -> R).
destruct_eq s.
 exact (Some (fun n => if eq_nat_dec n 0 then r else 0)).
 destruct (nth_error rho p) as [un |].
   exact (Some (fun n => INR (fact n) / INR (fact (n - k)) * un n)).
   exact None.
 destruct (interp_side_equa_in_N b rho) as [un |] ;
  [apply Some ; apply Rseq_opp ; exact un |
  exact None].
 destruct (interp_side_equa_in_N b1 rho) as [un |] ;
  [destruct (interp_side_equa_in_N b2 rho) as [vn |] ;
  [apply Some ; apply Rseq_plus ; [exact un | exact vn] |] |] ;
  exact None.
 destruct (interp_side_equa_in_N b1 rho) as [un |] ;
  [destruct (interp_side_equa_in_N b2 rho) as [vn |] ;
  [apply Some ; apply Rseq_prod ; [exact un | exact vn] |] |] ;
  exact None.
Defined.

Definition Invalid_context := False.

Definition interp_in_R (e : diff_equa)
 (rho : list (sigT Cn)) : Prop :=
let (s1, s2) := e in
match (interp_side_equa_in_R s1 rho), (interp_side_equa_in_R s2 rho) with
  | Some f1, Some f2 => forall (x : R), f1 x = f2 x
  | _, _ => Invalid_context
end.

Definition interp_in_R2 (e : diff_equa)
 (rho : list Cinfty) : Prop :=
let (s1, s2) := e in
match (interp_side_equa_in_R2 s1 rho), (interp_side_equa_in_R2 s2 rho) with
  | Some f1, Some f2 => forall (x : R), f1 x = f2 x
  | _, _ => Invalid_context
end.

Definition interp_in_N (e : diff_equa)
  (rho : list Rseq) : Prop :=
let (s1, s2) := e in
match (interp_side_equa_in_N s1 rho), (interp_side_equa_in_N s2 rho) with
  | Some un, Some vn => forall (n : nat), un n = vn n
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

Notation "[| e |]R" := (interp_in_R e%de) (at level 69).
Notation "[| e |]R2" := (interp_in_R2 e%de) (at level 69).
Notation "[| e |]N" := (interp_in_N e%de) (at level 69).