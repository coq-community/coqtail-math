Require Import Reals.
Require Import Rpser_def Rpser_sums Rpser_usual Rpser_derivative.
Require Import C_n_def C_n_usual C_n_facts.
Require Import Nth_derivative_def.
Require Import Rfunction_def Functions.
Require Import Rsequence_def.
Require Import List.
Require Import Ass_handling.

Local Open Scope R_scope.

(* This file defines the differential equations and their
 interpretation as propositions. *)

Inductive side_equa : Set :=
    | cst  : R -> side_equa
    | y    : forall (p : nat) (k : nat), side_equa
    | opp  : forall (s1 : side_equa), side_equa
    | plus : forall (s1 s2 : side_equa), side_equa.

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
Defined.

Fixpoint interp_side_equa_in_N (s : side_equa)
 (rho : list Rseq) : option (nat -> R).
destruct_eq s.
 exact (Some (cst_seq r)).
 destruct (nth_error rho p) as [un |].
   exact (Some (An_nth_deriv un k)).
   exact None.
 destruct (interp_side_equa_in_N b rho) as [un |] ;
  [apply Some ; apply Rseq_opp ; exact un |
  exact None].
 destruct (interp_side_equa_in_N b1 rho) as [un |] ;
  [destruct (interp_side_equa_in_N b2 rho) as [vn |] ;
  [apply Some ; apply Rseq_plus ; [exact un | exact vn] |] |] ;
  exact None.
Defined.

Fixpoint interp_side_equa_in_SN (s : side_equa)
 (rho : list Rseq) : option (nat -> R -> R).
destruct_eq s.
 exact (Some (fun n x => Rseq_pps (fun n => if eq_nat_dec n 0 then r else 0) x n)).
 destruct (nth_error rho p) as [un |].
   exact (Some (fun n x => Rseq_pps (An_nth_deriv un k) x n)).
   exact None.
 destruct (interp_side_equa_in_SN b rho) as [un |].
   exact (Some (fun n => - (un n))%F).
   exact None.
 destruct (interp_side_equa_in_SN b1 rho) as [un |].
   destruct (interp_side_equa_in_SN b2 rho) as [vn |].
     exact (Some (fun n => (un n) + (vn n))%F).
     exact None.
   exact None.
Defined.

Fixpoint interp_side_equa_in_R3 (s : side_equa)
 (rho : list (sigT infinite_cv_radius)) : option (R -> R).
destruct_eq s.
 exact (Some (fun _=> r)).
 destruct (nth_error rho p) as [[An rAn] |].
  exact (Some (nth_derive (sum An rAn) (C_infty_Rpser An rAn k))).
  exact None.
 destruct (interp_side_equa_in_R3 b rho) as [f |].
   exact (Some (- f)%F).
   exact None.
 destruct (interp_side_equa_in_R3 b1 rho) as [f |].
   destruct (interp_side_equa_in_R3 b2 rho) as [g |].
     exact (Some (f + g)%F).
     exact None.
   exact None.
Defined.

Definition Invalid_context := False.

Definition interp {A B : Type} (e : diff_equa) (rho : list A)
  (f : side_equa -> list A -> option B) (P : B -> B -> Prop) :=
let (s1, s2) := e in
match (f s1 rho), (f s2 rho) with
  | Some b1, Some b2 => P b1 b2
  | _, _ => Invalid_context
end.

Implicit Arguments interp[A B].

Definition interp_in_R (e : diff_equa) (rho : list (sigT Cn)) : Prop :=
  interp e rho interp_side_equa_in_R Rfun_eq.

Definition interp_in_R2 (e : diff_equa) (rho : list Cinfty) : Prop :=
  interp e rho interp_side_equa_in_R2 Rfun_eq.

Definition interp_in_R3 (e : diff_equa) (rho : list (sigT infinite_cv_radius)) : Prop :=
  interp e rho interp_side_equa_in_R3 Rfun_eq.

Definition interp_in_N (e : diff_equa) (rho : list Rseq) : Prop :=
  interp e rho interp_side_equa_in_N Rseq_eq.

Definition interp_in_SN (e : diff_equa) (rho : list Rseq) : Prop :=
  interp e rho interp_side_equa_in_SN (fun un vn => forall (n : nat) (x : R), un n x = vn n x).

Delimit Scope de_scope with de.

(* Automatically open scope C_scope for arguments of type C *)
Bind Scope de_scope with diff_equa.

Open Scope de_scope.

Notation "`c k" := (cst k) (at level 40) : de_scope.
Notation "- y" := (opp y) : de_scope.
Infix "+" := plus : de_scope.
Infix "-" := minus : de_scope.

Notation "[| e |]R" := (interp_in_R e%de) (at level 69).
Notation "[| e |]R2" := (interp_in_R2 e%de) (at level 69).
Notation "[| e |]R3" := (interp_in_R3 e%de) (at level 69).
Notation "[| e |]N" := (interp_in_N e%de) (at level 69).
Notation "[| e |]SN" := (interp_in_SN e%de) (at level 69).
