Require Import Reals.
Require Import Rpser_def Rpser_sums Rpser_usual Rpser_derivative.
Require Import Rfunction_classes.
Require Import Nth_derivative_def.
Require Import Rfunction_def Functions.
Require Import Rsequence_def.
Require Import List.
Require Import Option.

Local Open Scope Rseq_scope.

(* This file defines the differential equations and their
 interpretation as propositions. *)

Inductive side_equa : Set :=
    | cst  : forall (r : R), side_equa
    | scal : forall (r : R) (s : side_equa), side_equa
    | y    : forall (p : nat) (k : nat) (a : R), side_equa
    | opp  : forall (s1 : side_equa), side_equa
    | min  : forall (s1 s2 : side_equa), side_equa
    | plus : forall (s1 s2 : side_equa), side_equa
    | mult : forall (s1 s2 : side_equa), side_equa.

Definition diff_equa : Set := prod (side_equa) (side_equa).

Fixpoint interp_side_equa_in_N s (rho : list Rseq) : option Rseq :=
match s with
  | cst r      => Return (constant_seq r)
  | scal r e   => Bind (interp_side_equa_in_N e rho) (fun un => Return (r * un))
  | y i k a    => Bind (nth_error rho i) (fun un => Return (An_expand (An_nth_deriv un k) a))
  | opp e      => Bind (interp_side_equa_in_N e rho) (fun un => Return (- un))
  | min e1 e2  => Bind (interp_side_equa_in_N e1 rho) (fun un =>
                  Bind (interp_side_equa_in_N e2 rho) (fun vn => Return (un - vn)))
  | plus e1 e2 => Bind (interp_side_equa_in_N e1 rho) (fun un =>
                  Bind (interp_side_equa_in_N e2 rho) (fun vn => Return (un + vn)))
  | mult e1 e2 => Bind (interp_side_equa_in_N e1 rho) (fun un =>
                  Bind (interp_side_equa_in_N e2 rho) (fun vn => Return (un # vn)))
end.

Fixpoint interp_side_equa_in_R s (rho : list (sigT infinite_cv_radius)) : option (R -> R) :=
match s with
  | cst r      => Return (fun _ => r)
  | scal r e   => Bind (interp_side_equa_in_R e rho) (fun f => Return ((fun _ => r) * f)%F)
  | y i k a    => Bind (nth_error rho i) (fun f => Return (fun x => nth_derive (sum (projT1 f) (projT2 f))
                 (D_infty_Rpser (projT1 f) (projT2 f) k) (a * x)%R))
  | opp e      => Bind (interp_side_equa_in_R e rho) (fun f => Return (- f)%F)
  | min e1 e2  => Bind (interp_side_equa_in_R e1 rho) (fun f =>
                  Bind (interp_side_equa_in_R e2 rho) (fun g => Return (f - g)%F))
  | plus e1 e2 => Bind (interp_side_equa_in_R e1 rho) (fun f =>
                  Bind (interp_side_equa_in_R e2 rho) (fun g => Return (f + g)%F))
  | mult e1 e2 => Bind (interp_side_equa_in_R e1 rho) (fun f =>
                  Bind (interp_side_equa_in_R e2 rho) (fun g => Return (f * g)%F))
end.

Definition Invalid_context := False.

Definition interp {A B : Type} (e : diff_equa) (rho : list A)
  (f : side_equa -> list A -> option B) (P : B -> B -> Prop) :=
let (s1, s2) := e in
match (f s1 rho), (f s2 rho) with
  | Some b1, Some b2 => P b1 b2
  | _, _ => Invalid_context
end.

Definition interp_in_N e rho : Prop :=
  interp e rho interp_side_equa_in_N Rseq_eq.

Definition interp_in_R e rho : Prop :=
  interp e rho interp_side_equa_in_R Rfun_eq.

Declare Scope de_scope.
Delimit Scope de_scope with de.

(* Automatically open scope de_scope for arguments of type diff_equa *)
Bind Scope de_scope with diff_equa.
Bind Scope de_scope with side_equa.

Open Scope de_scope.

Notation "`c k" := (cst k) (at level 40) : de_scope.
Notation "- y" := (opp y) : de_scope.
(* Infix "*" := scal : de_scope. *)
Infix "+" := plus : de_scope.
Infix "*" := plus : de_scope.
Infix "-" := min : de_scope.
Infix ":=:" := (@pair side_equa side_equa) (at level 50): de_scope.

Notation "[| e |]N" := (interp_in_N e%de) (at level 69).
Notation "[| e |]R" := (interp_in_R e%de) (at level 69).
