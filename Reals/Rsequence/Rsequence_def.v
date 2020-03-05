(*
(C) Copyright 2010, COQTAIL team

Project Info: http://sourceforge.net/projects/coqtail/

This library is free software; you can redistribute it and/or modify it
under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation; either version 2.1 of the License, or
(at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301,
USA.
*)

(** Common definitions of real sequences. *)
Require Export Reals.

Declare Scope Rseq_scope.
Delimit Scope Rseq_scope with Rseq.

Local Open Scope R_scope.
Local Open Scope Rseq_scope.

Definition Rseq := nat -> R.

Bind Scope Rseq_scope with Rseq.

Implicit Type n : nat.
Implicit Type r : R.
Implicit Type Un Vn : Rseq.

(** * Morphism of functions on R to sequences. *)

Definition Rseq_constant r := (fun n => r).

Coercion Rseq_constant : R >-> Funclass.

Definition Rseq_plus Un Vn n := Un n + Vn n.
Definition Rseq_mult Un Vn n := Un n * Vn n.
Definition Rseq_opp Un n := Ropp (Un n).
Definition Rseq_inv Un n := Rinv (Un n).
Definition Rseq_sum := sum_f_R0.
Definition Rseq_prod Un Vn n := Rseq_sum (Rseq_mult Un (fun p => Vn (n - p)%nat)) n.

Infix "+" := Rseq_plus : Rseq_scope.
Infix "*" := Rseq_mult : Rseq_scope.
Infix "#" := Rseq_prod (at level 65) : Rseq_scope.
Notation "- u" := (Rseq_opp u) : Rseq_scope.
Notation "/ u" := (Rseq_inv u) : Rseq_scope.

Definition Rseq_minus Un Vn n := Un n - Vn n.
Definition Rseq_div Un Vn n := Un n / Vn n.
Definition Rseq_abs Un n := Rabs (Un n).

Notation "'|' Un '|'" := (Rseq_abs Un) (at level 39, format "'|' Un '|'") : Rseq_scope.
Infix "-" := Rseq_minus : Rseq_scope.
Infix "/" := Rseq_div : Rseq_scope.

Definition Rseq_shift Un n := Un (S n).
Definition Rseq_shifts Un N n := Un (N + n)%nat.

(* TODO : Caser ça où ça doit aller *)

Lemma n_modulo_2 : forall n:nat, {p | (n = 2 * p)%nat} + {p | n = S (2 * p)}.
Proof.
intro n ; induction n.
 left ; exists O ; intuition.
 case IHn ; intro H ; destruct H as (p,Hp) ;
 [right ; exists p | left ; exists (S p)] ; intuition; rewrite Hp; simpl; eauto with *.
Qed.

Definition Rseq_zip Un Vn n := match n_modulo_2 n with
| inl (exist _ p _) => Un p
| inr (exist _ p _) => Vn p
end.

(** * Extensionnal equality. *)

Definition Rseq_eq (Un Vn : Rseq) := forall n, Un n = Vn n.

Infix "==" := Rseq_eq (at level 70, no associativity) : Rseq_scope.

(** * Various properties. *)

Definition Rseq_eventually (P : Rseq -> Prop) (Un : Rseq) :=
  exists N, P (Rseq_shifts Un N).

Definition Rseq_eventually2 (P : Rseq -> Rseq -> Prop) (Un Vn : Rseq) :=
  exists N, P (Rseq_shifts Un N) (Rseq_shifts Vn N).

Definition Rseq_neq_0 Un := forall n, Un n <> 0.

Definition Rseq_growing Un := forall n,  Un n <= Un (S n).

Definition Rseq_strictly_growing Un := forall n, Un n < Un (S n).

Definition Rseq_decreasing Un := forall n, Un (S n) <= Un n.

Definition Rseq_strictly_decreasing Un := forall n, Un (S n) < Un n.

Definition Rseq_bound_max Un M := forall n, Un n <= M.

Definition Rseq_bound_min Un m := forall n, m <= Un n.

Definition Rseq_bound Un M := forall n, Rabs (Un n) <= M.

Definition Rseq_le Un Vn := forall n, Un n <= Vn n.

(** * Convergence of sequences. *)

Definition Rseq_cv Un l :=
  forall eps,
    eps > 0 ->
    exists N, (forall n, (n >= N)%nat -> R_dist (Un n) l < eps).

Definition Rseq_cv_pos_infty Un :=
  forall M,
    exists N, forall n, (n >= N)%nat -> M < Un n.

Definition Rseq_cv_neg_infty Un :=
  forall M,
    exists N, forall n, (n >= N)%nat -> Un n < M.

(** * Landau relations on sequences. *)

Definition Rseq_big_O Un Vn :=
  exists K, K >= 0 /\ exists N, forall n, (n >= N)%nat -> Rabs (Un n) <= K * Rabs (Vn n).

Definition Rseq_little_O Un Vn :=
  forall eps, eps > 0 -> exists N, forall n, (n >= N)%nat -> Rabs (Un n) <= eps * Rabs (Vn n).

Definition Rseq_equiv Un Vn := Rseq_little_O (Un - Vn) Un.

Notation "Un = 'O' ( Vn )" := (Rseq_big_O Un Vn) (at level 39, format "Un  =  'O' ( Vn )") : Rseq_scope.
Notation "Un = 'o' ( Vn )" := (Rseq_little_O Un Vn) (at level 40, format "Un  =  'o' ( Vn )") : Rseq_scope.
Notation "Un ~ Vn" := (Rseq_equiv Un Vn) (at level 5) : Rseq_scope.
(** printing ~	~ *)
(** * Usual sequences. *)

Definition Rseq_poly d n := (INR n) ^ d.

Definition Rseq_inv_poly d n :=
match n with
  | 0 => 0
  | _ => (/ INR n) ^ d
end.

Definition Rseq_pow r n := r ^ n.

Definition Rseq_alt := Rseq_mult (Rseq_pow (- 1)).
Definition Rseq_fact n := INR (fact n).

Create HintDb Rseq.
