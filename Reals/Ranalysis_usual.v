Require Import Rbase Ranalysis Rfunctions Rfunction_def.
Require Import MyRIneq.
Require Import Ranalysis_def Ranalysis_def_simpl Ranalysis_facts.

Local Open Scope R_scope.

(** * Derivability (thus continuity) of usual functions. *)

(** * Identity *)

Lemma derivable_pt_lim_in_id: forall D x,
  derivable_pt_lim_in id D x 1.
Proof.
intros D x eps eps_pos ; exists eps ; intros ; split.
 assumption.
 intros y [[_ Hneq] _] ; unfold growth_rate, id ; simpl.
  apply Rle_lt_trans with (Rabs 0) ; [| rewrite Rabs_R0 ; assumption].
  right ; apply Rabs_eq_compat ; field ; apply Rminus_eq_contra ;
  symmetry ; assumption.
Qed.

Lemma derivable_pt_in_id: forall (D : R -> Prop) (x : R),
  derivable_pt_in id D x.
Proof.
intros ; eexists ; eapply derivable_pt_lim_in_id.
Qed.

Lemma derivable_in_id: forall (D : R -> Prop),
  derivable_in id D.
Proof.
intros D x x_in ; eapply derivable_pt_in_id.
Qed.

(** Powers *)

Definition Dpow (n : nat) := match n with
  | O   => fun _ => 0
  | S m => fun x => (INR (S m)) * pow x m
end.

(*
Lemma derivable_pt_lim_in_pow: forall D x n,
  derivable_pt_lim_in (fun x => pow x n) D x (Dpow n x).
Proof.
intros D x n ; induction n.
 eapply derivable_pt_lim_in_ext with (fun _ => 1).
  intro ; reflexivity.
  apply derivable_pt_lim_in_const.
 eapply derivable_pt_lim_in_ext with (id * (fun x => pow x n))%F.
  intro ; reflexivity.
*)

(** Monomials *)

(** Inverse *)

(** Negative powers *)