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

Require Import Rsequence_def.
Require Import Rsequence_facts.
Require Import Rseries_def.
(* Require Import Rseries_facts. *)
Require Export Reals.
Require Import Lra.

Local Open Scope Rseq_scope.
(** printing ~	~ *)
(** * A tactic that constructs the limit of a sequence and the proof that this
 limit is exact *)

Ltac neq := fun n =>
  match goal with
    | id : (n <> 0)%R |- _ => id
    | id : (n > 0) |- _ => constr: (Rgt_not_eq _ _ id)
    | id : (n < 0) |- _ => constr: (Rlt_not_eq _ _ id)
    | _ =>
      match n with
      | Rabs ?a =>
        let H := neq a in constr: (Rabs_no_R0 _ H)
      end
  end.


Ltac rseq_fold Un := match Un with
    | ?Vn ?c ?Wn => let Vn' := rseq_fold Vn in let Wn' := rseq_fold Wn in constr:(Vn' c Wn')
    | fun x : nat => ?Vn x => rseq_fold Vn
    | fun x : nat => (?Vn + ?Wn)%R => idtac "bla"
    (*| fun x : nat => - ?Vn x => let Vn' := (rseq_fold Vn) in constr: (-Vn')
    | fun x : nat => / ?Vn x => let Vn' := (rseq_fold Vn) in constr: (/Vn')
    | fun x : nat => ?Vn => constr:(fun x => O)
    | fun x : nat => (?Vn x + ?Wn x)%R => 
        let Vn' := rseq_fold Vn in let Wn' := rseq_fold Wn in constr:(Vn' + Wn')
    | fun x : nat => (?Vn x - ?Wn x)%R => 
        let Vn' := rseq_fold Vn in let Wn' := rseq_fold Wn in constr:(Vn' - Wn')
    | fun x : nat => (?Vn x * ?Wn x)%R => 
        let Vn' := rseq_fold Vn in let Wn' := rseq_fold Wn in constr:(Vn' * Wn')
    | fun x : nat => (?Vn x / ?Wn x)%R => 
        let Vn' := rseq_fold Vn in let Wn' := rseq_fold Wn in constr:(Vn' / Wn')*)
    | _ => Un
end.

Ltac rseq_lim := fun Un => match goal with
(** Case 1: there exists a proof that the sequence converges in the hypothesis *)
    | id : Rseq_cv Un ?l |- _ => id
    | id : Rseq_cv_pos_infty Un |- _ => id
    | id : Rseq_cv_neg_infty Un |- _ => id
    | _ => 
(** Case 2:  we have to deconstruct the sequence to infer the limit *)
    match Un with
      (* constant *)
      | (Rseq_constant ?a) => constr:(Rseq_constant_cv a)
(* inverse *)
      | (/ ?Vn) =>
        let H1 := rseq_lim Vn in
        match type of H1 with
          | Rseq_cv Vn ?l => (* todo : l = 0*)
            let H2 := neq l in
            constr:(Rseq_cv_inv_compat _ _ H1 H2) 
          | Rseq_cv_pos_infty Vn =>
            constr:(Rseq_cv_pos_infty_inv_compat _ H1)
          | Rseq_cv_neg_infty Vn =>
            constr:(Rseq_cv_neg_infty_inv_compat _ H1) end
(* division *)
      | (?Vn/ ?Wn) =>
        let H1 := rseq_lim Vn in
        let H2 := rseq_lim Wn in
        match type of H1 with
          | Rseq_cv Vn ?lv  => match type of H2 with 
              | (Rseq_cv Wn ?lw) => (* todo : l = 0 *)
                let H3 := neq lw in constr:(Rseq_cv_div_compat _ _ _ _ H1 H2 H3) 
              | Rseq_cv_pos_infty Wn => 
                constr:(Rseq_cv_pos_infty_div_compat _ _ _ H2 H1)
              | Rseq_cv_neg_infty Wn => 
                constr:(Rseq_cv_neg_infty_div_compat _ _ _ H2 H1) end
         (* | Rseq_cv_pos_infty Vn => fail "todo" 
          | Rseq_cv_neg_infty Vn => fail "todo" *) end
(* opposite *)
      | (- ?Vn) =>
        let H1 := rseq_lim Vn in
        match type of H1 with 
          | Rseq_cv Vn ?l => constr:(Rseq_cv_opp_compat _ _ H1)
          | Rseq_cv_pos_infty Vn => constr:(Rseq_cv_pos_infty_opp_compat _ H1) 
          | Rseq_cv_neg_infty Vn => constr:(Rseq_cv_neg_infty_opp_compat _ H1) end
(* sum *)
      | (?Vn + ?Wn) =>
        let H1 := rseq_lim Vn in
        let H2 := rseq_lim Wn in
        match type of H1 with
          | Rseq_cv Vn ?lv  => match type of H2 with 
              | Rseq_cv _ ?lw => constr:(Rseq_cv_plus_compat _ _ _ _  H1 H2) 
              | Rseq_cv_pos_infty _ => constr:(Rseq_cv_finite_plus_pos_infty_r _ _ _ H1 H2)
              | Rseq_cv_neg_infty _ => constr:(Rseq_cv_finite_plus_neg_infty_r _ _ _ H1 H2) end
          | Rseq_cv_pos_infty Vn => match type of H2 with 
              | Rseq_cv _ ?lw => constr:(Rseq_cv_finite_plus_pos_infty_l _ _ _ H2 H1)
              | Rseq_cv_pos_infty _ => constr:(Rseq_cv_pos_infty_plus_compat _ _ H1 H2) end
              (* | Rseq_cv_neg_infty Wn =>  undertemined form *) 
          | Rseq_cv_neg_infty Vn => match type of H2 with 
              | Rseq_cv _ ?lw => constr:(Rseq_cv_finite_plus_neg_infty_l _ _ _ H2 H1)
              | Rseq_cv_neg_infty _ => constr:(Rseq_cv_neg_infty_plus_compat _ _ H1 H2)
              (* | Rseq_cv_pos_infty Wn =>  undertemined form *) end
              end
(* difference *)
      | (?Vn - ?Wn) =>
        let H1 := rseq_lim Vn in
        let H2 := rseq_lim Wn in
        match type of H1 with
          | Rseq_cv Vn ?lv  => match type of H2 with 
              | (Rseq_cv Wn ?lw) => constr:(Rseq_cv_minus_compat _ _ _ _  H1 H2) 
              | Rseq_cv_pos_infty Wn => constr:(Rseq_cv_finite_minus_pos_infty _ _ _ H1 H2)
              | Rseq_cv_neg_infty Wn => constr:(Rseq_cv_finite_plus_neg_infty_r _ _ _ H1 H2) end
          | Rseq_cv_pos_infty Vn => match type of H2 with 
              | (Rseq_cv Wn ?lw) => constr:(Rseq_cv_finite_minus_pos_infty _ _ _ H2 H1)
              (*| Rseq_cv_pos_infty Wn => undertemined form *)
              | Rseq_cv_neg_infty Wn => constr:(Rseq_cv_pos_minus_neg_infty _ _ H1 H2)  end
          | Rseq_cv_neg_infty Vn => match type of H2 with 
              | (Rseq_cv Wn ?lw) => constr:(Rseq_cv_finite_minus_neg_infty _ _ _ H2 H1)
              | Rseq_cv_pos_infty Wn => constr:(Rseq_cv_neg_minus_pos_infty _ _ H1 H2) end
              (* | Rseq_cv_neg_infty Wn =>  undertemined form *) 
              end
(* product *)
      | (?Vn * ?Wn) =>
        let H1 := rseq_lim Vn in
        let H2 := rseq_lim Wn in
        match type of H1 with
          | Rseq_cv Vn ?lv  => match type of H2 with 
              | (Rseq_cv Wn ?lw) => constr:(Rseq_cv_mult_compat _ _ _ _ H1 H2)
      (* TODO        | Rseq_cv_pos_infty Wn => constr:(Rseq_cv_pos_pos_infty_mult _ _ H1 H2)
              | Rseq_cv_neg_infty Wn => constr:(Rseq_cv_pos_neg_infty_mult _ _ H1 H2)  *) end
          | Rseq_cv_pos_infty Vn => match type of H2 with 
(* TODO              | (Rseq_cv Wn ?lw) => constr:(Rseq_cv_finite_minus_pos_infty _ _ _ H2 H1) *)
              | Rseq_cv_pos_infty Wn => constr:(Rseq_cv_pos_pos_infty_mult _ _ H1 H2)
              | Rseq_cv_neg_infty Wn => constr:(Rseq_cv_pos_neg_infty_mult _ _ H1 H2)  end
          | Rseq_cv_neg_infty Vn => match type of H2 with 
(* TODO              | (Rseq_cv Wn ?lw) => constr:(Rseq_cv_finite_minus_neg_infty _ _ _ H2 H1) *)
              | Rseq_cv_pos_infty Wn => constr:(Rseq_cv_neg_pos_infty_mult _ _ H1 H2) end
              | Rseq_cv_neg_infty Wn => constr:(Rseq_cv_neg_neg_infty_mult _ _ H1 H2)
              end

(* absolute value *)
      | |?Vn| =>
        let H := rseq_lim Vn in fail
(*         match type of H with *)
(*           | Rseq_cv Vn ?l => constr:(Rseq_cv_abs_compat _ _ H) *)
(*           |Rseq_cv_pos_infty Vn => constr:(Rseq_cv_abs_pos_infty _ H) *)
(*           |Rseq_cv_neg_infty Vn => constr:(Rseq_cv_abs_neg_infty _ H) *)
(*         end *)
  end
end.

Ltac rser_lim := fun Un => match goal with
    | id : Rser_cv Un ?l |- _ => id
    | id : Rser_cv_pos_infty Un |- _ => id
    | id : Rser_cv_neg_infty Un |- _ => id
    | _ =>     match Un with
        | _ => idtac
 end
end.
(* TODO *)

Ltac rseq_cv_construct := intros; match goal with
    | |- {l | Rseq_cv ?Un l} =>
      let H := rseq_lim Un in
      match type of H with
        | Rseq_cv _ ?l => exists l ; apply H
      end
    | |- {l | Rser_cv ?Un l} =>
      let H := rser_lim Un in
      match type of H with
        | Rser_cv _ ?l => exists l ; apply H
      end
    | |- Rseq_cv ?Un ?l =>
      let H := rseq_lim Un in
      match type of H with
        | Rseq_cv _ ?l' => replace l with l' ; [apply H | subst; try reflexivity; try field; intuition]
      end
    | |- Rser_cv ?Un ?l =>
      let H := rser_lim Un in
      match type of H with
        | Rser_cv _ ?l' => replace l with l' ; [apply H | subst; try reflexivity; try field; intuition]
      end
    | |- Rseq_cv_pos_infty ?Un => let H := rseq_lim Un in apply H
    | |- Rseq_cv_neg_infty ?Un => let H := rseq_lim Un in apply H
end.

(*
 Section Examples_infer.

Variables Un Vn Wn Xn Yn : nat -> R.
Variables u v w : R.
Hypothesis HUn : Rseq_cv Un u.
Hypothesis HVn : Rseq_cv Vn v.
Hypothesis HWn : Rseq_cv Wn w.
Hypothesis HXn : Rseq_cv_pos_infty Xn .
Hypothesis HYn : Rseq_cv_neg_infty Yn. 

Example tamer : Rseq_cv ((1 - Un) * Vn) (v - u * v).
Proof.
rseq_cv_construct.
Qed.
*)

(* Example test : { l | Rseq_cv (fun n => Un n) l}. *)
(* Proof. *)
(* rseq_cv_construct. *)
(* Qed. *)

(* Example tutu : forall a c d x : R, *)
(*    a <> 0 -> *)
(*    d <> 0 -> *)
(*    c < -5 -> *)
(*    x = (u * a + - v * - w)%R -> Rseq_cv (Un * Un + (Vn) * (Wn)+6) (u*u+v*w+6). *)
(* Proof. *)
(* rseq_cv_construct. *)
(* Qed. *)

(* End Examples_infer. *)

