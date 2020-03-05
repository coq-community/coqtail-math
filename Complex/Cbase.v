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

Require Export Cdefinitions.

(* begin hide *)
Lemma Req_or_neq : forall (x:R), {x = 0%R}+{x<>0%R}.
Proof.
intro x.
case (Rgt_ge_dec x 0) ; intro H1.
right ; intro Hfalse ; rewrite Hfalse in H1 ; apply False_ind ; lra.
case (Rle_lt_or_eq_dec x 0).
intuition.
clear H1 ; intro H1 ; right ; intro Hfalse ; rewrite Hfalse in H1 ; apply False_ind ; lra.
intro H ; left ; assumption.
Qed.
(* end hide *)

(** * Complex to real lemmas. *)
Lemma Cproj_right : forall z1 : C, (Cre z1, Cim z1) = z1.
Proof.
intros z1 ; elim z1 ; reflexivity.
Qed.

Lemma Ceq : forall z1 z2 : C, Cre z1 = Cre z2 /\ Cim z1 = Cim z2 <-> z1 = z2.
Proof.
intros z1 z2 ; split ; intro H.
 rewrite <- Cproj_right ; symmetry ; rewrite <- Cproj_right ; destruct H as (H, H0) ;
 rewrite H ; rewrite H0 ; reflexivity.
 split; rewrite H; reflexivity.
Qed.

(** Simple tactics using the projections *)

Ltac CusingR_simpl :=
rewrite <- Ceq ; simpl ; split.

Ltac CusingR_rec := match goal with
     | id:C |- _ => destruct id ; try CusingR_rec
end.

Ltac CusingR := intros; try CusingR_rec ; apply (proj1 (Ceq _ _)) ; split ; simpl ; auto with real.

Ltac CusingR_f := CusingR ; field.

(* begin hide *)
(* Annex tactic that should not be used *)
Ltac CusingRR :=  try rewrite <- Ceq in * .

Ltac CusingR_rec1 := unfold not in *;
match goal with
(* destruct complex *)
     | id:C |- _ => destruct id ; CusingRR ; try CusingR_rec1
(* logical destruct in goal *)
     | id: _|- _ -> _ => intros ; CusingRR ; try CusingR_rec1
     | id: _|- _ /\ _ => split ; CusingRR ; try CusingR_rec1
     | id: _ /\ _ |- _ => destruct id ; CusingRR ; try CusingR_rec1
     | id: _ \/ _ |- _ => destruct id ; CusingRR ; try CusingR_rec1
(* false*)
     | id: _ |- False => (apply id ; CusingR1) 
(* si le apply id echoue on continue le matching sur les clauses*) 

(* le ou a la fin sinon c'est galere*)
     | id: _|- _ \/ _ => try ((left ; CusingR1 ; fail) || (right ; CusingR1 ; fail)) ;
CusingRR ; simpl in *
     | _ => simpl in *
end
with
CusingR1 := intros ; CusingRR ; CusingR_rec1 ; subst ; intuition ;
try ((lra || (field ; CusingR1))).
(* end hide *)

(** * Field Lemmas. *)

Lemma C0_neq_R0_neq : forall z, z <> 0 <-> (Cre z <> 0%R \/ Cim z <> 0%R).
Proof.
intro z ; split ; intro H.
 destruct z as (a,b) ; case (Req_or_neq a) ; case (Req_or_neq b) ; intros Ha Hb.
  elim H ; rewrite Ha, Hb ; reflexivity.
  right ; intuition.
  left ; intuition.
  left ; intuition.
  intro Hf ; destruct H ; apply H ; rewrite Hf ; intuition.
Qed.
Hint Resolve C0_neq_R0_neq : complex.

Lemma HintC0_neq_R0_neq : forall z, (Cre z <> 0%R \/ Cim z <> 0%R) -> z <> 0.
Proof.
intros z. apply <- C0_neq_R0_neq.
Qed.
Hint Resolve HintC0_neq_R0_neq : complex.

Lemma C0_norm_R0 : forall z, z = 0 <-> Cnorm_sqr z = 0%R.
Proof.
intro z ; unfold Cnorm_sqr ; split ; intro Hrew.
 destruct (proj2 (Ceq z 0) Hrew) as (H1, H2) ; destruct z as (r1,r2);
 simpl in * ; rewrite H1 ; rewrite H2 ; field.
 apply (proj1 (Ceq _ _)) ; split.
  apply Rsqr_0_uniq.
  apply Rplus_eq_0_l with ((Cim z)²)%R ; [apply Rle_0_sqr | apply Rle_0_sqr |].
  unfold Rsqr.
  assumption.
  destruct z as (a,b) ; intuition. simpl in *.
 apply Rsqr_0_uniq.
 apply Rplus_eq_0_l with ((a)²)%R ; [apply Rle_0_sqr | apply Rle_0_sqr |].
 unfold Rsqr.
 rewrite Rplus_comm.
 assumption.
Qed.
Hint Resolve C0_norm_R0 : complex.

Lemma HC0_norm_R0 : forall z, Cnorm_sqr z = 0%R -> z = 0.
Proof.
intros. apply <- C0_norm_R0. assumption.
Qed.
Hint Resolve HC0_norm_R0 : complex.


(** Cre / Cim compatibility with simple operators *)

Lemma Cre_simpl : forall (a b : R), Cre (a +i b) = a.
Proof.
intros ; reflexivity.
Qed.

Lemma Cim_simpl : forall (a b : R), Cim (a +i b) = b.
Proof.
intros ; reflexivity.
Qed.

Lemma Cre_opp_compat : forall z, (- Cre z = Cre (-z))%R.
Proof.
intro z ; destruct z ; reflexivity.
Qed.

Lemma Cim_opp_compat : forall z, (- Cim z = Cim (-z))%R.
intro z ; destruct z ; reflexivity.
Qed.

Lemma Cre_add_compat : forall z1 z2, (Cre z1 + Cre z2 = Cre (z1 + z2))%R.
Proof.
intros z1 z2 ; destruct z1 ; destruct z2 ; reflexivity.
Qed.

Lemma Cim_add_compat : forall z1 z2, (Cim z1 + Cim z2 = Cim (z1 + z2))%R.
Proof.
intros z1 z2 ; destruct z1 ; destruct z2 ; reflexivity.
Qed.

Lemma Cre_minus_compat : forall z1 z2, (Cre z1 - Cre z2 = Cre (z1 - z2))%R.
Proof.
intros z1 z2 ; destruct z1 ; destruct z2 ; reflexivity.
Qed.

Lemma Cim_minus_compat : forall z1 z2, (Cim z1 - Cim z2 = Cim (z1 - z2))%R.
Proof.
intros z1 z2 ; destruct z1 ; destruct z2 ; reflexivity.
Qed.

Lemma Cre_scal_compat : forall z l, (Cre (l `* z) = l * Cre z)%R.
Proof.
intros z l ; destruct z ; reflexivity.
Qed.

Lemma Cim_scal_compat : forall z l, (Cim (l `* z) = l * Cim z)%R.
Proof.
intros z l ; destruct z ; reflexivity.
Qed.

Lemma Cre_eq_compat : forall z1 z2, z1 = z2 -> Cre z1 = Cre z2.
Proof.
intros a b H ; rewrite H ; reflexivity.
Qed.

Lemma Cim_eq_compat : forall z1 z2, z1 = z2 -> Cim z1 = Cim z2.
Proof.
intros a b H ; rewrite H ; reflexivity.
Qed.


(**  Addition. *)

Lemma Cadd_comm : forall z1 z2 : C, z1 + z2 = z2 + z1.
Proof.
CusingR.
Qed.
Hint Resolve Cadd_comm : complex.

Lemma Cadd_assoc : forall a b c : C, a + b + c = a + (b + c).
Proof.
CusingR.
Qed.
Hint Resolve Cadd_assoc : complex.

Lemma Cadd_0_l : forall z : C, 0 + z = z.
Proof.
CusingR.
Qed.
Hint Resolve Cadd_0_l : complex.

Lemma Cadd_0_r : forall z : C, z + 0 = z.
Proof.
CusingR.
Qed.
Hint Resolve Cadd_0_r : complex.

Lemma Cadd_opp_r : forall z : C, z + - z = 0.
Proof.
CusingR.
Qed.
Hint Resolve Cadd_opp_r : complex.

Lemma Cadd_opp_l : forall z : C, - z + z = 0.
Proof.
CusingR.
Qed.
Hint Resolve Cadd_opp_l : complex.

(** Opposite *)

Lemma Copp_invol : forall z, --z = z.
Proof.
CusingR.
Qed.
Hint Resolve Copp_invol : complex.

(** Minus *)

Lemma Copp_add_distr : forall z z', - (z + z') = -z - z'.
Proof.
CusingR_f.
Qed.
Hint Resolve Copp_add_distr : complex.

Lemma Copp_minus_distr : forall z z', - (z - z') = - z + z'.
Proof.
CusingR_f.
Qed.
Hint Resolve Copp_minus_distr : complex.

Lemma Cminus_antisym : forall z z', (z - z') = - (z' - z).
Proof.
CusingR_f.
Qed.
Hint Resolve Cminus_antisym : complex.

(**  Multiplication. *)
Lemma Cmult_comm : forall z1 z2 : C, z1 * z2 = z2 * z1.
Proof.
CusingR_f.
Qed.
Hint Resolve Cmult_comm : complex.

Lemma Cmult_assoc : forall z1 z2 z3 : C, z1 * z2 * z3 = z1 * (z2 * z3).
Proof.
CusingR_f.
Qed.
Hint Resolve Cmult_assoc : complex.

Lemma Cmult_1_l : forall z : C, 1 * z = z .
Proof.
CusingR_f.
Qed.
Hint Resolve Cmult_1_l : complex.

Lemma Cmult_1_r : forall z : C, z * 1= z .
Proof.
CusingR_f.
Qed.
Hint Resolve Cmult_1_r : complex.

Lemma Cinv_rew : forall a b : R, (a +i b) <> 0 -> /(a +i b) = (/ (a^2 + b^2)) `* (a +i - b)%R.
Proof.
intros a b ; simpl.
 destruct (C0_norm_R0 (a, b)).
 CusingR_f ; intuition.
Qed.

(** Division/Inverse *)

Lemma Cinv_l : forall z : C, z <> C0 -> / z * z = 1.
Proof.
intros z z_neq ; destruct z as (r, r0) ; apply (proj1 (Ceq _ _)) ; split ;
 compute.
 replace (r * / (r * r + r0 * r0) * r + - (- r0 * / (r * r + r0 * r0) * r0))%R with
     (((r * r) + - (- r0 * r0)) / (r * r + r0 * r0))%R.
 unfold Rdiv ; replace (- (- r0 * r0))%R with (r0 * r0)%R by field.
 apply Rinv_r. intro Hyp ; apply z_neq.
 apply (proj2 (C0_norm_R0 _)) ; unfold Cnorm_sqr ; intuition.
 field.
 replace (r * r + r0 * r0)%R with (Cnorm_sqr (r +i r0)).
 intro H ; apply z_neq ; apply (proj2 (C0_norm_R0 _) H).
 unfold Cnorm_sqr ; intuition.
 field.
 replace (r * r + r0 * r0)%R with (Cnorm_sqr (r +i r0)).
 intro H ; apply z_neq ; apply (proj2 (C0_norm_R0 _) H).
 unfold Cnorm_sqr ; intuition.
Qed.
Hint Resolve Cinv_l : complex.

Lemma Cinv_r : forall z:C, z <> C0 -> z * /z = 1.
Proof.
intros ; rewrite Cmult_comm ; apply Cinv_l ; assumption.
Qed.
Hint Resolve Cinv_r : complex.


(** Distributivity *)

Lemma Cmult_add_distr_l : forall z1 z2 z3 : C, z1 * (z2 + z3) = z1 * z2 + z1 * z3.
Proof.
CusingR_f.
Qed.
Hint Resolve Cmult_add_distr_l : complex.

Lemma Cmult_add_distr_r : forall z1 z2 z3 : C,  (z2 + z3) * z1= z2 * z1 + z3 * z1.
Proof.
CusingR_f.
Qed.
Hint Resolve Cmult_add_distr_r : complex.

(** 1 <> 0 *)
Lemma C1_neq_C0 : 1 <> 0.
Proof.
intro H ; apply (proj2 (Ceq _ _)) in H ; destruct H as (H, H0); compute in H ;
 apply R1_neq_R0 ; assumption.
Qed.
Hint Resolve C1_neq_C0 : complex.


(** * R Vector Space Lemmas *)

Lemma Cscal_1 : forall z : C, 1%R `* z = z.
Proof.
intro ; CusingR.
Qed.

Lemma Cscal_distr_C_l : forall x, forall u v, x `* (u + v) = x `* u + x `* v.
Proof.
CusingR.
Qed.

Lemma Cscal_distr_R_r : forall x y : R, forall z : C, (x + y)%R `* z = x `* z + y `* z.
Proof.
CusingR_f.
Qed.

Lemma Cscal_assoc : forall x y : R, forall z : C, (x * y)%R `* z = x `* (y `* z).
Proof.
CusingR_f.
Qed.

Lemma Crev_distr : forall x : R, forall u v : C, x `* (u + v) = x `* u + x `* v.
Proof.
CusingR.
Qed.


(** * Other properties (Cconj) *)
Lemma Cadd_conj : forall z : C, z + Cconj z = (C1 + C1) * (Cre z +i 0%R).
Proof.
CusingR_f.
Qed.

Lemma Cminus_conj : forall z : C, z - Cconj z = (C1 + C1) * (0%R +i Cim z).
Proof.
CusingR_f.
Qed.

Lemma Cmul_conj : forall z1 z2, (Cconj z1) * z2 = Cconj (z1 * (Cconj z2)).
Proof.
CusingR_f.
Qed.

(* Tactic to create complex from reals*)

Lemma Cexist_rep_complex : forall a b : R, exists x : C, Cre x = a /\ Cim x = b.
Proof.
intros a b.
exists (a +i b).
intuition.
Qed.

(* begin hide *)
(* This tactic may help (not sure) *)
Ltac RusingC a b := 
 let z := fresh "z" in
 let H := fresh "H" in 
 let H1 := fresh "H1" in
 let H2 := fresh "H2" in 
   destruct (Cexist_rep_complex a b) as (z, H) ; destruct H as (H1, H2) ;
   try (rewrite <- H1 in * ; rewrite <- H2 in *); 
   clear H1 ; clear H2 ; clear a ; clear b ; intuition.
(* end hide *)
