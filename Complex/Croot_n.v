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

Require Export Complex.
Require Import Cpow_plus.
(* Require Import Cpolar.
Open Scope C_scope. *)

Lemma Rdiv_1 : forall r : R, (r/1)%R = r.
Proof.
intros. field.
Qed.

Ltac ring_simpl1 :=  
match goal with
 | id : _|- _ => (ring_simplify in id) ; generalize dependent id
end
with ring_simpl := unfold Rdiv in * ; unfold Cdiv in * ;
do 10 (try ring_simpl1) ; intros ; try ring_simplify.

Ltac apply_tactic1 := fun tactic => 
match goal with
 | id : _|- _ => (apply tactic in id)
end.

(* begin hide *)
(** Tactic CusingR2 to simplify some expressions and to go in R *)
(*
********************************************
Warning ! these tactics were written to avoid very long
normalization. It should be improved or deleted !
The reader is strongly advised not to use this tactic because 
of very long computation.
********************************************
*)
Ltac CusingRR2 := simpl in * ;
try rewrite <- Ceq in * ; unfold Cdiv in * ; unfold Cconj in * ; unfold Cminus in * ;
unfold Rdiv in * ;
try rewrite Rplus_0_l ; try rewrite Rplus_0_r ;
try rewrite Cadd_0_l ; try rewrite Cadd_0_r ;
try rewrite Rmult_0_l ; try rewrite Rmult_0_r ; 
try rewrite Cmult_0_l ; try rewrite Cmult_0_r ; 
try rewrite Rmult_0_l ; try rewrite Rmult_0_r ; 
try rewrite <- Cre_add_compat in * ;
try rewrite Cim_add_compat in * ; try rewrite Cre_INC_INR in * ;
try rewrite <- Cre_opp_compat in * ; try rewrite Cim_INC in * ;
try rewrite Cpow_Cim_0 in * ; 
try rewrite Cpow_Cre_0 in * ; 
try rewrite Cim_inv_INC in * 
with CusingRR3 := repeat CusingRR2.

Ltac CusingR_rec2 := unfold not in *;
match goal with
(* destruct complex *)
     | id:C |- _ => destruct id ; try CusingR_rec2
(* logical destruct in goal *)
     | id: _|- _ -> _ => intros ; try CusingR_rec2
     | id: _|- _ /\ _ => split ; try CusingR_rec2
     | id: _ /\ _ |- _ => destruct id ; CusingRR3 ; try CusingR_rec2
     | id: _ \/ _ |- _ => destruct id ; CusingRR3 ; try CusingR_rec2
(* false*)
     | id: _ |- False => (apply id ; CusingR2) 


     | id: _|- _ \/ _ => try ((left ; CusingR2 ; fail) || (right ; CusingR2 ; fail)) ; simpl in *
     | _ => simpl in *
end
with
CusingR2 := intros ; CusingRR3 ; CusingR_rec2 ; subst.
(* end hide *)

(** Proof of existence of a squareroot *)

(* begin hide*)
Lemma Rle_Rminus: forall a b : R, a <= b -> 0 <= b - a.
Proof.
intuition. unfold "<=" in *. elim H ; intros. left ; apply Rlt_Rminus. assumption.
right. rewrite H0. ring. 
Qed.


Lemma Croot_sqrt_pos : forall a b : R, 0 <= (sqrt (a * a + b * b) - a) / 2.
Proof.
intros.
unfold Rdiv. replace 0%R with (0 * /2)%R by field. apply Rmult_le_compat_r.
lra. apply Rle_Rminus.
apply Rle_trans with (Rabs a).
split_Rabs. lra. intuition.
apply Rsqr_incr_0_var. rewrite Rsqr_sqrt.
rewrite <- Rsqr_abs. replace (Rsqr a) with (a * a)%R by intuition.
replace (a * a)%R with ((a * a) + 0)%R by intuition. 
rewrite Rplus_assoc. apply Rplus_le_compat_l. 
replace (0 + b * b)%R with (Rsqr b) by intuition.
intuition. apply (Cnorm_sqr_pos a b). apply sqrt_positivity.
apply (Cnorm_sqr_pos a b).
Qed.

Lemma Croot_sqrt_pos_plus : forall a b : R, 0 <= (sqrt (a * a + b * b) + a) / 2.
Proof.
intros.
unfold Rdiv. replace 0%R with (0 * /2)%R by field. apply Rmult_le_compat_r.
lra. replace a with (--a)%R by intuition. apply Rle_Rminus.
apply Rle_trans with (Rabs a).
split_Rabs. lra. intuition. lra.
replace (--a)%R with a by intuition.
apply Rsqr_incr_0_var. rewrite Rsqr_sqrt.
rewrite <- Rsqr_abs. replace (Rsqr a) with (a * a)%R by intuition. 
replace (a * a)%R with ((a * a) + 0)%R by intuition. 
rewrite Rplus_assoc. apply Rplus_le_compat_l. 
replace (0 + b * b)%R with (Rsqr b) by intuition.
intuition. apply (Cnorm_sqr_pos a b). apply sqrt_positivity.
apply (Cnorm_sqr_pos a b).
Qed.

Lemma sqrt_square2 : forall a : R, (a >= 0 -> (sqrt a) ^ 2 = a)%R.
Proof.
intros.
simpl. rewrite Rmult_1_r. apply sqrt_sqrt. intuition.
Qed.
(* end hide *)

Lemma Croot_pol_2 : forall z : C, {z1 | z1 ^ 2 = z}.
Proof.
intros. 
destruct z as (a, b).
destruct (Rlt_le_dec b 0).
(* case b < 0 *)
exists (sqrt ( (sqrt ( a * a + b * b) + a)/2),
- sqrt ( (sqrt ( a * a + b * b) - a)/2))%R.
CusingR_simpl ; ring_simplify.
(* real part *)
repeat rewrite sqrt_square2. field. destruct (Croot_sqrt_pos a b). intuition. intuition.
destruct (Croot_sqrt_pos_plus a b). intuition. intuition.
(* imaginary part *)
rewrite Rmult_assoc. rewrite <- sqrt_mult.
field_simplify ((sqrt (a * a + b * b) + a) / 2 * ((sqrt (a * a + b * b) - a) / 2))%R.
rewrite sqrt_square2. field_simplify ((a * a + b * b - a ^ 2) / 4)%R.
unfold Rdiv. replace (/4)%R with (/2 * /2)%R by field. rewrite sqrt_mult. 
replace (sqrt (/2 * /2))%R with (/2)%R by (rewrite sqrt_square ; try reflexivity ; lra).
replace (b ^ 2)%R with (-b * -b)%R by ring. rewrite sqrt_square. 
field. lra. 
replace (b ^ 2)%R with (Rsqr b) by (simpl ; rewrite Rmult_1_r ; intuition).
intuition. lra. apply Rle_ge . apply (Cnorm_sqr_pos a b).
apply Croot_sqrt_pos_plus. apply Croot_sqrt_pos.
(* case b >= 0 *)
exists (sqrt ( (sqrt ( a * a + b * b) + a)/2),
sqrt ( (sqrt ( a * a + b * b) - a)/2))%R.
CusingR_simpl ; ring_simplify.
(* real part *)
repeat rewrite sqrt_square2. field.
apply Rle_ge. apply Croot_sqrt_pos.
apply Rle_ge. apply Croot_sqrt_pos_plus.
(* imaginary part *)
rewrite Rmult_assoc. 
repeat rewrite <- sqrt_mult.
field_simplify ((sqrt (a * a + b * b) + a) / 2 * ((sqrt (a * a + b * b) - a) / 2))%R.
repeat rewrite sqrt_square2.
field_simplify ((a * a + b * b - a ^ 2) / 4)%R.
unfold Rdiv. replace (/4)%R with (/2 * /2)%R by field. rewrite sqrt_mult. 
replace (sqrt (/2 * /2))%R with (/2)%R by (rewrite sqrt_square ; try reflexivity ; lra).
replace (b ^ 2)%R with (b * b)%R by ring. rewrite sqrt_square. 
field. lra.  
replace (b ^ 2)%R with (Rsqr b) by (simpl ; rewrite Rmult_1_r ; intuition).
intuition. lra. apply Rle_ge . apply (Cnorm_sqr_pos a b).
apply Croot_sqrt_pos_plus. apply Croot_sqrt_pos.
Qed.

(* begin hide*)
Lemma sum_f_R0_eq_seq : forall (n : nat) (f g : nat -> R),
        (forall m : nat, (m <= n)%nat -> f m = g m) -> 
	sum_f_R0 f n = sum_f_R0 g n.
Proof.
intros n f g H.
induction n.
simpl. apply H. intuition.
simpl. rewrite IHn. rewrite H with (S n). reflexivity. intuition. intros m H2. apply H. intuition. 
Qed.

Lemma Cnorm_sqr_real : forall r9 r10, 
(r9 +i r10) <> 0 ->
((r9 + r9) * (r9 + r9) + (r10 + r10) * (r10 + r10))%R <> 0%R.
Proof.
intros a b H Habs.
apply (HC0_norm_R0 ((a + a)%R +i (b + b)%R)) in Habs.
apply H. replace ((a + a)%R +i (b + b)%R) with ((2 +i 0%R) * (a +i b)) in Habs by CusingR_f.
apply Cmult_integral in Habs. destruct Habs ; 
assert (H1 : (2 +i 0%R) = 0 -> False) ; CusingR2 ; (lra || intuition).
Qed.

Lemma Rpow_2_inf_0 : forall x, (x^2 < 0 -> False)%R.
Proof.
intros. 
replace (x ^ 2)%R with (Rsqr x) in * by (unfold Rsqr ; simpl ; ring).
assert (Rsqr x >= 0) by (auto with real).
lra.
Qed.

Lemma Rpow_2_opp_inf_0 : forall x, (-x^2 > 0 -> False)%R.
Proof.
intros.
replace (x ^ 2)%R with (Rsqr x) in * by (unfold Rsqr ; simpl ; ring).
assert (Rsqr x >= 0) by (auto with real).
lra.
Qed.
(* end hide*) 

(** Equality to 0 of a polynom of degree one *)

Lemma Pol_degree_1 : forall a b, (forall x, a * x + b = 0) -> (a = 0 /\ b = 0).
Proof.
intros.
assert (H1 : (a * 0 + b = 0)).
apply H.
assert (H2 : (a * 1 + b = 0)).
apply H.
rewrite Cmult_0_r in H1.
rewrite Cmult_1_r in H2.
rewrite Cadd_0_l in H1.
subst. rewrite Cadd_0_r in H2.
subst.
intuition.
Qed.

(** Unicicty of roots of a polynom of degree two*)

Lemma Cpol_2_root_unicity : forall x1 x2 x3 x4,
(forall x, (x + x1) * (x + x2) = (x + x3) * (x + x4)) ->
(x1 = x3 /\ x2 = x4) \/ (x1 = x4 /\ x2 = x3).
Proof.
intros x1 x2 x3 x4 H.
assert (H1 : (forall x : C, (x + x1) * (x + x2) = (x + x3) * (x + x4)) -> 
(forall x, (x1 + x2 - x3 - x4) * x + x1 * x2 - x3 * x4 = 0)).
intros H0 x.
assert (H1 : ((x + x1) * (x + x2) = (x + x3) * (x + x4) -> 
(x1 + x2 - x3 - x4) * x + x1 * x2 - x3 * x4 = 0)).
intros H1.
apply Cminus_diag_eq in H1. ring_simplify in H1.
repeat rewrite <- Cmult_add_distr_l in H1.
repeat rewrite <- Cmult_minus_distr_l in H1.
rewrite Cmult_comm in H1.
assumption.
apply H1. apply H0.
assert (H2 : (x1 + x2 - x3 - x4 = 0 /\ x1 * x2 - x3 * x4 = 0)).
apply Pol_degree_1.
intros x.
replace ((x1 + x2 - x3 - x4) * x + (x1 * x2 - x3 * x4)) with 
((x1 + x2 - x3 - x4) * x + x1 * x2 - x3 * x4) by ring.
apply H1.
intros x0.
apply H.
destruct H2 as [H0 H2].
assert (H3 : ((-x1 + x1) * (-x1 + x2) = (-x1 + x3) * (-x1 + x4))).
apply H.
assert (H4 : ((-x2 + x1) * (-x2 + x2) = (-x2 + x3) * (-x2 + x4))).
apply H. rewrite Cadd_opp_l in *.
(* From this point we do all in parallel *)
destruct (Ceq_dec x2 x1) ;
rewrite Cmult_0_l in *; rewrite Cmult_0_r in * ;
symmetry in H3 ; symmetry in H4 ;
apply Cmult_integral in H3 ; apply Cmult_integral in H4 ;
destruct H3 as [H3|H3] ; destruct H4 as [H4|H4] ;
rewrite Cadd_comm in * ; apply Cminus_diag_uniq in H3 ;
apply Cminus_diag_uniq in H4 ; subst ; ring_simpl ; intuition.
Qed.


(** Solve a polynom of degree two in the Complex field as a function of delta *)
Lemma Cpol_d_2 : forall a b c delta, (delta = b^2 - 4*a * c) ->
a <> 0 -> Cim a = 0%R -> Cim b = 0%R -> Cim c = 0%R ->
exists x1, exists x2, forall x, 
a * x ^ 2 + b * x + c =  a * (x + x1) * (x + x2)
/\ ((Cim delta) = 0%R /\ Cre delta > 0%R -> Cim x1 = 0%R /\ Cim x2 = 0%R) 
/\ ((Cim delta) = 0%R /\ Cre delta < 0%R -> Cim x1 <> 0%R /\ Cim x2 <> 0%R)
/\ ((Cim delta) = 0%R /\ Cre delta = 0%R -> x1 = x2 /\ Cim x1 = 0%R).
Proof.
intros a b c delta Hdelta Ha Hima Himb Himc.
destruct (Croot_pol_2 delta) as [delta1 Hsquare].
exists (( b / (a + a) - delta1 / (a + a))).
exists (( b / (a + a) + delta1 / (a + a))).
intros x.
repeat split. unfold Cdiv. ring_simplify.
rewrite Hsquare. rewrite Hdelta.
unfold Cminus. repeat rewrite Cadd_assoc.
apply Cadd_eq_compat_l.
ring_simplify. rewrite Rplus_0_l.
assert (H : (2 * 2 = 4)) by (CusingR_simpl ; ring).
rewrite <- H. replace ((R1+R1)%R, R0) with (IRC 2) by (reflexivity).
replace (a + a) with (2 * a) by (CusingR_simpl ; ring).
field. split. assumption. intro H0. rewrite <- Ceq in H0. simpl in H0.
destruct H0. assert (2 <> 0)%R by discrR. intuition.
CusingR2. ring_simpl. 
generalize H2. intro H3.
(apply Rmult_integral in H3 ; destruct H3 as [H3|H3]).
(apply Rmult_integral in H3 ; destruct H3 as [H3|H3]).
lra.
rewrite H3 in *. rewrite <- H1 in H0. ring_simpl.
apply Rpow_2_opp_inf_0 in H0. destruct H0.
rewrite H3. ring.
CusingR2. ring_simpl.
(apply Rmult_integral in H2 ; destruct H2 as [H2|H2]).
(apply Rmult_integral in H2 ; destruct H2 as [H2|H2]).
lra. rewrite H2 in H1. rewrite <- H1 in H0. ring_simpl.
apply Rpow_2_opp_inf_0 in H0. destruct H0.
rewrite H2. ring. 
CusingR2. ring_simpl.
apply Rmult_integral in H0 ; destruct H0 as [H0|H0].
apply Rmult_integral in H0 ; destruct H0 as [H0|H0].
apply Rmult_integral in H0 ; destruct H0 as [H0|H0].
lra.
apply Rinv_neq_0_compat in H0. destruct H0.
intro H8. ring_simplify in H8. apply Rmult_integral in H8. destruct H8 as [H8|H8].
lra.
replace (r9 ^ 2)%R with (Rsqr r9) in H8 by (unfold Rsqr ; simpl ; ring).
assert (H5 : (r9 = 0)%R). apply Rsqr_0_uniq ; assumption.
rewrite H5 in *. apply Ha. split ; reflexivity.
assumption.
rewrite H0 in *. ring_simpl. rewrite <- H2 in H1.
apply Rpow_2_inf_0 in H1. destruct H1. reflexivity.
CusingR2. ring_simpl.
apply Rmult_integral in H0 ; destruct H0 as [H0|H0].
apply Rmult_integral in H0 ; destruct H0 as [H0|H0].
apply Rmult_integral in H0 ; destruct H0 as [H0|H0].
lra.
apply Rinv_neq_0_compat in H0. destruct H0.
intro H8. ring_simplify in H8. apply Rmult_integral in H8. destruct H8 as [H8|H8].
lra.
replace (r9 ^ 2)%R with (Rsqr r9) in H8 by (unfold Rsqr ; simpl ; ring).
assert (H5 : (r9 = 0)%R). apply Rsqr_0_uniq ; assumption.
rewrite H5 in *. apply Ha. split ; reflexivity.
assumption.
rewrite H0 in *. ring_simpl. rewrite <- H2 in H1.
apply Rpow_2_inf_0 in H1. destruct H1.
reflexivity. unfold Cminus. apply Cadd_eq_compat_l.
assert (H0 : (delta = 0)) by (rewrite <- Ceq ; intuition).
rewrite H0 in *. 
assert (H1 : delta1 = 0). simpl in Hsquare. rewrite Cmult_1_r in Hsquare.
apply Cmult_integral in Hsquare. destruct Hsquare ; assumption.
rewrite H1. unfold Cdiv. ring.
CusingR2. ring_simpl.
apply Rmult_integral in H2 ; destruct H2 as [H2|H2].
apply Rmult_integral in H2 ; destruct H2 as [H2|H2].
lra.
rewrite H2 in *. ring_simplify in H1.
rewrite <- H1 in H0. replace (r2 ^ 2)%R with (Rsqr r2) in H0 by (unfold Rsqr ; simpl ; ring).
assert (H10 : (r2 = 0)%R). apply Rsqr_0_uniq. apply Ropp_eq_0_compat in H0.
ring_simplify in H0. assumption.
rewrite H10 in *. ring.
rewrite H2 in *. ring.
Qed.

(** Real properties that can be deduced from the resolution of a complex polynom*)
Lemma Cpol_2_real_delta_pos : forall a b c delta, ((delta = b^2 - 4*a * c ) ->
delta > 0 -> a <> 0 ->
exists x1, exists x2, forall x,
a * x ^ 2 + b * x + c =  a * (x + x1) * (x + x2))%R.
Proof.
intros a b c delta deltadef Hdelta Ha.
destruct (Cpol_d_2 (a +i 0%R) (b +i 0%R) (c +i 0%R) (delta +i 0%R)) as [x1 [x2 H1]].
CusingR2.
ring.
ring.
CusingR2.
reflexivity.
CusingR2.
reflexivity.
CusingR2.
reflexivity.
CusingR2.
reflexivity.
exists (Cre x1). exists (Cre x2).
assert (HRtoC : (forall x, Cre ((a +i 0%R) * (x +i 0%R) ^ 2 + (b +i 0%R) * (x +i 0%R) + (c +i  0%R)) = 
Cre ((a +i 0%R) * ((x +i 0%R) + x1) * ((x +i 0%R) + x2)))).
intros x.
apply Cre_eq_compat. generalize (H1 (x +i 0%R)). intro H0.
destruct H0 as [H2 [H3 [H4 H5]]].
 apply H2.
intros x.
generalize (H1 (x +i 0%R)). intro H0.
destruct H0 as [H2 [H3 [H4 H5]]].
assert (HCroot : (Cim x1 = 0%R /\ Cim x2 = 0%R)). apply H3. simpl. split. reflexivity. assumption.
CusingR2. ring_simpl. assumption.
Qed.

Lemma Cpol_2_real_delta_eq_0 : forall a b c delta, ((delta = b^2 - 4*a * c) ->
delta = 0 -> a <> 0 ->
exists x1, exists x2, forall x,
a * x ^ 2 + b * x + c =  a * (x + x1) * (x + x2))%R.
Proof.
intros a b c delta deltadef Hdelta Ha.
destruct (Cpol_d_2 (a +i 0%R) (b +i 0%R) (c +i 0%R) (delta +i 0%R)) as [x1 [x2 H1]]. 
CusingR2.
ring.
ring.
CusingR2.
reflexivity.
CusingR2.
reflexivity.
CusingR2.
reflexivity.
CusingR2.
reflexivity.
exists (Cre x1). exists (Cre x2).
assert (HRtoC : (forall x, Cre ((a +i 0%R) * (x +i 0%R) ^ 2 + (b +i 0%R) * (x +i 0%R) + (c +i  0%R)) = 
Cre ((a +i 0%R) * ((x +i 0%R) + x1) * ((x +i 0%R) + x2)))).
intros x.
apply Cre_eq_compat. generalize (H1 (x +i 0%R)). intro H0.
destruct H0 as [H2 [H3 [H4 H5]]].
 apply H2.
intros x.
generalize (H1 (x +i 0%R)). intro H0.
destruct H0 as [H2 [H3 [H4 H5]]].
assert (HCroot : (x1 = x2 /\ Cim x1 = 0%R)). apply H5. simpl. split. reflexivity. assumption.
CusingR2. subst. ring_simpl. assumption.
Qed.

Lemma Cpol_2_real_delta_eq_neg : forall a b c delta, ((delta = b^2 - 4*a * c) ->
delta < 0 -> a <> 0 ->
~ (exists x1, exists x2, forall x,  
a * x ^ 2 + b * x + c =  a * (x + x1) * (x + x2)))%R.
Proof.
intros a b c delta deltadef Hdelta Ha.
destruct (Cpol_d_2 (a +i 0%R) (b +i 0%R) (c +i 0%R) (delta +i 0%R)) as [x1 [x2 H1]]. 
CusingR2.
ring.
ring.
CusingR2.
reflexivity.
CusingR2.
reflexivity.
CusingR2.
reflexivity.
CusingR2.
reflexivity. 
intro H.
destruct H as (x3, H) . destruct H as (x4, H).
assert (forall x : C, (a +i 0%R) * x ^ 2 + (b +i  0%R) * x + (c +i  0%R) =
     (a +i 0%R) * (x + x1) * (x + x2)).
intro x. 
generalize (H1 x). intros H0.
destruct H0 as [H2 [H3 [H4 H5]]].
apply H2.
assert (H10 : forall x : C, (a +i 0%R) * x ^ 2 + (b +i  0%R) * x + (c +i  0%R) =
     (a +i 0%R) * (x + (x3 +i 0%R)) * (x + (x4 +i 0%R))).
intros x.
destruct x as (r, r0).
rewrite <- Ceq. split.
simpl. ring_simplify.
generalize (H r). intro H15. ring_simplify in H15.
replace (a * r ^ 2 - a * r0 ^ 2 + r * b + c)%R with ((a * r ^ 2 + r * b + c) - a* r0^2)%R by ring.
rewrite H15. ring.
simpl. ring_simplify.
generalize (H 1%R). intro H15. ring_simplify in H15.
generalize (H 0%R). intro H16. ring_simplify in H16.
rewrite <- H16 in H15. ring_simplify in H15.
rewrite <- Rmult_plus_distr_l in H15.
rewrite Rplus_comm in H15. symmetry in H15. rewrite Rplus_comm in H15.
apply Rplus_eq_reg_l in H15. rewrite Rplus_comm in H15.
apply Rplus_eq_reg_l in H15.
rewrite <- H15. ring.
assert (Htra :  (x1 = (x3 +i 0%R) /\ x2 = (x4 +i 0%R) \/ x1 = (x4 +i 0%R) /\ x2 = (x3 +i 0%R))).
assert (forall x : C, (x + (x3 +i 0%R)) * (x + (x4 +i 0%R))  = (x + x1) * (x + x2)).
intro x; apply Cmult_eq_reg_l with (a +i 0%R).
red; injection 1; auto.
generalize (H0 x) (H10 x); intros abs1 abs2.
ring_simplify in abs1 ; ring_simplify in abs2 ; ring_simplify.
rewrite <- abs1. rewrite abs2. reflexivity.
apply Cpol_2_root_unicity.
intros x. rewrite H2. reflexivity.
generalize (H1 0). intros Hdeltas.
destruct Hdeltas as [H2 [H3 [H4 H5]]].
clear H3 H5 H2.
assert (Habss : (Cim x1 <> 0%R /\ Cim x2 <> 0%R)).
apply H4. intuition. clear H4.
destruct Habss as (Habss1, Habss2).
destruct Htra as [[Htra1 Htra2]|[Htra1 Htra2]].
rewrite <- Ceq in Htra1.
destruct Htra1 as (Htra1, Htraabs).
simpl in Htraabs.
apply Habss1. assumption.
rewrite <- Ceq in Htra1.
destruct Htra1 as (Htra1, Htraabs).
simpl in Htraabs.
apply Habss1. assumption.
Qed.

Lemma Cfpol_root : forall a b c delta, ((delta = b^2 - 4*a * c) ->
delta >= 0 -> a <> 0 -> exists x, a * x ^ 2 + b * x + c = 0)%R.
Proof.
intros a b c delta Hdelta deltapos Ha.
destruct deltapos.
destruct (Cpol_2_real_delta_pos a b c delta) as [x H0].
assumption. assumption. assumption.
destruct H0 as (x1, H0).
exists (-x1)%R. rewrite H0. ring.
destruct (Cpol_2_real_delta_eq_0 a b c delta) as [x2 H5].
assumption. assumption. assumption.
destruct H5 as (x1, H0).
exists (-x1)%R. rewrite H0. ring.
Qed.

Lemma Cpol_pos : forall a b c delta, (delta = b^2 - 4*a * c)%R ->
 a <> 0%R ->
(forall x, 0 <> a*x*x+b*x+c)%R -> delta < 0%R.
intros a b c delta Hdelta Ha.
intro Hpoly.
destruct (total_order_T delta 0) as [[H|H]|H].
assumption.
destruct (Cfpol_root a b c delta).
assumption. intuition. assumption. 
destruct (Hpoly x). ring_simplify. symmetry. 
ring_simplify in H0. assumption.
destruct (Cfpol_root a b c delta).
assumption. intuition. assumption. 
destruct (Hpoly x). ring_simplify. symmetry. 
ring_simplify in H0. assumption.
Qed.


Lemma Pos_poly_del : forall a b c : R,
a <> 0%R -> a > 0%R -> (forall x, 0 <= a*x*x+b*x+c) -> b^2 - 4*a*c <=0.
Proof.
intros a b c Ha Haa Hpoly.
pose ( b^2 - 4*a*c)%R as delta.
destruct (total_order_T delta 0) as [[H|H]|H].
intuition. intuition.
destruct (Cfpol_root a b c delta).
reflexivity.
intuition.
assumption.
assert (H1 : (exists x1, exists x2, forall x,
a * x ^ 2 + b * x + c =  a * (x + x1) * (x + x2))%R).
apply Cpol_2_real_delta_pos with delta.
ring_simplify.
reflexivity.
assumption.
assumption.
destruct H1 as [x1 [x2 H1]].
assert (H9 : (0 > a * ( -(x1 + x2)/2 + x1) * ( - (x1 + x2)/2 + x2))%R).
replace ((- (x1 + x2) / 2 + x1))%R with ((x1 - x2) /2)%R by field.
replace ((- (x1 + x2) / 2 + x2))%R with (-(x1 - x2) /2)%R by field.
replace (a * ((x1 - x2) / 2) * (- (x1 - x2) / 2))%R with ( ((x1 - x2) / 2)^2 * (-a))%R by field.
replace 0%R with (  ((x1 - x2) / 2) ^ 2 * 0 )%R by ring.
apply Rmult_gt_compat_l.
assert (H10 : (x1 <> x2)).
intro H11. rewrite H11 in H1.
assert ((a * 0 ^ 2 + b * 0 + c)%R = (a * (0 + x2) * (0 + x2)))%R.
apply H1.
assert ((a * 1 ^ 2 + b * 1 + c)%R = (a * (1 + x2) * (1 + x2)))%R.
apply H1.
ring_simpl.
rewrite <- H2 in H3. unfold delta in H.
replace (a + b + c)%R with (c + a + b)%R in H3 by ring.
replace (c + 2 * a * x2 +a)%R with (c + a + 2 * a * x2)%R in H3 by ring.
apply Rplus_eq_reg_l in H3. subst.
replace ((2 * a * x2) ^ 2 - 4 * a * (a * x2 ^ 2))%R with (0)%R in H by ring .
lra.
replace (((x1 - x2) / 2) ^ 2)%R with (Rsqr (((x1 - x2) / 2))) by (unfold Rsqr ; simpl ; ring).
apply Rlt_0_sqr.
intro H30. replace 0%R with (0/2)%R in H30 by field.
unfold Rdiv in *. rewrite Rmult_comm in H30.
symmetry in H30. rewrite Rmult_comm in H30.
apply Rmult_eq_reg_l in H30. 
apply H10. symmetry in H30. auto with *.
apply Rinv_neq_0_compat.
discrR.
intuition.
assert ( 0 <= a * (- (x1 + x2) / 2 + x1) * (- (x1 + x2) / 2 + x2)).
rewrite <- H1. replace ( (- (x1 + x2) / 2) ^ 2)%R with ((- (x1 + x2) / 2) * (- (x1 + x2) / 2) )%R by ring.
rewrite <- Rmult_assoc. apply Hpoly.
lra.
Qed.

Require Import Cpolar.
Require Import Cexp.

Open Scope C_scope.


Lemma ast_fun_pos : forall n r, (n > 0)%nat -> r > 0 -> (r + 1) ^ n - r > 0.
Proof.
intros n r Hn Hr.
induction Hn.
simpl. ring_simplify. lra.
simpl. rewrite Rmult_plus_distr_r. replace 0%R with (0 + 0)%R by intuition.
unfold Rminus. rewrite Rplus_assoc. apply Rplus_lt_compat.
apply Rmult_gt_0_compat.
assumption.
apply pow_lt. lra.
rewrite Rmult_1_l. apply IHHn.
Qed.

(** ** Every positive real has a n root *)
Lemma exist_root_n_pos : forall r n, r >= 0 -> (n > 0)%nat -> {root | root ^ n = r}%R.
Proof.
intros r n Hr Hn.
pose (f := (fun x => x ^ n - r)%R).
assert (Cont_pow : forall x, continuity_pt f x).
unfold f. intros x. reg.
destruct (total_order_T r 0) as [[order|order]|order].
edestruct Rge_not_lt; eauto.
exists 0. rewrite order.
rewrite pow_ne_zero. reflexivity.
intuition.
assert (Hsup0 : r+1 > 0) by lra.
assert (Hpos : forall n, (n > 0)%nat -> (r + 1) ^ n - r > 0).
 intros n1 Hn1. apply ast_fun_pos. assumption. assumption.
assert (Hneg : 0 ^ n - r < 0). rewrite pow_ne_zero. lra.
 intuition.

generalize (IVT (fun x => x ^ n - r) 0 (r + 1) Cont_pow Hsup0 Hneg)%R.

intros H. destruct H as (x, H).
apply Hpos. assumption.
exists  x. intuition.
Qed.

(** ** Every complex has a n root *) 

Require Import Cpolar. (* requiring it earlier implies scope problems *)
Open Scope C_scope.

Lemma exist_root_n : forall n z, (n > 0)%nat -> {root | root ^ n = z}.
Proof.
intros n z Hn.
destruct (exists_principal_polar_form z) as [r [theta Hrt]].
destruct Hrt as [Hrpos [Htheta Hpol]].
rewrite Cmult_IRC_compat_l in Hpol.
rewrite <- Cexp_trigo_compat in Hpol.
destruct (exist_root_n_pos r n) as (root_real, Hreal); [ auto with * | | ].
apply Hn.
exists ( root_real * Cexp ((0 +i theta ) / INC n))%C.
rewrite Cpow_mul_distr_l.
rewrite IRC_pow_compat. rewrite Hreal. rewrite <- Cexp_mult.
field_simplify (INC n * ((0 +i  theta) / INC n))%C.
unfold Cdiv. try rewrite Cinv_1. try rewrite Cmult_1_r.
apply Hpol. 
apply not_0_INC. intuition.
Qed.
