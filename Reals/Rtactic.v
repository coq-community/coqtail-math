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

Require Import ZArith.
Require Import Reals.
Require Import Lia Lra.
Require Import DiscrR.
Require Import Rfunctions.
Open Scope R_scope.

Lemma Rmult_pow : forall x y n, (x * y) ^ n = x ^ n * y ^ n.
Proof.
intros x y n.
induction n ; simpl.
ring.
rewrite IHn.
ring.
Qed.

Lemma INR_0 : INR 0 = R0.
Proof.
reflexivity.
Qed.

Lemma IZR_0 : IZR 0 = R0.
Proof.
reflexivity.
Qed.

Lemma pow_0 : forall x, x ^ 0 = R1.
Proof.
intros x.
reflexivity.
Qed.

Lemma Rsqr_mul : forall x y, Rsqr (x * y) = x * x * y * y.
Proof.
intros x y.
unfold Rsqr. 
ring.
Qed.

Lemma Rsqr_div_unRsqr : forall x y, (y <> 0) -> Rsqr (x / y) = (x * x) / (y * y).
Proof.
intros x y H.
unfold Rsqr.
field.
assumption.
Qed.

Lemma Rsqr_add : forall x y, Rsqr (x + y) = x * x + 2 * x * y + y * y.
Proof.
intros x y.
unfold Rsqr. ring.
Qed.

Lemma Rsqr_minus : forall x y, Rsqr (x - y) = x * x - 2 * x * y + y * y.
Proof.
intros x y.
unfold Rsqr. ring.
Qed.

Lemma Rabs_div : forall x y, y <> 0 -> Rabs (x / y) = Rabs x / Rabs y.
Proof.
intros x y H.
unfold Rdiv.
rewrite Rabs_mult.
rewrite Rabs_Rinv. field.
apply Rabs_no_R0.
assumption.
intuition.
Qed.

Lemma sqrt_Rabs_mult_compat : forall x, sqrt (x * x) = Rabs x.
Proof.
intros x.
replace (x * x) with (Rsqr x) by (unfold Rsqr ; ring).
apply sqrt_Rsqr_abs.
Qed.

Lemma sqrt_Rabs_pow2 : forall x, sqrt (x ^ 2) = Rabs x.
Proof.
intros x.
simpl. rewrite Rmult_1_r.
apply sqrt_Rabs_mult_compat.
Qed.

Lemma Zpos_xO_IZR : forall x, IZR (Zpos (xO x)) = (R1 + R1) * IZR (Zpos x).
intros x.
rewrite Zpos_xO.
rewrite mult_IZR.
reflexivity.
Qed.

Lemma Zpos_xI_IZR : forall x, IZR (Zpos (xI x)) = (R1 + R1) * IZR (Zpos x) + R1.
Proof.
intros x.
rewrite Zpos_xI.
rewrite plus_IZR.
rewrite mult_IZR.
reflexivity.
Qed.

Lemma Zneg_xI_IZR : forall x, IZR (Zneg (xI x)) = (R1 + R1) * IZR (Zneg x) - R1.
Proof.
intros x.
rewrite Zneg_xI.
unfold Zminus.
rewrite plus_IZR.
rewrite mult_IZR.
rewrite Ropp_Ropp_IZR.
simpl.
ring.
Qed.

Lemma Zneg_xO_IZR : forall x, IZR (Zneg (xO x)) = (R1 + R1) * IZR (Zneg x).
intros x.
rewrite Zneg_xO.
rewrite mult_IZR.
reflexivity.
Qed.

Lemma Zneg_xH_IZR : IZR (Zneg xH) = -R1.
Proof.
intuition.
Qed.

Lemma Zpos_xH_IZR : IZR (Zpos xH) = R1.
Proof.
intuition.
Qed.

Lemma Rabs_right1 : forall x, x > 0 -> Rabs x = x.
Proof.
intros x H.
unfold Rabs.
destruct (Rcase_abs x).
lra.
reflexivity.
Qed.

Lemma Rabs_left_inv : forall x, 0 > x -> Rabs x = -x.
Proof.
intros.
apply Rabs_left.
intuition.
Qed.

Lemma Rabs_left1_inv : forall x, 0 >= x -> Rabs x = -x.
Proof.
intros.
apply Rabs_left1.
intuition.
Qed.

Lemma Rabs_add : forall x y, x >= 0 -> y >= 0 -> Rabs (x + y) = Rabs x + Rabs y.
Proof.
intros x y H H1.
unfold Rabs.
(destruct (Rcase_abs (x)) as [H2|[H2|H2]] ; [lra|idtac|idtac]) ; 
(destruct (Rcase_abs (y)) as [H3|[H3|H3]] ; [lra|idtac|idtac]) ;
(destruct (Rcase_abs (x + y)) as [H4|[H4|H4]] ; [lra|ring|ring]).
Qed.

Lemma Rabs_add1 : forall x y, 0 >= x -> 0 >= y -> Rabs (x + y) = Rabs x + Rabs y.
Proof.
intros x y H H1.
unfold Rabs.
(destruct (Rcase_abs (x)) as [H2|[H2|H2]] ; [idtac|lra|idtac]) ; 
(destruct (Rcase_abs (y)) as [H3|[H3|H3]] ; [idtac|lra|idtac]) ;
(destruct (Rcase_abs (x + y)) as [H4|[H4|H4]] ; [idtac|lra|idtac]).
ring. lra. rewrite H3. ring. lra. 
rewrite H2. ring. lra. rewrite H2. rewrite H3. ring.
reflexivity.
Qed. (* TODO à refaire en plus rapide *)

Lemma Rabs_minus : forall x y, x >= 0 -> 0 >= y -> Rabs (x - y) = Rabs x + Rabs y.
Proof.
intros x y H H1.
unfold Rabs.
(destruct (Rcase_abs (x)) as [H2|[H2|H2]] ; [lra|idtac|idtac]) ; 
(destruct (Rcase_abs (y)) as [H3|[H3|H3]] ; [idtac|lra|idtac]) ;
(destruct (Rcase_abs (x - y)) as [H4|[H4|H4]] ; [lra|idtac|idtac]).
ring. ring. rewrite H3. ring. rewrite H3. ring.
ring. ring. rewrite H3. ring. rewrite H3. rewrite H2. ring.
Qed.

Lemma Rabs_minus1 : forall x y, 0 >= x -> y >= 0 -> Rabs (x - y) = Rabs x + Rabs y.
Proof.
intros x y H H1.
unfold Rabs.
(destruct (Rcase_abs (x)) as [H2|[H2|H2]] ; [idtac|lra|idtac]) ; 
(destruct (Rcase_abs (y)) as [H3|[H3|H3]] ; [lra|idtac|idtac]) ;
(destruct (Rcase_abs (x - y)) as [H4|[H4|H4]] ; [idtac|lra|idtac]).
ring. lra. ring. lra. rewrite H2. ring.
lra. rewrite H2. rewrite H3. ring. rewrite H2. rewrite H3. ring.
Qed.

Lemma Rabs_2 : Rabs (2) = 2.
Proof.
unfold Rabs. destruct (Rcase_abs 2).
lra. reflexivity.
Qed.

Lemma Rabs_minus_dev : forall a b, a >= b -> Rabs (a - b) = a - b.
Proof.
intros a b H.
unfold Rabs.
destruct (Rcase_abs (a - b)).
lra.
ring.
Qed.

Lemma Rabs_minus_dev1 : forall a b, b >= a -> Rabs (a - b) = b - a.
Proof.
intros.
rewrite Rabs_minus_sym.
rewrite Rabs_minus_dev.
reflexivity.
assumption.
Qed.

Lemma Rsqr_pow2 : forall x, Rsqr x = x ^ 2.
Proof.
intros x.
unfold Rsqr.
simpl.
ring.
Qed.

Lemma scal_sum1 : forall (An : nat -> R) (N : nat) (x : R),
x * (sum_f_R0 An N) = sum_f_R0 (fun i => x * (An i)) N.
Proof.
intros An N x.
induction N.
reflexivity.
simpl. ring_simplify.
rewrite IHN. ring.
Qed.

Lemma sum_opp : forall (An : nat -> R) (N : nat) (x : R),
sum_f_R0 (fun n => -An n) N = - sum_f_R0 An N.
Proof.
intros An N x.
induction N.
reflexivity.
simpl. rewrite IHN.
ring.
Qed. 

Lemma sum_div : forall (x : R), x <> 0 -> 
forall (An : nat -> R) (N : nat), sum_f_R0 (fun n => An n / x) N = (sum_f_R0 An N) / x.
Proof.
intros x H An N.
induction N.
reflexivity.
simpl.
rewrite IHN.
field. assumption.
Qed.

Lemma Rabs_div_pos : forall x y, y > 0 -> Rabs ( x / y ) = Rabs x / y.
Proof.
intros x y H.
assert (H0 : (y <> 0)).
intros H1. rewrite H1 in H.
lra.
rewrite (Rabs_div x y H0).
rewrite (Rabs_right1 y H).
reflexivity.
Qed.

Lemma Rabs_div_neg : forall x y, 0 > y -> Rabs ( x / y ) = - Rabs x / y.
Proof.
intros x y H.
assert (H0 : (y <> 0)).
intros H1. rewrite H1 in H.
lra.
rewrite (Rabs_div x y H0).
rewrite (Rabs_left y H).
field. assumption.
Qed.

Lemma Rabs_Rinv_pos : forall x, x > 0 -> Rabs (/x) = / x.
Proof.
intros x H.
assert (H0 : ( x <> 0)).
intro H1. rewrite H1 in H. lra.
rewrite Rabs_Rinv.
rewrite Rabs_right.
reflexivity.
left. assumption.
assumption.
Qed.

Lemma Rabs_Rinv_neg : forall x, 0 > x -> Rabs (/x) = - / x.
Proof.
intros x H.
assert (H0 : ( x <> 0)).
intro H1. rewrite H1 in H. lra.
rewrite Rabs_Rinv.
rewrite Rabs_left.
field. assumption.
intuition.
assumption.
Qed.

Lemma minus_INR1 : forall a b, (a >= b)%nat -> INR (a - b) = INR a - INR b.
Proof.
intros a b H.
rewrite minus_INR.
reflexivity.
intuition.
Qed.

Lemma sqrt_mult1 : forall a b, a >= 0 -> b >= 0 -> sqrt (a * b) = sqrt a * sqrt b.
Proof.
intros a b H H1.
rewrite sqrt_mult.
reflexivity.
intuition. intuition.
Qed.

Lemma sqrt_mult_opp : forall a b, 0 >= a -> 0 >= b -> sqrt (a * b) = sqrt (-a) * sqrt (-b).
Proof.
intros a b H H1.
rewrite <- (sqrt_mult (-a) (-b)).
intuition.
intuition.
intuition.
Qed.

Ltac elim_INR x := (* idtac "elim_INR (" x ")" *)
match x with 
  | S ?a => rewrite (S_INR a); elim_INR a
  | plus ?a ?b => rewrite (plus_INR a b); elim_INR a; elim_INR b
  | minus ?a ?b => 
      match goal with
        | H : (a >= b)%nat |- _ => rewrite (minus_INR1 a b H)
        | _ => idtac
      end
  | mult ?a ?b => rewrite (mult_INR a b); elim_INR a; elim_INR b
  | O => rewrite INR_0
  | _ => idtac
end.


Ltac elim_IZR x := 
match x with 
  | (IZR (?a + ?b)) => rewrite (plus_IZR a b)
  | (IZR (?a - ?b)) => rewrite (Z_R_minus a b)
  | (IZR (?a * ?b)) => rewrite (mult_IZR a b)
  | (IZR (Z.succ ?n)) => rewrite (succ_IZR n)
  | (IZR (Zpower ?z (Z_of_nat ?n))) => rewrite <- (pow_IZR z n) 
  | (IZR (- ?n)) => rewrite (Ropp_Ropp_IZR n)
  | (IZR 0) => rewrite IZR_0
  | (IZR (Zpos xH)) => rewrite Zpos_xH_IZR
  | (IZR (Zneg xH)) => rewrite Zneg_xH_IZR
  | (IZR (Zpos (xO ?x))) => rewrite (Zpos_xO_IZR x)
  | (IZR (Zpos (xI ?x))) => rewrite (Zpos_xI_IZR x)
  | (IZR (Zneg (xO ?x))) => rewrite (Zneg_xO_IZR x)
  | (IZR (Zneg (xI ?x))) => rewrite (Zneg_xI_IZR x)	
  | (IZR ?x) => idtac
end.

Ltac elim_pow x := 
match x with
  | ((?y * ?z) ^ ?n) => rewrite (Rmult_pow y z n)
  | (?x ^ (?a + ?b)) => rewrite (pow_add x a b)
  | (?x ^ (S ?n)) => rewrite <- (tech_pow_Rmult x n)
  | (?x ^ 1) => rewrite (pow_1 x)
  | (?x ^ 0) => rewrite (pow_0 x)
  | (0 ^ ?n) => match goal with
      | H : (n <> 0) |- _ => rewrite (pow_ne_zero n H)
      | _ => idtac
    end
  | (1 ^ ?n) =>	match goal with
      | H : (n <> 0) |- _ => rewrite (pow_ne_zero n H)
      | _ => idtac
    end
end.

Ltac elim_Rsqr x :=
match x with
  | (?a * ?b) => rewrite (Rsqr_mul a b)
  | (?a / ?b) => match goal with 
      | H : (b <> 0) |- _ => rewrite (Rsqr_div_unRsqr a b H)
      | _ => idtac
    end
  | (?a + ?b) => rewrite (Rsqr_add a b)
  | (?a - ?b) => rewrite (Rsqr_minus a b)
  | ?a => rewrite (Rsqr_pow2 a)(* TODO manque plein de trucs*)
end.

Ltac estceunnumeral x := match x with
  | R0 => true
  | R1 => true
  | (?a + ?b) =>
      let a1 := (estceunnumeral a) in
      let a2 := (estceunnumeral b) in
      match a1 with
        | false => false
        | true => match a2 with
          | false => false
          | true => true
        end
      end
  | (?a * ?b) =>
      let a1 := (estceunnumeral a) in
      let a2 := (estceunnumeral b) in
      match a1 with
        | false => false
        | true => match a2 with
          | false => false
          | true => true
        end
      end
  | (?a / ?b) =>
      let a1 := (estceunnumeral a) in
      let a2 := (estceunnumeral b) in
      match a1 with
        | false => false
        | true => match a2 with
          | false => false
          | true => true
        end
      end
  | _ => false
end.

Ltac reduirenumeral x :=
  let h := fresh "H" in 
    (assert (h : x >= 0) by lra) ;
    rewrite (Rabs_right x h).

Ltac elim_Rabs x :=
match goal with
  | H : (x >= 0) |- _ => rewrite (Rabs_right x H)
  | H : (0 >= x) |- _ => rewrite (Rabs_left1_inv x H)
  | H : (0 > x) |- _ => rewrite (Rabs_left_inv x H)
  | H : (x > 0) |- _ => rewrite (Rabs_right1 x H)
  | _ =>
  
let z := estceunnumeral x in
  match z with
    | true => reduirenumeral x
    | false =>
  
match x with
  | (- ?a) => rewrite (Rabs_Ropp a)
  
  | (?a + ?b) =>
      let a1 := estceunnumeral a in 
      let b1 := estceunnumeral b in 
      match b1 with
        | false => idtac
        | true =>  let h := fresh "H" in
              assert (h : b >= 0) by lra
      end ; 
      match a1 with
        | false => idtac
        | true => let h := fresh "H" in
              assert (h : a >= 0) by lra
      end ;
      match goal with
        | H : a > 0 |- _ => generalize (Rgt_ge a 0 H) ; intro
        | H : 0 > a |- _ => generalize (Rgt_ge 0 a H) ; intro
        | H : b > 0 |- _ => generalize (Rgt_ge b 0 H) ; intro
        | H : 0 > b |- _ => generalize (Rgt_ge 0 b H) ; intro
      end ;            
      match goal with
        | H : a >= 0 |- _ => 
         match goal with 
          | H1 : b >= 0 |- _ => rewrite (Rabs_add a b H H1)
        end
        | H : 0 >= a |- _ => 
         match goal with 
          | H1 : 0 >= b |- _ => rewrite (Rabs_add1 a b H H1)
        end
      end
  
  | (?a - ?b) =>
      match goal with
        | H : a > 0 |- _ => generalize (Rgt_ge a 0 H) ; intro
        | H : 0 > a |- _ => generalize (Rgt_ge 0 a H) ; intro
        | H : b > 0 |- _ => generalize (Rgt_ge b 0 H) ; intro
        | H : 0 > b |- _ => generalize (Rgt_ge 0 b H) ; intro
        | H : a > b |- _ => generalize (Rgt_ge a b H) ; intro
        | H : b > a |- _ => generalize (Rgt_ge b a H) ; intro
      end ;
      match goal with
        | H : a >= b |- _ => rewrite (Rabs_minus_dev a b H)
        | H : b >= a |- _ => rewrite (Rabs_minus_dev1 a b H)
        | _ =>
          let a1 := estceunnumeral a in
            let b1 := estceunnumeral b in
              match b1 with
                | false => idtac
                | true => let h := fresh "H" in
                      assert (h : b >= 0) by lra
              end ; 
              match a1 with
                | false => idtac
                | true => let h := fresh "H" in
                      assert (h : a >= 0) by lra
              end ;
              match goal with
                | H : a >= 0 |- _ => 
                  match goal with
                    | H1 : 0 >= b |- _ => rewrite (Rabs_minus a b H H1)
                  end
                | H : 0 >= a |- _ => 
                  match goal with 
                    | H1 : b >= 0 |- _ => rewrite (Rabs_minus1 a b H H1)
                  end
              end
      end
  
  | (?a / ?b) =>
    match goal with 
      | H : (b <> 0) |- _ => rewrite (Rabs_div a b H)
      | H : (b > 0) |- _ => rewrite (Rabs_div_pos a b H)
      | H : (0 > b) |- _ => rewrite (Rabs_div_neg a b H)
      | _ => idtac "For more reductions assert :" b "<> 0" 
    end
  
  | (/ ?b) =>
    match goal with 
      | H : (b <> 0) |- _ => rewrite (Rabs_Rinv b H)
      | H : (b > 0) |- _ => rewrite (Rabs_Rinv_pos b H)
      | H : (0 > b) |- _ => rewrite (Rabs_Rinv_neg b H)
      | _ => idtac "For more reductions assert :" b "<> 0"
    end
  
  | (?a * ?b) => rewrite (Rabs_mult a b)
  | _ => idtac
(* TODO j'oublie des choses *)
end
end
end.


Ltac elim_sqrt x :=
match x with
  | (Rsqr ?x) => rewrite (sqrt_Rsqr_abs x)
  | (?x * ?x) => rewrite (sqrt_Rabs_mult_compat x)
  | (?x ^ 2) => rewrite (sqrt_Rabs_pow2 x)
  | (?a * ?b) => 
    match goal with
      | H : (a >= 0) |- _ => 
        match goal with 
          | H1 : (b >= 0) |- _ => rewrite (sqrt_mult1 a b H H1) 
          | _ => idtac
        end
      | H : ( 0 >= a) |- _ =>
        match goal with
          | H1 : (0 >= b) |- _ => rewrite (sqrt_mult_opp a b H H1) 
          | _ => idtac
        end
      | _ => idtac
    end
  
  | (?a / ?b) => 
    match goal with
      | H : (0 <= a) |- _ => 
        match goal with 
          | H1 : (0 < b) |- _ => rewrite (sqrt_div a b H H1) 
          | _ => idtac
        end
      | _ => idtac
    end
end.

Ltac simpl_function x := 
match x with
  | sum_f_R0 (fun l => _ + _) ?n => rewrite sum_plus (* TODO ok on fait tout*)
  | sum_f_R0 (fun l => _ - _) ?n => rewrite minus_sum
  | sum_f_R0 (fun l => _ * ?a) ?n => rewrite <- scal_sum
  | sum_f_R0 (fun l => ?a * _) ?n => rewrite <- scal_sum1
  | sum_f_R0 (fun l => ?a) ?n => rewrite sum_cte (* ?a n'est pas une fonction de l*)
  | sum_f_R0 (_) (S ?n) => rewrite tech5
  | sum_f_R0 (fun l => _ / ?b) ?n =>
    match goal with 
      | H : b <> 0 |- _ => rewrite (sum_div b H)
    end
  | sum_f_R0 (fun l => - _) ?n => rewrite sum_opp
end.

Ltac elim_ident1 X := (* idtac "elim_ident1 (" X ")";*)
match X with
  | (INR ?x) => elim_INR x
  | (IZR ?x) => elim_IZR (IZR x)
  | (?a ^ ?b) => elim_ident1 a ; elim_ident1 b ; elim_pow (a ^ b) 
  | (sum_f_R0 ?f ?x) => simpl_function (sum_f_R0 f x)
  
  | (Rabs ?x) => elim_ident1 x ; (elim_Rabs x)
  | (sqrt ?x) => elim_ident1 x ; (elim_sqrt x) 
  | (Rsqr ?x) => elim_ident1 x ; (elim_Rsqr x) 
  
  | (?r ?a ?b) => elim_ident1 a ; elim_ident1 b
  | (/ ?a) => elim_ident1 a
  
  | _ => idtac
end.

Ltac elim_infequal := 
match goal with
  | H : _ <= _ |- _ => apply Rle_ge in H
  | H : _ < _ |- _ => apply Rlt_gt in H
  | _ => idtac
end.

Ltac elim_ident := 
elim_infequal ; 
match goal with 
  | |- (?X1 = ?X2) => elim_ident1 X1 ; elim_ident1 X2
  | |- (?X1 < ?X2) => elim_ident1 X1 ; elim_ident1 X2
end.

Open Scope R_scope.



(** Reverse tactic, trying to solve goals with nat properties *)

Lemma mult_lt_O_compat : forall a b, lt O a -> lt O b -> lt O (mult a b).
Proof.
 intros a b Ha Hb.
 destruct a; [ inversion Ha | clear Ha ].
 destruct b; [ inversion Hb | clear Hb ].
 simpl.
 apply lt_O_Sn.
Qed.

Ltac nat_solve := match goal with
  | |- (0 <= ?n)%nat => apply le_O_n
  | |- (0 < ?a * ?b)%nat => apply mult_lt_O_compat; nat_solve
  | |- (0 < S ?a)%nat => apply lt_O_Sn
  | |- (?a > ?b)%nat => unfold gt; nat_solve
  | |- (?a >= ?b)%nat => unfold ge; nat_solve
  | |- (0 < fact ?n)%nat => apply lt_O_fact
  | |- _ => idtac
end.

Ltac INR_group term := match term with
  | 0 => replace 0 with (INR 0) by trivial
  | 1 => replace 1 with (INR 1) by trivial
  | 2 => replace 2 with (INR 2) by trivial
  | INR ?a * INR ?b => rewrite <- mult_INR
  | INR ?a + INR ?b => rewrite <- plus_INR
  | INR ?a - INR ?b => rewrite <- minus_INR
  | ?a * ?b => try INR_group a; try INR_group b; try rewrite <- mult_INR
  | ?a + ?b => try INR_group a; try INR_group b; try rewrite <- plus_INR
  | ?a - ?b => try INR_group a; try INR_group b; try rewrite <- minus_INR; [|lia]
  | INR ?a => idtac
end.

Ltac INR_solve := match goal with
  | |- INR ?a <> INR ?b => apply not_INR
  | |- INR ?a = INR ?b => let H := fresh in cut (H : a = b); [rewrite H; reflexivity | ]
  | |- ?a > ?b => apply Rlt_gt; try INR_solve
  | |- ?a >= ?b => apply Rle_ge; try INR_solve
  | |- 0 < ?a ^ 2 => rewrite <- (Rsqr_pow2 a); try INR_solve
  | |- 0 < ?a² => apply Rlt_0_sqr; try INR_solve
  | |- 0 <= ?a / ?b => apply Rle_mult_inv_pos; try INR_solve
  | |- 0 < ?a / ?b => apply Rlt_mult_inv_pos; try INR_solve
  | |- 0 < / ?a => apply Rinv_0_lt_compat; try INR_solve
  | |- 0 <= / ?a => apply Rlt_le; apply Rinv_0_lt_compat; try INR_solve
  | |- ?a <> ?b => try INR_group a; try INR_group b; try apply not_INR
  | |- ?a < ?b => try INR_group a; try INR_group b; try apply lt_INR
  | |- ?a <= ?b => try INR_group a; try INR_group b; apply le_INR
  | |- ?a = ?b => INR_group a; INR_group b; try reflexivity
  | |- ?a = ?b => INR_group a; INR_group b; let H := fresh in cut (H : a = b); [rewrite H; reflexivity | ]
  | |- ?a ?op ?b => INR_group a; INR_group b
  | |- ?a /\ ?b => split; try INR_solve
end; nat_solve; try lia.

Section examples.
  
  Definition aaa n m := INR (n + m).
  
  (*TODO il manque des cas > quand le >= existe*)
  
  Example hfdd : sum_f_R0 (fun n => (aaa n n) / 1) 0 = 1.
  Proof.
  assert (1 <> 0) by (intro Hc; lra).
  elim_ident.
  Abort.
  
  Example njfkl : forall y, Rabs (INR 5) * y + IZR 10 = 5 * y + 10.
  Proof.
  intros y.
  repeat elim_ident.
  ring.
  Qed.
  
  Example njfk : forall x, x <> 0 -> 1 / Rabs x + ((IZR (-5) + INR 7) + 4 ^ 2 + sqrt (5 * 5)) = IZR (2 * 9) + Rsqr 2 + Rabs (1 / x) + 1.
  Proof.
  intros.
  repeat elim_ident.
  ring.
  Qed.
  
  Example triangle n : INR (n * S n) / 2 + INR (S n) = INR (S n * S (S n)) / 2.
  Proof.
  intros.
  elim_ident.
  field.
  Qed.
  
  Example le0fact n : 0 < INR (S n * S (S n)) / INR (fact n).
  Proof.
  intros.
  INR_solve.
  Qed.
  
  Example fieldoblig n : 1 / INR (S n) - 1 / INR (S (S n)) = 1 / INR (S n * S (S n)).
  Proof.
  intros.
  elim_ident.
  field.
  INR_solve.
  Qed.
  
  Example pos_2np1_inv_sqr n : 0 < / (2 * (INR n) + 1) ^ 2.
  Proof.
  intros.
  INR_solve.
  Qed.
  
  Example inz n : 0 <> 2 * IZR n + 1.
  Proof.
  intros.
  prove_sup.
  discrR.
  lia.
  Qed.
  
End examples.

