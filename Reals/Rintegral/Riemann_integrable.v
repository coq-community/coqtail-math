Require Import Max.
Require Import Reals.
Require Import Lra.
Require Import RiemannInt.
Require Import Rfunction_classes_def.
Require Import Rextensionality.

Open Scope R_scope.


(*Replacing x by a word in RiemannInt_Px for x from 1 to 33*)

Section Copy_stdlib.

Lemma Riemann_integrable_opp_bound :
  forall (f:R -> R) (a b:R),
    Riemann_integrable f a b -> Riemann_integrable f b a.
Proof.
 apply RiemannInt_P1.
Qed.

Definition RinvN (N:nat) : posreal := mkposreal _ (RinvN_pos N).

Lemma Riemann_integrable_PI :
  forall (f:R -> R) (a b:R) (pr1 pr2:Riemann_integrable f a b),
    RiemannInt pr1 = RiemannInt pr2.
Proof.
 apply RiemannInt_P5.
Qed.

Lemma Riemann_integrable_continuity :
  forall (f:R -> R) (a b:R),
    a < b ->
    (forall x:R, a <= x <= b -> continuity_pt f x) -> Riemann_integrable f a b.
Proof.
 apply RiemannInt_P6.
Qed.

Lemma Riemann_integrable_singleton : forall (f:R -> R) (a:R), Riemann_integrable f a a.
Proof.
 apply RiemannInt_P7.
Qed.

Lemma Riemann_integrable_continuity_gen :
  forall (f:R -> R) (a b:R),
    a <= b ->
    (forall x:R, a <= x <= b -> continuity_pt f x) -> Riemann_integrable f a b.
Proof.
 apply continuity_implies_RiemannInt.
Qed.

Lemma RiemannInt_bound_exchange :
  forall (f:R -> R) (a b:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable f b a), RiemannInt pr1 = - RiemannInt pr2.
Proof.
 apply RiemannInt_P8.
Qed.

Lemma RiemannInt_bound_exchange_1 : 
  forall (f : R -> R) (a b : R) (pr1 : Riemann_integrable f a b),
    RiemannInt pr1 = - RiemannInt (Riemann_integrable_opp_bound f a b pr1).
Proof.
 intros. rewrite (RiemannInt_bound_exchange f a b pr1 (Riemann_integrable_opp_bound f a b pr1)).
 reflexivity.
Qed.

Lemma RiemannInt_singleton :
  forall (f:R -> R) (a:R) (pr:Riemann_integrable f a a), RiemannInt pr = 0.
Proof.
 apply RiemannInt_P9.
Qed.

Lemma Riemann_integrable_linear :
  forall (f g:R -> R) (a b l:R),
    Riemann_integrable f a b ->
    Riemann_integrable g a b ->
    Riemann_integrable (fun x:R => f x + l * g x) a b.
Proof.
 apply RiemannInt_P10.
Qed.

(*
TODO
Lemma RiemannInt_P11 :
  forall (f:R -> R) (a b l:R) (un:nat -> posreal)
    (phi1 phi2 psi1 psi2:nat -> StepFun a b),
    Un_cv un 0 ->
    (forall n:nat,
      (forall t:R,
        Rmin a b <= t <= Rmax a b -> Rabs (f t - phi1 n t) <= psi1 n t) /\
      Rabs (RiemannInt_SF (psi1 n)) < un n) ->
    (forall n:nat,
      (forall t:R,
        Rmin a b <= t <= Rmax a b -> Rabs (f t - phi2 n t) <= psi2 n t) /\
      Rabs (RiemannInt_SF (psi2 n)) < un n) ->
    Un_cv (fun N:nat => RiemannInt_SF (phi1 N)) l ->
    Un_cv (fun N:nat => RiemannInt_SF (phi2 N)) l.
*)


Lemma RiemannInt_linear :
  forall (f g:R -> R) (a b l:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable g a b)
    (pr3:Riemann_integrable (fun x:R => f x + l * g x) a b),
    RiemannInt pr3 = RiemannInt pr1 + l * RiemannInt pr2.
Proof.
 apply RiemannInt_P13.
Qed.

Lemma Riemann_integrable_constant : forall a b c:R, Riemann_integrable (fct_cte c) a b.
Proof.
 apply RiemannInt_P14.
Qed.

Lemma RiemannInt_constant :
  forall (a b c:R) (pr:Riemann_integrable (fct_cte c) a b),
    RiemannInt pr = c * (b - a).
Proof.
 apply RiemannInt_P15.
Qed.

Lemma Riemann_integrable_Rabs :
  forall (f:R -> R) (a b:R),
    Riemann_integrable f a b -> Riemann_integrable (fun x:R => Rabs (f x)) a b.
Proof.
 apply RiemannInt_P16.
Qed.

Lemma RiemannInt_le_Rabs :
  forall (f:R -> R) (a b:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable (fun x:R => Rabs (f x)) a b),
    a <= b -> Rabs (RiemannInt pr1) <= RiemannInt pr2.
Proof.
 apply RiemannInt_P17.
Qed.

Lemma RiemannInt_ext :
  forall (f g:R -> R) (a b:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable g a b),
    a <= b ->
    (forall x:R, a < x < b -> f x = g x) -> RiemannInt pr1 = RiemannInt pr2.
Proof.
 apply RiemannInt_P18.
Qed.

Lemma RiemannInt_le_ext :
  forall (f g:R -> R) (a b:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable g a b),
    a <= b ->
    (forall x:R, a < x < b -> f x <= g x) -> RiemannInt pr1 <= RiemannInt pr2.
Proof.
 apply RiemannInt_P19.
Qed.

Lemma RiemannInt_primitive :
  forall (f:R -> R) (a b:R) (h:a <= b)
    (pr:forall x:R, a <= x -> x <= b -> Riemann_integrable f a x)
    (pr0:Riemann_integrable f a b),
    RiemannInt pr0 = primitive h pr b - primitive h pr a.
Proof.
 apply RiemannInt_P20.
Qed.

Lemma Riemann_integrable_included_left :
  forall (f:R -> R) (a b c:R),
    Riemann_integrable f a b -> a <= c <= b -> Riemann_integrable f a c.
Proof.
 apply RiemannInt_P22.
Qed.

Lemma Riemann_integrable_included_right :
  forall (f:R -> R) (a b c:R),
    Riemann_integrable f a b -> a <= c <= b -> Riemann_integrable f c b.
Proof.
 apply RiemannInt_P23.
Qed.

Lemma Riemann_integrable_Chasles :
  forall (f:R -> R) (a b c:R),
    Riemann_integrable f a b ->
    Riemann_integrable f b c -> Riemann_integrable f a c.
Proof.
 apply RiemannInt_P24.
Qed.

Lemma RiemannInt_Chasles :
  forall (f:R -> R) (a b c:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable f b c) (pr3:Riemann_integrable f a c),
    RiemannInt pr1 + RiemannInt pr2 = RiemannInt pr3.
Proof.
 apply RiemannInt_P26.
Qed.

Lemma derivable_primitive :
  forall (f:R -> R) (a b x:R) (h:a <= b)
    (C0:forall x:R, a <= x <= b -> continuity_pt f x),
    a <= x <= b -> derivable_pt_lim (primitive h (FTC_P1 h C0)) x (f x).
Proof.
 apply RiemannInt_P28.
Qed.

(*
TODO to be done
Lemma RiemannInt_P29 :
  forall (f:R -> R) a b (h:a <= b)
    (C0:forall x:R, a <= x <= b -> continuity_pt f x),
    antiderivative f (primitive h (FTC_P1 h C0)) a b.

Lemma RiemannInt_P30 :
  forall (f:R -> R) (a b:R),
    a <= b ->
    (forall x:R, a <= x <= b -> continuity_pt f x) ->
    { g:R -> R | antiderivative f g a b }.

Record C1_fun : Type := mkC1
  {c1 :> R -> R; diff0 : derivable c1; cont1 : continuity (derive c1 diff0)}.

Lemma RiemannInt_P31 :
  forall (f:C1_fun) (a b:R),
    a <= b -> antiderivative (derive f (diff0 f)) f a b.

Lemma RiemannInt_P32 :
  forall (f:C1_fun) (a b:R), Riemann_integrable (derive f (diff0 f)) a b.

Lemma RiemannInt_P33 :
  forall (f:C1_fun) (a b:R) (pr:Riemann_integrable (derive f (diff0 f)) a b),
    a <= b -> RiemannInt pr = f b - f a.
TODO refaire FTC_Riemann avec C.
Lemma FTC_Riemann :
  forall (f:C1_fun) (a b:R) (pr:Riemann_integrable (derive f (diff0 f)) a b),
    RiemannInt pr = f b - f a.
*)

End Copy_stdlib.


Lemma RiemannInt_integrable_eq_compat : forall f g a b, (forall x, f x = g x) ->
  Riemann_integrable f a b -> Riemann_integrable g a b.
intros f g a b H X eps.
elim X with eps;intros x p; exists x.
elim p; intros x0 [p01 p02]; exists x0.
split; intros; [ rewrite <- (H t); apply p01 | ]; assumption.
Qed.

Lemma RiemannInt_integrable_minus : forall (f g:R -> R) (a b:R)
   (prf:Riemann_integrable f a b)
   (prg:Riemann_integrable g a b), (Riemann_integrable (fun x => f x - g x) a b).
Proof.
intros.
apply RiemannInt_integrable_eq_compat with (fun x => f x + (-1) * g x); [intros; ring|].
apply RiemannInt_P10; assumption.
Qed.

Lemma RiemannInt_minus :
  forall (f g:R -> R) (a b:R)
   (prf:Riemann_integrable f a b)
   (prg:Riemann_integrable g a b)
   (prfg:Riemann_integrable (fun x:R => f x - g x) a b),
     a<=b -> RiemannInt prfg = RiemannInt prf - RiemannInt prg.
Proof.
intros.
assert (REW: forall x y, x - y = x + (-1)*y) by (intros; ring); rewrite REW; clear REW.
pose proof (RiemannInt_P10 (-1) prf prg) as prfg'.
replace (RiemannInt prfg) with (RiemannInt prfg').
apply RiemannInt_P13.
apply RiemannInt_P18 ; intuition.
ring.
Qed.

Lemma RiemannInt_minus_1 : 
  forall (f g:R -> R) (a b:R)
   (prf:Riemann_integrable f a b)
   (prg:Riemann_integrable g a b),
     a<=b -> RiemannInt prf - RiemannInt prg = RiemannInt (RiemannInt_integrable_minus f g a b prf prg).
Proof.
 intros. rewrite (RiemannInt_minus _ _ _ _ prf prg) ; intuition.
Qed.


Lemma RiemannInt_linear_1 : 
  forall (f g:R -> R) (a b l:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable g a b),
    RiemannInt pr1 + l * RiemannInt pr2 = RiemannInt (Riemann_integrable_linear f g a b l pr1 pr2).
Proof.
 intros. symmetry. apply RiemannInt_linear.
Qed.

Lemma Riemann_integrable_add : 
   forall (f g:R -> R) (a b:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable g a b),
      Riemann_integrable (f + g)%F a b.
Proof.
 intros. apply RiemannInt_integrable_eq_compat with (fun x => f x + 1 * g x).
  intros. unfold plus_fct. ring.  apply Riemann_integrable_linear ; assumption.
Qed.

Lemma RiemannInt_add : 
  forall (f g:R -> R) (a b:R) (prf:Riemann_integrable f a b)
    (prg:Riemann_integrable g a b) (prfg:Riemann_integrable (f + g)%F a b), a <= b ->
    RiemannInt prf + RiemannInt prg = RiemannInt prfg.
Proof.
 intros. 
 pose proof (RiemannInt_P10 1 prf prg) as prfg'.
 replace (RiemannInt prfg) with (RiemannInt prfg').
  replace (RiemannInt prg) with (1 * RiemannInt prg) by ring.
  symmetry. apply RiemannInt_P13.
  
  apply RiemannInt_P18 ; intuition. unfold plus_fct. ring.
Qed.

Lemma RiemannInt_add_1 : 
 forall (f g:R -> R) (a b:R) (prf:Riemann_integrable f a b)
    (prg:Riemann_integrable g a b), a <= b ->
    RiemannInt prf + RiemannInt prg = RiemannInt (Riemann_integrable_add f g a b prf prg).
Proof.
 intros.
 apply RiemannInt_add. apply H.
Qed.  

Hint Rewrite RiemannInt_minus_1 : Rintegrals.
Hint Rewrite RiemannInt_linear_1 : Rintegrals.
Hint Rewrite RiemannInt_add_1 : Rintegrals.


Lemma continuity_RiemannInt_1 :
  forall (f:R -> R) (a b:R),
    (forall x:R, a <= x <= b \/ b <= x <= a -> continuity_pt f x) -> Riemann_integrable f a b.
Proof.
  intros; case (total_order_T a b); intro.
   elim s ; intro.
    apply RiemannInt_P6. assumption. intros. apply H. intuition.
    
    subst; apply RiemannInt_P7.

    apply Riemann_integrable_opp_bound. apply RiemannInt_P6. intuition.
     intros. apply H. intuition.
Qed.

(* TODO EN COURS copie de std lib Raffinage en cours *)
Lemma RiemannInt_derivable_pt_lim :
  forall (f:R -> R) (a x:R)
    (pr:forall x y:R,  Riemann_integrable f x y)
      (Hcont:continuity_pt f x),
      derivable_pt_lim (fun t1 => @RiemannInt f a t1 (pr a t1)) x (f x).
Proof.
 intros.
 unfold derivable_pt_lim. intros.
 (* epsilon is eps / 2 *)
 assert (H4:0 < eps / 2) by lra.
 destruct (Hcont _ H4) as [x1 [Hcont1 Hcont2]].
 exists (mkposreal _ Hcont1). (* TODO c'est pas le bon epsilon *)
 (* epsilon is eps / 2 end *)
 intros.
(* rewriting *)
 rewrite <- (RiemannInt_Chasles f a x (x+h) (pr a x) (pr x (x + h)) (pr a (x + h))).
 ring_simplify ((RiemannInt (pr a x) + RiemannInt (pr x (x + h)) - RiemannInt (pr a x))).
 replace (f x) with (RiemannInt (Riemann_integrable_constant x (x + h) (f x)) / h) 
  by (rewrite RiemannInt_constant; field; assumption).
  replace
  (RiemannInt (pr x (x + h)) / h - RiemannInt (Riemann_integrable_constant x (x + h) (f x)) / h)
    with ((RiemannInt (pr x (x + h)) + (-1) *  RiemannInt (Riemann_integrable_constant x (x + h) (f x))) / h) 
      by (unfold Rdiv ; ring).
  rewrite RiemannInt_linear_1.
(* end rewritiing *)
  unfold Rdiv in |- *; rewrite Rabs_mult; case (Rle_dec x (x + h)); intro.
(* case x <= x + h *)
(* passage de Rabs à l'interieur *)
  apply Rle_lt_trans with
     (RiemannInt
       (Riemann_integrable_Rabs _ _ _
         (Riemann_integrable_linear _ _ _ _ (-1) (pr x (x + h)) (Riemann_integrable_constant x (x + h) (f x)))) *
       Rabs (/ h)).
(* Preuve de Rabs int <= int Rabs *)
    do 2 rewrite <- (Rmult_comm (Rabs (/ h))); apply Rmult_le_compat_l.
    apply Rabs_pos. apply RiemannInt_le_Rabs. assumption.

(* Suite de la preuve avec int Rabs *)
    apply Rle_lt_trans with
      (RiemannInt (Riemann_integrable_constant x (x + h) (eps / 2)) * Rabs (/ h)).
  do 2 rewrite <- (Rmult_comm (Rabs (/ h))); apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply RiemannInt_P19; try assumption.
(* rewriting *)
  intros; replace (f x0 + -1 * fct_cte (f x) x0) with (f x0 - f x) by (intros ; unfold fct_cte ; simpl ; ring).
  unfold fct_cte.
(* end rewriting *)
(* x <> x0 *)
  assert (x <> x0) by (intro ; subst ; destruct H2 ; lra).
(* end x <> x0 *)
(* TODO pas besoin de x <= x+h là dedans*)
  left. simpl in *. unfold R_dist in *. apply Hcont2.
  unfold D_x, no_cond. repeat split. assumption.
  eapply Rlt_trans ; [|apply H1].
  assert (0 < x0 - x < h) by (intuition ; lra).
  rewrite Rabs_pos_eq. rewrite Rabs_pos_eq. intuition.
  apply Rle_trans with (x0 - x) ; intuition. intuition.
(* end TODO *) 
  

(*  rewrite Rabs_right. 
  apply Rplus_lt_reg_r with x; replace (x + (x1 - x)) with x1; [ idtac | ring ].
  apply Rlt_le_trans with (x + h). ring_simplify. apply H2.
   apply Rplus_le_compat_l. apply Rle_trans with x1. left.
   apply Rle_lt_trans with (Rabs h). apply RRle_abs. apply H1.
   (*unfold del.*) (*apply Rmin_l.*) right. reflexivity.
   destruct H2. lra.*)
(* TODO here need eps / 2 et x <= x + h*)
  rewrite RiemannInt_constant.
  rewrite Rmult_assoc; replace ((x + h - x) * Rabs (/ h)) with 1.
  ring_simplify. lra.
  rewrite Rabs_right.
  replace (x + h - x) with h; [ idtac | ring ].
  apply Rinv_r_sym.
  assumption.
  apply Rle_ge; left; apply Rinv_0_lt_compat.
  elim r; intro.
  apply Rplus_lt_reg_r with x; rewrite Rplus_comm, Rplus_0_r, Rplus_comm. assumption.
  elim H0; symmetry  in |- *; apply Rplus_eq_reg_l with x; rewrite Rplus_0_r;
    assumption.

(* case ~ x <= x + h *)
(* on insere la valeur absolu en echangeant les bornes *)
  apply Rle_lt_trans with 
    (RiemannInt
      (Riemann_integrable_Rabs _ _ _
         (Riemann_integrable_opp_bound _ _ _
          (Riemann_integrable_linear f (fct_cte (f x)) x 
           (x + h) (-1) (pr x (x + h))
           (Riemann_integrable_constant x (x + h) (f x))))) *
      Rabs (/ h)).
  do 2 rewrite <- (Rmult_comm (Rabs (/ h))); apply Rmult_le_compat_l.
  apply Rabs_pos. 
  rewrite RiemannInt_bound_exchange_1.
  rewrite Rabs_Ropp.
  apply RiemannInt_le_Rabs. left. intuition.
   apply Rle_lt_trans with
    (RiemannInt (Riemann_integrable_constant (x + h) x (eps / 2)) * Rabs (/ h)).
  do 2 rewrite <- (Rmult_comm (Rabs (/ h))); apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply RiemannInt_le_ext.
  auto with real.
  intros. unfold fct_cte in *. ring_simplify (-1 * f x).
  intros; replace (f x0 + -1 * fct_cte (f x) x0) with (f x0 - f x).
  unfold fct_cte in |- *; case (Req_dec x x0); intro.
  rewrite H3. ring_simplify (f x0 + - f x0). rewrite Rabs_R0; left;
    assumption.
  left; simpl in Hcont2 ; ring_simplify (f x0 + -1 * f x) ; apply Hcont2.
  repeat split.
  assumption.
  unfold R_dist. rewrite Rabs_left.
  apply Rplus_lt_reg_r with (x0 - x1); replace (x0 - x1 + x1) with x0 by ring.
  replace (- (x0 - x) + (x0 - x1)) with (x - x1) by ring.
  apply Rle_lt_trans with (x + h).
  unfold Rminus in |- *; apply Rplus_le_compat_l; apply Ropp_le_cancel.
  rewrite Ropp_involutive; apply Rle_trans with (Rabs h).

  rewrite <- Rabs_Ropp; apply RRle_abs.
  apply Rle_trans with x1;
    [ left; assumption | idtac ]. right. reflexivity.
  ring_simplify. now intuition.
  apply Rplus_lt_reg_r with x. ring_simplify. now intuition.
  unfold fct_cte in |- *; ring.
  rewrite RiemannInt_P15.
  rewrite Rmult_assoc; replace ((x - (x + h)) * Rabs (/ h)) with 1.
  rewrite Rmult_1_r; unfold Rdiv in |- *; apply Rmult_lt_reg_l with 2;
    [ prove_sup0
      | rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
        rewrite <- Rinv_r_sym;
          [ rewrite Rmult_1_l; pattern eps at 1 in |- *; rewrite <- Rplus_0_r;
            rewrite double; apply Rplus_lt_compat_l; assumption
            | discrR ] ].
  rewrite Rabs_left.
  replace (x - (x + h)) with (- h); [ idtac | ring ].
  rewrite Ropp_mult_distr_l_reverse; rewrite Ropp_mult_distr_r_reverse;
    rewrite Ropp_involutive; apply Rinv_r_sym.
  assumption.
  apply Rinv_lt_0_compat.
  assert (H8 : x + h < x).
  auto with real.
  apply Rplus_lt_reg_r with x. ring_simplify. rewrite Rplus_comm; assumption.
Qed.

Lemma RiemannInt_derivable_pt :
  forall (f:R -> R) (a x:R)
    (pr:forall x y:R,  Riemann_integrable f x y)
      (Hcont:continuity_pt f x),
      derivable_pt (fun t1 => @RiemannInt f a t1 (pr a t1)) x.
Proof.
 intros.
 unfold derivable_pt, derivable_pt_abs.
 exists (f x). apply RiemannInt_derivable_pt_lim.
assumption.
Qed.

Lemma derive_pt_RiemannInt : 
  forall (f:R -> R) (a x:R)
    (pr:forall x y:R,  Riemann_integrable f x y)
      (Hcont:continuity_pt f x),
        derive_pt (fun t => RiemannInt (pr a t)) x (RiemannInt_derivable_pt f a x pr Hcont) = f x.
Proof.
intros.
rewrite derive_pt_eq. apply RiemannInt_derivable_pt_lim.
apply Hcont.
Qed.
 
Lemma derive_pt_RiemannInt_1 : 
  forall (f:R -> R) (a x:R)
    (pr:forall x y:R,  Riemann_integrable f x y)
      (Hcont:continuity_pt f x) H1,
        derive_pt (fun t => RiemannInt (pr a t)) x H1 = f x.
Proof.
intros.
rewrite derive_pt_eq. apply RiemannInt_derivable_pt_lim.
apply Hcont.
Qed.


(* This lemma uses extentionality of continuity*)
Lemma derivable_pt_continuity_Riemann_implies_C1 : 
  forall f t0 (pr:forall t t0, Riemann_integrable f t t0), continuity f -> 
    C 1 (fun t => RiemannInt (pr t0 t)).
Proof.
intros.
assert (derivable (fun t => RiemannInt (pr t0 t))).
intro. apply RiemannInt_derivable_pt. apply H.
apply (C_S _ _ H0). 
apply C_0. apply continuity_ext with f.
intro. unfold derive. rewrite derive_pt_RiemannInt_1.
reflexivity.
apply H. apply H.
Qed.

(* TODO EN COURS preuve à changer pour ne pas utiliser la preuve sur derivable. *)
Lemma RiemannInt_continuity : forall a t0 (Hconta : continuity a) (Ha : forall t0 t, 
   Riemann_integrable a t0 t), continuity (fun t => RiemannInt (Ha t0 t)).
Proof.
 intros.
 apply derivable_continuous. unfold derivable. intros. apply RiemannInt_derivable_pt.
 apply Hconta.
Qed.
