Require Import Rsequence_def Rsequence_sums_facts.
Require Import Rpser.
Require Import Rfunction_facts Rextensionality.
Require Import Rfunction_classes.
Require Import Nth_derivative_def Nth_derivative_facts.
Require Import Dequa_def.
Require Import List.
Require Import Max.
Require Import Tactics.
Require Import Option.

Local Open Scope R_scope.

Lemma map_nth_error_None_iff : forall {A B : Type} (l : list A) (f : A -> B) (n : nat),
  nth_error l n = None <-> nth_error (map f l) n = None.
Proof.
intros A B l f n ; revert l ; induction n ; intro l.
 destruct l ; simpl ; split ; auto ; intro H ; inversion H.
 destruct l ; simpl ; [split ; auto ; intro H ; inversion H | apply IHn].
Qed.

Lemma map_nth_error_None : forall {A B : Type} (l : list A) (f : A -> B) (n : nat),
  nth_error l n = None -> nth_error (map f l) n = None.
Proof.
intros ; apply map_nth_error_None_iff ; assumption.
Qed.

Definition App {A B : Type} f (a : A) : option B := Bind f (fun g => g a).

Lemma interp_side_equa_in_N_R : forall s l Un f,
  interp_side_equa_in_N s (map (@projT1 _ infinite_cv_radius) l) = Some Un ->
  interp_side_equa_in_R s l = Some f ->
  {pr : infinite_cv_radius Un | sum Un pr == f}.
Proof.
intro s ; induction s ; simpl ; intros l Un f HN HR3.

 inversion HN ; inversion HR3 ; subst ; exists (constant_infinite_cv_radius r) ;
  apply constant_is_cst.

 destruct (interp_side_equa_in_N s (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb.
  destruct (interp_side_equa_in_R s l) eqn:Heqb0.
   specialize (IHs l r0 r1 Heqb Heqb0).
   inversion HR3 as [Hrew] ; destruct Hrew.
   inversion HN as [Hrew] ; destruct Hrew.
   destruct IHs as [rho Hrho].
   assert (pr : infinite_cv_radius (r * r0)).
    destruct (Req_dec r 0) as [Heq | Hneq].
     rewrite Heq ; simpl ; rewrite <- (infinite_cv_radius_ext (Rseq_constant 0)) ;
      [apply zero_infinite_cv_radius | intro n ; unfold Rseq_mult ;
      rewrite Rmult_0_l ; reflexivity].
     rewrite <- infinite_cv_radius_scal_compat ; assumption.
   exists pr ; intro x ; unfold mult_fct ; rewrite <- Hrho.
   apply sum_scal_compat.
  inversion HR3.
 inversion HN. 

 assert (Hrew := map_nth_error (@projT1 _ infinite_cv_radius) p l) ;
  unfold Bind in * ; destruct (nth_error l p).
  specialize (Hrew s (eq_refl (Some s))); destruct s as [An rAn] ;
  rewrite Hrew in HN ; inversion HN as [HN0] ; destruct HN0 ;
   inversion HR3 as [HR30] ; destruct HR30.
   assert (ppr: infinite_cv_radius (An_nth_deriv An k)).
    rewrite <- infinite_cv_radius_nth_derivable_compat ; assumption.
   assert (pr : infinite_cv_radius (An_expand (An_nth_deriv An k) a)).
    apply infinite_cv_radius_expand_compat ; assumption.
   exists pr ; intro x ; symmetry ; rewrite (sum_expand_compat _ ppr).
   erewrite <- nth_derive_sum_explicit ; reflexivity.
  inversion HR3.

 destruct (interp_side_equa_in_N s (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb.
  destruct (interp_side_equa_in_R s l) eqn:Heqb0.
   specialize (IHs l r r0 Heqb Heqb0).
   inversion HR3 as [Hrew] ; destruct Hrew.
   inversion HN as [Hrew] ; destruct Hrew.
   destruct IHs as [rho Hrho].
   assert (pr : infinite_cv_radius (- r)) by
    (rewrite <- infinite_cv_radius_opp_compat ; assumption).
   exists pr ; intro x ; unfold opp_fct ; rewrite <- Hrho ;
   apply sum_opp_compat.
  inversion HR3.
 inversion HN.

 destruct (interp_side_equa_in_N s1 (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb.
  destruct (interp_side_equa_in_N s2 (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb0.
   destruct (interp_side_equa_in_R s1 l) eqn:Heqb1.
    destruct (interp_side_equa_in_R s2 l) eqn:Heqb2.
     inversion HN as [Hrew] ; destruct Hrew ;
     inversion HR3 as [Hrew] ; destruct Hrew.
     specialize (IHs1 l r r1 Heqb Heqb1);
     specialize (IHs2 l r0 r2 Heqb0 Heqb2).
     destruct IHs1 as [rho1 Hrho1] ;
     destruct IHs2 as [rho2 Hrho2].
     assert (pr : infinite_cv_radius (r - r0)).
      apply infinite_cv_radius_minus_compat ; assumption.
     exists pr.
     intro x ; unfold minus_fct ; rewrite <- Hrho1, <- Hrho2 ;
     apply sum_minus_compat.
    inversion HR3.
   inversion HR3.
  inversion HN.
 inversion HN.

 destruct (interp_side_equa_in_N s1 (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb.
  destruct (interp_side_equa_in_N s2 (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb0.
   destruct (interp_side_equa_in_R s1 l) eqn:Heqb1.
    destruct (interp_side_equa_in_R s2 l) eqn:Heqb2.
     inversion HN as [Hrew] ; destruct Hrew ;
     inversion HR3 as [Hrew] ; destruct Hrew.
     specialize (IHs1 l r r1 Heqb Heqb1);
     specialize (IHs2 l r0 r2 Heqb0 Heqb2).
     destruct IHs1 as [rho1 Hrho1] ;
     destruct IHs2 as [rho2 Hrho2].
     assert (pr : infinite_cv_radius (r + r0)).
      apply infinite_cv_radius_plus_compat ; assumption.
     exists pr.
     intro x ; unfold plus_fct ; rewrite <- Hrho1, <- Hrho2 ;
     apply sum_plus_compat.
    inversion HR3.
   inversion HR3.
  inversion HN.
 inversion HN.

 destruct (interp_side_equa_in_N s1 (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb.
  destruct (interp_side_equa_in_N s2 (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb0.
   destruct (interp_side_equa_in_R s1 l) eqn:Heqb1.
    destruct (interp_side_equa_in_R s2 l) eqn:Heqb2.
     inversion HN as [Hrew] ; destruct Hrew ;
     inversion HR3 as [Hrew] ; destruct Hrew.
     specialize (IHs1 l r r1 Heqb Heqb1);
     specialize (IHs2 l r0 r2 Heqb0 Heqb2).
     destruct IHs1 as [rho1 Hrho1] ;
     destruct IHs2 as [rho2 Hrho2].
     assert (pr : infinite_cv_radius (r # r0)).
      apply infinite_cv_radius_prod_compat ; assumption.
     exists pr.
     intro x ; unfold mult_fct ; rewrite <- Hrho1, <- Hrho2 ;
     apply sum_mult_compat.
    inversion HR3.
   inversion HR3.
  inversion HN.
 inversion HN.
Qed.

Lemma map_nth_error2 {A B : Type} : forall f l p,
  nth_error l p = @None A -> nth_error (map f l) p = @None B.
Proof.
intros f l p ; revert l ; induction p ; intro l ; destruct l.
 trivial.
 intro Hf ; inversion Hf.
 trivial.
 simpl ; apply IHp.
Qed.

Lemma interp_side_equa_in_N_R_compat : forall s l un,
  interp_side_equa_in_N s (map (@projT1 _ infinite_cv_radius) l) = Some un ->
  {f | interp_side_equa_in_R s l = Some f}.
Proof.
intro s ; induction s ; intros l un H.
 exists (fun _ => r) ; reflexivity.

 simpl in * ; destruct (interp_side_equa_in_N s (map
 (@projT1 _ infinite_cv_radius) l)) eqn: Heqb.
  specialize (IHs l r0 Heqb); destruct IHs as [f Hf] ;
  exists ((fun _ => r) * f)%F ; rewrite Hf ; reflexivity.
 inversion H.

 assert (Hrew := map_nth_error (@projT1 _ infinite_cv_radius) p l) ;
 destruct (nth_error l p) eqn:Heqb.
  specialize (Hrew s (eq_refl (Some s))).
  destruct s as [An rAn] ; simpl in H, Hrew ; rewrite Hrew in H ;
   simpl in H ; exists (fun x => nth_derive (sum An rAn) (D_infty_Rpser An rAn k) (a * x)) ;
   simpl ; rewrite Heqb ; reflexivity.
   simpl in H.
 assert (T := map_nth_error2 (@projT1 _ infinite_cv_radius) _ _ Heqb).
 rewrite T in H ; inversion H.

 simpl in * ;
  destruct (interp_side_equa_in_N s (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb.
   specialize (IHs l r Heqb); destruct IHs as [f Hf].
   exists (- f)%F ; rewrite Hf ; reflexivity.
 inversion H.

 simpl in *.
  destruct (interp_side_equa_in_N s1 (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb.
   destruct (interp_side_equa_in_N s2 (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb0.
    specialize (IHs1 l r Heqb); destruct IHs1 as [f Hf] ;
    specialize (IHs2 l r0 Heqb0); destruct IHs2 as [g Hg].
    exists (f - g)%F ; rewrite Hf, Hg ; reflexivity.
   inversion H.
  inversion H.

 simpl in *.
  destruct (interp_side_equa_in_N s1 (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb.
   destruct (interp_side_equa_in_N s2 (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb0.
    specialize (IHs1 l r Heqb); destruct IHs1 as [f Hf] ;
    specialize (IHs2 l r0 Heqb0); destruct IHs2 as [g Hg].
    exists (f + g)%F ; rewrite Hf, Hg ; reflexivity.
   inversion H.
  inversion H.

 simpl in *.
  destruct (interp_side_equa_in_N s1 (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb.
   destruct (interp_side_equa_in_N s2 (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb0.
    specialize (IHs1 l r Heqb); destruct IHs1 as [f Hf] ;
    specialize (IHs2 l r0 Heqb0); destruct IHs2 as [g Hg].
    exists (f * g)%F ; rewrite Hf, Hg ; reflexivity.
   inversion H.
  inversion H.
Qed.

Lemma interp_equa_in_N_R : forall (e : diff_equa)
  (l : list (sigT infinite_cv_radius)),
  [| e |]N (map (@projT1 _ infinite_cv_radius) l) -> [| e |]R l.
Proof.
intros [s1 s2] l H ; simpl in *.
 destruct (interp_side_equa_in_N s1 (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb.
  destruct (interp_side_equa_in_N s2 (map (@projT1 _ infinite_cv_radius) l)) eqn:Heqb0.
   destruct (interp_side_equa_in_R s1 l) eqn:Heqb1.
    destruct (interp_side_equa_in_R s2 l) eqn:Heqb2.
     destruct (interp_side_equa_in_N_R s1 l r r1 Heqb Heqb1) as [rho1 Hrho1].
     destruct (interp_side_equa_in_N_R s2 l r0 r2 Heqb0 Heqb2) as [rho2 Hrho2].
     rewrite <- Hrho1, <- Hrho2 ; apply sum_ext ; assumption.
    destruct (interp_side_equa_in_N_R_compat _ _ _ Heqb0) as [f Hf] ;
    rewrite Hf in Heqb2 ; inversion Heqb2.
   destruct (interp_side_equa_in_N_R_compat _ _ _ Heqb) as [f Hf] ;
   rewrite Hf in Heqb1 ; inversion Heqb1.
  inversion H.
 inversion H.
Qed.
