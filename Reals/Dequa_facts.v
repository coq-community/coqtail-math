Require Import Rsequence_def Rsequence_sums_facts.
Require Import Rpser.
Require Import Rfunction_facts Rextensionality.
Require Import C_n_def C_n_facts C_n_usual.
Require Import Nth_derivative_def Nth_derivative_facts.
Require Import Dequa_def.
Require Import List.
Require Import Max.
Require Import Ass_handling.

Local Open Scope R_scope.

Fixpoint max_y_se (s : side_equa) : nat := match s with
  | y _ p      => p
  | opp s      => max_y_se s
  | plus s1 s2 => max (max_y_se s1) (max_y_se s2)
  | _ => O
end.

Definition max_y (e : diff_equa) : nat :=
let (s1, s2) := e in max (max_y_se s1) (max_y_se s2).

Definition Cinfty_to_Cn (c : Cinfty) (p : nat) : Cn p :=
let (f, Cf) := c in existT _ f (Cf p).

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

Definition OptionApp {A B : Type} (f : option (A -> B)) (a : A) : option B :=
match f with
  | None   => None
  | Some f => Some (f a)
end.

Lemma interp_side_equa_in_R2_R : forall (s : side_equa)
  (l : list Cinfty) (p : nat) (p_lb : (max_y_se s <= p)%nat),
  forall x,
  OptionApp (interp_side_equa_in_R2 s l) x =
  OptionApp (interp_side_equa_in_R s (map (fun cinf =>
    existT _ p (Cinfty_to_Cn cinf p)) l)) x.
Proof.
intro s ; induction s ; intros l n n_lb x ; simpl in *.

 reflexivity.

 destruct_eq (nth_error l p) ; symmetry in Heqb.
  rewrite (map_nth_error _ _ _ Heqb) ;
   destruct c as [h Ch] ; destruct (le_lt_dec k n) ;
   [ | exfalso ; omega] ; simpl ; f_equal ;
   apply nth_derive'_PI.
  rewrite (map_nth_error_None _ _ _ Heqb) ; reflexivity.

 destruct_eq (interp_side_equa_in_R2 s l) ;
 destruct_eq (interp_side_equa_in_R s (map (fun cinf : Cinfty =>
 existT Cn n (Cinfty_to_Cn cinf n)) l)) ; assert (Hrew := IHs l _ n_lb x) ;
 symmetry in Heqb, Heqb0 ; rewrite Heqb, Heqb0 in Hrew ; inversion Hrew.
  simpl ; f_equal ; apply Ropp_eq_compat ; assumption.
  reflexivity.

 destruct_eq (interp_side_equa_in_R2 s1 l) ;
 destruct_eq (interp_side_equa_in_R2 s2 l) ;
 destruct_eq (interp_side_equa_in_R s1 (map (fun cinf : Cinfty =>
 existT Cn n (Cinfty_to_Cn cinf n)) l)) ;
 destruct_eq (interp_side_equa_in_R s2 (map (fun cinf : Cinfty =>
 existT Cn n (Cinfty_to_Cn cinf n)) l)) ;
 assert (n_lb1 : (max_y_se s1 <= n)%nat) by (eapply le_trans ;
 [ | eapply n_lb] ; apply le_max_l) ;
 assert (n_lb2 : (max_y_se s2 <= n)%nat) by (eapply le_trans ;
 [ | eapply n_lb] ; apply le_max_r) ;
 assert (Hrew1 := IHs1 l _ n_lb1 x) ;
 assert (Hrew2 := IHs2 l _ n_lb2 x) ;
 symmetry in Heqb, Heqb0, Heqb1, Heqb2 ; rewrite Heqb, Heqb1 in Hrew1 ;
 rewrite Heqb0, Heqb2 in Hrew2 ; inversion Hrew1 ; inversion Hrew2.
  compute ; do 2 f_equal ; assumption.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Lemma interp_in_R2_R : forall (e : diff_equa) (l : list Cinfty),
  [| e |]R2 l <-> [| e |]R (map (fun cinf =>
    existT _ _ (Cinfty_to_Cn cinf (max_y e))) l).
Proof.
intros e l ; pose (p := max_y e) ; destruct e as [s1 s2] ;
 simpl in * ; fold p ;
 assert (p_lb1 : (max_y_se s1 <= p)%nat) by apply le_max_l ;
 assert (p_lb2 : (max_y_se s2 <= p)%nat) by apply le_max_r ;
 assert (Hrew1 := interp_side_equa_in_R2_R s1 l p p_lb1) ;
 assert (Hrew2 := interp_side_equa_in_R2_R s2 l p p_lb2).

 destruct_eq (interp_side_equa_in_R2 s1 l) ;
 destruct_eq (interp_side_equa_in_R s1 (map (fun cinf =>
    existT _ _ (Cinfty_to_Cn cinf p)) l)).
 destruct_eq (interp_side_equa_in_R2 s2 l) ;
 destruct_eq (interp_side_equa_in_R s2 (map (fun cinf =>
    existT _ _ (Cinfty_to_Cn cinf p)) l)).

 split ; intros H x.
  assert (T := Hrew1 x) ; inversion_clear T ;
  assert (T := Hrew2 x) ; inversion_clear T ;
  apply H.
  assert (T1 := Hrew1 x) ; inversion T1 as [H1 ] ;
  assert (T2 := Hrew2 x) ; inversion T2 as [H2 ] ;
  rewrite H1, H2 ; apply H.

 assert (Hf := Hrew2 0) ; inversion Hf.
 assert (Hf := Hrew2 0) ; inversion Hf.
 split ; intro H ; apply H.

 assert (Hf := Hrew1 0) ; inversion Hf.
 assert (Hf := Hrew1 0) ; inversion Hf.
 split ; intro H ; apply H.
Qed.

Lemma interp_in_R2_R_fold : forall (e : diff_equa) (l : list Cinfty),
  [| e |]R2 l ->
  { l' : list (sigT Cn) | [| e |]R2 l <->  [| e |]R l'}.
Proof.
intros e l Heq ; pose (p := max_y e) ;
 exists (map (fun cinf => existT _ p (Cinfty_to_Cn cinf p)) l) ;
 apply interp_in_R2_R.
Qed.

Definition OptionArg {A B : Type} (f : A -> B) (a : option A) : option B :=
match a with
  | Some x => Some (f x)
  | None => None
end.

Lemma interp_side_equa_in_N_SN : forall (s : side_equa) (l : list Rseq) (n : nat) (x : R),
  OptionArg (fun e => Rseq_pps e x n) (interp_side_equa_in_N s l)
  = OptionApp (OptionApp (interp_side_equa_in_SN s l) n) x.
Proof.
intros s l n x ; induction s.

 simpl ; f_equal.
 
 simpl ; destruct (nth_error l p) as [un |] ; reflexivity.

 simpl ; destruct (interp_side_equa_in_N s l) ;
  destruct (interp_side_equa_in_SN s l) ; simpl in * ;
  inversion IHs as [Heq ].
   rewrite Rseq_pps_opp_compat ; unfold Rseq_opp ;
    rewrite Heq ; reflexivity.
   reflexivity.

 simpl ; destruct (interp_side_equa_in_N s1 l) ;
  destruct (interp_side_equa_in_SN s1 l) ; simpl in * ;
  inversion IHs1 as [Heq1 ] ; destruct (interp_side_equa_in_N s2 l) ;
  destruct (interp_side_equa_in_SN s2 l) ; simpl in * ;
  inversion IHs2 as [Heq2 ] ; try reflexivity.
 rewrite Rseq_pps_plus_compat ; unfold Rseq_plus, plus_fct ;
 rewrite Heq1, Heq2 ; reflexivity.
Qed.

Lemma interp_equa_in_N_SN : forall (e : diff_equa) (l : list Rseq),
  [| e |]N l -> [| e |]SN l.
Proof.
intros [s1 s2] l Heq ; simpl in * ;
 assert (H1 := interp_side_equa_in_N_SN s1 l) ;
 assert (H2 := interp_side_equa_in_N_SN s2 l).
 
 destruct (interp_side_equa_in_N s1 l).
  destruct (interp_side_equa_in_N s2 l).
   destruct (interp_side_equa_in_SN s1 l).
    destruct (interp_side_equa_in_SN s2 l).
    simpl in * ; intros n x ;
     assert (H1' := H1 n x) ; inversion_clear H1' ;
     assert (H2' := H2 n x) ; inversion_clear H2' ;
     apply Rseq_pps_ext ; assumption.
    assert (H2' := H2 O 0) ; inversion H2'.
   assert (H1' := H1 O 0) ; inversion H1'.
  destruct Heq.
 destruct Heq.
Qed.

Lemma interp_side_equa_in_N_R3 : forall (s : side_equa)
  (l : list (sigT infinite_cv_radius)) (Un : Rseq) (f : R -> R),
  interp_side_equa_in_N s (map (@projT1 _ infinite_cv_radius) l) = Some Un ->
  interp_side_equa_in_R3 s l = Some f ->
  {pr : infinite_cv_radius Un | sum Un pr == f}.
Proof.
intro s ; induction s ; simpl ; intros l Un f HN HR3.

 inversion HN ; inversion HR3 ; subst ; exists (cst_infinite_cv_radius r) ;
  apply constant_is_cst.

 assert (Hrew := map_nth_error (@projT1 _ infinite_cv_radius) p l) ;
 destruct (nth_error l p).
  specify2 Hrew s (eq_refl (Some s)) ; destruct s as [An rAn] ;
  rewrite Hrew in HN ; inversion HN as [HN0] ; destruct HN0 ;
  inversion HR3 as [HR30] ; destruct HR30.
  assert (pr : infinite_cv_radius (An_nth_deriv An k)).
   rewrite <- infinite_cv_radius_nth_derivable_compat ; assumption.
  exists pr ; symmetry ; apply nth_derive_sum_explicit.
 inversion HR3.

 destruct_eq (interp_side_equa_in_N s (map (@projT1 _ infinite_cv_radius) l)).
  destruct_eq (interp_side_equa_in_R3 s l).
   symmetry in Heqb ; symmetry in Heqb0 ; specify5 IHs l r r0 Heqb Heqb0.
   inversion HR3 as [Hrew] ; destruct Hrew.
   inversion HN as [Hrew] ; destruct Hrew.
   destruct IHs as [rho Hrho].
   assert (pr : infinite_cv_radius (- r)) by
    (rewrite infinite_cv_radius_opp_compat ; assumption).
   exists pr ; intro x ; unfold opp_fct ; rewrite <- Hrho ;
   apply sum_opp_compat.
  inversion HR3.
 inversion HN.

 destruct_eq (interp_side_equa_in_N s1 (map (@projT1 _ infinite_cv_radius) l)).
  destruct_eq (interp_side_equa_in_N s2 (map (@projT1 _ infinite_cv_radius) l)).
   destruct_eq (interp_side_equa_in_R3 s1 l).
    destruct_eq (interp_side_equa_in_R3 s2 l).
     inversion HN as [Hrew] ; destruct Hrew ;
     inversion HR3 as [Hrew] ; destruct Hrew.
     symmetry in Heqb, Heqb0, Heqb1, Heqb2.
     specify5 IHs1 l r r1 Heqb Heqb1 ;
     specify5 IHs2 l r0 r2 Heqb0 Heqb2.
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

Lemma interp_side_equa_in_N_R3_compat : forall s l un,
  interp_side_equa_in_N s (map (@projT1 _ infinite_cv_radius) l) = Some un ->
  {f | interp_side_equa_in_R3 s l = Some f}.
Proof.
intro s ; induction s ; intros l un H.
 exists (fun _ => r) ; reflexivity.

 assert (Hrew := map_nth_error (@projT1 _ infinite_cv_radius) p l) ;
 destruct_eq (nth_error l p).
  specify2 Hrew s (eq_refl (Some s)).
  destruct s as [An rAn] ; simpl in H, Hrew ; rewrite Hrew in H.
  exists (nth_derive (sum An rAn) (C_infty_Rpser An rAn k)).
  simpl ; rewrite <- Heqb ; reflexivity.
 symmetry in Heqb ; simpl in H.
 assert (T := map_nth_error2 (@projT1 _ infinite_cv_radius) _ _ Heqb).
 rewrite T in H ; inversion H.

 simpl in * ;
  destruct_eq (interp_side_equa_in_N s (map (@projT1 _ infinite_cv_radius) l)) ;
  symmetry in Heqb.
   specify3 IHs l r Heqb ; destruct IHs as [f Hf].
   exists (- f)%F ; rewrite Hf ; reflexivity.
 inversion H.

 simpl in *.
  destruct_eq (interp_side_equa_in_N s1 (map (@projT1 _ infinite_cv_radius) l)) ;
  symmetry in Heqb.
   destruct_eq (interp_side_equa_in_N s2 (map (@projT1 _ infinite_cv_radius) l)) ;
   symmetry in Heqb0.
    specify3 IHs1 l r Heqb ; destruct IHs1 as [f Hf] ;
    specify3 IHs2 l r0 Heqb0 ; destruct IHs2 as [g Hg].
    exists (f + g)%F ; rewrite Hf, Hg ; reflexivity.
   inversion H.
  inversion H.
Qed.

Lemma interp_equa_in_N_R3 : forall (e : diff_equa)
  (l : list (sigT infinite_cv_radius)),
  [| e |]N (map (@projT1 _ infinite_cv_radius) l) -> [| e |]R3 l.
Proof.
intros [s1 s2] l H ; simpl in *.
 destruct_eq (interp_side_equa_in_N s1 (map (@projT1 _ infinite_cv_radius) l)).
  destruct_eq (interp_side_equa_in_N s2 (map (@projT1 _ infinite_cv_radius) l)).
   destruct_eq (interp_side_equa_in_R3 s1 l).
    destruct_eq (interp_side_equa_in_R3 s2 l).
     symmetry in Heqb, Heqb0, Heqb1, Heqb2.
     destruct (interp_side_equa_in_N_R3 s1 l r r1 Heqb Heqb1) as [rho1 Hrho1].
     destruct (interp_side_equa_in_N_R3 s2 l r0 r2 Heqb0 Heqb2) as [rho2 Hrho2].
     rewrite <- Hrho1, <- Hrho2 ; apply sum_ext ; assumption.
    symmetry in Heqb0 ;
    destruct (interp_side_equa_in_N_R3_compat _ _ _ Heqb0) as [f Hf] ;
    rewrite Hf in Heqb2 ; inversion Heqb2.
   symmetry in Heqb ;
   destruct (interp_side_equa_in_N_R3_compat _ _ _ Heqb) as [f Hf] ;
   rewrite Hf in Heqb1 ; inversion Heqb1.
  inversion H.
 inversion H.
Qed.