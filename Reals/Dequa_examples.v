Require Import Rpser_def Rpser_facts Rpser_usual.
Require Import Rfunction_facts Rextensionality.
Require Import C_n_def C_n_facts C_n_usual.
Require Import Dequa_def.
Require Import List.

Local Open Scope R_scope.

Lemma nth_derive_ext : forall n f g (prf : C n f) (prg : C n g), f == g ->
    nth_derive f prf == nth_derive g prg.
Proof.
intro n ; induction n ; intros f g prf prg f_eq_g x.
 simpl ; trivial.
 simpl ; apply IHn.
 intro a ; unfold derive ; rewrite derive_pt_eq.
 apply derivable_pt_lim_ext with g.
 intro ; symmetry ; auto.
 rewrite <- derive_pt_eq ; reflexivity.
Qed.

Lemma derivable_nth_derive : forall n f (pr : derivable f) (pr1 : C (S n) f)
 (pr2 : C n (derive f pr)) l x, nth_derive (derive f pr) pr2 x = l ->
 nth_derive f pr1 x = l.
Proof.
intros n f pr pr1 pr2 l x Hl.
 simpl.
  rewrite nth_derive_ext with (g := derive f pr) (prg := pr2).
  assumption.
  intro ; unfold derive ; apply pr_nu_var ; reflexivity.
Qed.

Definition de_id : diff_equa := (y 0 1, cst 1)%de.
Definition rho_de_id : list (sigT Cn) :=
  (existT _ 1%nat (existT _ id (C_infty_id 1%nat))) :: nil.

Lemma diff_equa_id : [| de_id |]R rho_de_id.
Proof.
intro x ; unfold nth_derive', nth_derive, derive.
 rewrite derive_pt_eq ; apply derivable_pt_lim_id.
Qed.

Definition de_cos : diff_equa := (y 0 2, - y 0 0)%de.
Definition rho_de_cos : list (sigT Cn) :=
  (existT _ 2%nat (existT (C 2) cosine (C_infty_Rpser _ _ 2%nat))) :: nil.

Lemma diff_equa_cos : [| de_cos |]R rho_de_cos.
Proof.
intro x ; unfold nth_derive' ; simpl ; unfold derive.
 replace ((- cosine)%F x) with
 (derive_pt (- sine) x (derivable_pt_opp _ _ (derivable_pt_sine x))).
 rewrite derive_pt_eq.
 apply derivable_pt_lim_ext with (- sine)%F.
 intro a ; simpl ; symmetry ; rewrite derive_pt_eq ; apply derivable_pt_lim_cosine.
 apply derivable_pt_lim_opp ; apply derivable_pt_lim_sine.
 rewrite derive_pt_eq ; apply derivable_pt_lim_opp ; apply derivable_pt_lim_sine.
Qed.

Require Import Rsequence_def.

Definition Option_app_Prop {A : Type} (P : A -> Prop) (Oa : option A) : Prop :=
match Oa with
  | None   => True
  | Some a => P a
end.

Definition corresponding_Rpser (l : list Rseq)
 (cvl : forall n, Option_app_Prop infinite_cv_radius (nth_error l n)) : list Cinfty.
induction l.
 apply nil.
 apply cons.
  assert (H := cvl O) ; simpl in H ; exists (sum a H) ; apply C_infty_Rpser.
  apply IHl ; intro n ; apply (cvl (S n)).
Defined.

(*
Lemma diff_sequences_functions : forall (e : diff_equa) (l : list Rseq)
  (cvl : forall n, Option_app_Prop infinite_cv_radius (nth_error l n)),
  [| e |]N l ->
  [| e |]R2 (corresponding_Rpser l cvl).
Proof.
intros [s1 s2] l cvl Heq.
 destruct s1.
 simpl in *.

Qed.

Lemma side_sequences_functions : forall (s : side_equa) (l : list Rseq)
 (cvl : forall n, Option_app_Prop infinite_cv_radius (nth_error l n))

*)
