(* Require Import Rpser_def Rpser_facts Rpser_usual.
Require Import Rfunction_facts Rextensionality.
Require Import C_n_def C_n.
Require Import Dequa_def.
Require Import Program.

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

Lemma diff_equa_cos : [| y 0 2 = - y 0 0 |] [existT C_infty cosine (C_infty_Rpser _ _)].
Proof.
intro x ; simpl ; unfold derive.
 replace ((- cosine) x) with (derive_pt (- sine) x (derivable_pt_opp _ _ (derivable_pt_sine x))).
 rewrite derive_pt_eq.
 apply derivable_pt_lim_ext with (- sine).
 intro a ; simpl ; symmetry ; rewrite derive_pt_eq ; apply derivable_pt_lim_cosine.
 rewrite <- derive_pt_eq ; reflexivity.
 reg ; [apply Ropp_eq_compat ; rewrite derive_pt_eq ; apply derivable_pt_lim_sine |
  apply derivable_pt_sine].
Qed.

Lemma diff_equa_sin : [| y 0 2 = - y 0 0 |] [existT C_infty sine (C_infty_Rpser _ _)].
Proof.
intro x ; simpl ; unfold derive.
 replace ((- sine) x) with (derive_pt cosine x (derivable_pt_cosine x)).
 rewrite derive_pt_eq.
 apply derivable_pt_lim_ext with cosine.
 intro a ; simpl ; symmetry ; rewrite derive_pt_eq ; apply derivable_pt_lim_sine.
 rewrite <- derive_pt_eq ; reflexivity.
 rewrite derive_pt_eq ; apply derivable_pt_lim_cosine.
Qed.
*)