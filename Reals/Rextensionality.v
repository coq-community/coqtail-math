Require Import Reals.
Require Import Rfunction_facts.
Require Import Rsequence_def.
Require Import Rpser_def Rpser_sums.

Section Functions_extensionality.

Variables f g : R -> R.
Hypothesis fg_ext : f == g.

Lemma continuity_ext : continuity f -> continuity g.
Proof.
intros f_cont x eps eps_pos.
 destruct (f_cont x _ eps_pos) as [delta [delta_pos Hdelta]].
 exists delta ; split ; [assumption |].
 intros ; do 2 rewrite <- fg_ext ; auto.
Qed.

Lemma derivable_pt_lim_ext : forall x l, derivable_pt_lim f x l ->
  derivable_pt_lim g x l.
Proof.
intros x l Hl eps eps_pos ; destruct (Hl _ eps_pos) as [delta Hdelta] ;
 exists delta ; intros ; do 2 rewrite <- fg_ext ; auto.
Qed.

Lemma derivable_pt_ext : forall x, derivable_pt f x ->
  derivable_pt g x.
Proof.
intros x [df Hdf] ; exists df ; apply derivable_pt_lim_ext ; trivial.
Qed.

Lemma derivable_ext : derivable f -> derivable g.
Proof.
intros f_deriv x ; apply derivable_pt_ext ; auto.
Qed.

Lemma derive_pt_ext (x : R) (prf : derivable_pt f x) (prg : derivable_pt g x) :
  derive_pt f x prf = derive_pt g x prg.
Proof.
apply pr_nu_var2 ; assumption.
Qed.

Lemma derive_ext (prf : derivable f) (prg : derivable g) :
  derive f prf == derive g prg.
Proof.
intro x ; unfold derive ; apply derive_pt_ext.
Qed.

End Functions_extensionality.

Section Rpser_extensionality.

Variables An Bn : Rseq.
Hypothesis AnBn_ext : (An == Bn)%Rseq.

Lemma gt_Pser_ext : forall x, (gt_Pser An x == gt_Pser Bn x)%Rseq.
Proof.
intros x n ; unfold gt_Pser ; rewrite AnBn_ext ; reflexivity.
Qed.

Lemma gt_abs_Pser_ext : forall x, (gt_abs_Pser An x == gt_abs_Pser Bn x)%Rseq.
Proof.
intros x n ; unfold gt_abs_Pser ; rewrite AnBn_ext ; reflexivity.
Qed.

Lemma Cv_radius_weak_ext : forall r, Cv_radius_weak An r <-> Cv_radius_weak Bn r.
Proof.
intro r ; split ; intros [B HB] ; exists B ; intros x [i Hi] ; subst ;
 [rewrite <- gt_abs_Pser_ext | rewrite gt_abs_Pser_ext] ; apply HB ; exists i ; reflexivity.
Qed.

Lemma finite_cv_radius_ext : forall r, finite_cv_radius An r <->
  finite_cv_radius Bn r.
Proof.
intro r ; split ; intros [rho_lb rho_ub] ; split ; intros r' Hr' ;
 [rewrite <- Cv_radius_weak_ext | rewrite <- Cv_radius_weak_ext
 | rewrite Cv_radius_weak_ext | rewrite Cv_radius_weak_ext] ; auto.
Qed.

Lemma infinite_cv_radius_ext : infinite_cv_radius An <->
  infinite_cv_radius Bn.
Proof.
split ; intros rho r ; [rewrite <- Cv_radius_weak_ext |
 rewrite Cv_radius_weak_ext] ; trivial.
Qed.


End Rpser_extensionality.

