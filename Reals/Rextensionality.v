Require Import Reals.
Require Import Rsequence_def.
Require Import Rpser_def Rpser_def_simpl Rpser_base_facts Rpser_sums Rpser_cv_facts.
Require Import Rinterval Ranalysis_def Rfunction_facts.
Require Import Tactics.

(** * Extensionality of the common properties of functions. *)

(** Usual properties. *)

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

(** * Extensionality of power serie related concepts. *)

Section Rpser_extensionality.

Variables An Bn : Rseq.
Hypothesis AnBn_ext : (An == Bn)%Rseq.

Lemma sum_f_R0_ext : (sum_f_R0 An == sum_f_R0 Bn)%Rseq.
Proof.
intro n ; induction n ; simpl ; rewrite AnBn_ext ;
 [| rewrite IHn] ; reflexivity.
Qed.

Lemma Pser_ext : forall x l, Pser An x l <-> Pser Bn x l.
Proof.
intros x l ; split ; intros HP eps eps_pos ; destruct (HP _ eps_pos) as [N HN] ;
 exists N ; intros n n_lb ;
 [rewrite (sum_eq _ (fun n => An n * x ^ n)%R) |
 rewrite (sum_eq _ (fun n => Bn n * x ^ n)%R)] ;
 ((apply HN ; assumption) || (intros ; rewrite AnBn_ext ; reflexivity)).
Qed.

Lemma weaksum_r_ext : forall (r : R) (rAn : Cv_radius_weak An r)
 (rBn : Cv_radius_weak Bn r),
 weaksum_r An r rAn == weaksum_r Bn r rBn.
Proof.
intros r rAn rBn x.
 unfold weaksum_r ; destruct (Rlt_le_dec (Rabs x) r) ; trivial.
 destruct (Rpser_abel _ _ rAn x r0) as [l1 Hl1] . pose proof Hl1 as Hl0.
  rewrite Pser_ext in Hl0.
 destruct (Rpser_abel _ _ rBn x r0) as [l2 Hl2].
 simpl ; eapply Rpser_unique ; eassumption.
Qed.

Lemma sum_r_ext : forall (r : R) (rAn : finite_cv_radius An r)
 (rBn : finite_cv_radius Bn r),
 sum_r An r rAn == sum_r Bn r rBn.
Proof.
intros r rAn rBn x.
 unfold sum_r ; destruct (Rlt_le_dec (Rabs x) r) ; trivial ;
  apply weaksum_r_ext.
Qed.

Lemma sum_ext : forall (rAn : infinite_cv_radius An)
  (rBn : infinite_cv_radius Bn),
  sum An rAn == sum Bn rBn.
intros rAn rBn x ; unfold sum ; apply weaksum_r_ext.
Qed.

End Rpser_extensionality.

