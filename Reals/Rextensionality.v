Require Import Reals.
Require Import Rfunction_facts.

Section Extensionality.

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

End Extensionality.