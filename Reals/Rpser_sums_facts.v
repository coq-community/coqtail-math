Require Import Reals.
Require Import Rsequence_def.
Require Import Rpser_def Rpser_sums Rpser_base_facts Rpser_cv_facts.

Require Import Rextensionality.
Require Import Rfunction_def.

Open Local Scope R_scope.

Section sum_compatibilities.

Variables An Bn : Rseq.
Hypotheses
  (rAn : infinite_cv_radius An)
  (rBn : infinite_cv_radius Bn).

Lemma sum_opp_compat : forall (rAn' : infinite_cv_radius (- An)),
  sum (- An)%Rseq rAn' == (- sum An rAn)%F.
Proof.
intros rAn' x.
 assert (H1 := sum_sums (- An)%Rseq rAn' x) ;
 assert (H2 := Pser_opp_compat _ _ _ (sum_sums An rAn x)) ;
 eapply Pser_unique ; eassumption.
Qed.

Lemma sum_plus_compat : forall (rAnBn : infinite_cv_radius (An + Bn)),
  sum (An + Bn)%Rseq rAnBn == (sum An rAn + sum Bn rBn)%F.
Proof.
intros rAnBn x.
 assert (Ha := sum_sums An rAn x) ;
 assert (Hb := sum_sums Bn rBn x) ;
 assert (H1 := sum_sums (An + Bn)%Rseq rAnBn x) ;
 assert (H2 := Pser_add_compat _ _ _ _ _ Ha Hb) ;
 eapply Pser_unique ; eassumption.
Qed.

Lemma sum_minus_compat : forall (rAnBn : infinite_cv_radius (An - Bn)),
  sum (An - Bn)%Rseq rAnBn == (sum An rAn - sum Bn rBn)%F.
Proof.
intros rAnBn x.
 assert (Ha := sum_sums An rAn x) ;
 assert (Hb := sum_sums Bn rBn x) ;
 assert (H1 := sum_sums (An - Bn)%Rseq rAnBn x) ;
 assert (H2 := Pser_minus_compat _ _ _ _ _ Ha Hb) ;
 eapply Pser_unique ; eassumption.
Qed.

End sum_compatibilities.