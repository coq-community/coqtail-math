Require Import Rsequence Rsequence_stdlib.
Require Import Rseries_def Rseries_base_facts.

Local Open Scope Rseq_scope.


(** * Properties about positive term series *)

Lemma Rser_pos_growing: forall Un,
 (forall n, 0 <= Un n) -> Rseq_growing (Rseq_sum Un).
Proof.
intros Un Un_pos n ; transitivity (Rseq_sum Un n + 0)%R.
 rewrite Rplus_0_r ; reflexivity.
 apply Rplus_le_compat_l ; trivial.
Qed.

Lemma Rser_pos_strictly_growing: forall Un,
 (forall n, 0 < Un n) -> Rseq_strictly_growing (Rseq_sum Un).
Proof.
intros Un Un_pos n ; apply Rle_lt_trans with (Rseq_sum Un n + 0)%R.
 rewrite Rplus_0_r ; reflexivity.
 apply Rplus_lt_compat_l ; trivial.
Qed.

(** Positive term series convergence caracterization *)

Lemma Rser_pos_bound_cv : forall Un M,
 (forall n, 0 <= Un n) -> Rser_bound_max Un M -> { l | Rser_cv Un l }.
Proof.
intros Un M Un_pos Hb ; destruct ub_to_lub with (Rseq_sum Un) as [l Hl].
eapply Rseq_bound_max_has_ub ; eassumption.
exists l ; try apply tech10; apply Un_cv_crit_lub ; [apply Rser_pos_growing |] ; assumption.
Qed.

(** Properties using classical logic *)

Section Classical_facts.

Variables Un Vn : nat -> R.
Hypothesis Un_pos : forall n, 0 <= Un n.
Hypothesis NNPP : forall p : Prop, ~ ~ p -> p.
Hypothesis classic: forall P : Prop, P \/ ~ P.

(** Positive series are either convergent or go to infinity *)

Lemma Rser_pos_cv_dec : (exists l, Rser_cv Un l) \/ (Rser_cv_pos_infty Un).
Proof.
destruct (classic (exists l, Rser_cv Un l)) as [yes | no].
 left ; exact yes.
 right ; apply Rseq_unbounded_growing.
  apply NNPP.
  apply Rser_pos_growing ; assumption.
  intros [M HM] ; apply no ; destruct (Rser_pos_bound_cv _ _ Un_pos HM) as [l Hl] ;
  exists l ; assumption.
Qed.

End Classical_facts.


(** If a gt-positive series converges on an extractor, then it converges *)

Lemma Rser_cv_growing_subseq_compat: forall (An : Rseq) (phi : extractor) l,
  (forall n, 0 <= An n) ->  Rseq_cv ((Rseq_sum An) ⋅ phi)%Rseq l -> Rser_cv An l.
Proof.
intros An phi l A_pos Hcv ;
 apply Rseq_subseq_growing_cv_compat with ((Rseq_sum An) ⋅ phi).
 exists phi ; trivial.
 assumption.
 intro ; transitivity (Rseq_sum An n + 0)%R.
  rewrite Rplus_0_r ; reflexivity.
  simpl ; apply Rplus_le_compat_l ; trivial.
Qed.

(** If a gt-positive series converges on even or odd integers, then it converges *)

Lemma Rser_cv_growing_even_compat: forall An l,
  (forall n, 0 <= An n) ->  Rseq_cv (fun n => (Rseq_sum An (2*n))) l ->
  Rser_cv An l.
Proof.
intros An l An_pos Hcv ; assert (Hex : is_extractor (mult 2)) by (intro n ; lia) ;
apply Rser_cv_growing_subseq_compat with (exist _ _ Hex) ; assumption.
Qed.

Lemma Rser_cv_growing_odd_compat: forall An l,
  (forall n, 0 <= An n) ->  Rseq_cv (fun n => (Rseq_sum An (S (2*n)))) l ->
  Rser_cv An l.
Proof.
intros An l An_pos Hcv ; assert (Hex : is_extractor (fun n => S (2 * n))) by (intro n ; lia) ;
apply Rser_cv_growing_subseq_compat with (exist _ _ Hex) ; assumption.
Qed.
