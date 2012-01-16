Require Import Rsequence_def Rsequence_sums_facts Rsequence_rewrite_facts.
Require Import MyNat.
Require Import Rfunction_def.

Local Open Scope R_scope.

Definition D (f : R -> R) : R -> R := fun x => f (x + 1) - f x.
Definition Int (a b: nat) (f : R -> R) : R :=
  Rseq_sum (Rseq_shifts (fun n => f (INR n)) a) (b - a).

Lemma D_opp_compat : forall f, D (- f)%F == (- D f)%F.
Proof.
intros f x ; unfold D, opp_fct ; ring.
Qed.

Lemma D_plus_compat : forall f g, D (f + g)%F == (D f + D g)%F.
Proof.
intros f g x ; unfold D, plus_fct ; ring.
Qed.

Lemma D_minus_compat : forall f g, D (f - g)%F == (D f - D g)%F.
Proof.
intros f g x ; unfold D, minus_fct, Rminus ; ring.
Qed.

Lemma Int_D: forall a b f, (a <= b)%nat -> Int a b (D f) = f (INR b + 1) - f (INR a).
Proof.
intros a b ; revert a ; induction b ; intros a f altb.
 inversion altb ; reflexivity.
 unfold Int in * ; destruct a ; simpl minus.
  rewrite Rseq_sum_simpl ; rewrite (minus_n_O b), IHb ; [| apply le_0_n].
  unfold Rseq_shifts, D ; rewrite <- minus_n_O ; simpl plus ;
  rewrite S_INR ; ring.
  erewrite Rseq_sum_ext ; [| apply Rseq_shift_shifts] ;
  rewrite Rseq_sum_shift_compat.
  unfold Rseq_shift ; rewrite Rseq_sum_simpl, IHb ; unfold Rseq_shifts, D.
  rewrite minus_Sn_m, le_plus_minus_r, plus_0_r, S_INR, S_INR.
   ring.
   transitivity (S a) ; [apply le_n_Sn | assumption].
   apply le_S_n ; assumption.
   apply le_S_n ; assumption.
Qed.

Fixpoint Fp (n : nat) : R -> R := fun x =>
match n with
  | O   => 1
  | S m => (x - INR m) * Fp m x
end.

Lemma D_Fp_S_simpl : forall x n, D (Fp (S n)) x = INR (S n) * Fp n x.
Proof.
intros x n ; induction n.
 unfold D, Fp ; simpl ; ring.

 replace (INR(S(S n))) with (1+ INR(S n)) by (simpl; auto with *). 
 rewrite Rmult_plus_distr_r; simpl Fp at 3.
 rewrite Rmult_comm with  (x - INR n) (Fp n x).
 rewrite <- Rmult_assoc.
 rewrite <- IHn.
 unfold D, Fp.
 replace (INR (S n)) with (1 + INR n) by (simpl; case n; auto with *).
 ring.
Qed.