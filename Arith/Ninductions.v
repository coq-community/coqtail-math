
Require Import Arith MyNat.

Lemma nat_strong : forall (P : nat -> Prop), P O ->
 (forall N, (forall n, (n <= N)%nat -> P n) -> P (S N)) -> forall n, P n.
Proof.
intros P PO PS ; assert (H : forall N n, (n <= N)%nat -> P n).
 intro N ; induction N ; intros n nleN ; inversion_clear nleN.
  assumption.
  apply PS, IHN.
  apply IHN ; assumption.
 intro n ; apply H with n ; reflexivity.
Qed.

Lemma nat_ind2 : forall (P : nat -> Prop), 
  P O -> P (S O) -> (forall m, P m -> P (S (S m))) -> forall n, P n. 
Proof.
intros P P0 P1 PSS ; apply nat_strong.
 assumption.
 intros [] HN.
  assumption.
  apply PSS, HN, le_n_Sn.
Qed.
