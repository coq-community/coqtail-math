Require Import QArith Qabs.

Open Local Scope Q_scope.

Add Parametric Relation : Q Qle 
   reflexivity proved by Qle_refl
   transitivity proved by Qle_trans 
 as Qle_order.

Add Parametric Relation : Q Qlt
   transitivity proved by Qlt_trans 
 as Qlt_order.

Instance subrelation_le_eq : subrelation Qeq Qle.
intros x y H.
rewrite H.
apply Qle_refl.
Qed.


Add Morphism Qplus with signature Qlt ++> Qlt ++> Qlt as Qplus_lt_morphism.
intros a b H1 c d H2.
destruct a as [a₁ a₂]; destruct b as [b₁ b₂]; destruct c as [c₁ c₂]; destruct d as [d₁ d₂]; simpl.
unfold Qlt in *.
simpl in *.

replace ('(b₂ * d₂))%Z with ('b₂ * 'd₂)%Z; [|auto with zarith].
replace ('(a₂ * c₂))%Z with ('a₂ * 'c₂)%Z; [|auto with zarith].

replace ((a₁ * 'c₂ + c₁ * 'a₂) * ('b₂ * 'd₂))%Z with
        ((a₁ * 'b₂) * ('d₂ * 'c₂)  + (c₁ * 'd₂) * ('a₂ * 'b₂))%Z; [|ring].
replace ((b₁ * 'd₂ + d₁ * 'b₂) * ('a₂ * 'c₂))%Z with 
        ((b₁ * 'a₂) * ('d₂ * 'c₂) + (d₁ * 'c₂) * ('a₂ * 'b₂))%Z;[|ring].
apply Zplus_le_lt_compat.
apply Zmult_le_compat_r; auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
constructor.
Qed.

Add Morphism Qplus with signature Qle ++> Qle ++> Qle as Qplus_le_morphism.
 intros; apply Qplus_le_compat; assumption.
Qed.

Definition Qeq_pos x y := 0 <= x /\ x == y.

Definition Qle_pos x y := 0 <= x /\ x <= y.

Instance Qle_pos_transitive : Transitive Qle_pos.
intros ? ? ? [? ?] [? ?]; split; auto.
eapply transitivity; eassumption.
Qed.

Instance subrelation_le_pos : subrelation Qle_pos Qle.
intros ? ? [? ?]; assumption.
Qed.

Instance Qeq_pos_transitive : Transitive Qeq_pos.
intros ? ? ? [? ?] [? ?]; split; auto.
eapply transitivity; eassumption.
Qed.

Instance subrelation_eq_pos : subrelation Qeq_pos Qeq.
intros ? ? [? ?]; assumption.
Qed.

Instance Qeq_pos_symmetric : Symmetric Qeq_pos.
intros ? ?  [H1 H2]; split.
rewrite<- H2; assumption.
apply symmetry; assumption.
Qed.

Add Morphism Qmult with signature  Qle ++> Qeq_pos ++> Qle as Qmult_le_morphism.
  intros x y H1 a b [H2 H3].
  rewrite H3.
  apply Qmult_le_compat_r; auto.
  rewrite<- H3.
  assumption.
Qed.

Definition Qmax (p q : Q) : Q := 
   if Qlt_le_dec p q then q else p.
Lemma Qmax_comm : forall p q, (Qmax p q == Qmax q p)%Q.
  intros p q.
  unfold Qmax; destruct (Qlt_le_dec p q); destruct (Qlt_le_dec q p); 
  auto with qartih.
Qed.
Lemma le_Qmax : forall p q r:Q, (p <= q)%Q -> (p <= Qmax q r)%Q.
Proof.
intros p q r H.
unfold Qmax. destruct (Qlt_le_dec q r).
transitivity q. apply H. auto with qarith.
apply H.
Qed.

Lemma lt_Qmax : forall p q r:Q, (p < q)%Q -> (p < Qmax q r)%Q.
Proof.
intros p q r H.
unfold Qmax ; destruct (Qlt_le_dec q r).
transitivity q ; auto with qarith.
apply H.
Qed.

Lemma Qmult_pos_le_compat : 
   forall a b c d:Q, 0 <= a <= b -> 0 <= c <= d -> a*c <= b*d.
  intros.
  apply transitivity with (b*c).
  apply Qmult_le_compat_r; intuition.
  setoid_rewrite Qmult_comm.
  apply Qmult_le_compat_r; intuition.
  apply transitivity with a; intuition.
Qed.

Lemma Qmult_pos_compat : 
  forall x y, 0 < x -> 0 < y -> 0 < x * y.
intros.
setoid_replace 0 with (0 * y).
apply Qmult_lt_compat_r; assumption.
ring.
Qed.

Lemma Qdiv_pos : 
  forall n, forall x :Q, 0 < x -> 0 < x * (1 # n).
intros; apply Qmult_pos_compat.
assumption.
auto with qartih.
Qed.

Lemma Qplus_le_lt_compat : 
  forall a b c d, a <= b -> c < d -> a+c < b + d.
Admitted.