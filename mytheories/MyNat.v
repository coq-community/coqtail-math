Require Import Arith Lia.

Lemma lt_S_lt_eq_dec : forall m n, S m < n ->
  { m < n } + { m = n }.
Proof.
intros m n H ; destruct (lt_eq_lt_dec m n) as [[ | ] | ].
 left ; assumption.
 right ; assumption.
 exfalso ; lia.
Qed.

Lemma ge_refl : forall m, ge m m.
Proof.
intro; constructor.
Qed.

Lemma ge_trans : forall a b c, ge a b -> ge b c -> ge a c.
Proof.
  unfold ge; intros; eapply le_trans; eassumption.
Qed.

Lemma lt_exist : forall m n, m < n ->
  { p | m + p = n }.
Proof.
intro m ; induction m ; intros n mltn.
 exists n ; trivial.
 destruct n as [| n] ; [exfalso ; lia |] ;
 destruct (IHm n (lt_S_n m n mltn)) as [p Hp] ;
 exists p ; intuition lia.
Qed.

Require Setoid.

Add Parametric Relation : nat le
reflexivity proved by le_refl
transitivity proved by le_trans as le.

Add Parametric Relation : nat lt
transitivity proved by lt_trans as lt.

Add Parametric Relation : nat gt
transitivity proved by gt_trans as gt.

Add Parametric Relation : nat ge
reflexivity proved by ge_refl
transitivity proved by ge_trans as ge.
