Require Import Omega.

Lemma lt_S_lt_eq_dec : forall m n, S m < n ->
  { m < n } + { m = n }.
Proof.
intros m n H ; destruct (lt_eq_lt_dec m n) as [[ | ] | ].
 left ; assumption.
 right ; assumption.
 exfalso ; omega.
Qed.

Lemma lt_exist : forall m n, m < n ->
  { p | m + p = n }.
Proof.
intro m ; induction m ; intros n mltn.
 exists n ; trivial.
 destruct n as [| n] ; [exfalso ; omega |] ;
 destruct (IHm n (lt_S_n m n mltn)) as [p Hp] ;
 exists p ; intuition.
Qed.

Require Setoid.

Add Parametric Relation : nat le
reflexivity proved by le_refl
transitivity proved by le_trans as le.

