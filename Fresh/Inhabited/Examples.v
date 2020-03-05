Require Import Monad.

Lemma ex_inhabited_sig : forall A (f : A -> Prop),  ex f -> [ sig f ].
Proof.
intros A f Hex.
destruct Hex as (x, fx).
constructor.
exists x.
apply fx.
Qed.

Lemma ex_is_inhabited_sig A (f : A -> Prop) :  ex f <-> [ sig f ].
Proof.
firstorder.
Qed.

Lemma Prop_inhabited_stable : forall P : Prop, P -> [P].
Proof.
auto.
Qed.

Lemma Prop_inhabited_inversion : forall P : Prop, [P] -> P.
Proof.
firstorder.
Qed.

Lemma Type_inhabited_stable : forall P : Type, P -> [P].
Proof.
auto.
Qed.

Definition epsilon := forall (A : Type) (f : A -> Prop), (exists x, f x) -> { x | f x }.

Definition algebraic := forall P : Type, [ P ] -> P.

Lemma Type_inhabited_inversion_implies_epsilon : algebraic -> epsilon.
Proof.
intros Hs A f Hex.
apply Hs.
apply ex_inhabited_sig; assumption.
Qed.

Require Import InhabitedTactics.

Lemma unlift_example : forall (P Q : Type) (R : Prop), [ P ] -> [ P -> Q ] -> [ Q -> R ] -> R.
Proof.
intros P Q R p pq qr.
unlift.
tauto.
Qed.

Lemma unlift_example2  : forall (P Q R : Type), [ P ] -> [ P -> Q ] -> [ Q -> R ] -> [ R ].
Proof.
intros P Q R p pq qr.
unlift.
tauto.
Qed.

Lemma unlift_example3  : forall (P Q R : Type), [ P ] -> [ P -> Q ] -> [ Q -> R ] -> R.
Proof.
intros P Q R p pq qr.
Abort.

Lemma stronger_inhabited_in_hypothese : forall A B, ([A] -> [B]) -> (A -> [B]).
Proof.
eauto.
Qed.

Definition not (A : Type) : Type := A -> False.

(* to show that ([A] -> [B]) is strictely stronger than (A -> [B]) *)

Lemma stronger_inhabited_in_hypothese' :
  (forall A B, (A -> [B]) -> ([A] -> [B])) ->
  True (* something strong and bad here (?) *).
Proof.
intros HH. 
(* big complicated proof here *)
apply I.
Qed.

Lemma inhabited_sum_or : forall (A B : Type) (P : Prop), 
 (([A] \/ [B]) -> P) <-> ((A + B) -> P).
Proof.
intros; split.
  intuition.
  intros ? [ [ ] | [ ] ]; auto.
Qed.
