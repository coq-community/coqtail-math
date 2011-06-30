Axiom choice : forall A (B : A -> Type), (forall x, inhabited (B x)) -> inhabited (forall x, B x).

Definition epsilon := forall A (B : A -> Prop), (exists x, B x) -> {x | B x}.

Definition T A := epsilon -> A.
Definition U A := inhabited A.

Lemma U_T : forall A, T A -> U A.
Proof.
intros A H; unfold T, U in *.
assert (Hi : inhabited ((inhabited epsilon) -> A)).
apply choice; auto.
intros [Hi]; constructor; intuition.
destruct Hi as [Hi]; constructor; apply Hi.
clear; unfold epsilon.
apply (choice Type); intros A; apply choice; intros B; apply choice.
intros [x Hx]; constructor; eauto.
Qed.

Lemma T_U : forall A, U A -> T A.
Proof.
intros A H; unfold T, U in *; intros Heps.
destruct (Heps A (fun _ => True)); auto.
destruct H; eauto.
Qed.
