Require Import Arith.
Require Import Eqdep_dec.
Require Import Peano_dec.

Theorem K_nat :
  forall (x:nat) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p.
Proof.
  intros; apply K_dec_set with (p := p).
  apply eq_nat_dec.
  assumption.
Qed.

Theorem eq_rect_eq_nat :
  forall (p:nat) (Q:nat->Type) (x:Q p) (h:p=p), x = eq_rect p Q x p h.
Proof.
  intros; apply K_nat with (p := h); reflexivity.
Qed.

Scheme le_ind := Induction for le Sort Prop.
(** * Two proofs of [n<m] are equals *)

Theorem lt_PI : forall (n m : nat) (pr1 pr2 : n < m),
  pr1 = pr2.
Proof. 
unfold lt ; intros n m ; induction pr1 using le_ind ; intro pr2.
    replace (le_n (S n)) with
      (eq_rect _ (fun n0 => S n <= n0) (le_n (S n)) _ (refl_equal (S n))).
      generalize (refl_equal(S n)).
      pattern (S n) at 2 4 6 10, pr2; case pr2; [intro | intros m l e].
      rewrite <- eq_rect_eq_nat; trivial.
      contradiction (le_Sn_n m); rewrite <- e; assumption.
      reflexivity.
    replace (le_S (S n) m pr1) with
      (eq_rect _ (fun n0 => S n <= n0) (le_S (S n) m pr1) _ (refl_equal (S m))).
      generalize (refl_equal (S m)).
      pattern (S m) at 1 3 4 6, pr2; case pr2; [intro Heq | intros m0 l HeqS].
      contradiction (le_Sn_n m); rewrite Heq; assumption.
      injection HeqS; intro Heq; generalize l HeqS.
      rewrite <- Heq; intros; rewrite <- eq_rect_eq_nat.
      rewrite (IHpr1 l0); reflexivity.
      reflexivity.
Qed.