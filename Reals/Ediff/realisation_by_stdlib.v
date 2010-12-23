Require Import Reals.
Require Import integrales.
Require Import RiemannInt.

Lemma continuity_implies_RiemannInt1 :   forall (f:R -> R) (a b:R),
    (forall x:R, (a <= x <= b \/ b <= x <= a) -> continuity_pt f x) -> Riemann_integrable f a b.
Proof.
intros.
destruct (Rle_dec a b).
apply continuity_implies_RiemannInt; intuition.
assert (b <= a) ; intuition.
apply RiemannInt_P1.
apply continuity_implies_RiemannInt; intuition.
Qed.

Lemma RiemannInt_P320 : forall (f:R -> R) (H : derivable f) (cont1 : continuity (derive f H))(a b:R), Riemann_integrable (derive f H) a b.
Proof.
  intro f; intros; case (Rle_dec a b); intro;
    [ apply continuity_implies_RiemannInt; try assumption; intros;
      apply (cont1)
      | assert (H1 : b <= a);
        [ auto with real
          | apply RiemannInt_P1; apply continuity_implies_RiemannInt;
            try assumption; intros; apply (cont1) ] ].
Qed.

Lemma RiemannInt_P310 :   forall (f:R -> R) (H : derivable f) (cont1 : continuity (derive f H)) (a b:R),
    a <= b -> antiderivative (derive f H) f a b.
Proof.
  intro f; intros; unfold antiderivative in |- *; split; try assumption; intros;
    split with (H x); reflexivity.
Qed.

Lemma RiemannInt_P330 :   forall (f:R -> R)(H : derivable f) (cont1 : continuity (derive f H)) (a b:R) (pr:Riemann_integrable (derive f H) a b),
    a <= b -> RiemannInt pr = f b - f a.
Proof.
  intro f; intros;
    assert
      (H1 : forall x:R, a <= x <= b -> continuity_pt (derive f H) x).
  intros; apply (cont1).
  rewrite (RiemannInt_P20 H0 (FTC_P1 H0 H1) pr);
    assert (H2 := RiemannInt_P29 H0 H1); assert (H3 := RiemannInt_P310 f H cont1 a b H0);
      elim (antiderivative_Ucte (derive f H) _ _ _ _ H2 H3);
        intros C H4; repeat rewrite H4;
          [ ring
            | split; [ right; reflexivity | assumption ]
            | split; [ assumption | right; reflexivity ] ].
Qed.

Lemma RiemannInt_P340 : forall (f:R -> R) (H: derivable f) (cont1 : continuity (derive f H)) (a b:R) (pr:Riemann_integrable (derive f H) a b),
    RiemannInt pr = f b - f a.
Proof.
  intro f; intros; case (Rle_dec a b); intro.
    apply RiemannInt_P330; assumption.
    assert (H0 : b <= a);
        [ auto with real
          | assert (H1 := RiemannInt_P1 pr); rewrite (RiemannInt_P8 pr H1);
            rewrite (RiemannInt_P330 _ _ cont1 b a H1 H0); ring ].
Qed.

Module Real_std_lib : Integrals.

Definition Riemann_integrable := Riemann_integrable.
Definition RiemannInt_P1 := RiemannInt_P1.
Definition RiemannInt := RiemannInt.
Definition RiemannInt_ext := RiemannInt_P5.
Definition Riemann_integrable_singleton := RiemannInt_P7.
Definition continuity_implies_RiemannInt := continuity_implies_RiemannInt1.
Definition RiemannInt_opp := RiemannInt_P8.
Definition RiemannInt_singleton := RiemannInt_P9.
Definition Riemann_integrable_linear := RiemannInt_P10.
Definition RiemannInt_linear := RiemannInt_P13.
Definition Riemann_integrable_const := RiemannInt_P14.
Definition RiemannInt_const := RiemannInt_P15.
Definition Riemann_integrable_Rabs := RiemannInt_P16.
Definition Riemann_integrable_chasles := RiemannInt_P24.
Definition RiemannInt_monotony := RiemannInt_P22.
Definition RiemannInt_monotony2 := RiemannInt_P23.
Definition RiemannInt_chasles := RiemannInt_P26.
Definition derive_Riemann_integrable := RiemannInt_P320.
Definition FTC_Riemann := RiemannInt_P340.


End Real_std_lib.


