Require Import ZArith Omega.
Open Scope Z_scope.

Definition sqr a := Zmult a a.

Lemma euler_four_square_identity : forall a b c d w x y z : Z,
  (sqr a + sqr b + sqr c + sqr d) *
  (sqr w + sqr x + sqr y + sqr z) =
  sqr (a*w + b*x + c*y + d*z) +
  sqr (a*x - b*w - c*z + d*y) +
  sqr (a*y + b*z - c*w - d*x) +
  sqr (a*z - b*y + c*x - d*w).
Proof.
  intros.
  unfold sqr.
  ring.
Qed.

Definition sum_of_2_squares (n : Z) : Type :=
  sigT (fun a => sig (fun b => n = sqr a + sqr b)).

(*
Definition even n := sig (fun _ : True => Zeven n).
Definition odd n := sig (fun _ : True => Zodd n).
*)

(* En attendant une bonne solution pour even/odd *)

Variable even odd : Z -> Type.

Axiom even_sum : forall a b, even (a + b) -> (odd a * odd b) + (even a * even b).
Axiom even_add : forall a b, even a -> even b -> even (a + b).
Axiom odd_add : forall a b, odd a -> odd b -> even (a + b).
Axiom even_sub : forall a b, even a -> even b -> even (a - b).
Axiom odd_sub : forall a b, odd a -> odd b -> even (a - b).
Axiom even_sqr : forall a, even a -> even (a * a).
Axiom odd_sqr : forall a, odd a -> odd (a * a).
Axiom even_sqrt : forall a, even (a * a) -> even a.
Axiom odd_sqrt : forall a, odd (a * a) -> odd a.
Axiom even_def : forall n a, 2 * a = n -> even n.
Axiom even_div : forall n, even n -> 2 * (n / 2) = n.

Lemma sqr_double : forall n, 4 * sqr n = sqr (2 * n).
Proof.
  intros; unfold sqr; ring.
Qed.

Lemma half : forall m, sum_of_2_squares (2 * m) -> sum_of_2_squares m.
Proof.
  intros m (x, (y, Hm)).
  assert (even_aabb := even_def _ _ Hm).
  exists ((x - y) / 2). exists ((x + y) / 2).
  apply Zmult_reg_l with 4; [ omega | ].
  rewrite Zmult_plus_distr_r.
  do 2 rewrite sqr_double.
  replace (4 * m) with (2 * (2 * m)) by ring; rewrite Hm.
  destruct (even_sum _ _ even_aabb) as [(Ox, Oy) | (Ex, Ey)].
    apply odd_sqrt in Ox. apply odd_sqrt in Oy.
    repeat rewrite even_div.
      unfold sqr; ring.
      apply odd_add; auto.
      apply odd_sub; auto.
    apply even_sqrt in Ex. apply even_sqrt in Ey.
    repeat rewrite even_div.
      unfold sqr; ring.
      apply even_add; auto.
      apply even_sub; auto.
Qed.

(*
http://planetmath.org/encyclopedia/ProofOfLagrangesFourSquareTheorem.html
(le site est down le 13 février 2012 à 19h)
*)


  