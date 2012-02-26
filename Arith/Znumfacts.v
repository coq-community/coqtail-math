Require Import ZArith Omega Znumtheory.
Require Import Natsets MyNat Ztools Zeqm.

(** * Number theory : factorisation, computation of Bezout coefficients and modular inverse *)

(*
TODO : idéalement, on aurait un Z_prime_rect rapide, pour l'extraction
avec une fonction de factorisation.
Encore mieux, la preuve du un schéma d'induction devrait utiliser
la factorisation

  p1^a1 * p2^a2 * ..

en mémoizant le calcul sur les nombres premiers. (En supposant que la
compatibilité wrt. multiplication est plus économique pour la propriété
sur les nombres premiers, ce qui est probablement largement le cas pour
lagrange)

*)


(** Induction on natural numbers via prime numbers and multiplication *)

Lemma Z_prime_ind : forall P : Z -> Prop,
  ((P 0) ->
  (P 1) ->
  (forall n, prime n -> P n) ->
  (forall a b, P a -> P b -> P (a * b)) ->
    forall n, 0 <= n -> P n)%Z.
Proof.
intros P P0 P1 Pprime Psplit.
assert (Hind : forall (N : nat) n, 0 <= n -> (Zabs_nat n < N)%nat -> P n).
 intro N ; induction N ; intros n n_lb n_ub.
  inversion n_ub.
  destruct (prime_dec n) as [Hprime | Hnprime].
   apply Pprime ; assumption.
  destruct (Z_eq_dec n 0) as [Hnull | Hnnull].
   subst ; apply P0.
  destruct (Z_eq_dec n 1) as [Hone | Hnone].
   subst ; apply P1.
  assert (n_big : 1 < n) by omega.
  destruct (not_prime_divide _ n_big Hnprime) as [p [[p_lb p_ub] [q Hpq]]].
   subst ; apply Psplit ; apply IHN.
   apply Zmult_le_0_reg_r with p ; omega.
admit.
 omega.
admit.
 intros n n_pos ; apply Hind with (S (Zabs_nat n)) ; auto.
Qed. 

Lemma Z_prime_rect : forall P : Z -> Type,
  ((P 0) ->
  (P 1) ->
  (forall n, prime n -> P n) ->
  (forall a b, P a -> P b -> P (a * b)) ->
  forall n, 0 <= n -> P n)%Z.
Proof.
(*
intros P P0 P1 Pprime Psplit.
assert (Hind : forall (N : nat) n, 0 <= n -> (Zabs_nat n < N)%nat -> P n).
 intro N ; induction N ; intros n n_lb n_ub.
  destruct (lt_n_O _ n_ub).
  destruct (prime_dec n) as [Hprime | Hnprime].
   apply Pprime ; assumption.
  destruct (Z_eq_dec n 0) as [Hnull | Hnnull].
   subst ; apply P0.
  destruct (Z_eq_dec n 1) as [Hone | Hnone].
   subst ; apply P1.
  assert (n_big : 1 < n) by omega.
  destruct (not_prime_divide _ n_big Hnprime) as [p [[p_lb p_ub] [q Hpq]]].
   subst ; apply Psplit ; apply IHN.
   apply Zmult_le_0_reg_r with p ; omega.
admit.
 omega.
admit.
 intros n n_pos ; apply Hind with (S (Zabs_nat n)) ; auto.
Qed. 
*)
Admitted.


(** Bezout coefficients: a lot easier to use than the stdlib *)

Lemma bezout_inj : forall a b,
  {u : Z & {v | u * a + v * b = Zgcd a b}}.
Proof.
  intros a b.
  destruct (euclid a b) as (u, v, d, E, H).
  destruct (Z_le_dec 0 d) as [L|L].
    exists u; exists v.
    rewrite (Zis_gcd_gcd _ _ _ L H).
    auto.
    
    exists (- u); exists (- v).
    assert (L2 : 0 <= - d) by omega.
    rewrite (Zis_gcd_gcd _ _ _ L2).
      rewrite <- E; ring.
      apply Zis_gcd_opp, Zis_gcd_sym; auto.
Qed.

Lemma rel_prime_bezout : forall a b, rel_prime a b ->
  {u : Z & {v | u * a + v * b = 1}}.
Proof.
  intros a b RP.
  rewrite <- (proj2 (Zgcd_1_rel_prime a b)); auto.
  apply bezout_inj.
Qed.


(** Multiplication is often injective in Z/pZ *)

Lemma modular_mult_inj : forall p n, prime p ->
  ~ (0 ≡ n [p]) -> forall x y, x * n ≡ y * n [p] -> x ≡ y [p].
Proof.
  intros p n Pp Nn x y E.
  apply eqm_minus_0, divide_eqm; notzero.
  
  assert (D : (p | (x - y) * n)).
    apply divide_eqm; notzero.
    ring_simplify.
    rewrite E.
    red; f_equal; ring.
  
  destruct (prime_mult _ Pp _ _ D) as [D1|D2]; auto.
  exfalso; apply Nn.
  symmetry; apply divide_eqm; auto.
  notzero.
Qed.


(** Computing the modular inverse in Z_pZ *)

Lemma modular_inverse : forall p x, prime p -> ~(x ≡ 0 [p]) -> { y | x * y ≡ 1 [p] }.
Proof.
  intros p x Pp Nd.
  assert (rel_prime (x mod p) p).
    apply Pp.
    assert (A : p > 0) by notzero; pose proof Z_mod_lt x p A.
    unfold eqm in Nd; rewrite Zmod_0_l in Nd.
    omega.
    
    destruct (rel_prime_bezout _ _ H) as (u, (v, Huv)).
    exists u.
    rewrite <- Huv.
    assert (REW : x mod p ≡ x [p]) by (red; rewrite Zmod_mod; auto) (* TODO dans un lemme *).
    rewrite REW.
    apply eqm_minus_0.
    ring_simplify.
    apply multiple_eqm with (- v); auto.
Qed.
