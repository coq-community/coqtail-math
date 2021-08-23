Require Import ZArith Lia Znumtheory.
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


(** Informative version, derived from the stdlib *)

Definition prime_dec_aux_inf:
  forall p m,
    { n | 1 < n < m /\ ~ rel_prime n p } +
    { forall n, 1 < n < m -> rel_prime n p }.
Proof.
  intros p m.
  case (Z_lt_dec 1 m); intros H1;
    [ | right; intros; exfalso; lia ].
  pattern m; apply natlike_rec; auto with zarith;
    [ right; intros; exfalso; lia | ].
  intros x Hx IH; destruct IH as [E|F].
    left; destruct E as (n,((H0,H2),H3));exists n; auto with zarith.
    
    destruct (rel_prime_dec x p) as [Y|N].
      right; intros n [HH1 HH2].
      case (Zgt_succ_gt_or_eq x n); auto with zarith.
      intros HH3; subst x; auto.
      
      case (Z_lt_dec 1 x); intros HH1.
        left; exists x; split; auto with zarith.
        right; intros n [HHH1 HHH2]; contradict HHH1; auto with zarith.
Defined.


(** Informative version, derived from the stdlib *)

Theorem not_prime_divide_inf:
 forall p, 1 < p -> ~ prime p -> { n | 1 < n < p  /\ (n | p) }.
Proof.
  intros p Hp Hp1.
  case (prime_dec_aux_inf p p); intros H1.
  - case H1; intros n [Hn1 Hn2].
    generalize (Zgcd_is_pos n p); intros Hpos.
    case (Z_le_lt_eq_dec 0 (Z.gcd n p)); auto with zarith; intros H3.
    + case (Z_le_lt_eq_dec 1 (Z.gcd n p)); auto with zarith; intros H4.
      * exists (Z.gcd n p); split; auto.
        { split; auto.
          apply Z.le_lt_trans with n; auto with zarith.
          generalize (Zgcd_is_gcd n p); intros tmp; inversion_clear tmp as [Hr1 Hr2 Hr3].
          case Hr1; intros q Hq.
          case (Zle_or_lt q 0); auto with zarith; intros Ht;
          try solve [
            absurd (n <= 0 * Z.gcd n p) ; auto with zarith;
            pattern n at 1; rewrite Hq; auto with zarith ].
            
            apply Z.le_trans with (1 * Z.gcd n p); auto with zarith.
            pattern n at 2; rewrite Hq; auto with zarith.
          }
        { generalize (Zgcd_is_gcd n p); intros Ht; inversion Ht; auto. }
        
      * case Hn2; red.
        rewrite H4; apply Zgcd_is_gcd.
      
    + generalize (Zgcd_is_gcd n p); rewrite <- H3; intros tmp;
        inversion_clear tmp as [Hr1 Hr2 Hr3].
      absurd (n = 0); auto with zarith.
      case Hr1; auto with zarith.
    
  - elim Hp1; constructor; auto.
    intros n [Hn1 Hn2].
    case Zle_lt_or_eq with ( 1 := Hn1 ); auto with zarith.
    intros H2; subst n; red; apply Zis_gcd_intro; auto with zarith.
Defined.

Lemma Pcompare_notEq_notEq : forall a b,
    (Pcompare a b Lt <> Eq) /\ (Pcompare a b Gt <> Eq).
Proof.
  intros a; induction a; intros b; destruct b; split; intros E; simpl in E;
    try solve [
          inversion E |
          auto |
          eapply (proj1 (IHa _)); eauto |
          eapply (proj2 (IHa _)); eauto
        ].
Qed.

Lemma Pcompare_Eq_eq : forall a b, Pcompare a b Eq = Eq -> a = b.
Proof.
  intros a; induction a; intros b; destruct b; intros E; simpl in E;
    try solve [
          inversion E |
          auto |
          f_equal; apply IHa; eauto
        ].
  exfalso; eapply Pcompare_notEq_notEq; eauto.
  exfalso; eapply (proj1 (Pcompare_notEq_notEq _ _)); eauto.
Defined.

Lemma Zcompare_Eq_eq : forall n m : Z, (n ?= m) = Eq -> n = m.
Proof.
  intros [ | p | p ] [ | q | q] E; simpl in E;
    reflexivity ||
                solve [ inversion E ] ||
                (f_equal; eapply Pcompare_Eq_eq; eauto).
  fold (p ?= q)%positive; destruct ((p ?= q)%positive); auto || inversion E.
Defined.

Definition Z_le_lt_eq_dec x y : x <= y -> {x < y} + {x = y}.
Proof.
  pose (Zcompare_Eq_iff_eq := 
    fun x y => conj (fun E : (x ?= y) = Eq => Zcompare_Eq_eq x y E)
      (fun E : x = y =>
        eq_ind_r (fun x0 => (x0 ?= y) = Eq) (Z.compare_refl y) E)).
  intro H.
  apply Zcompare_rec with (n := x) (m := y); intros E.
    right. elim (Zcompare_Eq_iff_eq x y); auto with arith.
    left. elim (Zcompare_Eq_iff_eq x y); auto with arith.
    absurd (x > y); auto with arith.
Defined.

(** Induction on natural numbers via prime numbers and multiplication *)

Lemma Z_prime_rect : forall P : Z -> Type,
  ((P 0) ->
  (P 1) ->
  (forall n, prime n -> P n) ->
  (forall a b, P a -> P b -> P (a * b)) ->
    forall n, 0 <= n -> P n)%Z.
Proof.
  intros P P0 P1 Pprime Psplit.
  assert (Hind : forall (N : nat) n, 0 <= n -> (Z.abs_nat n < N)%nat -> P n).
    intro n ; induction n ; intros i ipos imax.
      (* i = n is the only interesting case *)
      exfalso; inversion imax.
      destruct (Z_le_lt_eq_dec i (Z_of_nat n)) as [|E]. lia. apply IHn; lia.
      rewrite E in *; clear E i ipos imax.
      
      (* Case: n is prime *)
      destruct (prime_dec (Z_of_nat n)) as [Hprime | Hnprime]. apply Pprime ; assumption.
      
      (* Case: n <= 1 *)
      destruct n. subst; apply P0.
      destruct n. subst; apply P1.
      
      (* Case: n = a * b *)
      set (z := Z_of_nat (S (S n))).
      assert (n_big : 1 < z) by (unfold z; lia).
      destruct (not_prime_divide_inf _ n_big Hnprime) as [a [[amin amax] b_eqz]].
      destruct (Zdivide_inf _ _ b_eqz) as [b eqz]; clear b_eqz; rewrite eqz.
      
      (* Bounds on b come from bounds on a *)
      assert (Bb : 1 < b < z).
        assert (1 < b) by (apply Zmult_lt_reg_r with a; lia).
        split; auto.
        rewrite <- (Zmult_1_r b), eqz.
        apply Zmult_lt_compat_l; try lia.
      
      (* Main argument *)
      apply Psplit; apply IHn; lia.
  
  intros n n_pos ; apply Hind with (S (Z.abs_nat n)) ; auto.
Defined.

Lemma Z_prime_ind : forall P : Z -> Prop,
  ((P 0) ->
  (P 1) ->
  (forall n, prime n -> P n) ->
  (forall a b, P a -> P b -> P (a * b)) ->
    forall n, 0 <= n -> P n)%Z.
Proof.
  intros; apply Z_prime_rect; auto.
Qed.


(** Bezout coefficients: a lot easier to use than the stdlib *)

Lemma bezout_inj : forall a b,
  {u : Z & {v | u * a + v * b = Z.gcd a b}}.
Proof.
  intros a b.
  destruct (euclid a b) as (u, v, d, E, H).
  destruct (Z_le_dec 0 d) as [L|L].
    exists u; exists v.
    rewrite (Zis_gcd_gcd _ _ _ L H).
    auto.
    
    exists (- u); exists (- v).
    assert (L2 : 0 <= - d) by lia.
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
    lia.
    
    destruct (rel_prime_bezout _ _ H) as (u, (v, Huv)).
    exists u.
    rewrite <- Huv.
    assert (REW : x mod p ≡ x [p]) by (red; rewrite Zmod_mod; auto) (* TODO dans un lemme *).
    rewrite REW.
    apply eqm_minus_0.
    ring_simplify.
    apply divide_eqm. notzero.
    exists (- v); auto.
Qed.
