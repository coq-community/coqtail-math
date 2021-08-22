Require Import ZArith Lia Znumtheory.

(** * Contains some useful lemmas not in stdlib and a tactic *)


(** A convenient and simple tactic to prove 0<x or 0<>x *)

Lemma Zmult_neq_0_compat : forall a b, 0 <> a -> 0 <> b -> 0 <> a * b.
Proof.
  intros [] [] P Q I; simpl in *;
    inversion I; tauto.
Qed.

Lemma Zmult_le_1_compat : forall a b, 1 <= a -> 1 <= b -> 1 <= a * b.
Proof.
  intros a b.
  replace a with (1 + (a - 1)) by lia.
  replace b with (1 + (b - 1)) by lia.
  generalize (a - 1).
  generalize (b - 1).
  intros c d.
  intros.
  assert (0 <= c) by lia.
  assert (0 <= d) by lia.
  ring_simplify.
  assert (0 <= d * c) by auto with *.
  lia.
Qed.

Lemma Zsquare_pos : forall x, 0 <> x -> 0 < x * x.
Proof.
  intros [] E; simpl; reflexivity || tauto.
Qed.

Ltac notzero :=
  lazymatch goal with
  | |- ?a <> 0 => apply not_eq_sym; notzero
  | |- ?a > 0 => cut (0 < a); [ apply Zcompare_Gt_Lt_antisym | ]; notzero
  | |- 0 < ?a * ?a => apply Zsquare_pos; notzero
  | |- 0 < ?a ^ 2 => replace (a ^ 2) with (a * a) by ring; notzero
  | |- 0 <  ?a * ?b => apply Zmult_lt_0_compat; notzero
  | |- 0 <> ?a * ?b => apply Zmult_neq_0_compat; notzero
  | |- 0 < Zpos _ => reflexivity
  | |- 0 > Zneg _ => reflexivity
  | |- 0 <> Zpos _ => let I := fresh "I" in intros I; inversion I
  | |- 0 <> Zneg _ => let I := fresh "I" in intros I; inversion I
  | Pp : prime ?p |- 0 < ?p => pose proof prime_ge_2 p Pp; lia
  | Pp : prime ?p |- 0 <> ?p => pose proof prime_ge_2 p Pp; lia
  | Pp : prime ?p |- 1 <> ?p => pose proof prime_ge_2 p Pp; lia
  | Pp : prime ?p |- ?p <> 0 => pose proof prime_ge_2 p Pp; lia
  | Pp : prime ?p |- ?p <> 1 => pose proof prime_ge_2 p Pp; lia
  | Pp : prime ?p |- ?p > 0 => pose proof prime_ge_2 p Pp; lia
  | |- 0 < _  => auto with *; try lia
  | |- 0 <> _ => auto with *; try lia
  | |- _ => idtac
  end.


(** Subsumed by tactic [notzero] but also useful, since it shows up in
Search *)

Lemma prime_not_0 p : prime p -> p <> 0.
Proof.
  intro; notzero.
Qed.

Lemma prime_not_1 p : prime p -> p <> 1.
Proof.
  intro; notzero.
Qed.


(** Extraction from the Zdivide predicate *)

Lemma Zdivide_inf : forall a b, (a | b) -> { q | b = q * a }.
Proof.
  intros a b D.
  exists (b / a).
  rewrite Zmult_comm.
  destruct (Z.eq_dec a 0).
    subst; destruct D; lia.
    
    apply Z_div_exact_full_2; auto with *.
    apply Zdivide_mod; auto.
Defined.


(** About Zmod or Zdiv *)

Lemma Z_mult_div_mod : forall a b, b <> 0 -> b * (a / b) = a - a mod b.
Proof.
  intros a b N.
  pose proof Z_div_mod_eq_full a b; lia.
Qed.

Lemma Zdivide_square : forall a b, (a | b) -> (a * a | b * b).
Proof.
  intros a b (k, Ek).
  exists (k * k); subst; ring.
Qed.

Lemma Zmult_divide_compat_rev_l: forall a b c : Z, c <> 0 -> (c * a | c * b) -> (a | b).
Proof.
  intros a b c Nc (k, Hk).
  exists k.
  eapply Zmult_reg_l; eauto.
  rewrite Hk; ring.
Qed.

Lemma Z_mult_div_bounds : forall a b, 0 < b -> a - b < b * (a / b) <= a.
Proof.
  intros a b N; split.
    pose proof Z_mod_lt a b.
    rewrite Z_mult_div_mod; lia.
    
    apply Z_mult_div_ge; lia.
Qed.


(** About square *)

Lemma Zle_0_square : forall a, 0 <= a * a.
Proof.
  intros []; intuition; try (simpl; intro H; inversion H).
Qed.

Lemma Zeq_0_square : forall a, a * a = 0 -> a = 0.
Proof.
  intros [] H; intuition simpl; inversion H.
Qed.

Lemma rewrite_power_2 : forall x, x ^ 2 = x * x.
Proof.
  (* TODO virer ça .. ? *)
  intros; ring.
Qed.

Lemma sqrt_eq_compat : forall a b, 0 <= a -> 0 <= b ->
  a * a = b * b -> a = b.
Proof.
  intros a b Pa Pb E.
  destruct (Z.eq_dec 0 (a + b)) as [F|F].
    lia.
    
    cut (a - b = 0); [ lia | ].
    apply (Zmult_reg_l _ _ (a + b)); notzero.
    ring_simplify.
    rewrite rewrite_power_2, E.
    ring.
Qed.

Lemma sqrt_eq_compat_abs : forall a b, a * a = b * b -> Z.abs a = Z.abs b.
Proof.
  intros a b E.
  destruct (Z.eq_dec 0 (Z.abs a + Z.abs b)) as [F|F].
    lia.
    
    cut (Z.abs a - Z.abs b = 0); [ lia | ].
    apply (Zmult_reg_l _ _ (Z.abs a + Z.abs b)); notzero.
    ring_simplify.
    rewrite <- Z.abs_square, <- (Z.abs_square b) in E.
    rewrite rewrite_power_2, E.
    ring.
Qed.

Lemma sqrt_le_compat : forall a b, 0 <= a -> 0 <= b ->
  a * a <= b * b -> a <= b.
Proof.
  intros a b Pa Pb E.
  destruct (Z.eq_dec 0 (a + b)) as [F|F].
    lia.
    
    cut (0 <= b - a); [ lia | ].
    apply Zmult_le_reg_r with (a + b); notzero.
    ring_simplify.
    do 2 rewrite rewrite_power_2; lia.
Qed.


(** About Z.abs *)

Lemma Zabs_nat_inj : forall a b, 0 <= a -> 0 <= b -> Z.abs_nat a = Z.abs_nat b -> a = b.
Proof.
  intros a b Pa Pb E.
  rewrite <- (Z.abs_eq a), <- (Z.abs_eq b); eauto.
  do 2 rewrite <- inj_Zabs_nat.
  auto.
Qed.


(* TODO (prouver et déplacer) ou virer *)
Lemma Zdivide_square_rev : forall a b, (a * a | b * b) -> (a | b).
Proof.
  intros a b D.
  destruct (Z.eq_dec a 0).
    subst; simpl in D.
    destruct D as (q, Hq); ring_simplify (q * 0) in Hq.
    destruct b; inversion Hq.
    exists 0; ring.
    
    exists (b / a).
    rewrite Zmult_comm, Z_mult_div_mod; auto.

    (* TODO déplacer et prouver : inutilisé mais intéressant.
    un peu intéressant, c'est dur environ comme sqrt(n)∈Q => sqrt(n)∈N *)
Abort.

Lemma Zpow_mod (a b m : Z) : (a ^ b) mod m = ((a mod m) ^ b) mod m.
Proof.
  assert (b < 0 \/ 0 <= b) as [bz | bz] by lia.
  - rewrite 2 Z.pow_neg_r; auto.
  - rewrite <-(Z2Nat.id b); auto.
    rewrite <-2Zpower_nat_Z.
    generalize (Z.to_nat b); intros n. clear b bz.
    destruct (Z.eq_dec m 0).
    + subst. now rewrite !Zmod_0_r.
    + induction n. easy. simpl.
      rewrite Z.mul_mod, IHn, Z.mul_mod_idemp_r; auto.
Qed.

(* When we already have a proof [pr] of [P] and the goal is [Q], it is
   enough to prove [P = Q] *)

Ltac exact_eq pr :=
  generalize pr;
  let A := fresh in
  assert (A : forall P Q : Prop, P = Q -> P -> Q) by congruence;
  apply A; clear A.

(* If [H] is a hypothesis of the form [P -> Q], assert a proof of [P]
   and remove the [P ->] from [H] *)

Tactic Notation "spec" hyp(H) :=
  match type of H with
  | ?P -> _ =>
    let h := fresh in
    assert (h : P); [ | specialize (H h); clear h ]
  end.

Tactic Notation "spec" hyp(H) "by" tactic(t) :=
  match type of H with
  | ?P -> _ =>
    let h := fresh in
    assert (h : P) by t;
    specialize (H h); clear h
  end.
