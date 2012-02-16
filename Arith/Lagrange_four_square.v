Require Import ZArith Omega MyNat Div2.
Open Scope Z_scope.


(** Definitions on [nat] and [Z] *)

Definition Zsqr a := Zmult a a.

Definition Z_sum_of_4_squares (n : Z) : Type :=
  sigT (fun a => sigT (fun b => sigT (fun c => sig (fun d =>
    n = Zsqr a + Zsqr b + Zsqr c + Zsqr d)))).

Definition sum_of_4_squares (n : nat) : Type :=
  sigT (fun a => sigT (fun b => sigT (fun c => sig (fun d =>
    (n = a * a + b * b + c * c + d * d)%nat)))).

Lemma sum_of_4_squares_nat_Z : forall n,
  sum_of_4_squares n -> Z_sum_of_4_squares (Z_of_nat n).
Proof.
  intros n (a, (b, (c, (d, Hn)))); subst.
  repeat rewrite inj_plus; repeat rewrite inj_mult.
  repeat eexists.
Qed.

Lemma sum_of_4_squares_Z_nat : forall n,
  Z_sum_of_4_squares (Z_of_nat n) -> sum_of_4_squares n.
Proof.
  intros n (a, (b, (c, (d, Hn)))).
  exists (Zabs_nat a); exists (Zabs_nat b); exists (Zabs_nat c); exists (Zabs_nat d).
  apply inj_eq_rev; rewrite Hn.
  repeat rewrite inj_plus; repeat rewrite inj_mult.
  unfold Zsqr.
  f_equal; [ f_equal ; [ f_equal | ] | ];
    rewrite <- Zabs_square; f_equal; rewrite inj_Zabs_nat; auto.
Qed.


(** Euler's identity, compatibility of the 4-square property wrt. multiplication *)

Lemma euler_four_square_identity : forall a b c d w x y z : Z,
  (Zsqr a + Zsqr b + Zsqr c + Zsqr d) *
  (Zsqr w + Zsqr x + Zsqr y + Zsqr z) =
  Zsqr (a*w + b*x + c*y + d*z) +
  Zsqr (a*x - b*w - c*z + d*y) +
  Zsqr (a*y + b*z - c*w - d*x) +
  Zsqr (a*z - b*y + c*x - d*w).
Proof.
  intros.
  unfold Zsqr.
  ring.
Qed.

Definition Z_sum_of_2_squares (n : Z) : Type :=
  sigT (fun a => sig (fun b => n = Zsqr a + Zsqr b)).

Lemma mult_Z_sum_of_4_square_compat : forall n m,
  Z_sum_of_4_squares n -> Z_sum_of_4_squares m ->
    Z_sum_of_4_squares (n * m).
Proof.
  intros n m (a, (b, (c, (d, Hn)))) (x, (y, (z, (t, Hm)))); subst.
  rewrite euler_four_square_identity.
  repeat eexists.
Qed.

Lemma mult_sum_of_4_square_compat : forall n m,
  sum_of_4_squares n -> sum_of_4_squares m ->
    sum_of_4_squares (n * m).
Proof.
  intros n m Nn Nm.
  apply sum_of_4_squares_Z_nat.
  apply sum_of_4_squares_nat_Z in Nn; apply sum_of_4_squares_nat_Z in Nm.
  rewrite inj_mult.
  apply mult_Z_sum_of_4_square_compat; auto.
Qed.



(** Part about even/odd reasoning. May be removed in the future. *)

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

Lemma sqr_double : forall n, 4 * Zsqr n = Zsqr (2 * n).
Proof.
  intros; unfold Zsqr; ring.
Qed.

Lemma half : forall m, Z_sum_of_2_squares (2 * m) -> Z_sum_of_2_squares m.
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
      unfold Zsqr; ring.
      apply odd_add; auto.
      apply odd_sub; auto.
    apply even_sqrt in Ex. apply even_sqrt in Ey.
    repeat rewrite even_div.
      unfold Zsqr; ring.
      apply even_add; auto.
      apply even_sub; auto.
Qed.



(** Properties on prime numbers *)

(* refaire prime sur nat, refaire l'amaurythmétique dans Type au lieu de Prop *)

Variable prime : nat -> Type.

Variable prime_ge_2 : forall n, prime n -> (2 <= n)%nat.

Fixpoint prod n f :=
  match n with
  | O => S O
  | S n => mult (f n) (prod n f)
  end.

Definition bforall n {X} P (xs : nat -> X) : Type := forall i, lt i n -> P (xs i).

Variable factorisation : forall x, x <> O ->
  sigT (fun n => sigT (fun ps =>
    (bforall n prime ps * (prod n ps = x))%type)).

Definition eqmod (m : Z) (a b : Z) := Zmod a m = Zmod b m.

Parameter prime_sqr_simpl : forall p i j, eqmod p (Zsqr i) (Zsqr j) -> eqmod p i j.

Lemma factor_not_zero : forall n ps, bforall n prime ps -> prod n ps <> O.
Proof.
  intros n; induction n; intros ps Pps; simpl; auto.
  remember (ps n) as psn; remember (prod n ps) as pps; destruct psn; destruct pps;
    try (exfalso; simpl; eapply IHn; [ | eauto ]; intros i Hi; solve [eauto]).
    
    exfalso.
    pose proof (prime_ge_2 (ps n) (Pps _ (le_refl _))).
    omega.
    
    simpl; intros I; inversion I.
Qed.

Lemma prime_ind_l : forall P,
  (P O) ->
  (P 1%nat) ->
  (forall p, prime p -> P p) ->
  (forall p n, prime p -> P n -> P (mult p n)) ->
    forall n, P n.
Proof.
  intros P H0 H1 Hp Hpn x.
  destruct x as [ | x ]; [ auto | ].
  destruct (factorisation (S x)) as (n, (ps, (Pps, Hpsx))); [ auto | ].
  generalize x Hpsx; clear Hpsx x.
  induction n.
    simpl; intros x Ex1; rewrite <- Ex1; assumption.
    
    simpl; intros x Ex; rewrite <- Ex.
    apply Hpn.
      apply Pps; auto.
      remember (prod n ps) as psn; destruct psn as [ | psn].
        eauto.
        apply IHn.
          intros i Hi; eauto.
          auto.
Qed.

Lemma prime_ind : forall P,
  (P 0%nat) ->
  (P 1%nat) ->
  (forall n, prime n -> P n) ->
  (forall a b, P a -> P b -> P (a * b))%nat ->
    forall n, P n.
Proof.
  intros; apply prime_ind_l; eauto.
Qed.




(** Finite and decidable subsets of nat *)

Definition IBN : bool -> nat := fun b => (if b then 1 else 0)%nat.

Definition inter (P Q : nat -> bool) := fun i => andb (P i) (Q i).

Definition union (P Q : nat -> bool) := fun i => orb (P i) (Q i).

Fixpoint count n P :=
  match n with
  | O => O
  | S n => (IBN (P n) + count n P)%nat
  end.

(* This lemma is a corollary of the next one that is more elegant. TODO *)

Lemma count_drawers : forall P Q n,
  (n < count n P + count n Q)%nat -> { i | lt i n /\ P i = true /\ Q i = true  }.
Proof.
  intros P Q n; induction n; intros CPQ.
    exfalso; inversion CPQ.
    
    remember (P n) as Pn; remember (Q n) as Qn;
      symmetry in HeqPn, HeqQn.
    
    destruct Pn; destruct Qn; eauto;
      (destruct IHn as (i, (Bi, (Pi, Qi)));
        [ simpl in CPQ; rewrite HeqPn, HeqQn in CPQ; simpl in CPQ; omega
        | exists i; auto ]).
Qed.

Lemma count_union n P Q : (count n (union P Q) + count n (inter P Q) =
  count n P + count n Q)%nat.
Proof.
  induction n; auto; simpl.
  unfold IBN, union, inter in *.
  remember (P n) as Pn; remember (Q n) as Qn.
  destruct Pn; destruct Qn; simpl; omega.
Qed.

Definition nat_decidable P := forall n : nat, P n + (P n -> False).

Definition nat_dec_bool P (Pdec : nat_decidable P) : nat -> bool :=
  fun n => if Pdec n then true else false.

Lemma nat_dec_bool_true : forall P (Pdec : nat_decidable P) n,
  nat_dec_bool P Pdec n = true -> P n.
Proof.
  intros P Pdec n; unfold nat_dec_bool in *; destruct (Pdec n).
    auto.
    intros i; inversion i.
Qed.

Lemma nat_dec_bool_false : forall P (Pdec : nat_decidable P) n,
  nat_dec_bool P Pdec n = false -> P n -> False.
Proof.
  intros P Pdec n; unfold nat_dec_bool in *; destruct (Pdec n).
    intros i; inversion i.
    auto.
Qed.

Definition injective n (f : nat -> nat) := forall i j,
  lt i n -> lt j n -> f i = f j -> i = j.

Definition bound n m (f : nat -> nat) := forall i, lt i n -> lt (f i) m.

Record natset := mknatset { natset_bound : nat; natset_charact : nat -> bool }.

Definition mknatset_dec n P (Pdec : nat_decidable P) :=
  mknatset n (nat_dec_bool P Pdec).

Program Definition image n m (f : nat -> nat) : natset :=
  mknatset_dec m (fun y => { x | y = f x /\ lt x n}) _.
Next Obligation.
  intros y.
  induction n.
    right; intros (x, (_, I)); inversion I.
    destruct (eq_nat_dec (f n) y) as [E|E].
      left; exists n; eauto.
      destruct IHn as [(x, (Hxy, Bx)) | I].
        left; exists x; eauto.
        right; intros (x, (Hxy, Bx)); apply I; exists x; split.
          auto.
          destruct (eq_nat_dec x n) as [G|G].
            subst; tauto.
            omega.
Defined.

Definition card (S : natset) := count (natset_bound S) (natset_charact S).

Lemma card_image_injective : forall n m f,
  injective n f -> bound n m f ->
    card (image n m f) = n.
Proof.
  intros n m; generalize n; clear n; induction m; intros n f If Bf.
    compute.
    destruct n; auto.
    specialize (Bf O (lt_O_Sn _)); inversion Bf.
    
    unfold card, image, image_obligation_1 (*ouch*).
    simpl.
    unfold nat_dec_bool.
    (* arf *)
Admitted.



(** 4-square property on prime numbers (the interesting part) *)

Lemma prime_dividing_sum_of_two_squares_plus_one : forall p, prime p -> (2 <= p)%nat ->	
  sigT (fun l => sigT (fun m => sig (fun k => p * k = 1 + l * l + m * m)%nat)).
Proof.
  intros p Pp Op.
  (* arithmétique modulaire, pas forcément dans Z d'ailleurs *)
  (*
  pose (P := fun i => {l | eqmod p (Z_of_nat i) (sqr l)}).
  pose (Q := fun i => {m | eqmod p (Z_of_nat i) (- 1 - sqr m)}).
  assert (Pdec : nat_decidable P).
    admit.
  
  assert (Qdec : nat_decidable Q).
    admit.
  
  assert nat as p_nat by admit.
  
  destruct (count_drawers (nat_dec_bool P Pdec) (nat_dec_bool Q Qdec) p_nat).
    unfold lt.
    transitivity (div2 (p_nat + 1) + div2 (p_nat + 1))%nat.
    
      admit (* impair. Il faudra probablement le refaire avec nat. *).
      
      apply plus_le_compat.
      
        admit (* aïe *).
        
        admit (* même chose *).
    
    (* destruct machin *)
    
(*
  si P est vrai pour au moins p
  si Q est vrai pour au moins p
  dans un ensemble de taille 2p-1, alors exists x P x /\ Q x.
*)
(* Raisonnement modulo, pas de quaternions ici *)
*)
Admitted.

Lemma sum_of_4_squares_prime_factor_decreasing :
  forall p, prime p -> forall m, (1 < m < p)%nat ->
    sum_of_4_squares (m * p) ->
      sigT (fun n => ((0 < n < m)%nat * sum_of_4_squares (n * p))%type).
Proof.
  (* Arithmétique modulaire et compliquée *)
Admitted.

Lemma sum_of_4_squares_prime : forall p, prime p -> sum_of_4_squares p.
Proof.
  (* Application itérée du précédent lemme *)
Admitted.


(** Trivial application of the previous lemma and euler's identity *)

Theorem lagrange_4_square_theorem : forall n, sum_of_4_squares n.
Proof.
  intros n; apply prime_ind.
    repeat (exists O); auto.
    exists (S O); repeat (exists O); auto.
    apply sum_of_4_squares_prime.
    apply mult_sum_of_4_square_compat.
Qed.

(*
http://planetmath.org/encyclopedia/ProofOfLagrangesFourSquareTheorem.html
(le site est down le 13 février 2012 à 19h)
*)

