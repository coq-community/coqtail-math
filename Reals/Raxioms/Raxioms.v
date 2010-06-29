Require Export ZArith_base.
Require Export Rdefinitions.
Open Local Scope R_scope.

Axiom Rplus_comm : forall r1 r2:R, r1 + r2 = r2 + r1.
Axiom Rplus_assoc : forall r1 r2 r3:R, r1 + r2 + r3 = r1 + (r2 + r3).
Axiom Rplus_0_l : forall r:R, R0 + r = r.

Axiom Rplus_opp_r : forall r:R, r + - r = R0.

Axiom Rmult_comm : forall r1 r2:R, r1 * r2 = r2 * r1.
Axiom Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 = r1 * (r2 * r3).
Axiom Rmult_1_l : forall r:R, R1 * r = r.

(** Ça change un peu **)
Axiom Rinv_l : forall (r:R) (H : r <> R0), (Rinv r H) * r = R1.

(** Lui je le virerais bien pour avoir 0 < 1 plutôt **)
Axiom R1_neq_R0 : R1 <> R0.

Axiom Rmult_plus_distr_l : forall r1 r2 r3:R, r1 * (r2 + r3) = r1 * r2 + r1 * r3.


(** Plus d'ordre total, on utilise le tiers exclu maintenant ! **)
(** Axiom total_order_T : forall r1 r2:R, {r1 < r2} + {r1 = r2} + {r1 > r2}. **)

Axiom Rlt_asym : forall r1 r2:R, r1 < r2 -> ~ r2 < r1.
Axiom Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.
Axiom Rplus_lt_compat_l : forall r r1 r2:R, r1 < r2 -> r + r1 < r + r2.
Axiom Rmult_lt_compat_l : forall r r1 r2:R, R0 < r -> r1 < r2 -> r * r1 < r * r2.

Boxed Fixpoint INR (n:nat) : R :=
  match n with
  | O => R0
  | S O => R1
  | S n => INR n + R1
  end.

Definition IZR (z:Z) : R :=
  match z with
  | Z0 => R0
  | Zpos n => INR (nat_of_P n)
  | Zneg n => - INR (nat_of_P n)
  end.

(** Lui il change pas **)
Axiom archimed : forall r:R, IZR (up r) > r /\ IZR (up r) - r <= R1.

(** La complétude par contre... **)
(** Ouvert à discussion, pour l'instant, ce que ça représente c'est :
  toute série dyadique converge. **)
(** C'est pas très efficace, faudrait peut-être définir de manière abstraite
  ce que c'est qu'une somme itérée et utiliser un foncteur sur les suites. **)

Lemma neq_2_0 : R1 + R1 <> R0.
Proof.
Admitted.

Fixpoint pow r N := match N with
| O => R1
| S N => r * pow r N
end.

Fixpoint dyadic (f : nat -> bool) N := match N with
| O => R0
| S N => dyadic f N + (if f N then R1 else R0) * pow (Rinv (R1 + R1) neq_2_0) N
end.

Definition is_upper_bound (f : nat -> bool) (m : R) := forall N, dyadic f N <= m.
Definition is_lub (f : nat -> bool) (m:R) :=
  is_upper_bound f m /\ (forall b:R, is_upper_bound f b -> m <= b).
Axiom completeness : forall (f : nat -> bool),
  { m : R | is_lub f m }.
