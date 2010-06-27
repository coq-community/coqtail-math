Require Export ZArith_base.
Require Export Rdefinitions.
Open Local Scope R_scope.

Axiom Rplus_comm : forall r1 r2:R, r1 + r2 = r2 + r1.
Axiom Rplus_assoc : forall r1 r2 r3:R, r1 + r2 + r3 = r1 + (r2 + r3).
Axiom Rplus_0_l : forall r:R, 0 + r = r.

Axiom Rplus_opp_r : forall r:R, r + - r = 0.

Axiom Rmult_comm : forall r1 r2:R, r1 * r2 = r2 * r1.
Axiom Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 = r1 * (r2 * r3).
Axiom Rmult_1_l : forall r:R, 1 * r = r.

(** Ça change un peu **)
Axiom Rinv_l : forall r:R (H : r <> 0), / r H * r = 1.

(** Lui je le virerais bien pour avoir 0 < 1 plutôt **)
Axiom R1_neq_R0 : 1 <> 0.

Axiom Rmult_plus_distr_l : forall r1 r2 r3:R, r1 * (r2 + r3) = r1 * r2 + r1 * r3.


(** Plus d'ordre total, on utilise le tiers exclu maintenant ! **)
(** Axiom total_order_T : forall r1 r2:R, {r1 < r2} + {r1 = r2} + {r1 > r2}. **)

Axiom Rlt_asym : forall r1 r2:R, r1 < r2 -> ~ r2 < r1.
Axiom Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.
Axiom Rplus_lt_compat_l : forall r r1 r2:R, r1 < r2 -> r + r1 < r + r2.
Axiom Rmult_lt_compat_l : forall r r1 r2:R, 0 < r -> r1 < r2 -> r * r1 < r * r2.

Boxed Fixpoint INR (n:nat) : R :=
  match n with
  | O => 0
  | S O => 1
  | S n => INR n + 1
  end.

Definition IZR (z:Z) : R :=
  match z with
  | Z0 => 0
  | Zpos n => INR (nat_of_P n)
  | Zneg n => - INR (nat_of_P n)
  end.

(** Lui il change pas **)
Axiom archimed : forall r:R, IZR (up r) > r /\ IZR (up r) - r <= 1.

(** La complétude par contre... **)
(** Ouvert à discussion, pour l'instant, ce que ça représente c'est :
  toute série dyadique converge. **)
(** C'est pas très efficace, faudrait peut-être définir de manière abstraite
  ce que c'est qu'une somme itérée et utiliser un foncteur sur les suites. **)

Lemma 2_neq_0 : 2 <> 0.
Proof. blabla. Qed.

Fixpoint pow r N := match N with
| 0 => 1
| S N => r * pow r N
end.

Fixpoint dyadic f N := match N with
| 0 => 0
| S N => dyadic f N + (if f N then 1 else 0) * pow (/ 2 2_neq_0) N
end.

Definition is_upper_bound (f : nat -> bool) (m : R) := forall N, dyadic f N <= m.
Definition is_lub (f : nat -> bool) (m:R) :=
  is_upper_bound f m /\ (forall b:R, is_upper_bound f b -> m <= b).
Axiom completeness : forall (f : nat -> bool),
  { m : R | is_lub f m }.
