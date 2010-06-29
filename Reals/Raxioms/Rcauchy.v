Require Import ZArith_base.
Require Import QArith Qabs.
Require Import Setoid SetoidClass Morphisms.

Require Import Rcauchy_lemmas.

Definition R := nat -> Q.
Open Local Scope Q_scope.

Definition Req u v := 
  forall ε, ε > 0 -> exists N:nat, forall n m, (n > N)%nat -> (m > N)%nat -> 
      Qabs (u n - v m) < ε.

Lemma equiv_trans : Transitive Req.
intros x y z H1 H2 ε ?. 
assert (Hε : (ε * (1#2)) > 0).
apply Qdiv_pos.
assumption.

destruct (H1 (ε * (1#2)) Hε) as [N₁ H₁ ?]. 
destruct (H2 (ε * (1#2)) Hε) as [N₂ H₂ ?]. 
exists (Max.max N₁ N₂).
intros n m Hn Hm.
apply Qle_lt_trans with (Qabs ((x n - y m) + (y m - z m))).
setoid_replace (x n - y m + (y m - z m)) with (x n - z m); [|ring].
apply Qle_refl.
apply Qle_lt_trans with ((Qabs (x n - y m)) + (Qabs (y m - z m))).
eapply Qabs_triangle.
setoid_replace ε with (ε * (1#2) + ε*(1#2)); [|field].
assert (Qabs (x n - y m) < ε * (1#2)).
apply H₁. 
apply le_lt_trans with (Max.max N₁ N₂); [ apply Max.le_max_l | assumption].
apply le_lt_trans with (Max.max N₁ N₂); [ apply Max.le_max_l | assumption].
assert (Qabs (y m - z m) < ε * (1#2)).
apply H₂.
apply le_lt_trans with (Max.max N₂ N₁); [ apply Max.le_max_l | rewrite Max.max_comm; assumption].
apply le_lt_trans with (Max.max N₂ N₁); [ apply Max.le_max_l | rewrite Max.max_comm; assumption].
auto with qarith.
apply Qplus_lt_morphism; assumption.
Qed.

Lemma equiv_sym : Symmetric Req.
intros x y H.
intros ε Hpos.
destruct (H ε Hpos) as [N Hε].
exists N.
intros.
setoid_replace (y n - x m) with (- (x m - y n)).
rewrite Qabs_opp.
apply Hε; assumption.
ring.
Qed.

Add Parametric Relation : R Req 
   symmetry proved by equiv_sym 
   transitivity proved by equiv_trans
 as Req_per.
Instance defaut_relation_Req : DefaultRelation Req.

Program Instance R_partial_setoid : PartialSetoid R := {
  pequiv := Req
}.
Next Obligation.
 intuition; auto.
Qed. 

Open Local Scope R_scope.
Delimit Scope R_scope with R.

Definition R0 : R := fun _ => 0%Q.
Definition R1 : R := fun _ => 1%Q.
Definition Rplus (u v : R) : R := fun n => (u n) + (v n).
Definition Rmult (u v : R) : R := fun n => (u n) * (v n).
Definition Ropp (u : R) : R := fun n => - (u n).
Definition Rabs (u : R) := fun n => Qabs (u n).
Definition Rpositive (u : R) := exists v, u =~= v /\ forall n, (v n > 0)%Q.
Definition Rlt u v := Rpositive (Rplus v (Ropp u)).

Definition Rinv u (H : ~(u =~= R0)) := fun n => Qinv (u n).

Infix "+" := Rplus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Notation "/ x H" := (Rinv x H) (at level 100) : R_scope.
Infix "<" := Rlt : R_scope.


(* A bit too much... why omega can't do that ? *)
Ltac max_solve trm := match constr:trm with 
    O => fail
 | S ?p => 
       eassumption 
    || (eapply Max.le_max_l; max_solve p)
    || eauto with zarith
    || (eapply le_lt_trans; max_solve p)
    || (rewrite Max.max_comm; max_solve p)
   end.
Tactic Notation "max_solve" := max_solve 6%nat. 

Add Morphism Rplus : Rplus_comp. 
intros u₁ u₂ H1 v₁ v₂ H2.
intros ε Hpos.
assert (Hε : (ε * (1#2)) > 0).
apply Qdiv_pos.
assumption.
destruct (H1 (ε*(1#2)) Hε)%Q as [N₁ H₁]; clear H1.
destruct (H2 (ε*(1#2))%Q Hε) as [N₂ H₂]; clear H2.
exists (Max.max N₁ N₂).
intros n m Hn Hm.
unfold Rplus.
setoid_replace (u₁ n + v₁ n - (u₂ m + v₂ m))%Q with ((u₁ n - u₂ m) + (v₁ n - v₂ m))%Q;[|ring].
apply Qle_lt_trans with ((Qabs (u₁ n - u₂ m)) + (Qabs (v₁ n - v₂ m)))%Q.
apply Qabs_triangle.
setoid_replace ε with (ε * (1#2) + ε*(1#2))%Q; [|field].
apply Qplus_lt_morphism.
apply H₁; max_solve.
apply H₂; max_solve.
Qed.

Fixpoint bounded_abs_max u n := match n with 
   O => Qabs (u O)
 | S p => Qmax (bounded_abs_max u p) (Qabs (u p))
end.

Lemma bounded_correct: 
  forall u N n, (n < N)%nat -> (Qabs (u n) <= (bounded_abs_max u N))%Q.
induction N; simpl.
intuition.
intros. 
inversion H.
rewrite Qmax_comm.

apply le_Qmax.
apply Qle_refl.
apply le_Qmax.
apply IHN.
omega.
Qed.

Lemma bounded : 
  forall u v:R, u =~= u -> exists M, forall n:nat, (Qabs (u n) <= M)%Q.
intros.
destruct (H 1%Q) as [N HN].
auto with qarith qartih.
exists (Qmax (bounded_abs_max u (S N)) (Qabs (u (S N)) + 1))%Q.
intros n. 
elim (le_lt_dec n N); intros Hdec.
apply le_Qmax.
apply bounded_correct.
omega.
rewrite Qmax_comm.
apply le_Qmax.
assert (Qabs (u n) - Qabs(u (S N)) <= 1).
apply Qle_trans with (Qabs (u n - u(S N))).
apply Qabs_triangle_reverse.
apply Qlt_le_weak.
apply HN.
assumption.
omega.
rewrite Qplus_comm.
setoid_replace (Qabs (u n)) with 
               ((Qabs (u n) - Qabs (u (S N))) + Qabs (u (S N)))%Q;[|ring].
apply Qplus_le_compat.
assumption.
apply Qle_refl.
Qed.

Add Morphism Rmult : Rmult_comp.
intros u₁ u₂ H1 v₁ v₂ H2.
intros ε Hpos.

assert (EC : (exists C, forall n, Qabs (u₁ n) < C /\ Qabs (u₂ n) < C /\ Qabs (v₁ n) < C /\ Qabs (v₂ n) < C)%Q).
(** skip at first read **)
assert (EA₁ :(exists A₁, forall n, Qabs (u₁ n) < A₁)%Q).
destruct (bounded u₁ u₁) as [A₁ HA₁].
eapply transitivity; [|symmetry];eassumption.
exists (A₁ + 1)%Q.
intros n; eapply Qle_lt_trans.
eapply HA₁.
setoid_replace A₁ with (A₁ + 0)%Q at 1; [|ring].
apply Qplus_le_lt_compat; auto with qarith qartih.
destruct EA₁ as [A₁ HA₁]. 
assert (EA₂ :(exists A₂, forall n, Qabs (u₂ n) < A₂)%Q).
destruct (bounded u₂ u₂) as [A₂ HA₂].
eapply transitivity; [symmetry|];eassumption.
exists (A₂ + 1)%Q.
intros n; eapply Qle_lt_trans.
eapply HA₂.
setoid_replace A₂ with (A₂ + 0)%Q at 1; [|ring].
apply Qplus_le_lt_compat; auto with qarith qartih.
destruct EA₂ as [A₂ HA₂]. 

assert (EB₁ :(exists B₁, forall n, Qabs (v₁ n) < B₁)%Q).
destruct (bounded v₁ v₁) as [B₁ HB₁].
eapply transitivity; [|symmetry];eassumption.
exists (B₁ + 1)%Q.
intros n; eapply Qle_lt_trans.
eapply HB₁.
setoid_replace B₁ with (B₁ + 0)%Q at 1; [|ring].
apply Qplus_le_lt_compat; auto with qarith qartih.
destruct EB₁ as [B₁ HB₁]. 
assert (EB₂ :(exists B₂, forall n, Qabs (v₂ n) < B₂)%Q).
destruct (bounded v₂ v₂) as [B₂ HB₂].
eapply transitivity; [symmetry|];eassumption.
exists (B₂ + 1)%Q.
intros n; eapply Qle_lt_trans.
eapply HB₂.
setoid_replace B₂ with (B₂ + 0)%Q at 1; [|ring].
apply Qplus_le_lt_compat; auto with qarith qartih.
destruct EB₂ as [B₂ HB₂]. 
exists (Qmax (Qmax A₁ A₂) (Qmax B₁ B₂)).
intros n.
let rec t trm := match constr:trm with 
    O => fail
 | S ?p => 
   first [ apply HA₁ | apply HA₂ | apply HB₁ | apply HB₂  | apply lt_Qmax; t p| rewrite Qmax_comm; t p]
end in repeat split; t 6%nat.
(** Ok, you can continue your reading here. *)
destruct EC as [C HC].
assert (Hpos_C : C > 0).
apply Qle_lt_trans with (Qabs (u₁ O)).
apply Qabs_nonneg.
elim (HC O); intuition.
assert (Hpos_complique : (ε * (Qinv C)*(1#3)) > 0).
apply Qdiv_pos.
apply Qmult_pos_compat.
assumption.
apply Qinv_lt_0_compat.
assumption.
destruct (H1 (ε * (Qinv C)*(1#3))%Q Hpos_complique) as [N₁ H₁]; clear H1.
destruct (H2 (ε * (Qinv C)*(1#3))%Q Hpos_complique) as [N₂ H₂]; clear H2.
exists (Max.max N₁ N₂).
intros n m Hn Hm.
unfold Rmult.
setoid_replace (u₁ n * v₁ n - u₂ m * v₂ m) 
               with (u₁ n * (v₁ n - v₂ m) + v₂ m * (u₁ n - u₂ m))%Q; [|ring].
eapply Qle_lt_trans.
eapply Qabs_triangle.
do 2 rewrite Qabs_Qmult.
apply Qle_lt_trans with 
    ((C * (ε * / C * (1 # 3))+ (C * (ε * / C * (1 # 3)))))%Q.
apply Qplus_le_morphism; (apply Qmult_pos_le_compat; (split; [ apply Qabs_nonneg | ])).
elim (HC n); intuition.
apply Qlt_le_weak; apply H₂; max_solve.
elim (HC m); intuition.
apply Qlt_le_weak; apply H₁; max_solve.
setoid_replace (C * (ε * / C * (1 # 3)) + C * (ε * / C * (1 # 3)))%Q
               with ((2#3)*ε)%Q.
setoid_replace ε with (1*ε)%Q at 2.
apply Qmult_lt_compat_r.
assumption.
auto with qarith qartih.
field.
field.
intro Abs; rewrite Abs in Hpos_C.
inversion Hpos_C.
Qed.

Lemma far_from_zero : 
  forall u:R, u =~= u -> ~(u =~= R0) -> exists N, forall n:nat, (n > N)%nat -> (Qabs (u n) > 0)%Q.
(* Il faut EM pour prouver ça. *)
Admitted.

(* This is the most difficult thing I have ever written with setoids. *)
Definition sign_rinv : relation (forall x:R, ~(x=~=R0) -> R).
refine (respectful_hetero R R (fun x => ~(x =~= R0) -> R) (fun x => ~(x =~= R0) -> R) 
           Req 
           _).
intros x y. 
refine (respectful_hetero (~(x =~= R0)) (~(y =~= R0)) (fun _ => R) (fun _ => R) 
           (fun x y => True) (fun _ _ => Req)).
Defined. 

(* It's complicated. Ok. But no body has to understand it. 
   The important thing is that the following morphism just say 
   what we want it to say. *)
Instance Rinv_comp : Morphism sign_rinv Rinv.
intros u v Huv π₁ π₂ _.
intros ε Hpos.

destruct (far_from_zero u) as [Nu].
eapply transitivity;[|symmetry];eassumption.
assumption.
destruct (far_from_zero v) as [Nv].
eapply transitivity;[symmetry|];eassumption.
assumption.
exists (Max.max Nu Nv).
intros n m Hn Hm.
unfold Rinv.

Admitted.
