Require Raxiom.
Require Import ZArith.

(* We use sequences of the form (z_n/2^n) so the property "Zseq_Cauchy" is quite verbose *)

Definition pow2 : nat -> positive := fix f n := match n with O => xH |  S n' => xO (f n') end.

Definition Zseq_Cauchy (Un : nat -> Z) : Type := forall neps : nat,
  {N : nat & forall p q, (N <= p)%nat -> (N <= q)%nat -> 
    (
      Zneg (pow2 p * pow2 q)  <=
      ((Un p) * Zpos (pow2 q) - (Un q) * Zpos (pow2 p)) * Zpos (pow2 neps) <=
      Zpos (pow2 p * pow2 q)
    )%Z
  }.

Module Rrealize : Raxiom.CReals.
  (*Inductive _R : Type := Rcauchy : forall Un, Zseq_Cauchy Un -> _R.*)
  
  Record _R : Type := Rdef {
    Rseq : nat -> Z;
    Rcauchy : Zseq_Cauchy Rseq
  }.
  
  Definition R := _R.
  
  Program Definition Const (c : Z) := Rdef (fun n => (c * Zpos (pow2 n))%Z) _.
  Next Obligation.
  Proof.
    intros neps.
    exists O; intros p q _ _.
    repeat rewrite <- Zmult_assoc.
    rewrite (Zmult_comm (Zpos (pow2 p))).
    rewrite Zminus_diag, Zmult_0_l.
    split.
     apply Zlt_le_weak, Zlt_neg_0.
     apply Zle_0_pos.
  Qed.
  
  Definition R0 := Const Z0.
  Definition R1 := Const 1%Z.
  
  Require Import Max.
  
  Program Definition Radd a b := Rdef (fun n => (Rseq a n + Rseq b n)%Z) _.
  (*Program Definition Radd a b := match a, b with Rcauchy u Hu, Rcauchy v Hv =>
    Rcauchy (fun n => (u n + v n)%Z) _
  end.*)
  Next Obligation.
  Proof.
    destruct a as (u, Hu).
    destruct b as (v, Hv).
    intros neps.
    destruct (Hu (S neps)) as (Nu, HNu).
    destruct (Hv (S neps)) as (Nv, HNv).
    exists (max Nu Nv).
    intros p q Hp Hq.
    assert (Hpu := max_lub_l _ _ _ Hp);
    assert (Hpv := max_lub_r _ _ _ Hp);
    assert (Hqu := max_lub_l _ _ _ Hq);
    assert (Hqv := max_lub_r _ _ _ Hq); clear Hp Hq.
    assert (U := HNu p q Hpu Hqu).
    assert (V := HNv p q Hpv Hqv).
    assert (HR : forall a b c d e f g, (((a + b) * c - (d + e) * f) * g = (a * c - d * f) * g + (b * c - e * f) * g)%Z)
      by (intros; ring).
    rewrite HR.
    cut (forall e f a b,
      (Zneg e <= a * 2 * f <= Zpos e ->
      Zneg e <= b * 2 * f <= Zpos e ->
      Zneg e <= a * f + b * f <= Zpos e)%Z).
     intros HA; apply HA; simpl pow2 in U, V; rewrite Zpos_xO, Zmult_assoc in U, V; assumption.
     clear.
     intros e f a b Ha Hb.
     rewrite <- (Zopp_involutive (Zneg e)), Zopp_neg in *.
     repeat rewrite <- (Zmult_comm f), Zmult_assoc in *; rewrite <- (Zmult_comm f).
     assert (He : (0 < Zpos e)%Z) by reflexivity.
     remember (Zpos e) as Pe.
     remember (f * a)%Z as fa.
     remember (f * b)%Z as fb.
     omega.
  Qed.
  
  Program Definition Rmul a b := Rdef (fun n => (Rseq a n * Rseq b n * Zpos (pow2 n))%Z) _.
  Next Obligation.
   (* TODO *)
  Admitted.
  
  Program Definition Ropp a := Rdef (fun n => - Rseq a n)%Z _.
  Next Obligation.
    destruct a as (u, Hu).
    intros neps.
    destruct (Hu neps) as (N, HN).
    exists N; intros p q Hp Hq.
    pose proof HN p q Hp Hq.
    cut (forall e a a' b b' f, (Zneg e <= (a * a' - b * b') * f <= Zpos e ->
      Zneg e <= (- a * a' - - b * b') * f <= Zpos e)%Z).
     intros HA; apply HA; auto.
     
     clear.
     intros e a a' b b' f Hab.
     rewrite Zmult_minus_distr_r in *.
     repeat rewrite <- Zopp_mult_distr_l in *.
     rewrite <- (Zopp_involutive (Zneg e)), Zopp_neg in *.
     assert (He : (0 < Zpos e)%Z) by reflexivity.
     remember (Zpos e) as Pe.
     remember (a * a' * f)%Z as fa.
     remember (b * b' * f)%Z as fb.
     omega.
  Qed.
  
  Definition Rsub a b := Radd a (Ropp b).
  
  (*Inductive _Rlt : R -> R -> Type :=
    | Rlt_c : forall (neps : nat) (N : nat) u (Hu : Zseq_Cauchy u) v (Hv : Zseq_Cauchy v),
        (forall n, le N n -> u n * Zpos (pow2 neps) + 1 < v n * Zpos (pow2 neps))%Z ->
        _Rlt (Rcauchy u Hu) (Rcauchy v Hv).*)
  
  (*Definition Rlt (a b : R) : Type := match a, b with
    | Rcauchy u Hu, Rcauchy v Hv => sigT (fun neps => sigT (fun N =>
        forall n, le N n -> u n * Zpos (pow2 neps) + Zpos (pow2 n) < v n * Zpos (pow2 neps))%Z)
  end.*)
  
  Definition Rlt (a b : R) : Type := sigT (fun neps => sigT (fun N =>
    forall n, le N n -> 
      Rseq a n * Zpos (pow2 neps) + Zpos (pow2 n) <=
      Rseq b n * Zpos (pow2 neps))%Z).
  
  Definition Rgt (r1 r2 : R) := Rlt r2 r1.
  Definition Rdiscr (r1 r2 : R) := sum (Rlt r1 r2) (Rlt r2 r1).
  Definition Req (r1 r2 : R) := Rdiscr r1 r2 -> False.
  Definition Rle (r1 r2 : R) := sumor (Rlt r1 r2) (Req r1 r2).
  Definition Rge (r1 r2 : R) := Rle r2 r1.
  
  Program Definition Rinv (x : R) (_ : Rdiscr x R0) :=
    Rdef (fun n => Zdiv (Zpos (pow2 n)) (Rseq x n))%Z _.
  Next Obligation.
    Let P2 := fun n => Zpos (pow2 n).
    destruct x as (u, Cu).
    destruct H as [ xneg | xpos ].
      (* Cas : x < 0 *)
      admit.
      
      (* Cas : x > 0 *)
      destruct xpos as (en, (Nen, Hen)).
      simpl Rseq in Hen.
      simpl.
      intros neps.
      
      Open Scope Z_scope.
      (* |up - uq| < ε |up uq| pour p, q assez grands. *)
      (* |up - uq| < ε * δ²/2   donc δ = 2^-(2*en+2) *)
      (* aussi, trouver n pour δ/2 < up, uq *)
      assert (epscut : { N | (forall p q, le N p -> le N q ->
          ((u q * P2 p - u p * P2 q) * P2 neps
          <= u p * P2 p * u q * P2 q
          <= (u q * P2 p - u p * P2 q) * P2 neps)) /\
          forall n, le N n -> 0 < u n}).
        admit.
      (* Check epscut.*) (* endassert →→ tactique "now" ? *)
      
      destruct epscut as (N, (HN, upos)).
      exists N.
      intros p q Pp Pq.
      specialize (HN p q Pp Pq); destruct HN as (HNl, HNu).
      apply (Z_div_le _ _ (u p)) in HNl.
      (* SUPER RELOU, il faut gérer la division dans Z avec les ≤ dans tous les sens. *)
      split.
        (* - 2p2q <= _ *)
        admit.
        
        (* _ <= + 2p2q *)
        unfold Zdiv.
        
  Admitted.
  
  Definition Rdiv x y (p : Rdiscr y R0) := Rmul x (Rinv y p).
  
  Lemma Rlt_trans : forall x y z, Rlt x y -> Rlt y z -> Rlt x z.
  Proof.
   intros (x, Cx) (y, Cy) (z, Cz) (nxy, (Nxy, Hxy)) (nyz, (Nyz, Hyz)).
   exists nxy; exists (max Nxy Nyz).
   intros n Hn.
   eapply Zle_trans.
    apply Hxy; eapply max_lub_l; eauto.
    cut (y n <= z n)%Z.
     intros H.
     apply Zmult_le_compat_r; auto.
     apply Zlt_le_weak; reflexivity.
     
     apply (Zmult_lt_0_le_reg_r _ _ (Zpos (pow2 nyz))).
      reflexivity.
      refine (Zle_trans _ _ _ _ (Hyz n (max_lub_r _ _ _ Hn))).
      rewrite <- Zplus_0_r at 1.
      apply Zplus_le_compat_l; apply Zlt_le_weak; reflexivity.
  Qed.
  
  Lemma Rlt_asym : forall x y : R, Rlt x y -> Rlt y x -> False.
   intros (x, Cx) (y, Cy) (nxy, (Nxy, Hxy)) (nyx, (Nyx, Hyx)).
   simpl Rseq in *.
   pose (N := max Nxy Nyx).
   assert (Zpospos : forall p, (0 < Zpos p)%Z) by reflexivity.
   remember (Zpos (pow2 nxy)) as n1.
   remember (Zpos (pow2 nyx)) as n2.
   assert (Pn1 : (0 < n1)%Z) by (subst; reflexivity).
   assert (Pn2 : (0 < n2)%Z) by (subst; reflexivity).
   assert (XY := Hxy N (le_max_l _ _)).
   assert (YX := Hyx N (le_max_r _ _)).
   assert (XY2 := Zmult_le_compat_r _ _ n2 XY (Zlt_le_weak _ _ Pn2)).
   assert (YX2 := Zmult_le_compat_r _ _ n1 YX (Zlt_le_weak _ _ Pn1)).
   rewrite Zmult_plus_distr_l in *.
   repeat rewrite <- Zmult_assoc in *.
   rewrite <- (Zmult_comm n1) in *.
   repeat rewrite Zmult_assoc in *.
   cut (forall a b p, (0 < p -> a + p * n1 <= b -> b + p * n2 <= a -> False)%Z).
    intros HF; eapply (HF _ _ (Zpos (pow2 N)) (eq_refl _)); eauto.
    clear -Pn1 Pn2.
    intros.
    assert (0 < p * n1)%Z by (apply Zmult_lt_0_compat; auto).
    assert (0 < p * n2)%Z by (apply Zmult_lt_0_compat; auto).
    set (p * n1)%Z in *.
    set (p * n2)%Z in *.
    omega.
  Qed.
  
  Lemma JOKER {P} : P.
  Admitted.
  
  Lemma Zneg_Zpos : forall p, Zneg p = Zopp (Zpos p).
  Proof.
   reflexivity.
  Qed.
  
  Lemma Req_lt_compat_l : forall a b c : R, Req a b -> Rlt a c -> Rlt b c.
  Proof.
   intros (a, Ca) (b, Cb) (c, Cc) Heq (nac, (Nac, Hac)).
   assert (Q : forall {a b}, ((a + b) -> False) -> (a -> False))
     by intuition; assert (Nltab := Q _ _ Heq); clear Heq.
   set (neps := S (S nac)).
   destruct (Ca neps) as (Na, HNa).
   destruct (Cb neps) as (Nb, HNb).
   destruct (Cc neps) as (Nc, HNc).
   assert (Easy : sigT (fun N => (le Nac N * le Na N * le Nb N * le Nc N)%type)) by admit.
   destruct Easy as (N, (((NNac, NNa), NNb), NNc)).
   exists neps; exists N.
   intros n Hn.
   simpl Rseq.
   assert (HNa' := HNa N n NNa JOKER).
   assert (HNb' := HNb N n NNb JOKER).
   assert (HNc' := HNc N n NNc JOKER).
   assert (Hac' := Hac n JOKER).
   simpl Rseq in *.
   unfold neps in *; simpl pow2 in *; rewrite Zpos_xO, (Zpos_xO (pow2 nac)) in *.
   rewrite Zneg_Zpos, Zpos_mult_morphism in *.
   set (DN := Zpos (pow2 N)) in *.
   set (Dn := Zpos (pow2 n)) in *.
   set (DE := Zpos (pow2 nac)) in *.
   
   destruct (Z_lt_le_dec (a N * 4 * DE + 2 * DN) (b N * 4 * DE)) as [AB | AB].
    elimtype False.
    (*clear Hn Dn HNc' Hac' n.*)
    apply Nltab.
    exists nac; exists N; intros.
    simpl Rseq.
    fold DE.
    assert (HNa'' := proj1 (HNa N n0 NNa JOKER)).
    assert (HNb'' := HNb N n0 NNb JOKER).
    rewrite Zneg_Zpos, Zpos_mult_morphism in *.
    set (Dn0 := Zpos (pow2 n0)) in *; fold DN in HNa'', HNb''.
    apply Zmult_lt_0_le_reg_r with (4 * DN)%Z; [ reflexivity | ].
    rewrite Zmult_plus_distr_l.
    ring_simplify.
    apply Zle_trans with (4 * a N * DE * Dn0 + 5 * Dn0 * DN)%Z.
     apply Zplus_le_reg_r with (- 4 * a n0 * DE * DN - 5 * DN * Dn0)%Z.
     ring_simplify.
     assert (AP : forall a a' b b', a = a' -> b = b' -> Zle a b -> Zle a' b')
       by (intros; subst; auto).
     refine (AP _ _ _ _ _ _ HNa''); ring.
     
     apply Zle_trans with (4 * DE * Dn0 * b N - DN * Dn0)%Z.
      replace (5 * Dn0 * DN)%Z with (5 * DN * Dn0)%Z by ring.
      replace (4 * DE * Dn0 * b N)%Z with (4 * DE * b N * Dn0)%Z by ring.
      rewrite <- Zmult_plus_distr_l.
      rewrite <- Zmult_minus_distr_r.
      apply Zmult_gt_0_le_compat_r; [ reflexivity | ].
      
      
    clear HNa HNb HNc Hac.
    ring_simplify.
    replace (2 * (2 * DE))%Z with (4 * DE)%Z in * by ring.
    remember (4 * DE)%Z as DE4.
    rewrite Zmult_comm, Zmult_assoc, (Zmult_comm DE), <- HeqDE4.
    rewrite <- Zmult_assoc, <- HeqDE4 in AB.

    assert (I1 : (b n * DN * DE4 + Dn * DN <= b N * Dn * DE4)%Z).
      admit.
    assert (I2 : (b N * Dn * DE4 <= a N * Dn * DE4 + 2 * Dn * DN)%Z).
      replace (b N * Dn * DE4)%Z with (Dn * (b N * DE4))%Z by ring.
      replace (a N * Dn * DE4 + 2 * Dn * DN)%Z with (Dn * (a N * DE4 + 2 * DN))%Z by ring.
(*      replace (a N * DE4)%Z with (a N * 4 * DE)%Z by (subst; ring).
      refine (Zmult_le_compat_l _ _ Dn AB JOKER).
    assert (I3 : (a N * Dn * DE4 + 2 * Dn * DN <= c N * Dn * DE4)%Z).
      admit.
    assert (I4 : (c N * Dn * DE4 <= c n * DN * DE4 - Dn * DN)%Z).
      admit.
    assert (I5 := Zle_trans _ _ _ I1 (Zle_trans _ _ _ I2 (Zle_trans _ _ _ I3 I4))).
    repeat rewrite <- Zmult_assoc in I5.
    repeat rewrite (Zmult_comm DN) in I5.
    repeat rewrite Zmult_assoc in I5.
    rewrite <- Zmult_plus_distr_l, <- Zmult_minus_distr_r in I5.
    assert (I6 := Zmult_lt_0_le_reg_r _ _ _ JOKER I5).
    assert (0 < Dn)%Z by reflexivity.
    repeat rewrite <- (Zmult_comm DE4) in *.
    set (DE4 * c n)%Z in *.
    set (DE4 * b n)%Z in *.
    omega.*)
    admit.
    admit.
    admit.
    admit.
  Qed.
  
  Lemma Req_lt_compat_r : forall x1 x2 y : R, Req x1 x2 -> Rlt y x1 -> Rlt y x2.
  Admitted. (* TODO *)
  
  Lemma Radd_lt_compat_l : forall x y1 y2 : R, Rlt y1 y2 -> Rlt (Radd x y1) (Radd x y2).
  Admitted. (* TODO *)
  
  Lemma Radd_eq_compat_l : forall x y1 y2, Req y1 y2 -> Req (Radd x y1) (Radd x y2).
  Admitted. (* TODO *)
  
  Lemma Rmul_lt_compat_l : forall x y1 y2 : R, Rlt R0 x -> Rlt y1 y2 -> Rlt (Rmul x y1) (Rmul x y2).
  Admitted. (* TODO *)
  
  Lemma Rmul_eq_compat_l : forall x y1 y2, Req y1 y2 -> Req (Rmul x y1) (Rmul x y2).
  Admitted. (* TODO *)
  
  Lemma Rinv_0_lt_compat : forall (x : R) (pr : Rlt R0 x) (pr' : Rdiscr x R0), Rlt R0 (Rinv x pr').
  Admitted. (* TODO *)
  
  Lemma Radd_comm : forall a b, Req (Radd a b) (Radd b a).
  Admitted. (* TODO *)
  
  Lemma Radd_assoc : forall x y z, Req (Radd (Radd x y) z) (Radd x (Radd y z)).
  Admitted. (* TODO *)
  
  Lemma Radd_opp_r : forall x, Req (Radd x (Ropp x)) R0.
  Admitted. (* TODO *)
  
  Lemma Radd_0_l : forall x, Req (Radd R0 x) x.
  Proof.
    intros x [Lt | Lt]; destruct Lt as (NE, (N, HN));
      assert (HNN := HN N (le_refl _));
      simpl in HNN;
      set (Rseq x N * Zpos (pow2 NE))%Z in *;
      assert (0 < Zpos (pow2 N))%Z by reflexivity;
      omega.
  Qed.
  
  Lemma Rmul_add_distr_l a b c : Req (Rmul a (Radd b c)) (Radd (Rmul a b) (Rmul a c)).
  Admitted. (* TODO *)
  
  Lemma Rmul_comm : forall a b, Req (Rmul a b) (Rmul b a).
  Proof.
    intros a b [Lt | Lt]; destruct Lt as (NE, (N, HN));
      assert (HNN := HN N (le_refl _));
      simpl in HNN;
      rewrite (Zmult_comm (Rseq b N)) in HNN;
      set (Rseq a N * Rseq b N * Zpos (pow2 N) * Zpos (pow2 NE))%Z in *;
      assert (0 < Zpos (pow2 N))%Z by reflexivity;
      omega.
  Qed.
  
  Lemma Rmul_assoc : forall x y z, Req (Rmul (Rmul x y) z) (Rmul x (Rmul y z)).
  Proof.
    assert (BAH : forall a a' c, (a = a' -> 0 < c -> a + c <= a' -> False)%Z) by (intros; omega).
    intros a b c [Lt | Lt]; destruct Lt as (NE, (N, HN));
      assert (HNN := HN N (le_refl _));
      simpl in HNN;
      (refine (BAH _ _ _ _ _ HNN); [ ring | reflexivity ]).
  Qed.
  
  Lemma Rmul_1_l : forall x, Req (Rmul R1 x) x.
  Admitted. (* TODO *)
  
  Lemma Rinv_l : forall (x : R) (pr : Rdiscr x R0), Req (Rmul (Rinv x pr) x) R1.
  Admitted. (* TODO *)
  
  Lemma Rlt_0_1 : Rlt R0 R1.
  Proof.
    exists O; exists O; intros n Hn.
    simpl; rewrite Zpos_mult_morphism; omega.
  Qed.
  
  Fixpoint IPR (p : positive) : R :=
    match p with
      | xI p => Radd (Rmul (Radd R1 R1) (IPR p)) R1
      | xO p => Rmul (Radd R1 R1) (IPR p)
      | xH => R1
    end.
  Arguments Scope IPR [positive_scope].
  
  Definition IZR (z : BinInt.Z) : R :=
    match z with
      | Z0 => R0
      | Zpos p => IPR p
      | Zneg p => Ropp (IPR p)
    end.
  Arguments Scope IZR [Z_scope].
  
  Definition Rdist x y d : Type := prod (Rlt (Rsub x y) d) (Rlt (Ropp d) (Rsub x y)).
  
  Definition Rup (x : R) : Z := let (N, _) := Rcauchy x 1%nat in (Zdiv (Rseq x N) (Zpos (pow2 N))).
  
  Lemma Rup_spec : forall r : R, Rdist r (IZR (Rup r)) R1.
  Proof.
    intros (u, Hu).
    unfold Rup; simpl.
    destruct (Hu 1%nat) as (N, HN).
    split; exists O; exists N; intros n Hn.
    destruct (HN N n (le_refl _) Hn) as (NS, NI).
    simpl Hu.
    assert (HNN := Hu 1%nat).
    simpl Rup.
    
    
  Admitted.
  
  Definition Rseq_Cauchy (Un : nat -> R) : Type := forall eps, Rlt R0 eps ->
    {N : nat & forall p q, (N <= p)%nat -> (N <= q)%nat -> Rdist (Un p) (Un q) eps}.
  
  Definition Rseq_cv (Un : nat -> R) (l : R) : Type := forall eps, Rlt R0 eps ->
    {N : nat & forall n, (N <= n)%nat -> Rdist (Un n) l eps}.
  
  Lemma Rcomplete : forall Un, Rseq_Cauchy Un -> {l : R & Rseq_cv Un l}.
  Admitted. (* TODO *)
  
End Rrealize.
