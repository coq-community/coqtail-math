Require Import ZArith Lia MyNat Div2.

(** Finite and computable subsets of [nat], by functions in [nat -> bool] *)


(** Tactics *)

Ltac rem t x Hx :=
  pose (x := t); assert (Hx : x = t) by reflexivity;
    try rewrite <- Hx in *; clearbody x.

Ltac destruct_if t :=
  lazymatch t with
  | if ?t then _ else _ =>
      let Eqb := fresh "Eqb" in
      let b := fresh "b" in
      rem t b Eqb; destruct b
  | ?u ?v => destruct_if u || destruct_if v
  end.

Ltac auto_if :=
  match goal with
  | |- ?T => destruct_if T
  | H : ?T |- _ => destruct_if T
  end.

Ltac impossible := exfalso; discriminate || lia || tauto.

Ltac dumb_aux :=
  auto || auto with * || discriminate
  || intuition || tauto || lia.

Ltac dumb :=
  try solve
    [ impossible
    | subst; dumb_aux || (simpl in *; dumb_aux)
    | intros; dumb_aux || (simpl in *; dumb_aux) ].


(** * Basic operations and types *)

Definition bset := nat -> bool.

Definition singleton (x : nat) : bset :=
  fun y => if eq_nat_dec x y then true else false.

Definition inter (P Q : bset) : bset := fun i => andb (P i) (Q i).

Definition union (P Q : bset) : bset := fun i => orb (P i) (Q i).


(** Bounded cardinal *)

Definition IBN : bool -> nat := fun b => (if b then 1 else 0)%nat.

Fixpoint count n P :=
  match n with
  | O => O
  | S n => (IBN (P n) + count n P)%nat
  end.


(** Comparison *)

Definition same (P Q : bset) : Prop := forall i, P i = Q i.

Fixpoint same_bool n P Q :=
  match n with
  | O => true
  | S n => if Bool.eqb (P n) (Q n) then same_bool n P Q else false
  end.

(* TODO les typesclasses peuvent nous aider ? *)

Lemma same_true n P Q : same_bool n P Q = true -> forall i, i < n -> P i = Q i.
Proof.
  induction n; intros E i L.
    impossible.
    
    simpl in E.
    auto_if; dumb.
    destruct (eq_nat_dec i n); dumb.
    apply Bool.eqb_true_iff.
    subst; dumb.
Qed.

Lemma same_false n P Q : same_bool n P Q = false -> { i | i < n /\ P i <> Q i }.
Proof.
  induction n; simpl; intros I.
    impossible.
    
    remember (Bool.eqb (P n) (Q n)) as b.
    destruct b.
      destruct IHn as (i, (Li, Di)); eauto.
      destruct (Bool.eqb_false_iff (P n) (Q n)); eauto.
Qed.



(* This lemma is a corollary of the next one that is more elegant. TODO *)

Lemma count_union_inter n P Q : (count n (union P Q) + count n (inter P Q) =
  count n P + count n Q)%nat.
Proof.
  induction n; auto; simpl.
  unfold IBN, union, inter in *.
  remember (P n) as Pn; remember (Q n) as Qn.
  destruct Pn; destruct Qn; simpl; lia.
Qed.

Lemma not_empty P n : O < count n P -> { i | i < n /\ P i = true }.
Proof.
  intros CP.
  induction n.
    simpl in CP; impossible.
    
    simpl in CP.
    rem (P n) Pn EPn; destruct Pn.
      exists n; auto.
      
      destruct IHn as (i, Hi); dumb.
      exists i; dumb.
Defined.

Lemma count_union n P Q : count n (union P Q) =
  count n P + count n Q - count n (inter P Q).
Proof.
  rewrite <- count_union_inter.
  auto with *.
Qed.

Lemma count_inter n P Q : count n (inter P Q) =
  count n P + count n Q - count n (union P Q).
Proof.
  rewrite <- count_union_inter.
  auto with *.
Qed.

Lemma count_bound P n : count n P <= n.
Proof.
  induction n.
    dumb.
    simpl; destruct (P n); dumb.
Qed.

Lemma count_drawers : forall P Q n,
  n < count n P + count n Q -> { i | i < n /\ P i = true /\ Q i = true }.
Proof.
  intros P Q n L.
  destruct (not_empty (inter P Q) n) as (i, Hi).
    rewrite count_inter.
    pose proof count_bound (union P Q) n.
    lia.
    
    exists i; intuition; unfold inter in *;
      destruct (P i); destruct (Q i); intuition.
Defined.


Definition injective domain (f : nat -> nat) := forall i j,
  i < domain -> j < domain -> f i = f j -> i = j.

Definition bounded domain bound (f : nat -> nat) := forall i, i < domain -> f i < bound.

Fixpoint has_antecedent (f : nat -> nat) domain y :=
  match domain with
  | O => false
  | S domain => if eq_nat_dec (f domain) y then true else has_antecedent f domain y
  end.

(* TODO delete def ? *)
Fixpoint number_of_pals_____OUT (f : nat -> nat) domain x :=
  match domain with
  | O => 0
  | S domain => (if eq_nat_dec (f domain) (f x) then 1 else 0) + number_of_pals_____OUT f domain x
  end.

(** [image f dom] is the set f({0, ..., dom-1}) *)
Definition image (f : nat -> nat) domain : bset := has_antecedent f domain.

Lemma image_true f dom y :
  image f dom y = true -> { i | i < dom /\ f i = y }.
Proof.
  induction dom; intros A; dumb.
  destruct (eq_nat_dec (f dom) y) as [E|E].
    exists dom; eauto.
    
    destruct IHdom as (i, Hi).
      simpl in A.
      auto_if; dumb.
      
      exists i; dumb.
Defined.

Lemma image_false : forall f domain y,
  image f domain y = false -> forall x, x < domain -> f x = y -> False.
Proof.
  intros f dom; induction dom; intros y T x Bx Exy.
    inversion Bx.
    
    simpl in T.
    auto_if; dumb.
      apply (IHdom y T x); dumb.
      cut (x <> dom); dumb.
Qed.

Lemma image_true_pr f dom y :
  forall i, i < dom -> y = f i -> image f dom y = true.
Proof.
  intros i L E.
  remember (image f dom y) as b; symmetry in Heqb.
  destruct b; [ reflexivity | exfalso ].
  exfalso; eapply image_false; eauto.
Qed.

Lemma image_false_pr f dom y :
  (forall i, i < dom -> y <> f i) -> image f dom y = false.
Proof.
  intros NE.
  remember (image f dom y) as b; symmetry in Heqb.
  destruct b; [ exfalso | reflexivity ].
  destruct (image_true _ _ _ Heqb) as (n, Hn).
  specialize (NE n); intuition.
Qed.

Fixpoint sum n f := match n with O => O | S n => f n + sum n f end.

Definition is_duplicate f n := IBN (has_antecedent f n (f n)).

Definition is_duplicate_outside f bound n :=
  if lt_dec bound (f n) then IBN (has_antecedent f n (f n)) else O.

(** TODO unifier l'ordre des variables bound/domain *)

Fixpoint count_outside domain bound f :=
  match domain with
  | O => O
  | S domain => (if lt_dec (f domain) bound then 1 else 0) + count_outside domain bound f
  end.

(*
Lemma count_image : forall domain bound f,
  count bound (image f domain)
  + sum domain (is_duplicate f)
  = domain
  + sum domain (is_duplicate_outside f bound).
Proof.
  intros.
  replace f with div2.
  replace domain with 24%nat.
  replace bound with 5%nat.
  simpl count; simpl sum.
  idtac "utilise un dessin !".
  fail.
  simpl.
  
  
  intros domain bound f; induction domain.
    clear; induction bound; auto with *.
    
    simpl.
    rewrite (plus_comm domain), <- plus_assoc, (plus_comm _ domain).
    rewrite <- IHdomain; clear.
    induction bound.
      simpl.
      induction domain.
        simpl.
    unfold is_duplicate, is_duplicate_outside.
    destruct (lt_dec (f domain) bound) as [L|NL].
      repeat rewrite plus_assoc.
      rewrite (plus_comm _ 1).
      rewrite <- (plus_assoc 1), <- IHdomain.
        simpl.
    remember (f domain) as y0.
        
        intros i; auto.
        
      rewrite IHdomain.
    clear IHdomain.
    
   
(*
  intros domain bound f; induction bound.
    auto.
    
    simpl.
    rewrite <- IHbound.
    f_equal.
    clear.
    induction domain.
      auto.
      
      simpl.
      rewrite IHdomain.
      rewrite plus_comm.
      f_equal.
      destruct (eq_nat_dec (f bound) domain).
*)    
  intros domain bound f Bf; induction domain.
    clear; induction bound; auto.
    (***
Ça ne marche pas il faut faire une partie du membre gauche qui
compte aussi les points qui ne sont pas dans l'image (quand f pas bornée
par [bound])

On a une partie "is_duplicate" qui parle de l'injectivité

Il faut faire une partie "count outside" qui parle de la bornitude
***)
    simpl.
    simpl; rewrite IHdomain.
    clear.
    induction bound.
      auto.
      
      simpl.
      rewrite <- IHbound.
      repeat rewrite plus_assoc.
      
      f_equal.
      rewrite plus_comm.
      f_equal.
      
      destruct (eq_nat_dec (f domain) bound).
        exfalso.
        
        simpl.
        auto.
        
      destruct (eq_nat_dec (f bound) domain).
        simpl.
      simpl.
        simpl.
    f_equal.
    assert (forall a b c d, a = b ) as App; apply App; clear App.
    Require Import Arith.
    apply plus_reg.
Qed.
*)

Lemma image_injective_plus_one : forall domain f,
  same (image f (S domain)) (union (image f domain) (singleton (f domain))).
Proof.
  intros dom f i.
  unfold union, singleton.
  simpl; auto_if; auto with *.
Qed.

(* The converse is true, but osef. *)
Lemma count_same S T : same S T -> forall n, count n S = count n T.
Proof.
  intros E n; induction n; simpl; dumb.
  rewrite E; dumb.
Qed.

Lemma count_same_bounded S T n : (forall i, i < n -> S i = T i) -> count n S = count n T.
Proof.
  intros E; induction n; simpl; dumb.
  repeat (f_equal; dumb).
Qed.

Lemma count_union_singleton P a n :
  P a = false -> a < n ->
    count n (union P (singleton a)) = S (count n P).
Proof.
  intros Ma L.
  induction n; dumb.
  unfold union, singleton; simpl.
  destruct (eq_nat_dec a n).
    subst; rewrite Ma; simpl.
    f_equal; apply count_same_bounded; intros i Li.
    auto_if; dumb.
    
    rewrite plus_n_Sm, <- IHn; dumb.
    repeat f_equal; auto with *.
Qed.

Lemma count_image_injective_plus_one : forall domain f bound,
  injective (S domain) f -> bounded (S domain) bound f ->
    count bound (image f (S domain)) = S (count bound (image f domain)).
Proof.
  intros dom f M If Bf.
  pose proof image_injective_plus_one dom f as HS.
  erewrite count_same; [ | eassumption ].
  rewrite count_union_singleton; dumb.
    apply image_false_pr; intros i L E.
    apply If in E; dumb.
Qed.

Lemma injective_S dom f : injective (S dom) f -> injective dom f.
Proof.
  intros If i j Bi Bj.
  apply If; dumb.
Qed.

Lemma bounded_S dom M f : bounded (S dom) M f -> bounded dom M f.
Proof.
  intros If i Bi.
  apply If; dumb.
Qed.

Lemma count_image_injective : forall domain bound f,
  injective domain f -> bounded domain bound f ->
    count bound (image f domain) = domain.
Proof.
  intros dom M f Injf Bf.
  induction dom.
    simpl; clear.
    induction M; auto.
    
    rewrite count_image_injective_plus_one; dumb.
    rewrite IHdom; dumb.
      apply injective_S; auto.
      apply bounded_S; auto.
Qed.

(*
Fact example :
  let A := (fun x => if lt_dec x 20 then true else false) in
  let B := (fun x => if lt_dec 18 x then true else false) in
  { i | inter A B i = true }.
Proof.
  intros.
  cut { i | i < 100 /\ inter A B i = true}.
    intros (i, []); exists i; eauto.
  
  apply not_empty.
  auto.
Defined.

Eval compute in projT1 example.
*)

(*
Record natset := mknatset { natset_bound : nat; natset_charact : nat -> bool }.

Definition mknatset_dec n P (Pdec : nat_decidable P) :=
  mknatset n (nat_dec_bool P Pdec).

Program Definition image n m (f : nat -> nat) : natset :=
  mknatset_dec m (fun y => { x | y = f x /\ x < n}) _.
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
            lia.
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

*)
