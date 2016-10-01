Require Import Vec_def.
Require Import Omega.
Require Import Ass_handling.
Require Import PI.

Lemma Vget_PI : forall {A : Type} {n : nat} (v : Vec A n) (m : nat) (mltn1 mltn2 : m < n),
      Vget v m mltn1 = Vget v m mltn2.
Proof.
intros A n v ; induction v.
 intros m H ; apply False_ind ; omega.
 destruct m ; simpl ; auto.
Qed.

Lemma Vmap_sound : forall (A B : Type) (n : nat) (f : A -> B) (v : Vec A n)
  (p : nat) (pltn : p < n), Vget (Vmap f v) p pltn = f (Vget v p pltn).
Proof.
intros A B n f v ; induction v ; intros p pltn.
 inversion pltn.
 destruct p ; [reflexivity | simpl ; apply IHv].
Qed.

Lemma Vmap_full_sound : forall (A B : Type) (n : nat)
  (f : forall (m : nat) (mltn : m < n), A -> B)
  (v : Vec A n) (p : nat) (pltn : p < n),
  Vget (Vmap_full f v) p pltn = f p pltn (Vget v p pltn).
Proof.
intros A B n f v ; induction v ; intros p pltn.
 inversion pltn.
 destruct p ; simpl ; [| rewrite IHv ] ;
 f_equal ; apply lt_PI.
Qed.

Definition Vec_rect2 : forall A (P : forall n, Vec A n -> Vec A n -> Type),
  P 0 Vnil Vnil -> (forall n h1 h2 (v1 v2 : Vec A n), P n v1 v2 -> P (S n) (Vcon h1 v1) (Vcon h2 v2)) ->
  forall n v1 v2, P n v1 v2 :=
fun A P H0 HS => fix F (n : nat) {struct n} :=
match n return forall (v1 v2 : Vec A n), P n v1 v2 with
| 0 => fun v1 =>
  match v1 in Vec _ m return
    match m with
    | 0 => forall v2 : Vec A m, P m v1 v2
    | S _ => False -> False
    end
  with
  | Vnil => fun v2 =>
    match v2 in Vec _ m return
      match m return forall v2 : Vec A m, Type with
      | 0 => fun v2 => P 0 Vnil v2 
      | S _ => fun v2 => False -> False
      end v2
    with
    | Vnil => H0
    | Vcon _ _ => False_rect _
    end
  | Vcon _ _ => False_rect _
  end
| S n =>
  let F := F n in
  fun v1 => match v1 in Vec _ m return
    match m with
    | 0 => False -> False
    | S m' => (forall v1 v2, P m' v1 v2) -> forall v2 : Vec A m, P m v1 v2 
    end
  with
  | Vnil => False_rect _
  | Vcon h1 v1 => fun F v2 =>
    match v2 in Vec _ m return
      match m return forall v2 : Vec A m, Type with
      | 0 => fun v2 => False -> False
      | S m => fun v2 => forall v1 : Vec A m, (forall v2, P _ v1 v2) -> P (S m) (Vcon h1 v1) v2
      end v2
    with
    | Vnil => False_rect _
    | Vcon h2 v2 => fun v1 F => HS _ h1 h2 v1 v2 (F v2)
    end v1 (F v1)
  end F
end.

Lemma Vec_ext_eq : forall (A : Type) (n : nat) (v1 v2 : Vec A n)
  (Hext : forall (p : nat) (pr : p < n), Vget v1 p pr = Vget v2 p pr),
  v1 = v2.
Proof.
intros A n v1 v2; pattern n, v1, v2; apply Vec_rect2; clear.
+ reflexivity.
+ intros n h1 h2 v1 v2 IH H; f_equal.
  - assert (pr : 0 < S n) by auto with arith.
    now apply (H 0 pr).
  - apply IH; intros p pr.
    assert (prS : S p < S n) by auto with arith.
    specialize (H _ prS); simpl in H.
    erewrite (Vget_PI v1), (Vget_PI v2); eassumption.
Qed.

Lemma genVec_pr_get : forall (n p : nat) (pr : p < n),
  Vget (genVec_pr n) p pr = exist _ p pr.
Proof.
intros n p pr ; unfold genVec_pr ; rewrite Vmap_full_sound ;
 reflexivity.
Qed.

Definition PI_fun {A n} (P : forall (m : nat), m < n -> A) :=
  forall (m : nat) (pr1 pr2 : m < n), P m pr1 = P m pr2.

Lemma genVec_P_get : forall (A : Type) (n : nat) (P : forall (m : nat), m < n -> A)
 (m : nat) (mltn : m < n), PI_fun P -> Vget (genVec_P n P) m mltn = P m mltn.
Proof.
intros A n P m mltn HP ; unfold genVec_P ; rewrite Vmap_full_sound ;
reflexivity.
Qed.

Lemma genVec_get : forall (n p : nat) (pr : p < n), Vget (genVec n) p pr = p.
Proof.
intro n ; induction n ; intros p pr.
 inversion pr.
 destruct p ; [| simpl ; rewrite Vmap_full_sound] ; reflexivity.
Qed.

(*
Lemma genVec2_get : forall (n p : nat) (pr : p < n), Vget (genVec2 n) p pr = p.
Proof.
intros n p pr ; unfold genVec2, genVec_P ;
 rewrite Vmap_sound ; apply genVec_pr_get.
Qed.

Lemma genVec_genVec_pr : forall (n : nat), genVec n = genVec2 n.
Proof.
intros ; apply Vec_ext_eq ; intros ;
 rewrite genVec_get, genVec2_get ; reflexivity.
Qed.
*)
