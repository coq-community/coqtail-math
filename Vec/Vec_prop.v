Require Import Vec_def.
Require Import Omega.
Require Import Destruct.
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

Lemma Vmap_full_sound : forall (A : Type) (n : nat)
  (f : forall (m : nat) (mltn : m < n), A -> Type)
  (v : Vec A n) (p : nat) (pltn : p < n),
  Vget (Vmap_full f v) p pltn = f p pltn (Vget v p pltn).
Proof.
intros A n f v ; induction v ; intros p pltn.
 inversion pltn.
 destruct p ; simpl ; [| rewrite IHv ] ;
 f_equal ; apply lt_PI.
Qed.

Definition Vec_ext {A n} (v1 v2 : Vec A n) := forall (p : nat) (pr : p < n), Vget v1 p pr = Vget v2 p pr.

Lemma Vec_ext_eq : forall (A : Type) (n : nat) (v1 v2 : Vec A n)
  (Hext : forall (p : nat) (pr : p < n), Vget v1 p pr = Vget v2 p pr),
  v1 = v2.
Proof.
refine (fix F A n (v1 : Vec A n) {struct v1} :=
match v1 in Vec _ n return forall v2 : Vec A n, Vec_ext v1 v2 -> v1 = v2 with
| Vnil =>
  fun v2 => match v2 in Vec _ n return
    match n return Vec A n -> Type with
    | 0 => fun v2 => Vec_ext Vnil v2 -> Vnil = v2
    | S _ => fun _ => True
    end v2
  with
  | Vnil => fun _ => eq_refl _
  | _ => I
  end
| Vcon n x v1 => _
end
).

refine (
  (fun v2 => match v2 in Vec _ n return
    match n return Vec A n -> Type with
    | 0 => fun _ => True
    | S n => fun v2 => forall v0 : Vec A n, _ -> _ -> (Vcon x v0) = v2
    end v2
  with
  | Vnil => I
  | Vcon n y v2 => _
  end v0 (F _ _ v0))
).
intros; clear F; f_equal.
change (Vget (Vcon x v4) 0 (lt_0_Sn _) = Vget (Vcon y v3) 0 (lt_0_Sn _)); intuition.
apply H; intros p Hp.
assert (Hlt : S p < S n1) by auto with arith.
replace (Vget v4 p Hp) with (Vget (Vcon x v4) (S p) Hlt) by (simpl; apply Vget_PI).
replace (Vget v3 p Hp) with (Vget (Vcon y v3) (S p) Hlt) by (simpl; apply Vget_PI).
intuition.
Qed.

Lemma genVec_get : forall (n p : nat) (pr : p < n), Vget (genVec n) p pr = p.
Proof.
intro n ; induction n ; intros p pr.
 inversion pr.
 destruct p ; [| simpl ; rewrite Vmap_sound, IHn] ; reflexivity.
Qed.

Lemma genVec_pr_get : forall (n p : nat) (pr : p < n), proj1_sig (Vget (genVec_pr n) p pr) = p.
Proof.
intro n ; induction n ; intros p pr.
 inversion pr.
 destruct p.
  simpl ; reflexivity.
  simpl ; rewrite Vmap_sound.
  assert (H := IHn p (lt_S_n _ _ pr)).
   destruct (Vget (genVec_pr n) p (lt_S_n p n pr)) as [k Hk] ;
   simpl in * ; auto.
Qed.

Definition PI_fun {n} (P : forall (m : nat), m < n -> Type) :=
  forall (m : nat) (pr1 pr2 : m < n), P m pr1 = P m pr2.

Lemma genVec_P_get : forall (n : nat) (P : forall (m : nat), m < n -> Type)
 (m : nat) (mltn : m < n), PI_fun P -> Vget (genVec_P n P) m mltn = P m mltn.
Proof.
intros n P m mltn HP ; unfold genVec_P ;
 rewrite Vmap_sound ; assert (Heq := genVec_pr_get n m mltn) ;
 destruct (Vget (genVec_pr n) m mltn) ; simpl in Heq ; subst ;
 apply HP.
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