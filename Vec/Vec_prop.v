Require Import Vec_def.
Require Import Omega.
Require Import Destruct.

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

Lemma Vec_ext_eq : forall (A : Type) (n : nat) (v1 v2 : Vec A n)
  (Hext : forall (p : nat) (pr : p < n), Vget v1 p pr = Vget v2 p pr),
  v1 = v2.
Admitted.
(* TODO : prove that extensional equality on Vec implies equality *)

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

Lemma genVec2_get : forall (n p : nat) (pr : p < n), Vget (genVec2 n) p pr = p.
Proof.
intros n p pr ; unfold genVec2.
 rewrite Vmap_sound ; apply genVec_pr_get.
Qed.

Lemma genVec_genVec_pr : forall (n : nat), genVec n = genVec2 n.
Proof.
intros ; apply Vec_ext_eq ; intros ;
 rewrite genVec_get, genVec2_get ; reflexivity.
Qed.