Require Import Reals.
Require Import C_n_def C_n.
Require Import Functions.
Require Import Vec_def Vec_prop.
Require Import VecDep_def.
Require Import Program.
Require Import Destruct.
Require Import Max.

Inductive side_equa (n : nat) : Set :=
    | const : R -> side_equa n
    | y : forall (p : nat) (k : nat) (pltn : p < n), side_equa n
    | opp : forall (s1 : side_equa n), side_equa n
    | plus : forall (s1 s2 : side_equa n), side_equa n
    | mult : forall (s1 s2 : side_equa n), side_equa n.

Implicit Arguments y [n].
Implicit Arguments opp [n].
Implicit Arguments plus [n].
Implicit Arguments mult [n].

Definition minus {n : nat} (s1 s2 : side_equa n) := plus s1 (opp s2).

Definition diff_equa (n : nat) : Set := prod (side_equa n) (side_equa n).

Fixpoint max_y_se {n} (s : side_equa n) (m : nat) : nat :=
match s with
  | const _    => O
  | y p k _    => let b := eq_nat_dec m p in if b then k else O
  | opp s      => max_y_se s m
  | plus s1 s2 => max (max_y_se s1 m) (max_y_se s2 m)
  | mult s1 s2 => max (max_y_se s1 m) (max_y_se s2 m)
end.

Definition max_y {n} (e : diff_equa n) m : nat :=
  let (s1 , s2) := e in max (max_y_se s1 m) (max_y_se s2 m).

Definition Con_se {n : nat} (s : side_equa n) : Vec Type n :=
  genVec_P n (fun m mltn => Cn (max_y_se s m)).

Lemma Con_se_simpl : forall (n : nat) (s : side_equa n) (m : nat) (mltn : m < n),
  Vget (Con_se s) m mltn = Cn (max_y_se s m).
Proof.
intros ; apply genVec_P_get ; unfold PI_fun ; auto.
Qed.

Lemma Con_se_opp : forall (n : nat) (s : side_equa n), Con_se (opp s) = Con_se s.
Proof.
intros n s ; apply Vec_ext_eq ; intros p pltn ;
 do 2 rewrite Con_se_simpl ; reflexivity.
Qed.

Definition Con_se_plus1 {n : nat} (s1 s2 : side_equa n) :
 forall (rho : VecDep (Con_se (plus s1 s2))), VecDep (Con_se s1).
assert (Cn_pr : forall k1 k2, Cn (max k1 k2) -> Cn k1).
 intros k1 k2 [f Cf] ; exists f ; eapply C_le ;
 [eapply le_max_l | eassumption].
assert (F : forall (m : nat) (mltn : m < n),
     Vget (Con_se (plus s1 s2)) m mltn -> Vget (Con_se s1) m mltn).
 clear -Cn_pr ; intros m mltn ; do 2 rewrite Con_se_simpl ; intro H ;
 simpl in * ; eapply Cn_pr ; eassumption.
intro H ;
 assert (T := @VDmap_full n (Con_se (plus s1 s2))
 (fun m mltn _ => Vget (Con_se s1) m mltn) F H).
replace (Con_se s1) with (Vmap_full
         (fun (m : nat) (mltn : m < n) (_ : Type) => Vget (Con_se s1) m mltn)
         (Con_se (plus s1 s2))).
 exact T.
 apply Vec_ext_eq ; intros p pltn.
 rewrite Vmap_full_sound ; reflexivity.
Defined.

Definition Con_se_plus2 {n : nat} (s1 s2 : side_equa n) :
 forall (rho : VecDep (Con_se (plus s1 s2))), VecDep (Con_se s2).
assert (Cn_pr : forall k1 k2, Cn (max k1 k2) -> Cn k2).
 intros k1 k2 [f Cf] ; exists f ; eapply C_le ;
 [eapply le_max_r | eassumption].
assert (F : forall (m : nat) (mltn : m < n),
     Vget (Con_se (plus s1 s2)) m mltn -> Vget (Con_se s2) m mltn).
 clear -Cn_pr ; intros m mltn ; do 2 rewrite Con_se_simpl ; intro H ;
 simpl in * ; eapply Cn_pr ; eassumption.
intro H ;
 assert (T := @VDmap_full n (Con_se (plus s1 s2))
 (fun m mltn _ => Vget (Con_se s2) m mltn) F H).
replace (Con_se s2) with (Vmap_full
         (fun (m : nat) (mltn : m < n) (_ : Type) => Vget (Con_se s2) m mltn)
         (Con_se (plus s1 s2))).
 exact T.
 apply Vec_ext_eq ; intros p pltn.
 rewrite Vmap_full_sound ; reflexivity.
Defined.

Definition Con_se_mult1 {n : nat} (s1 s2 : side_equa n) :
 forall (rho : VecDep (Con_se (mult s1 s2))), VecDep (Con_se s1).
assert (Cn_pr : forall k1 k2, Cn (max k1 k2) -> Cn k1).
 intros k1 k2 [f Cf] ; exists f ; eapply C_le ;
 [eapply le_max_l | eassumption].
assert (F : forall (m : nat) (mltn : m < n),
     Vget (Con_se (mult s1 s2)) m mltn -> Vget (Con_se s1) m mltn).
 clear -Cn_pr ; intros m mltn ; do 2 rewrite Con_se_simpl ; intro H ;
 simpl in * ; eapply Cn_pr ; eassumption.
intro H ;
 assert (T := @VDmap_full n (Con_se (mult s1 s2))
 (fun m mltn _ => Vget (Con_se s1) m mltn) F H).
replace (Con_se s1) with (Vmap_full
         (fun (m : nat) (mltn : m < n) (_ : Type) => Vget (Con_se s1) m mltn)
         (Con_se (mult s1 s2))).
 exact T.
 apply Vec_ext_eq ; intros p pltn.
 rewrite Vmap_full_sound ; reflexivity.
Defined.

Definition Con_se_mult2 {n : nat} (s1 s2 : side_equa n) :
 forall (rho : VecDep (Con_se (mult s1 s2))), VecDep (Con_se s2).
assert (Cn_pr : forall k1 k2, Cn (max k1 k2) -> Cn k2).
 intros k1 k2 [f Cf] ; exists f ; eapply C_le ;
 [eapply le_max_r | eassumption].
assert (F : forall (m : nat) (mltn : m < n),
     Vget (Con_se (mult s1 s2)) m mltn -> Vget (Con_se s2) m mltn).
 clear -Cn_pr ; intros m mltn ; do 2 rewrite Con_se_simpl ; intro H ;
 simpl in * ; eapply Cn_pr ; eassumption.
intro H ;
 assert (T := @VDmap_full n (Con_se (mult s1 s2))
 (fun m mltn _ => Vget (Con_se s2) m mltn) F H).
replace (Con_se s2) with (Vmap_full
         (fun (m : nat) (mltn : m < n) (_ : Type) => Vget (Con_se s2) m mltn)
         (Con_se (mult s1 s2))).
 exact T.
 apply Vec_ext_eq ; intros p pltn.
 rewrite Vmap_full_sound ; reflexivity.
Defined.

Definition Con {n : nat} (e : diff_equa n) : Vec Type n :=
  genVec_P n (fun m mltn => Cn (max_y e m)).

Lemma Con_simpl : forall (n : nat) (e : diff_equa n) (m : nat) (mltn : m < n),
  Vget (Con e) m mltn = Cn (max_y e m).
Proof.
intros ; apply genVec_P_get ; unfold PI_fun ; auto.
Qed.

Definition Con_l {n : nat} (s1 s2 : side_equa n) :
 forall (rho : VecDep (Con (s1 , s2))), VecDep (Con_se s1).
assert (Cn_pr : forall k1 k2, Cn (max k1 k2) -> Cn k1).
 intros k1 k2 [f Cf] ; exists f ; eapply C_le ;
 [eapply le_max_l | eassumption].
assert (F : forall (m : nat) (mltn : m < n),
     Vget (Con (s1, s2)) m mltn -> Vget (Con_se s1) m mltn).
 clear -Cn_pr ; intros m mltn ; rewrite Con_simpl,
  Con_se_simpl ; intro H ; simpl in * ; eapply Cn_pr ;
 eassumption.
intro H ;
 assert (T := @VDmap_full n (Con (s1 , s2))
 (fun m mltn _ => Vget (Con_se s1) m mltn) F H).
replace (Con_se s1) with (Vmap_full
         (fun (m : nat) (mltn : m < n) (_ : Type) => Vget (Con_se s1) m mltn)
         (Con (s1 , s2))).
 exact T.
 apply Vec_ext_eq ; intros p pltn.
 rewrite Vmap_full_sound ; reflexivity.
Defined.

Definition Con_r {n : nat} (s1 s2 : side_equa n) :
 forall (rho : VecDep (Con (s1 , s2))), VecDep (Con_se s2).
assert (Cn_pr : forall k1 k2, Cn (max k1 k2) -> Cn k2).
 intros k1 k2 [f Cf] ; exists f ; eapply C_le ;
 [eapply le_max_r | eassumption].
assert (F : forall (m : nat) (mltn : m < n),
     Vget (Con (s1, s2)) m mltn -> Vget (Con_se s2) m mltn).
 clear -Cn_pr ; intros m mltn ; rewrite Con_simpl,
  Con_se_simpl ; intro H ; simpl in * ; eapply Cn_pr ;
 eassumption.
intro H ;
 assert (T := @VDmap_full n (Con (s1 , s2))
 (fun m mltn _ => Vget (Con_se s2) m mltn) F H).
replace (Con_se s2) with (Vmap_full
         (fun (m : nat) (mltn : m < n) (_ : Type) => Vget (Con_se s2) m mltn)
         (Con (s1 , s2))).
 exact T.
 apply Vec_ext_eq ; intros p pltn.
 rewrite Vmap_full_sound ; reflexivity.
Defined.

Fixpoint interp_equa {n : nat} (s : side_equa n) (rho : VecDep (Con_se s)) : R -> R.
destruct s.
 exact (fun _ => r).
 pose (VDget rho p pltn) as F ; rewrite Con_se_simpl in F ;
  destruct F as [f Cnf].
   simpl in Cnf ; destruct (eq_nat_dec p p) as [| Hf] ; [| apply False_rec ;
   clear -Hf ; auto].
   eapply nth_derive ; eassumption.
 apply opp_fct ; eapply interp_equa ; rewrite <- Con_se_opp ; eassumption.
 apply plus_fct ; eapply interp_equa ; [eapply Con_se_plus1 |
 eapply Con_se_plus2] ; eassumption.
 apply mult_fct ; eapply interp_equa ; [eapply Con_se_mult1 |
 eapply Con_se_mult2] ; eassumption.
Defined.

Fixpoint interp {n : nat} (e : diff_equa n) (rho : VecDep (Con e)) : Prop :=
(match e as e0 return VecDep (Con e0) -> Prop with
  | (s1 , s2) => fun rho => forall x,
   (interp_equa s1 (Con_l _ _ rho)) x = (interp_equa s2 (Con_r _ _ rho)) x
end) rho.

Delimit Scope de_scope with de.

Notation "`c k" := (const k) (at level 40) : de_scope.
Notation "- y" := (opp y) : de_scope.
Infix "+" := plus : de_scope.
Infix "-" := minus : de_scope.
Infix "*" := mult : de_scope.
Infix "=" := eq : de_scope.

Notation "[| e |]" := (interp e%de) (at level 69).