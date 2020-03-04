Require Import Lt.
Require Import Vec_def Vec_prop.

Inductive VecDep : forall (n : nat), Vec Type n -> Type :=
  | VDnil : VecDep 0 Vnil
  | VDcon : forall {A : Type} {n : nat} {v : Vec Type n} (hd : A) (tl : VecDep n v),
            VecDep (S n) (Vcon A v).

Arguments VecDep [n] _.
Arguments VDcon [A n v] hd tl.

Fixpoint VDget {n : nat} {v : Vec Type n} (vd : VecDep v)
         (m : nat) (mltn : m < n) : Vget v m mltn.
Proof.
destruct vd.
 apply False_rect ; eapply lt_n_O ; eassumption.
 destruct m.
  exact hd.
  simpl ; apply VDget ; apply vd.
Defined.

Fixpoint VDupdate {n : nat} {v : Vec Type n} {A : Type} (vd : VecDep v) (m : nat)
  (mltn : m < n) (a : A) {struct vd} : VecDep (Vupdate v m mltn A).
destruct vd.
 constructor.
 destruct m.
  constructor ; [exact a | exact vd].
  constructor ; [exact hd |].
  apply VDupdate ; [exact vd | exact a].
Defined.

Fixpoint VDmap {n : nat} {v : Vec Type n} (f : Type -> Type)
 (fd : forall m mltn, Vget v m mltn -> f (Vget v m mltn))
 (vd : VecDep v) : VecDep (Vmap f v).
Proof.
destruct vd.
 constructor.
 constructor.
  change (f (Vget (Vcon A v) O (lt_O_Sn _))) ; apply fd ;
  assumption.
  apply VDmap ; [| apply vd].
  intros m mltn H.
  erewrite Vget_PI ; eapply (fd (S m) (lt_n_S _ _ mltn)) ; simpl.
  erewrite Vget_PI ; eassumption.
Defined.

Fixpoint VDmap_full {n : nat} {v : Vec Type n}
  (f : forall (m : nat) (mltn : m < n), Type -> Type)
  (fd : forall m mltn, Vget v m mltn -> f m mltn (Vget v m mltn))
  (vd : VecDep v) : VecDep (Vmap_full f v).
Proof.
destruct vd.
 constructor.
 constructor.
  apply fd ; simpl ; exact hd.
  apply VDmap_full ; [| apply vd].
  intros m mltn Hget.
  erewrite Vget_PI ; eapply (fd (S m) (lt_n_S _ _ mltn)) ;
  simpl ; erewrite Vget_PI ; eassumption.
Defined.
