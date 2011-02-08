Require Import Lt.
Require Import Vec_def.

Inductive VecDep : forall (n : nat), Vec Type n -> Type :=
  | VDnil : VecDep 0 (Vnil Type)
  | VDcon : forall {A : Type} {n : nat} {v : Vec Type n} (hd : A) (tl : VecDep n v),
            VecDep (S n) (Vcon _ A v).

Fixpoint VDget {n : nat} {v : Vec Type n} (vd : VecDep n v)
         (m : nat) (mltn : m < n) : Vget v m mltn.
Proof.
destruct vd.
 apply False_rect ; eapply lt_n_O ; eassumption.
 destruct m.
  exact hd.
  simpl ; apply VDget ; apply vd.
Defined.
