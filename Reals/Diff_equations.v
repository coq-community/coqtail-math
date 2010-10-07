Require Import Reals.
Require Import C_n.

Inductive Fin : nat -> Set :=
    | zero : Fin 1
    | Fs : forall (n : nat), Fin n -> Fin (S n).

Inductive diff_equa (n : nat) : Set :=
    | const : R -> diff_equa n
    | y : forall (p : Fin n) (k : nat), diff_equa n
    | plus : diff_equa n -> diff_equa n -> diff_equa n
    | mult : diff_equa n -> diff_equa n -> diff_equa n.

