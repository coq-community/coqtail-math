Ltac destruct_eq H := let b := fresh "b" in remember H as b ; destruct b.

Ltac copy H := let b := fresh H in assert (b := H).
