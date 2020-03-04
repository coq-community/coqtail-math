(* destruct_eq yields an equality between H and the values that
it can have. Analogous to case_eq *)

Ltac destruct_eq H := let b := fresh "b" in remember H as b ; destruct b.

Ltac copy H := let b := fresh H in assert (b := H).

(* use n Thm Hyp consumes the hypothesis Hyp to produce a thm based
on Thm *)
Ltac use n Thm Hyp := let H := fresh "H" in match n with
  | 0 => assert (H := Thm Hyp)
  | 1 => assert (H := Thm _ Hyp)
  | 2 => assert (H := Thm _ _ Hyp)
end ; clear Hyp.

Ltac specify Hyp Term := let T := fresh "H" in
  assert (T := Hyp Term) ; clear Hyp ;
  rename T into Hyp.

Ltac specify2 Hyp T1 T2 := let T := fresh "H" in
  assert (T := Hyp T1 T2) ; clear Hyp ;
  rename T into Hyp.

Ltac specify3 Hyp T1 T2 T3 := let T := fresh "H" in
  assert (T := Hyp T1 T2 T3) ; clear Hyp ;
  rename T into Hyp.

Ltac specify4 Hyp T1 T2 T3 T4 := let T := fresh "H" in
  assert (T := Hyp T1 T2 T3 T4) ; clear Hyp ;
  rename T into Hyp.

Ltac specify5 Hyp T1 T2 T3 T4 T5 := let T := fresh "H" in
  assert (T := Hyp T1 T2 T3 T4 T5) ; clear Hyp ;
  rename T into Hyp.

Ltac ass_apply := match goal with
 | H: _ |- _ => eapply H
end.
