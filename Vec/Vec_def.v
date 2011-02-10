Require Import Le Lt.

Inductive Vec (A : Type) : nat -> Type :=
  | Vnil : Vec A 0
  | Vcon : forall {n : nat} (hd : A) (tl : Vec A n), Vec A (S n).

Implicit Arguments Vnil [A].
Implicit Arguments Vcon [A n].

Fixpoint Vconcat {A : Type} {m n : nat} (v1 : Vec A m) (v2 : Vec A n) : Vec A (m + n) :=
match v1 in Vec _ m return Vec A (m + n) with
  | Vnil         => v2
  | Vcon _ hd tl => Vcon hd (Vconcat tl v2)
end.

Fixpoint Vupdate {A : Type} {n : nat} (v : Vec A n) (m : nat) (mltn : m < n) (a : A)
 {struct v} : Vec A n.
destruct v.
 constructor.
 destruct m.
  constructor ; [exact a | exact v].
  constructor.
   exact hd.
   eapply (Vupdate _ _ v m (lt_S_n _ _ mltn) a).
Defined.

Fixpoint Vget {A : Type} {n : nat} (v : Vec A n) (m : nat) (mltn : m < n) : A.
destruct v.
 apply False_rect ; eapply lt_n_O ; eassumption.
 destruct m.
  exact hd.
  eapply Vget ; [| eapply lt_S_n ] ; eassumption.
Defined.

Fixpoint Vmap {A B : Type} {n : nat} (f : A -> B) (v : Vec A n) : Vec B n :=
match v in (Vec _ n0) return (Vec B n0) with
  | Vnil         => Vnil
  | Vcon _ hd tl => Vcon (f hd) (Vmap f tl)
end.


Fixpoint Vmap_full {A : Type} {n : nat} (f : forall (m : nat) (mltn : m < n), A -> Type)
  (v : Vec A n): Vec Type n.
destruct v.
 constructor.
 constructor.
  exact (f O (lt_0_Sn _) hd).
  eapply Vmap_full.
  eexact (fun  m mltn => f (S m) (lt_n_S _ _ mltn)).
  assumption.
Defined.

Fixpoint genVec_pr (n : nat) : Vec {p |  p < n} n :=
match n as n0 return Vec {p | p < n0} n0 with
  | O    => Vnil
  | S n' => Vcon (exist _ O (lt_O_Sn _))
            (Vmap (fun P => let (p , pr) := (P : sig (fun p => p < n')) in
            exist _ (S p) (lt_n_S p n' pr)) (genVec_pr n'))
end.

Fixpoint genVec (n : nat) : Vec nat n := match n as n0 return Vec nat n0 with
  | O    => Vnil
  | S n' => Vcon O (Vmap S (genVec n'))
end.

Definition genVec_P {A : Type} (n : nat) (P : forall m, m < n -> A) : Vec A n :=
  Vmap (fun (H : sig (fun p => p < n)) => let (p , pr) := H in P p pr) (genVec_pr n).

(*
Definition genVec2 (n : nat) : Vec nat n := genVec_P n (fun m _ => m).
*)