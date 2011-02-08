Require Import Le Lt.

Inductive Vec (A : Type) : nat -> Type :=
  | Vnil : Vec A 0
  | Vcon : forall {n : nat} (hd : A) (tl : Vec A n), Vec A (S n).

Fixpoint Vmap {A B : Type} {n : nat} (f : A -> B) (v : Vec A n) : Vec B n :=
match v in (Vec _ n0) return (Vec B n0) with
  | Vnil         => Vnil B
  | Vcon _ hd tl => Vcon B (f hd) (Vmap f tl)
end.

Fixpoint Vconcat {A : Type} {m n : nat} (v1 : Vec A m) (v2 : Vec A n) : Vec A (m + n) :=
match v1 in Vec _ m return Vec A (m + n) with
  | Vnil         => v2
  | Vcon _ hd tl => Vcon A hd (Vconcat tl v2)
end.

Fixpoint Vget {A : Type} {n : nat} (v : Vec A n) (m : nat) (mltn : m < n) : A.
destruct v.
 apply False_rect ; eapply lt_n_O ; eassumption.
 destruct m.
  exact hd.
  eapply Vget ; [| eapply lt_S_n ] ; eassumption.
Defined.

Fixpoint genVec_pr (n : nat) : Vec {p |  p <= n} n :=
match n as n0 return Vec {p | p <= n0} n0 with
  | O    => Vnil _
  | S n' => Vcon _ (exist _ O (le_O_n _))
            (Vmap (fun P => let (p , pr) := (P : sig (fun p => p <= n')) in
            exist _ (S p) (le_n_S p n' pr)) (genVec_pr n'))
end.

Fixpoint genVec (n : nat) : Vec nat n := match n as n0 return Vec nat n0 with
  | O    => Vnil nat
  | S n' => Vcon _ O (Vmap S (genVec n'))
end.

Definition genVec2 (n : nat) : Vec nat n :=
  Vmap (fun (P : sig (fun p => p <= n)) => let (p , _) := P in p) (genVec_pr n).