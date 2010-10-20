Notation " [ a ] " := (inhabited a).

Definition join : forall (A : Type), [[A]] -> [A]
  := fun A m => match m with inhabits m => m end.

Definition map : forall (A B : Type), (A -> B) -> [A] -> [B]
  := fun A B f m => match m with inhabits x => inhabits (f x) end.

Definition lift : forall (A : Type), A -> [A]
  := inhabits.

Definition choice := forall A (B : A -> Type),
  (forall x, [ B x ]) -> [ forall x, B x ].

Lemma map_composition : forall A B C (f : B -> C) (g : A -> B) (m : [A]),
  map A C (fun y => f (g y)) m = map B C f (map A B g m).
Proof.
intros A B C f g m.
refine (match m with inhabits x => _ end).
reflexivity.
Qed.

Lemma map_id : forall A (m : [A]),
  map A A (fun y => y) m = m.
Proof.
intros A m.
refine (match m with inhabits x => _ end).
reflexivity.
Qed.

Lemma map_lift : forall A B (f : A -> B) (x : A),
  map A B f (lift A x) = lift B (f x).
Proof.
auto.
Qed.

Lemma join_map_join : forall A (m : [[[A]]]),
  join A (map [[A]] [A] (join A) m) = join A (join [A] m).
Proof.
intros A m.
refine (match m with inhabits x => _ end).
reflexivity.
Qed.

Lemma join_map_lift : forall A (m : [A]),
  join A (map A [A] (lift A) m) = m.
Proof.
intros A m.
refine (match m with inhabits x => _ end).
reflexivity.
Qed.

Lemma join_lift : forall A (m : [A]),
  join A (lift [A] m) = m.
Proof.
auto.
Qed.

Lemma join_map_map : forall A B (f : A -> B) (m : [[A]]),
  join B (map [A] [B] (map A B f) m) = map A B f (join A m).
Proof.
intros A B f mm.
refine (match mm with inhabits x => _ end).
reflexivity.
Qed.