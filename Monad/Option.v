Definition Return : forall (A : Type), A -> option A := Some.

Definition Bind : forall (A B : Type), option A -> (A -> option B) -> option B :=
fun A B Oa f => match Oa with
  | None   => None
  | Some a => f a
end.

Definition Map : forall (A B : Type) (f : A -> B), option A -> option B :=
fun A B f Oa => match Oa with
  | None   => None
  | Some a => Some (f a)
end.

Definition Join : forall (A : Type), option (option A) -> option A :=
fun A OOa => match OOa with
  | None          => None
  | Some None     => None
  | Some (Some a) => Some a
end.

Implicit Arguments Return [A].
Implicit Arguments Bind [A B].
Implicit Arguments Map [A B].
Implicit Arguments Join [A].

Section Monad_properties.

Variables A B C : Type.
Variable a : A.
Variable Oa : option A.
Variable OOa : option (option A).
Variable f : A -> option B.
Variable g : B -> option C.
Variable h : A -> B.

Definition Return_Bind : Bind (Return a) f = f a.
Proof.
reflexivity.
Qed.

Definition Bind_Return : Bind Oa (@Return A) = Oa.
Proof.
destruct Oa ; reflexivity.
Qed.

Definition Bind_Bind : Bind (Bind Oa f) g = Bind Oa (fun r => Bind (f r) g).
Proof.
destruct Oa ; reflexivity.
Qed.

Definition Map_is_Bind : Map h Oa = Bind Oa (fun x => Some (h x)).
Proof.
reflexivity.
Qed.

Definition Join_is_Bind : Join OOa = Bind OOa (fun x => x).
Proof.
destruct OOa as [Ob |] ; [destruct Ob |] ; reflexivity.
Qed.

End Monad_properties.



