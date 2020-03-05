Definition Return {A : Type} : A -> option A := @Some A.

Definition Bind {A B : Type} : option A -> (A -> option B) -> option B :=
fun Oa f => match Oa with
  | None   => None
  | Some a => f a
end.

Definition Map {A B : Type} (f : A -> B) : option A -> option B :=
fun Oa => match Oa with
  | None   => None
  | Some a => Some (f a)
end.

Definition Join {A : Type} : option (option A) -> option A :=
fun OOa => match OOa with
  | None          => None
  | Some None     => None
  | Some (Some a) => Some a
end.

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

Definition Map_is_Bind : Map h Oa = Bind Oa (fun x => Return (h x)).
Proof.
reflexivity.
Qed.

Definition Join_is_Bind : Join OOa = Bind OOa (fun x => x).
Proof.
destruct OOa as [Ob |] ; [destruct Ob |] ; reflexivity.
Qed.

End Monad_properties.



