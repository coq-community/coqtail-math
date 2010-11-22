Require Import Monad.
Require Import Examples.

(* Examples *)

Definition EM := forall (P : Prop), P \/ ~ P.

(** One representation of [-1,1] **)

Inductive SB : Type := NO | Z | PO.
Definition RR := nat -> SB.

Section partial_function.
  Parameter A B : Type.
  Parameter x : A.
  Parameter y : B.
  Parameter AC : choice.
  
  Lemma toto : [ {f : A -> B | forall z, z <> x -> f z = y} ].
  Proof.
   destruct (AC A (fun z => {r | r = y})) as [f].
    intro; constructor; eauto.
    
    constructor.
    pose (g := fun z => proj1_sig (f z)).
    exists g; intros z _.
    unfold g; destruct (f z); auto.
  Qed.
  
  Lemma toto' : [ {f : A -> B | forall z, z <> x -> f z = y} ].
  Proof.
   destruct (AC A (fun z => {r | r = y})) as [f].
    intro.
    constructor.
    eauto.
    
    constructor.
    pose (g := fun z => proj1_sig (f z)).
    exists g.
    intros z Hz.
    unfold g.
    destruct (f z).
    auto.
  Qed.
End partial_function.


(** Speaking of a function which decide whether f n = P0 for all n or not **)
(* This is not very nice *)
Definition eq_one_dec : choice -> EM ->
  [ { DEC : RR -> bool |
       forall f,
         ((forall n : nat, f n = PO) -> DEC f = true) /\
         ((exists n : nat, f n <> PO) -> DEC f = false) } ].
Proof.
intros Ch Em.
destruct (AC RR
  (fun f => {b |
    ((forall n : nat, f n = PO) -> b = true) /\
    ((exists n : nat, f n <> PO) -> b = false)})) as [D].
 intros u.
 destruct (Em (exists n : nat, u n <> PO)) as [Ex | Not].
  constructor.
  exists false; split; [ | reflexivity]; intros Hf.
  destruct Ex as (n, Hn).
  apply False_ind; intuition.
    
  constructor.
  exists true; intuition.
 
 constructor.
 pose (DD := (fun x => proj1_sig (D x))).
 exists DD.
 unfold DD.
 intros f.
 destruct (D f) as [b [Hb1 Hb2]].
 split; intros Hf; simpl; intuition.
Qed.
