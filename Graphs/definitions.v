Require Import List.
Require Export Bool.
Require Import Arith.


Definition vertex := nat.

Definition vertices := list vertex.

Definition edge := (vertex * vertex)%type.

Definition edges := list edge.

(*Definition path := vertex->vertex->nat->Prop.*)

Definition path_reflexive (p : vertex->vertex->nat->Prop) : Prop :=
forall v : vertex, p v v 0.

Definition path_unique (p  : vertex->vertex->nat->Prop) : Prop :=
forall v v0 : vertex, (p v v0 0)->(v=v0).

Definition path_trans (p : vertex->vertex->nat->Prop) : Prop :=
forall v1 v2 v3 n m, (p v1 v2 n)->(p v2 v3 m)->(p v1 v3 (n+m)).

Definition path_back (p : vertex -> vertex -> nat -> Prop) : Prop :=
forall v1 v2 n, (p v1 v2 (S n))->(exists v3, (p v1 v3 1)/\(p v3 v2 n)).

Definition path_dec (p : vertex->vertex->nat->Prop) : Prop :=
forall v1 v2 n, (p v1 v2 n)\/(not (p v1 v2 n)).

(*Definition path_dec (p : vertex->vertex->nat->Prop) : Type :=
forall v1 v2 n, {p v1 v2 n}+{not (p v1 v2 n)}.*)

Definition path := { p : vertex->vertex->nat->Prop | path_reflexive p /\ path_trans p /\ path_unique p /\ path_back p /\ path_dec p}.

Definition Graph := (vertices * path)%type.

Set Implicit Arguments.

(*et dans la librairie standard ?*)
Inductive belong (a : Type) : a->(list a)->Prop :=
| belong_y : forall v e, belong v (cons v e)
| belong_n : forall v1 v2 e, (belong v1 e)->(belong v1 (cons v2 e)).


Lemma vertex_dec : forall x y : vertex, {x=y}+{x<>y}.
intro.
induction x.
intro.
destruct y.
left.
reflexivity.
right.
intro.
inversion H.

induction y.
right.
intro.
inversion H.
destruct IHx with y.
left.
rewrite e ; reflexivity.
right.
intro.
apply n.
inversion H.
reflexivity.
Qed.

Lemma edge_dec : forall e e' : edge, {e=e'}+{e<>e'}.
Proof.
destruct e.
destruct e' as (v',v0').
destruct (vertex_dec v v').
rewrite e.
destruct (vertex_dec v0 v0').
rewrite e0.
left.
reflexivity.
right.
intro.
apply n.
assert (snd(v',v0)=snd (v',v0')).
rewrite H.
reflexivity.
simpl in H0.
exact H0.
right.
intro.
apply n.
assert (fst(v,v0)=fst(v',v0')).
rewrite H.
reflexivity.
simpl in H0.
exact H0.
Qed.

Lemma belong_dec : forall (a : Type), forall (v:a) (e:list a), (forall b c: a, (b=c)\/(b<>c))->(belong v e)\/(not (belong v e)).
Proof.
intros.
induction e.
right.
intro.
inversion H0.
destruct (H v a0).
left.
rewrite H0.
apply belong_y.
destruct IHe.
left.
apply belong_n.
exact H1.
right.
intro.
apply H1.

inversion H2.
assert False.
apply H0.
exact H5.
contradiction H4.
exact H5.
Qed.

Inductive edges_to_path2 (e : edges) : vertex->vertex->nat->Prop :=
| edges_to_path2_0 : forall v, (edges_to_path2 e v v 0)
| edges_to_path2_Sn : forall v1 v2 v3 n, (belong (v1,v2) e)->(edges_to_path2 e v2 v3 n)->(edges_to_path2 e v1 v3 (S n)).

Definition concat (a : Type) (e e0 : list a) : list a.
intros.
induction e.
apply e0.
apply (a0::IHe).
Defined.

Lemma belong_stable : forall (a : Type) (e e0: list a) (v:a), (belong v e)->(belong v (concat e0 e)).
Proof.
do 2 intro.
generalize e.
clear e.
induction e0 ; intros.
simpl.
exact H.
simpl.
apply belong_n.
apply IHe0.
exact H.
Qed.

Lemma concat_transfer : forall (a: Type) (e e0 : list a) (v0 : a), (concat e (v0::e0))=(concat (concat e (v0::nil)) e0).
Proof.
intro.
induction e ; intros.
simpl.
split ; intro ; exact H.

simpl.
rewrite (IHe e0 v0).
reflexivity.
Qed.

(*Lemma belong_transfer : forall (e e0 : edges) (v v0 : edge), (belong v (concat e (v0::e0)))<->(belong v (concat (concat e (v0::nil)) e0)).
Proof.
intro.
induction e ; intros.
simpl.
split ; intro ; exact H.

simpl.
destruct (edge_dec v a).
rewrite e1.
split ; intro ; apply belong_y.

destruct IHe with e0 v v0.
split ; intro ; apply belong_n ; (apply H0 || apply H).

inversion H1.
assert False.
apply n.
exact H4.
contradiction H3.
exact H4.

inversion H1.
assert False.
apply n.
exact H4.
contradiction H3.
exact H4.
Qed.*)

Lemma edges_to_path2_stable : forall (e e0 : edges) (v v0 : vertex) (n : nat), (edges_to_path2 e v v0 n)->(edges_to_path2 (concat e0 e) v v0 n).
Proof.
do 5 intro.
generalize e, e0, v, v0.
clear e. clear e0. clear v. clear v0.
induction n ; intros.
inversion H.
apply edges_to_path2_0.
inversion H.
apply edges_to_path2_Sn with v2.
apply belong_stable.
exact H1.
apply IHn.
exact H4.
Qed.

Lemma edges_to_path2_path : forall e : edges, (path_reflexive (edges_to_path2 e))/\(path_trans (edges_to_path2 e))/\(path_unique (edges_to_path2 e)) /\(path_back (edges_to_path2 e))/\(path_dec (edges_to_path2 e)).
split.
unfold path_reflexive ; intro.
apply edges_to_path2_0.

split.
unfold path_trans.
do 5 intro.
generalize v1, v2, v3, m.
clear v1. clear v2. clear v3. clear m.
induction n ; intros ; simpl.
inversion H.
exact H0.
inversion H.
apply edges_to_path2_Sn with v4.
exact H2.
apply IHn with v2.
exact H5.
exact H0.

split.
unfold path_unique.
intros.
inversion H.
reflexivity.

split.
Lemma edges_to_path_back : forall e, path_back (edges_to_path2 e).
unfold path_back.
intros.
inversion H.
exists v3.
split.
apply edges_to_path2_Sn with v3.
exact H1.
apply edges_to_path2_0.
exact H4.
Qed.
apply edges_to_path_back.

unfold path_dec.
generalize e.
clear e.

assert (1=1).
reflexivity.



Fixpoint eq a b {struct a}:=
match (a,b) with
(0,0)=> true
| (S n, S m)=> (eq n m)
| _ => false
end.

Fixpoint belong_list (e0:edges) (v1:vertex) : vertices :=
match e0 with
| nil => nil
| (a,b)::f=> if (eq a v1) then (b::(belong_list f v1)) else (belong_list f v1) 
end.

Inductive belong_listi : edges->vertex->vertices->Prop :=
| belong_listi_nil : forall v, belong_listi nil v nil
| belong_listi_y : forall v v1 e l, (belong_listi e v l)->(belong_listi ((v,v1)::e) v (v1::l)) 
| belong_listi_n : forall v v1 v2 e l, (belong_listi e v l)->(v<>v2)->(belong_listi ((v2,v1)::e) v l).

Lemma belong_list_i : forall e0 v1, belong_listi e0 v1 (belong_list e0 v1).
Proof.
intros.
induction e0.
simpl.
apply belong_listi_nil.
destruct a.
destruct (vertex_dec v v1).
rewrite e.
simpl.
assert (forall v2, eq v2 v2=true).
intro.
induction v2.
simpl.
reflexivity.
simpl.
exact IHv2.

rewrite (H v1).
apply belong_listi_y.
exact IHe0.

simpl.

assert (forall v v1, (v<>v1)->(eq v v1=false)).
intro.
induction v2.
intros.
destruct v2.
contradiction H.
reflexivity.
simpl.
reflexivity.
intros.
destruct v3.
simpl.
reflexivity.
simpl.
apply IHv2.
intro.
apply H.
rewrite H0.
reflexivity.

assert (eq v v1=false).
apply H.
exact n.
rewrite H0.
apply belong_listi_n.
exact IHe0.
intro.
apply n.
rewrite H1.
reflexivity. 
Qed.

assert (forall e0 v, belong_listi e0 v nil -> (forall v0, not (belong (v,v0) e0))).
intro.
induction e0.
repeat intro.
inversion H1.
repeat intro.
inversion H0.
destruct (IHe0 v) with v0.
exact H4.
inversion H1.
assert (fst (v,v0)=fst(v3,v2)).
rewrite H10, H2.
reflexivity.
simpl in H9.
assert False.
apply H7.
exact H9.
contradiction H12.
exact H10.

assert (forall e v, exists l : vertices, belong_listi e v l).
intros.
exists (belong_list e v).
apply belong_list_i.

assert (forall e v0 v2 x, (belong_listi e v0 x)->((belong v2 x)<->(belong (v0,v2) e))).
intro.
induction e.
intros.
inversion H2.
split ; intro.
inversion H3.
inversion H3.


intros.
split ; intro.
inversion H2.
destruct (vertex_dec v1 v2).
rewrite e1.
apply belong_y.

apply belong_n.
destruct (IHe v0 v2 l).
exact H8.
apply H9.
rewrite <- H7 in H3.
inversion H3.
contradiction n.
rewrite H13.
reflexivity.
exact H13.

apply belong_n.
destruct (IHe v0 v2 x).
exact H6.
apply H10.
exact H3.

inversion H3.
rewrite <- H6 in H2.
inversion H2.
apply belong_y.
contradiction H13.
reflexivity.
destruct a.
destruct (vertex_dec v v0).
rewrite e1 in H2.
inversion H2.
apply belong_n.
destruct (IHe v0 v2 l).
exact H13.
apply H15.
exact H6.
contradiction H14.
reflexivity.
destruct (IHe v0 v2 x).
inversion H2.
contradiction n.
exact H13.
apply H9.
exact H6.


assert (forall n l e v2, ((exists v0, belong v0 l /\ edges_to_path2 e v0 v2 n)\/
(forall v0, (belong v0 l)->(not (edges_to_path2 e v0 v2 n))))).
intro.
induction n.
intros.
destruct (belong_dec v2 l).
intros.
destruct (vertex_dec b c).
left.
exact e0.
right.
exact n.
left.
exists v2.
split.
exact H3.
apply edges_to_path2_0.
right.
repeat intro.
apply H3.
inversion H5.
rewrite <- H7.
exact H4.
intro.
assert (forall e v1 v2, (edges_to_path2 e v1 v2 (S n))\/
(not (edges_to_path2 e v1 v2 (S n)))).
intros.
destruct H1 with e v1.
destruct IHn with x e v2.
left.
destruct H4.
destruct H4.
apply edges_to_path2_Sn with x0.
destruct H2 with e v1 x0 x.
exact H3.
apply H6.
exact H4.
exact H5.
right.
intro.
inversion H5.
apply H4 with v3.
destruct (H2 e v1 v3 x).
exact H3.
apply H12.
exact H7.
exact H10.


induction l.
intros.
right.
intros.
inversion H4.

intros.
destruct (H3 e a v2).
left.
exists a.
split.
apply belong_y.
exact H4.
destruct IHl with e v2.
left.
destruct H5.
destruct H5.
exists x.
split.
apply belong_n.
exact H5.
exact H6.
right.
intros.
destruct (vertex_dec v0 a).
rewrite e0.
exact H4.
apply H5.
inversion H6.
contradiction n0.
exact H9.
intros.
destruct n.
destruct (vertex_dec v1 v2).
left.
rewrite e0.
apply edges_to_path2_0.
right.
intro.
apply n.
inversion H4.
reflexivity.

destruct H1 with e v1.
destruct H3 with n x e v2.
left.
destruct H5.
destruct H5.
apply edges_to_path2_Sn with x0.
destruct H2 with e v1 x0 x.
exact H4.
apply H7.
exact H5.
exact H6.
right.
intro.
inversion H6.
apply H5 with v3.
destruct (H2 e v1 v3 x).
exact H4.
apply H13.
exact H8.
exact H11.
Defined.

Definition edges_to_path (e : edges) : path.
intro.
exists (edges_to_path2 e). 
apply edges_to_path2_path.
Defined.


(*Definition edges_to_path (e : edges) : path.
intro.
exists (edges_to_path2 e).
split.
unfold path_reflexive ; intro.
apply edges_to_path2_0.
unfold path_trans.
do 5 intro.
generalize v1, v2, v3, m.
clear v1. clear v2. clear v3. clear m.
induction n ; intros ; simpl.
inversion H.
exact H0.
inversion H.
apply edges_to_path2_Sn with v4.
exact H2.
apply IHn with v2.
exact H5.
exact H0.
Defined.*)

Definition path_to_edges (p:path) (e:edges) : Prop.
intros.
destruct p.
apply (forall v1 v2, (belong (v1,v2) e)<->(x v1 v2 1)).
Defined.

Definition equal_list (a : Type) ( v : list a) (v0 : list a) : Prop :=
forall u : a, (belong u v)<->(belong u v0).

Lemma equal_list_nil : forall a : Type, forall v : list a, equal_list v nil-> v=nil.
Proof.
intros.
unfold equal_list in H.
destruct v.
reflexivity.
destruct (H a0).
assert (belong a0 nil).
apply H0.
apply belong_y.
inversion H2.
Qed.

(*Definition equal_list (v v0 : vertices) : Prop :=
equal_list_a v v0.
(*forall u : vertex, belong u v <-> belong u v0.*)

Definition equal_edges (e e0 : edges) : Prop :=
forall u : edge, belong u e <-> belong u e0.*)

Definition equal_path (p p0 : path) : Prop.
intros.
destruct p.
destruct p0.
apply (forall n : nat, forall u u0 : vertex, ((x u u0 n)<->(x0 u u0 n))).
Defined.

Definition equal_graph (g g0 : Graph) : Prop.
intros.
destruct g.
destruct g0.
apply ((equal_list v v0)/\(equal_path p p0)).
Defined.

Lemma Eqpath_edges : forall p e, (equal_path (edges_to_path e) p)<->(path_to_edges p e).
Proof.
intros ; split ; intro.
unfold path_to_edges.
unfold edges_to_path in H.
unfold equal_path in H.
destruct p.
intros ; split ; intro.
destruct H with 1 v1 v2.
apply H1.
apply edges_to_path2_Sn with v2.
exact H0.
apply edges_to_path2_0.
destruct H with 1 v1 v2.
assert (edges_to_path2 e v1 v2 1).
apply H2.
exact H0.
inversion H3.
inversion H8.
rewrite <- H10.
exact H5.

unfold equal_path.
unfold edges_to_path.
unfold path_to_edges in H.
destruct p.
induction n.

intros ; split ; intro.
inversion H0.
apply a.
assert (u=u0).
apply a.
exact H0.
rewrite H1.
apply edges_to_path2_0.
intros ; split ; intro.


destruct a as (a1,a2).
destruct a2 as (a2,a3).
inversion H0.
unfold path_trans in a2.
assert (x u u0 (1+n)).
apply a2 with v2.
apply (H u v2).
exact H2.
apply (IHn v2 u0).
exact H5.
simpl in H6.
exact H6.


destruct a.
destruct H2.
destruct H3.
destruct H4.
unfold path_back in H4.
destruct (H4 u u0 n).
exact H0.
destruct H6.
apply edges_to_path2_Sn with x0.
apply (H u x0).
exact H6.
apply (IHn x0 u0).
exact H7.
Defined.

Definition adjacence := (vertex * vertices)%type.

Definition adjacences := list adjacence.

Definition equal_adjacences (a a0 : adjacences) : Prop :=
forall u v, (exists l, (belong v l)/\(belong (u,l) a)) <-> (exists l, (belong v l)/\(belong (u,l) a0)).

Fixpoint reduct_adjacences (a:adjacences) : adjacences :=
match a with
nil => nil
| (b,nil)::t => (reduct_adjacences t)
| (b,c::l)::t=> (b,c::l)::(reduct_adjacences t)
end.

Inductive reduct_adjacences2 : adjacences->adjacences->Prop :=
| reduct_adjacences2_t : forall a a0 b c, (reduct_adjacences2 a a0)->(reduct_adjacences2 ((b,c)::a) ((b,c)::a0))
| reduct_adjacences2_nil : forall a a0 b, (reduct_adjacences2 a a0)->(reduct_adjacences2 ((b,nil)::a) a0)
| reduct_adjacences2_nileq : forall a b, reduct_adjacences2 ((b,nil)::a) a.


Lemma equal_reduct_adjacences : forall a, equal_adjacences a (reduct_adjacences a).
Proof.
intro.
unfold equal_adjacences.
intros.
induction a.
split ; intro ; exact H.
destruct a as (b,v0).
induction v0.
simpl.
split ; intro ; destruct H.
apply IHa.
exists x.
destruct H.
split.
exact H.
inversion H.
rewrite <- H2 in H0.
inversion H0.
exact H5.
rewrite <-H3 in H0.
inversion H0.
exact H6.

destruct IHa.
destruct H1.
exists x.
exact H.

exists x0.
destruct H1.
split.
exact H1.
apply belong_n.
exact H2.

simpl.

split.

intro.

destruct H.
destruct H.
inversion H0.

exists x.
split.
exact H.
rewrite <- H4.
apply belong_y.

destruct IHa.
destruct H5.
exists x.
split.
exact H.
exact H3.

exists x0.
destruct H5 ; split.
exact H5.
apply belong_n.
exact H7.



intro.

destruct H.
destruct H.
inversion H0.

exists x.
split.
exact H.
rewrite <- H4.
apply belong_y.

destruct IHa.
destruct H6.
exists x.
split.
exact H.
exact H3.

exists x0.
destruct H6 ; split.
exact H6.
apply belong_n.
exact H7.
Qed.

Lemma equal_adjacences_nil : forall a : adjacences, equal_adjacences a nil-> (reduct_adjacences a= nil).
Proof.
intros.
unfold equal_adjacences in H.
induction a.
simpl.
reflexivity.
destruct a.
destruct v0.
simpl.
apply IHa.
intros.
destruct (H u v0).
split ; intro.
apply H0.
destruct H2.
exists x.
destruct H2 ;split.
exact H2.
apply belong_n.
exact H3.

destruct H2.
destruct H2.
inversion H3.

destruct (H v v0).

assert (exists l : list vertex, belong v0 l /\ belong (v,l) nil).
apply H0.
exists (v0::v1).
split.
apply belong_y.
apply belong_y.

destruct H2.
destruct H2.
inversion H3.
Qed.

Lemma equal_adjacences_com :  forall a a0, (equal_adjacences a a0)->(equal_adjacences a0 a).
Proof.
unfold equal_adjacences.
intros.
destruct (H u v).
split.
apply H1.
apply H0.
Qed.

Lemma equal_adjacences_ref : forall a, equal_adjacences a a.
Proof.
intro.
split ; intro ; exact H.
Qed.

Lemma equal_adjacences_trans : forall a b c, (equal_adjacences a b)->(equal_adjacences b c)->(equal_adjacences a c).
Proof.
unfold equal_adjacences.
intros.
split ; intro ; destruct (H u v) ; destruct (H0 u v).
apply H4, H2 ; exact H1.
apply H3, H5 ; exact H1.
Qed.




Lemma vertices_dec : forall l l' : vertices, {l=l'}+{l<>l'}.
Proof.
apply list_eq_dec.
exact vertex_dec.
Qed.

Lemma adjacence_dec : forall a a' : adjacence, {a=a'}+{a<>a'}.
Proof.
intros.
destruct a.
destruct a' as (v',v0').
destruct (vertex_dec v v').
rewrite e.
destruct (vertices_dec v0 v0').
rewrite e0.
left.
reflexivity.
right.
intro.
apply n.
assert (snd(v',v0)=snd (v',v0')).
rewrite H.
reflexivity.
simpl in H0.
exact H0.
right.
intro.
apply n.
assert (fst(v,v0)=fst(v',v0')).
rewrite H.
reflexivity.
simpl in H0.
exact H0.
Qed.

Lemma adjacences_dec : forall l l' : adjacences, {l=l'}+{l<>l'}.
Proof.
apply list_eq_dec.
apply adjacence_dec.
Qed.

Definition ap_path (p : path) (a b : vertex) ( n : nat) : Prop.
intros.
destruct p.
(*destruct a0.
destruct H0.
destruct H1.
destruct H2.
unfold path_dec in H3.
destruct (H3 a b n).*)
apply (x a b n).
Defined.

Lemma path_to_edges_constr : forall p, (exists v, forall a b, (ap_path p a b 1)->((belong a v)/\(belong b v)))->(exists e, (path_to_edges p e)).
Proof.
unfold path_to_edges.
intros.
destruct p.
simpl in H.
destruct H.

assert (forall v1 v2, exists e : edges, forall a b, ((belong (a,b) e))<->((x a b 1)/\(belong a v1)/\(belong b v2))).
intro.
induction v1.
exists nil.
split ; intros.
inversion H0.
destruct H0.
destruct H1.
inversion H1.

assert (forall v2 v3, exists e : edges, (forall a b, (belong (a,b) e)<->
(((x a b 1)/\(belong a v1)/\(belong b v2))\/((x a b 1)/\(a=a0)/\(belong b v3))))).
intros.
induction v3.
destruct IHv1 with v2.
exists x1.
intros.
destruct H0 with a1 b.
split ; intro.
left.
apply H1.
exact H3.
apply H2.
destruct H3.
exact H3.
destruct H3.
destruct H4.
inversion H5.
destruct a.
destruct H1.
destruct H2.
destruct H3.
destruct IHv3.
destruct (H4 a0 a1 1).
exists ((a0,a1)::x1).
intros.
destruct H5 with a b.
destruct (edge_dec (a,b) (a0,a1)).
rewrite e.
split ; intro.
right.
assert (snd(a,b)=snd(a0,a1)).
rewrite e.
reflexivity.
simpl in H10.
rewrite H10.
assert (fst(a,b)=fst(a0,a1)).
rewrite e.
reflexivity.
simpl in H11.
rewrite H11.
split.
exact H6.
split.
reflexivity.
apply belong_y.
apply belong_y.
split ; intro.
inversion H9.
contradiction n.
rewrite H12, H13.
reflexivity.
destruct H7.
exact H12.
left.
exact H7.
right.
destruct H7.
destruct H14.
split.
exact H7.
split.
exact H14.
apply belong_n.
exact H15.
apply belong_n.
apply H8.
destruct H9.
left.
exact H9.
right.
destruct H9.
destruct H10.
split.
exact H9.
split.
exact H10.
inversion H11.
contradiction n.
rewrite H10, H14.
reflexivity.
exact H14.
exists x1.
intros.
destruct H5 with a b.
split ; intro.
destruct H7.
exact H9.
left.
exact H7.
right.
destruct H7.
destruct H10.
split.
exact H7.
split.
exact H10.
apply belong_n.
exact H11.
apply H8.
destruct H9.
left.
exact H9.
right.
destruct H9.
destruct H10.
split.
exact H9.
split.
exact H10.
inversion H11.
rewrite H14, H10 in H9.
contradiction H6.
exact H14.

intro.
destruct H0 with v2 v2.
exists x1.
intros.
destruct H1 with a1 b.
split ; intro.
destruct H2.
exact H4.
destruct H2.
split.
exact H2.
destruct H5.
split.
apply belong_n.
exact H5.
exact H6.
destruct H2.
destruct H5.
split.
exact H2.
split.
rewrite H5.
apply belong_y.
exact H6.
apply H3.
destruct H4.
destruct H5.
inversion H5.
right.
split.
rewrite <- H9.
exact H4.
split.
reflexivity.
exact H6.
left.
split.
exact H4.
split.
exact H9.
exact H6.

destruct H0 with x0 x0.
exists x1.
intros.
destruct H1 with v1 v2.
split ; intro.
destruct H2.
exact H4.
exact H2.
apply H3.
split.
exact H4.
apply H.
exact H4.
Qed.

Inductive adjacences_to_edges : adjacences->edges->Prop :=
| adjacences_to_edges_nil : adjacences_to_edges nil nil
| adjacences_to_edges_b_nil : forall a e b, (adjacences_to_edges a e)->(adjacences_to_edges ((b,nil)::a) e)
| adjacences_to_edges_b_c : forall a e b c l, (adjacences_to_edges ((b,l)::a) e)->(adjacences_to_edges ((b,c::l)::a) ((b,c)::e)).

Inductive edges_to_adjacences : edges->adjacences->Prop :=
| edges_adjacence_nil : edges_to_adjacences nil nil
| edges_to_adjacences_b_nil : forall a e b, (edges_to_adjacences e a)->(edges_to_adjacences e ((b,nil)::a))
| edges_to_adjacences_b_c : forall a e b c l, (edges_to_adjacences e ((b,l)::a))->(edges_to_adjacences ((b,c)::e) ((b,c::l)::a)).

Inductive adjacences_to_path2 : adjacences->vertex->vertex->nat->Prop :=
| adjacences_to_path2_0 : forall a v, (adjacences_to_path2 a v v 0)
| adjacences_to_path2_1 : forall a b c l, (belong (b,l) a)->(belong c l)->(adjacences_to_path2 a b c 1)
| adjacences_to_path2_Sn : forall a b c d n m, (n>0)->(m>0)->(adjacences_to_path2 a b c n)->(adjacences_to_path2 a c d m)->(adjacences_to_path2 a b d (n+m)).

Definition path_to_adjacences (p:path) (a:adjacences) : Prop.
intros.
destruct p.
apply (forall v1 v2, (exists l, (belong (v1,l)) a /\ (belong v2 l))<->(x v1 v2 1)).
Defined.

Lemma Hunique : forall a, (path_unique (adjacences_to_path2 a)).
unfold path_unique.
intros.
inversion H.
reflexivity.
rewrite H0 in H1, H2.
destruct n.
inversion H1.
inversion H0.
Qed.

Lemma Hback : forall a, (path_back (adjacences_to_path2 a)).
(*unfold path_back.
do 4 intro.
generalize v1 v2.
clear v1. clear v2.*)
assert (forall n a m v1 v2, (m < n)->(adjacences_to_path2 a v1 v2 (S m))->(exists v3, adjacences_to_path2 a v1 v3 1 /\ adjacences_to_path2 a v3 v2 m)).
intro ; intro. induction n ; intros.
inversion H.

inversion H0.

exists v2.
split.
apply adjacences_to_path2_1 with l.
exact H2.
exact H6.
apply adjacences_to_path2_0.

destruct n0.
inversion H2.
destruct (IHn n0 v1 c).
simpl in H1.
inversion H1.
rewrite <- H10 in H.
destruct m0.
inversion H3.
rewrite (plus_comm n0 (S m0)) in H.
simpl in H.
assert (m0+n0<n).
apply lt_S_n.
exact H.
apply plus_lt_reg_l with m0.
rewrite (plus_comm m0 n).
apply lt_plus_trans.
exact H9.

exact H4.

destruct H9.
simpl in H1.
inversion H1.

destruct n0.
exists c.
split.
exact H4.
simpl.
exact H8.

exists x.
split.
exact H9.

apply adjacences_to_path2_Sn with c.
apply lt_O_Sn.
exact H3.
exact H10.
exact H8.

unfold path_back.
intros.
apply H with (S n).
apply lt_n_Sn.
exact H0.
Qed.

Lemma Htrans : forall a, (path_trans (adjacences_to_path2 a)).
Proof.
unfold path_trans.
intros.
destruct n.
simpl.
assert (v1=v2).
apply Hunique with a.
exact H.
rewrite H1.
exact H0.

destruct m.
rewrite (plus_comm (S n) 0).
simpl.
assert (v2=v3).
apply Hunique with a.
exact H0.
rewrite <- H1.
exact H.

apply adjacences_to_path2_Sn with v2.
apply lt_O_Sn.
apply lt_O_Sn.
exact H.
exact H0.
Qed.

Lemma Hreflexive : forall a, path_reflexive (adjacences_to_path2 a).
Proof.
unfold path_reflexive.
intros.
apply adjacences_to_path2_0.
Qed.

Lemma adjacences_to_path2_stable : forall (a a0 : adjacences) (v1 v2:vertex) n, 
(adjacences_to_path2 a v1 v2 n)->
(forall v3 v4, (exists v5, (belong (v3,v5) a)/\(belong v4 v5))->
(exists v5, (belong (v3,v5) a0)/\(belong v4 v5)))->
(adjacences_to_path2 a0 v1 v2 n).
Proof.
do 5 intro.
generalize v1, v2.
clear v1 v2.
induction n ; intros.
inversion H.
apply adjacences_to_path2_0.
destruct n.
simpl in H1, H2.
rewrite H1 in H2.
inversion H2.
simpl in H1.
inversion H1.
assert (path_back (adjacences_to_path2 a)).
apply Hback.
unfold path_back in H1.
destruct H1 with v1 v2 n.
exact H.
destruct H2.
destruct n.
inversion H3.
rewrite <- H6.
clear H4 H5 H6.
clear a1 v.
inversion H2.
clear H6 H7 H8.
clear b c.
destruct H0 with v1 x.
exists l.
split.
exact H4.
exact H5.
destruct H6.
apply adjacences_to_path2_1 with x0.
exact H6.
exact H7.
destruct n.
inversion H5.
destruct m.
inversion H6.
simpl in H4.
inversion H4.
rewrite (plus_comm n (S m)) in H13.
simpl in H13.
inversion H13.

destruct n.
simpl in H4, H5.
rewrite H4 in H5.
inversion H5.
simpl in H4.
inversion H4.


assert (1+(S n)=S (S n)).
simpl.
reflexivity.
rewrite <- H4.
apply adjacences_to_path2_Sn with x.
apply lt_n_Sn.
apply lt_O_Sn.


inversion H2.
clear H7 H8 H9.
clear a1 b c.
destruct H0 with v1 x.
exists l.
split.
exact H5.
exact H6.
destruct H7.
apply adjacences_to_path2_1 with x0.
exact H7.
exact H8.
destruct n0.
inversion H6.
destruct m.
inversion H7.
simpl in H5.
inversion H5.
rewrite (plus_comm n0 (S m)) in H14.
simpl in H14.
inversion H14.

apply IHn.

exact H3.

exact H0.
Qed.

Lemma belong_stable_l : forall (v : vertex) l1 l2, (belong v l1)->(belong v (concat l1 l2)).
Proof.
do 2 intro.
induction l1.
intros.
inversion H.
intros.
inversion H.
simpl.
apply belong_y.
simpl.
apply belong_n.
apply IHl1.
exact H2.
Qed.

Lemma belong_stable_r : forall (v : vertex) l1 l2, (belong v l2)->(belong v (concat l1 l2)).
Proof.
do 2 intro.
induction l1.
intros.
simpl.
exact H.
intros.
simpl.
apply belong_n.
apply IHl1.
exact H.
Qed.

Lemma belong_stable_rl : forall (v:vertex) l1 l2, (belong v (concat l1 l2))->((belong v l1) \/ (belong v l2)).
Proof.
do 2 intro.
induction l1.
intros.
simpl in H.
right.
exact H.
intros.
simpl in H.
inversion H.
left.
apply belong_y.
destruct IHl1 with l2.
exact H2.
left.
apply belong_n.
exact H4.
right.
exact H4.
Qed.

Lemma Hdec : forall a, path_dec (adjacences_to_path2 a).
Proof.
unfold path_dec.

assert (forall v1 v2 a, (adjacences_to_path2 a v1 v2 0)\/(not (adjacences_to_path2 a v1 v2 0))).
intros.
destruct (vertex_dec v1 v2).
rewrite e.
left.
apply adjacences_to_path2_0.
right.
intro.
inversion H.
contradiction n.
destruct n0.
inversion H1.
inversion H0.

assert (forall (v1: vertex) a, exists l, forall (v3: vertex), (exists l1, (belong (v1,l1) a)/\(belong v3 l1) )<->(belong v3 l)).
intros.
induction a.
exists nil.
split ; intro.
destruct H0.
destruct H0.
inversion H0.
inversion H0.
destruct IHa.
destruct a.
destruct (vertex_dec v1 v).
rewrite e.
exists (concat l x).
split ; intro.
destruct H0 with v3.
destruct H1.
destruct H1.
inversion H1.
apply belong_stable_l.
rewrite <- H7.
exact H4.
apply belong_stable_r.
apply H2.
exists x0.
rewrite e.
split.
exact H7.
exact H4.

destruct H0 with v3.
destruct belong_stable_rl with v3 l x.
exact H1.
exists l.
split.
apply belong_y.
exact H4.
destruct H3.
exact H4.
exists x0.
destruct H3.
split.
apply belong_n.
rewrite <- e.
exact H3.
exact H5.
exists x.
split ; intro.
destruct H0 with v3.
apply H2.
destruct H1.
destruct H1.
inversion H1.
contradiction n.
exists x0.
split.
exact H7.
exact H4.
destruct H0 with v3.
destruct H3.
exact H1.
destruct H3.
exists x0.
split.
apply belong_n.
exact H3.
exact H4.

assert (forall v1 v2 a, (adjacences_to_path2 a v1 v2 1)\/(not (adjacences_to_path2 a v1 v2 1))).
intros.
destruct H0 with v1 a.
destruct (belong_dec v2 x).
intros.
destruct (vertex_dec b c).
left.
exact e.
right.
exact n.
destruct H1 with v2.
destruct H4.
exact H2.
destruct H4.
left.
apply adjacences_to_path2_1 with x0.
exact H4.
exact H5.
right.
intro.
inversion H3.
destruct H1 with v2.
apply H2.
apply H9.
exists l.
split.
exact H4.
exact H5.
destruct n.
inversion H5.
destruct m.
inversion H6.
inversion H4.
rewrite (plus_comm n (S m)) in H13.
inversion H13.

assert (forall n a m, (S (S m) <= n)->(forall v1 v2, 
(exists l, (forall v3, ((exists l1, belong (v1,l1) a /\ belong v3 l1)/\(adjacences_to_path2 a v3 v2 (S m)))<->(belong v3 l)))->
(adjacences_to_path2 a v1 v2 (S (S m)))\/(not (adjacences_to_path2 a v1 v2 (S (S m)))))).


intro.
induction n.
intros.
inversion H2.

intros.
inversion H2.
destruct H3.
destruct x.
right.
intro.
assert (path_back (adjacences_to_path2 a)).
apply Hback.
unfold path_back in H6.
destruct H6 with v1 v2 (S m).
exact H4.
destruct H7.
inversion H7.
destruct H3 with x.
assert (belong x nil).
apply H14.
split.
exists l.
split.
exact H9.
exact H10.
exact H8.
inversion H16.
destruct n0.
inversion H10.
destruct m0.
inversion H11.
inversion H9.
rewrite (plus_comm n0 (S m0)) in H18.
inversion H18.
left.
assert (S (S m)= 1+(S m)).
reflexivity.
rewrite H4.
apply adjacences_to_path2_Sn with v.
apply lt_O_Sn.
apply lt_O_Sn.
destruct H3 with v.
destruct H7.
apply belong_y.
destruct H7.
destruct H7.
apply adjacences_to_path2_1 with x0.
exact H7.
exact H9.
destruct H3 with v.
destruct H7.
apply belong_y.
exact H8.

apply IHn.
exact H5.
exact H3.

intros.
generalize a, v1, v2.
clear a v1 v2.
destruct n.
intros.
apply H.
induction n.
intros.
apply H1.

(*
assert (forall a (v1 v2: vertex), exists l, forall (v3 : vertex), 
((exists l1, (belong (v1,l1) a /\ belong v3 l1))/\(adjacences_to_path2 a v3 v2 (S n)))<->(belong v3 l)).

intro.
induction a.
intros.
exists nil.
split ; intro.
destruct H3.
destruct H3.
destruct H3.
inversion H3.
inversion H3.*)

assert (forall l v2 a2, exists l2, forall v0, 
((belong v0 l)/\(adjacences_to_path2 a2 v0 v2 (S n))<->(belong v0 l2))).
intro.
induction l ; intros.
exists nil.
split ; intros.
destruct H3.
inversion H3.
inversion H3.

destruct IHl with v2 a2.
destruct IHn with a2 a v2.
exists (a::x).
intro.
destruct H3 with v0.
split ; intros.
destruct H7.
inversion H7.
apply belong_y.
apply belong_n.
apply H5.
split.
exact H11.
exact H8.
inversion H7.
split.
apply belong_y.
exact H4.
destruct H6.
exact H10.
split.
apply belong_n.
exact H6.
exact H12.

exists x.
intro.
destruct H3 with v0.
split ; intro.
apply H5.
destruct H7.
inversion H7.
contradiction H4.
rewrite H11 in H8.
exact H8.
split.
exact H11.
exact H8.
destruct H6.
exact H7.
split.
apply belong_n.
exact H6.
exact H8.

assert (forall a (v1: vertex), exists l, forall (v : vertex), (exists l0, (belong (v1,l0) a)/\(belong v l0))<->(belong v l)).
intros.
induction a.
exists nil.
split ; intro.
destruct H4.
destruct H4.
inversion H4.
inversion H4.

destruct a.
destruct (vertex_dec v1 v).
rewrite e.
destruct IHa.
exists (concat l x).
intro.
destruct H4 with v0.
split ; intro.
destruct H7.
destruct H7.
inversion H7.
apply belong_stable_l.

rewrite <- H11.
exact H8.
apply belong_stable_r.
apply H5.
rewrite e.
exists x0.
split.
exact H11.
exact H8.
destruct belong_stable_rl with v0 l x.
exact H7.
exists l.
split.
apply belong_y.
exact H8.
destruct H6.
exact H8.
exists x0.
destruct H6.
split.
apply belong_n.
rewrite <- e.
exact H6.
exact H9.
destruct IHa.
exists x.
intro.
destruct H4 with v0.
split ; intro.
apply H5.
destruct H7.
destruct H7.
inversion H7.
contradiction n0.
exists x0.
split.
exact H11.
exact H8.
destruct H6.
exact H7.
destruct H6.
exists x0.
split.
apply belong_n.
exact H6.
exact H8.

intros.
apply H2 with (S (S n)).
apply le_refl.

destruct H4 with a v1.
destruct H3 with x v2 a.
exists x0.
intro.
destruct H5 with v3.
clear H5.
destruct H6 with v3.
clear H6.

split ; intro.
destruct H6.
destruct H6.
destruct H6.
apply H5.
split.
apply H7.
exists x1.
split.
exact H6.
exact H11.
exact H10.

destruct H9.
exact H6.
split.
destruct H8.
exact H9.

exists x1.
exact H8.
exact H10.
Qed.

Lemma adjacences_to_path2_path : forall a, (path_reflexive (adjacences_to_path2 a))/\(path_trans (adjacences_to_path2 a))/\(path_unique (adjacences_to_path2 a))/\(path_back (adjacences_to_path2 a))/\(path_dec (adjacences_to_path2 a)).
Proof.
intro.
split.
apply Hreflexive.
split.
apply Htrans.
split.
apply Hunique.
split.
apply Hback.
apply Hdec.
Qed.

Definition adjacences_to_path (a : adjacences) : path.
intro.
exists (adjacences_to_path2 a). 
apply adjacences_to_path2_path.
Defined.

Lemma Eqpath_adjacences : forall p a, (equal_path (adjacences_to_path a) p)<->(path_to_adjacences p a).
Proof.
intros ; split ; intro.
unfold path_to_adjacences.
unfold adjacences_to_path in H.
unfold equal_path in H.
destruct p.

intros ; split ; intro ; destruct H with 1 v1 v2.
apply H1.
destruct H0.
destruct H0.
apply adjacences_to_path2_1 with x0.
exact H0.
exact H3.
assert (adjacences_to_path2 a v1 v2 1).
apply H2.
exact H0.
inversion H3.
exists l.
split.
exact H4.
exact H5.
inversion H3.
exists l.
split.
exact H12.
exact H13.

destruct (plus_is_one n0 m0).
exact H12.
destruct a3.
assert False.
apply (lt_O_neq n0).
exact H13.
rewrite H20.
reflexivity.
contradiction H22.
destruct a3.
assert False.
apply (lt_O_neq m0).
exact H14.
rewrite H21.
reflexivity.
contradiction H22.


unfold equal_path.
unfold adjacences_to_path.
unfold path_to_adjacences in H.
destruct p.

assert (forall n, forall m u u0, (m<n)-> (adjacences_to_path2 a u u0 m <-> x u u0 m)).
intro ; induction n ; intros.
inversion H0.
split ; intro; destruct H with u u0.

inversion H1.
destruct a0.
apply H8.
apply H2.
exists l.
split.
exact H4.
exact H5.

destruct a0.
destruct H13.
apply H13 with c.
destruct (IHn n0 u c).
rewrite <- H11 in H0.
inversion H5.
rewrite <- H15 in H0.
rewrite (plus_comm n0 1) in H0.
simpl in H0.
apply lt_S_n.
exact H0.
rewrite <- H16 in H0.
rewrite (plus_comm n0 (S m1)) in H0.
simpl in H0.
apply plus_lt_reg_l with m1.
rewrite (plus_comm m1 n).
apply lt_plus_trans.
apply lt_S_n.
exact H0.

apply H15.
exact H6.

destruct (IHn m0 c u0).
rewrite <- H11 in H0.
inversion H4.
rewrite <- H15 in H0.
simpl in H0.
apply lt_S_n.
exact H0.
rewrite <- H16 in H0.
simpl in H0.
apply plus_lt_reg_l with m1.
rewrite (plus_comm m1 n).
apply lt_plus_trans.
apply lt_S_n.
exact H0.

apply H15.
exact H7.

destruct a0.
destruct H5.
destruct H6.
destruct H7.
destruct m.
assert (u=u0).
apply H6.
exact H1.
rewrite H9.
apply adjacences_to_path2_0.
destruct H7 with u u0 m.
exact H1.
destruct IHn with m u u0.
apply lt_S_n.
exact H0.
destruct m.
destruct H3.
exact H1.
destruct H3.
apply adjacences_to_path2_1 with x1.
exact H3.
exact H12.

assert (1+S m=S (S m)).
simpl.
reflexivity.
rewrite <- H12.
apply adjacences_to_path2_Sn with x0.
apply lt_O_Sn.
apply lt_O_Sn.
destruct H9.
destruct H with u x0.
destruct H15.
exact H9.
destruct H15.
apply adjacences_to_path2_1 with x1.
exact H15.
exact H16.
destruct IHn with (S m) x0 u0.
apply lt_S_n.
exact H0.
apply H14.
destruct H9.
exact H15.

intros.
apply (H0 (S n) n u u0).
apply lt_n_Sn.
Defined.

Lemma reduct_adjacences_nil : forall a v v0, (reduct_adjacences ((v,v0)::a) = nil)->(v0=nil).
Proof.
intros.
destruct v0.
reflexivity.
inversion H.
Qed.

Lemma adjacences_to_edges_reduct_nil : forall a e, (adjacences_to_edges a e)->(reduct_adjacences a= nil)->(e=nil).
Proof.
intros.
induction a.
inversion H.
reflexivity.
destruct a.
assert (v0=nil).
apply reduct_adjacences_nil with a0 v.
exact H0.
rewrite H1 in H, H0.
apply IHa.
inversion H.
exact H5.
simpl in H0.
exact H0.
Qed.

Lemma belong_adjacences_edges : forall a e u v, (edges_to_adjacences e a)->((belong (u,v) e)<->(exists l, (belong v l)/\(belong (u,l) a))).
Proof.
intro.
induction a.
intros.
inversion H.
split ; intro.
inversion H1.
destruct H1.
destruct H1.
inversion H2.

destruct a.
induction v0.

intros.
inversion H.
destruct (IHa e u v0).
exact H2.
split ; intro.
destruct H4.
exact H6.
exists x.
destruct H4.
split.
exact H4.
apply belong_n.
exact H7.
apply H5.
destruct H6.
destruct H6.
exists x.
split.
exact H6.
inversion H7.
rewrite H11 in H6.
inversion H6.
exact H10.

intros.

inversion H.
destruct (edge_dec (u,v1) (v,a)).
split ; intro.
exists (a::v0).
split.
assert (snd (u,v1)=snd(v,a)).
rewrite e1.
reflexivity.
simpl in H7.
rewrite H7.
apply belong_y.
assert (fst (u,v1)=fst(v,a)).
rewrite e1.
reflexivity.
simpl in H7.
rewrite H7.
apply belong_y.
rewrite e1.
apply belong_y.

destruct (IHv0 e0 u v1).
exact H2.
split ; intro.
destruct H6.
inversion H8.
assert False.
apply n.
rewrite H11, H10.
reflexivity.
contradiction H9.
exact H10.

destruct H6.
inversion H9.
rewrite <- H13.
exists (a::x).
split.
apply belong_n.
exact H6.
apply belong_y.
exists x.
split.
exact H6.
apply belong_n.
exact H12.

apply belong_n.
apply H7.
destruct H8.
destruct H8.
inversion H9.

exists v0.
split.
rewrite H13 in H8.
inversion H8.
assert False.
apply n.
rewrite H16, H12.
reflexivity.
contradiction H15.
exact H16.
apply belong_y.

exists x.
split.
exact H8.
apply belong_n.
exact H12.
Qed.


Lemma belong_edges_adjacences : forall a e u v, (adjacences_to_edges a e)->((exists l, (belong v l)/\(belong (u,l) a))<->(belong (u,v) e)).
Proof.

intro.
induction a.
intros.
inversion H.
split ; intro.
destruct H0.
destruct H0.
inversion H2.
inversion H0.

destruct a.
induction v0.
intros.
destruct (IHa e u v0).
inversion H.
exact H3.
split ; intro.
apply H0.
destruct H2.
destruct H2.
inversion H3.
rewrite H7 in H2.
inversion H2.
exists x.
split.
exact H2.
exact H6.

destruct H1.
exact H2.
destruct H1.
exists x.
split.
exact H1.
apply belong_n.
exact H3.

intros.
inversion H.
destruct (IHv0 e0 u v1).
exact H5.
destruct (edge_dec (u,v1) (v,a)).
assert (fst (u,v1)=fst (v,a)).
rewrite e1 ; reflexivity.
simpl in H8.
assert (snd (u,v1)=snd (v,a)).
rewrite e1 ; reflexivity.
simpl in H9.
rewrite H8, H9.
split ; intro.
apply belong_y.
exists (a::v0).
split.
apply belong_y.
apply belong_y.

split ; intro.
apply belong_n.
apply H6.
destruct H8.
destruct H8.
inversion H9.
exists v0.
rewrite H13 in H8.
inversion H8.
destruct n.
rewrite H12, H16.
reflexivity.
split.
exact H16.
apply belong_y.

exists x.
split.
exact H8.
apply belong_n.
exact H12.

inversion H8.
destruct n.
rewrite H12, H11.
reflexivity.

destruct H7.
exact H11.
destruct H7.
inversion H13.
exists (a::v0).
split.
apply belong_n.
rewrite <- H17.
exact H7.
apply belong_y.

exists x.
split.
exact H7.
apply belong_n.
exact H16.
Qed.


Lemma Eqadjacence_edges : forall a a0 e e0, (edges_to_adjacences e a)->(equal_adjacences a a0)->(adjacences_to_edges a0 e0)->(equal_list e e0).
Proof.
intro.
unfold equal_list.
unfold equal_adjacences.
intros.
split ; intro ; destruct u.
destruct belong_edges_adjacences with a0 e0 v v0.
exact H1.
apply H3.
destruct (H0 v v0).
apply H5.
destruct belong_adjacences_edges with a e v v0.
exact H.
apply H7.
exact H2.

destruct belong_adjacences_edges with a e v v0.
exact H.
apply H4.
destruct (H0 v v0).
apply H6.
destruct belong_edges_adjacences with a0 e0 v v0.
exact H1.
apply H8.
exact H2.
Qed.

Lemma Eqedges_adjacences : forall a a0 e e0, (adjacences_to_edges a0 e0)->(equal_list e e0)->(edges_to_adjacences e a)->(equal_adjacences a a0).
Proof.
intro.
unfold equal_list.
unfold equal_adjacences.
intros.
split ; intro.

destruct belong_edges_adjacences with a0 e0 u v.
exact H.
apply H4.
destruct (H0 (u,v)).
apply H5.

destruct belong_adjacences_edges with a e u v.
exact H1.
apply H8.
exact H2.

destruct belong_adjacences_edges with a e u v.
exact H1.
apply H3.
destruct (H0 (u,v)).
apply H6.

destruct belong_edges_adjacences with a0 e0 u v.
exact H.
apply H7.
exact H2.
Qed.

(*Maintenant, des propriétés de graphe*)

Definition connected_v (v : vertices) (x : vertex->vertex->nat->Prop) : Prop :=
forall u u0, (belong u v)->(belong u0 v)->(exists n, x u u0 n).

Definition empty (G : Graph) : Prop.
intro.
destruct G.
apply (v=nil).
Defined.


Definition connected (G : Graph) : Prop.
intro.
destruct G.
destruct p.
apply (connected_v v x).
Defined.

Definition deprived (G : Graph) (v : vertex) : Graph.
intros.
destruct G.
induction v0.
apply (nil,p).
destruct (vertex_dec a v).
apply IHv0.
destruct IHv0.
apply (a::v1,p).
Defined.


Lemma connected_decomposition : forall G : Graph, (connected G)->(not (empty G))->(exists u : vertex, (belong u v))

(*reste : isomorphisme de graphs, définition par matrice, union disjointe de graphes, intersection, union, Delta, puissance de graphe(?), algo de flot//flot(?), graphe chordal, cographe, graphe à distance héréditaire, clique, étoile, stable, décomposition modulaire (?)*)