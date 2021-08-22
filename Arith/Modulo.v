(*
(C) Copyright 2010, COQTAIL team

Project Info: http://sourceforge.net/projects/coqtail/

This library is free software; you can redistribute it and/or modify it
under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation; either version 2.1 of the License, or
(at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301,
USA.
*)

Require Import NArith.
Require Import Lia.
Require Import Max.

Inductive eqmod (n:nat) : nat -> nat -> Prop :=
     | eqmod_base : forall k, k < n -> eqmod n k k
     | eqmod_nS : forall k l, eqmod n k l -> eqmod n k (n + l).

Lemma pred_itere : forall n, 0 < n -> forall m, {k:nat | m < n} + {k | m = n + k}.
Proof.
intros n n_pos m ; induction m.
 left ; exists 0 ; assumption.
 case (Compare_dec.le_lt_dec (S m) n) ; intro Hyp.
 case (Compare_dec.le_lt_eq_dec _ _ Hyp) ; clear Hyp ; intro Hyp.
 left ; exists 0 ; assumption.
 right ; exists 0 ; rewrite Hyp ; trivial.
 case IHm ; intro H.
 left ; exists 0 ; apply False_ind ; destruct H as (_,Hf) ; lia.
 destruct H as (k,Hk) ; right ; exists (S k).
 rewrite <- plus_n_Sm ; rewrite Hk ; simpl ; reflexivity.
Qed.

Lemma eqmod_bounded : forall n m l, eqmod n l m -> l < n.
Proof.
intros n m l eqmodnl ; induction eqmodnl ; assumption.
Qed.

Lemma eqmod_uniqueness1 : forall n m l, l < n -> eqmod n l m -> forall p, p < n ->
      p <> l -> ~eqmod n p m. 
Proof.
intros n m l l_ub eqmodnl p p_ub p_neq Hf ;
 induction eqmodnl.
 inversion Hf ; intuition lia.
 apply IHeqmodnl.
 assumption.
 assumption.
 inversion Hf.
 assert (Temp := eqmod_bounded _ _ _ Hf).
 apply False_ind ; clear -H1 Temp ; intuition lia.
 assert (Temp := Plus.plus_reg_l _ _ _ H) ; rewrite <- Temp ; assumption.
Qed.

Lemma eqmod_uniqueness2 : forall n m l l', l < n -> l' < n -> eqmod n m l' -> eqmod n m l -> l = l'.
Proof.
intros n m l l' l_ub l'_ub eqmodnl eqmodnl' ; inversion eqmodnl'.
 inversion eqmodnl ; intuition lia.
 rewrite <- H1 in l_ub ; apply False_ind ; clear -l_ub ; intuition lia.
Qed.

Lemma eqmod_uniqueness : forall n m l l', eqmod n l m -> eqmod n l' m -> l = l'.
Proof.
intros n m l l' eqmodnl eqmodnl'.
 induction eqmodnl.
 induction eqmodnl'.
 reflexivity.
 apply False_ind ; intuition lia.
 apply IHeqmodnl ; inversion eqmodnl'.
 apply False_ind ; intuition lia.
 assert (Temp := Plus.plus_reg_l _ _ _ H) ;
 rewrite <- Temp ; assumption.
Qed.

Lemma disjoints_prelim : forall n, 0 < n -> forall M m, m < max n M ->
      {k | k < n /\ eqmod n k m /\ forall l, l <> k -> ~ eqmod n l m}.
Proof.
intros n n_pos M ; induction M ; intros m m_ub.
 rewrite max_l in m_ub ; [| intuition].
 exists m ; repeat split ; [assumption | |].
 constructor ; assumption.
 intros l l_neq Hyp ; apply l_neq ; apply eqmod_uniqueness with (n:=n) (m:=m).
 intuition.
 constructor ; assumption.
 case (Compare_dec.le_lt_dec m (max n M)) ; intro m_ub'.
 case (Compare_dec.le_lt_eq_dec _ _ m_ub') ; clear m_ub' ; intro m_ub'.
 apply IHM ; intuition.
 case (pred_itere _ n_pos m) ; intro Hyp.
  exists 0 ; apply False_ind ; destruct Hyp as (_,Hf).
  assert (Hf' : n <= m).
  apply Le.le_trans with (max n M) ; [apply Max.le_max_l | rewrite m_ub' ; intuition].
  intuition lia.
  destruct Hyp as (k,Hk).
  case (Compare_dec.le_lt_dec k n) ; intro Temp.
  case (Compare_dec.le_lt_eq_dec _ _ Temp) ; clear Temp ; intro Temp.
  exists k ; repeat split ; [assumption | |].
  rewrite Hk ; constructor ; constructor ; assumption.
  intros l l_neq eqmodnl ; assert (l_ub := eqmod_bounded _ _ _ eqmodnl) ;
  apply (eqmod_uniqueness1 _ _ _ l_ub eqmodnl _ Temp).
  intro Hf ; apply l_neq ; symmetry ; assumption.
  rewrite Hk ; constructor ; constructor ; assumption.
  exists 0 ; repeat split.
  assumption.
  rewrite Hk ; constructor.
  replace n with (n+0) in Temp by intuition ; rewrite Temp ; repeat constructor ; assumption.
  intros l l_neq eqmodnl ; rewrite Hk in eqmodnl.
  apply l_neq ; apply eqmod_uniqueness2 with (n:=n) (m:=l).
  apply (eqmod_bounded _ _ _ eqmodnl).
  assumption.
  inversion eqmodnl.
  apply False_ind ; intuition lia.
  assert (Temp2 := Plus.plus_reg_l _ _ _ H) ;
  replace n with (n+0) in Temp by intuition ; rewrite Temp2, Temp in H1.
  clear -H1 ; inversion H1.
  apply False_ind ; intuition lia.
  repeat (rewrite itere_S in H) ; assert (Temp2 := Plus.plus_reg_l _ _ _ H) ; rewrite <- Temp2 ;
  assumption.
  constructor.
  apply (eqmod_bounded _ _ _ eqmodnl).
  assert (k_ub : k < max n M).
  rewrite Hk in m_ub' ; intuition lia.
  destruct (IHM k k_ub) as (p, [p_ub [eqmodnp noteqmodnl]]) ; exists p ; repeat split.
  assumption.
  assert (H := eqmod_nS _ _ _ eqmodnp).
  rewrite Hk ; assumption.
  intros l l_neq_p eqmodnl.
  rewrite Hk in eqmodnl ; inversion eqmodnl.
  clear -H ; intuition lia.
  repeat (rewrite itere_S in H) ; assert (Temp2 := Plus.plus_reg_l _ _ _ H) ;
  replace n with (n+0) in Temp by intuition.
  rewrite Temp2 in H1.
  apply (noteqmodnl _ l_neq_p H1).
  exists 0 ; apply False_ind.
  assert (max n M = M).
  clear -m_ub m_ub' ; induction n.
  intuition.
  case (Max.max_dec (S n) M) ; intro H.
  rewrite H in m_ub'.
  case (Max.max_dec (S n) (S M)) ; intro H'.
  rewrite H' in m_ub ; apply False_ind ; intuition lia.
  assert (M < m).
  apply Lt.le_lt_trans with (max (S n) M).
  apply Max.le_max_r.
  rewrite H ; assumption.
  rewrite H' in m_ub.
  apply False_ind ; intuition lia.
  assumption.
  assert (m < max (S n) (S M)).
  apply Lt.lt_le_trans with (max n (S M)).
  assumption.
  generalize M ; clear ; induction n.
  intuition.
  intro M ; replace (max (S (S n)) (S M)) with (S (max (S n) M)) by intuition.
  replace (max (S n) (S M)) with (S (max n M)) by intuition.
  apply Le.le_n_S.
  destruct M.
  repeat (rewrite Max.max_comm ; simpl); intuition.
  apply IHn.
  simpl in H0.
  intuition lia.
Qed.

Lemma disjoints : forall n, 0 < n -> forall m,
      {k | k < n /\ eqmod n k m /\ forall l, l <> k -> ~ eqmod n l m}.
Proof.
intros n n_pos m ; apply disjoints_prelim with (M:= (S m)) ; intuition.
Qed.

Lemma surjectif : forall n m p, m < n -> eqmod n m (n * p + m).
Proof.
intros n m p m_ub ; induction p.
 replace (n * 0) with 0 by lia ; constructor ; assumption.
 replace ((n * S p) + m) with (n + ((n * p) + m)).
 constructor ; assumption.
 rewrite Mult.mult_succ_r ; lia.
Qed.

Lemma n_decomp : forall N n m p, 0 < n -> p < (S N) * n -> eqmod n m p -> {k | p = k * n + m}.
Proof.
intro N ; induction N ; intros n m p n_pos p_ub p_eqmodn.
 exists 0 ; inversion p_eqmodn.
 intuition.
 rewrite <- H1 in p_ub ; apply False_ind ; intuition lia.
 case (Compare_dec.le_lt_dec p ((S N) * n)) ; intro p_ub2.
 case (Compare_dec.le_lt_eq_dec _ _ p_ub2) ; intro H.
 apply (IHN _ _ _ n_pos H p_eqmodn).
  rewrite H in p_eqmodn.
  replace (S N * n) with (N * n + n) in p_eqmodn.
  destruct (IHN n m (N * n) n_pos) as (k, Hk).
  apply Mult.mult_lt_compat_r ; [constructor | apply n_pos].
  inversion p_eqmodn.
  apply False_ind.
  assert (N * n < 0).
  apply Plus.plus_lt_reg_l with n.
  intuition lia.
  apply (Lt.lt_n_O _ H3).
  replace l with (N * n) in H2.
  assumption.
  intuition lia.
  exists (S k) ; simpl ; rewrite <- Plus.plus_assoc ; rewrite <- Hk ; intuition.
  apply Plus.plus_comm.
  assert (Hrew : p = n + (p - n)).
  apply Minus.le_plus_minus.
  apply Le.le_trans with (S N * n) ; intuition lia;
  try (apply Le.le_trans with (S 0 * n) ; intuition ; apply Mult.mult_le_compat_r ;
  intuition).
  destruct (IHN n m (p-n) n_pos) as (k, Hk).
  apply Plus.plus_lt_reg_l with n.
  rewrite <- Hrew ; intuition.
  rewrite Plus.plus_comm in Hrew ; rewrite Hrew in p_eqmodn ; inversion p_eqmodn.
  apply False_ind ; apply Lt.lt_irrefl with n.
  apply Lt.lt_trans with (S N * n).
  intuition lia.
  apply Lt.lt_trans with p.
  assumption.
  rewrite Hrew ; assumption.
  assert (Hrew' : l = p - n) by intuition lia.
  rewrite Hrew' in H1 ; assumption.
  exists (S k) ; simpl ; rewrite <- Plus.plus_assoc ; rewrite <- Hk ; intuition.
Qed.
