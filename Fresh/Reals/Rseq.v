Require Import Raxiom Rconvenient Repsilon.
Require Import ZArith.

Module Rsequence (Import T : CReals).
  Module Rconvenient := (Rconvenient T). Import Rconvenient.
  Module Repsilon := (Repsilon T). Import Repsilon.
  Open Scope R_scope.
  
  Definition Rseq := nat -> R.
  
  Definition Rseq_add (a b : Rseq) : Rseq := fun n => a n + b n.
  Definition Rseq_mul (a b : Rseq) : Rseq := fun n => a n * b n.
  Definition Rseq_sub (a b : Rseq) : Rseq := fun n => a n - b n.
  Definition Rseq_opp (a : Rseq) : Rseq := fun n => - a n.
  
  (* There are bugs in the ring tactic: (ring_simplify; reflexivity > ring) *)
  (* Declaring a bigger setoid (e.g. for Rlt) would help *)
  (* The fourier tactic would also help *)
  Lemma Rseq_cv_unique : forall u l l',
    Rseq_cv u l -> Rseq_cv u l' -> l == l'.
  Proof.
    intros u l l' Cu Cu'.
    apply Rsub_lt_pos_eq; intros e epos.
    destruct (halfpos e epos) as (e', (e'pos, ee')).
    destruct (Cu e' e'pos) as (N, HN).
    destruct (Cu' e' e'pos) as (N', HN').
    pose (n := plus N N').
    destruct (HN n (le_plus_l _ _)) as (ule, eul).
    destruct (HN' n (le_plus_r _ _)) as (ul'e, eul').
    split.
      apply Rlt_trans with (u n + e' - l').
        apply Radd_lt_cancel_r with (l' - l - e').
        apply (Req_lt_compat (- e') (u n - l)); auto; ring_simplify; reflexivity. (* arg *)
        
        apply Req_lt_compat_r with (u n + e' - (u n - e')).
          rewrite ee'; ring.
          
          apply Radd_lt_cancel_r with (- e').
          apply (Req_lt_compat (u n - l') e'); auto; ring_simplify; reflexivity.
      
      apply Rlt_trans with (u n + e' - l).
        apply Radd_lt_cancel_r with (l - l' - e').
        apply (Req_lt_compat (- e') (u n - l')); auto; ring_simplify; reflexivity.
        
        apply Req_lt_compat_r with (u n + e' - (u n - e')).
          rewrite ee'; ring.
          
          apply Radd_lt_cancel_r with (- e').
          apply (Req_lt_compat (u n - l) e'); auto; ring_simplify; reflexivity.
  Qed.
  
  Lemma Rseq_add_cv_compat : forall u v lu lv,
    Rseq_cv u lu -> Rseq_cv v lv -> Rseq_cv (Rseq_add u v) (lu + lv).
  Proof.
    intros u v lu lv Hu Hv e epos.
    destruct (halfpos e epos) as (e', (e'pos, ee')).
    destruct (Hu e' e'pos) as (Nu, HNu).
    destruct (Hv e' e'pos) as (Nv, HNv).
    pose (N := plus Nu Nv).
    exists N; intros n Hn.
    unfold Rdist; unfold Rseq_add.
    split.
      apply (Req_lt_compat ((u n - lu) + (v n - lv)) (e' + e')).
        ring_simplify; reflexivity.
        rewrite ee'; reflexivity.
        apply Radd_lt_compat; apply HNu || apply HNv; unfold N in *; omega.
      apply (Req_lt_compat (- e' - e') ((u n - lu) + (v n - lv))).
        rewrite ee'; ring_simplify; reflexivity.
        ring_simplify; reflexivity.
        apply Radd_lt_compat; apply HNu || apply HNv; unfold N in *; omega.
  Qed.
  
  Lemma Rseq_opp_cv_compat : forall u l,
    Rseq_cv u l -> Rseq_cv (Rseq_opp u) (- l).
  Proof.
    intros u l C.
    intros e ep; destruct (C e ep) as (N, HN); exists N; intros n Hn.
    destruct (HN n Hn) as (A, B); unfold Rdist, Rseq_opp.
    split; apply Ropp_lt_contravar_reciprocal; eapply Req_lt_compat;
      [ | | apply B | | | apply A ]; ring_simplify; reflexivity.
  Qed.
  
End Rsequence.