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
        apply (Rlt_eq_compat (- e') (u n - l)); auto; ring_simplify; reflexivity. (* arg *)
        
        apply Req_lt_compat_r with (u n + e' - (u n - e')).
          rewrite ee'; ring.
          
          apply Radd_lt_cancel_r with (- e').
          apply (Rlt_eq_compat (u n - l') e'); auto; ring_simplify; reflexivity.
      
      apply Rlt_trans with (u n + e' - l).
        apply Radd_lt_cancel_r with (l - l' - e').
        apply (Rlt_eq_compat (- e') (u n - l')); auto; ring_simplify; reflexivity.
        
        apply Req_lt_compat_r with (u n + e' - (u n - e')).
          rewrite ee'; ring.
          
          apply Radd_lt_cancel_r with (- e').
          apply (Rlt_eq_compat (u n - l) e'); auto; ring_simplify; reflexivity.
  Qed.
  
End Rsequence.