Require Import Reals.
Require Import Rsequence_def Rsequence_facts Rsequence_cv_facts.

Require Import List.
Require Import Option.
Require Import Ass_handling.

Inductive rseq :=
  | val : forall (n : nat), rseq
  | rseq_opp : forall (r : rseq), rseq
  | rseq_plus : forall (rl rr : rseq), rseq.

Inductive rseq_limit :=
  | minus_inf : rseq_limit
  | finite : forall (l : R), rseq_limit
  | plus_inf : rseq_limit.

Definition is_limit r l := match l with
  | minus_inf => Rseq_cv_neg_infty r
  | finite l => Rseq_cv r l
  | plus_inf => Rseq_cv_pos_infty r
end.

Lemma is_limit_ext : forall r s k l,
  is_limit r k ->
  r == s -> k = l ->
  is_limit s l.
Proof.
intros r s k [] Hrk Hrs Hkl ;
 [ eapply Rseq_cv_neg_infty_eq_compat
 | eapply Rseq_cv_eq_compat ; [symmetry |]
 | eapply Rseq_cv_pos_infty_eq_compat ]
 ; subst ; eassumption.
Qed.

Definition Rseq_with_limit := {r : Rseq & {l : rseq_limit | is_limit r l}}.

Definition rseq_limit_opp l := match l with
  | minus_inf => plus_inf
  | finite u  => finite (- u)
  | plus_inf  => minus_inf
end.

Lemma rseq_limit_opp_is_limit : forall r l,
  is_limit r l ->
  is_limit (- r) (rseq_limit_opp l).
Proof.
intros r [] Hl ; simpl ;
 [ apply Rseq_cv_neg_infty_opp_compat
 | apply Rseq_cv_opp_compat
 | apply Rseq_cv_pos_infty_opp_compat] ;
 assumption.
Qed.

Definition rseq_limit_add ll lr := match ll, lr with
  | minus_inf , plus_inf  => None
  | plus_inf  , minus_inf => None
  | minus_inf , _         => Some minus_inf
  | _         , minus_inf => Some minus_inf
  | plus_inf , _         => Some plus_inf
  | _         , plus_inf => Some plus_inf
  | finite u , finite v  => Some (finite (u + v))
end.

Fixpoint comp_limit (r : rseq) (env : list Rseq_with_limit) : option rseq_limit :=
match r with
  | val n => Bind (nth_error env n) (fun x => Return (projT1 (projT2 x)))
  | rseq_opp r => Bind (comp_limit r env) (fun l => Some (rseq_limit_opp l))
  | rseq_plus rl rr => Bind (comp_limit rl env) (fun ll =>
                       Bind (comp_limit rr env) (fun lr => rseq_limit_add ll lr))
end.

Fixpoint comp_rseq (r : rseq) (env : list Rseq_with_limit) := match r with
  | val n => Bind (nth_error env n) (fun un => Some (projT1 un))
  | rseq_opp r => Bind (comp_rseq r env) (fun un => Some (Rseq_opp un))
  | rseq_plus rl rr => Bind (comp_rseq rl env) (fun un =>
                       Bind (comp_rseq rr env) (fun vn => Some (Rseq_plus un vn)))
end.

Ltac fold_is_limit := match goal with
  | |- Rseq_cv ?r ?l => fold (is_limit r (finite l))
  | |- Rseq_cv_neg_infty ?r => fold (is_limit r minus_inf)
  | |- Rseq_cv_pos_infty ?r => fold (is_limit r plus_inf)
end.

Lemma comp_rseq_limit_compat : forall r env un l,
  comp_rseq r env = Some un ->
  comp_limit r env = Some l ->
  is_limit un l.
Proof.
intros r env ; induction r ; intros un l Hun Hl ; simpl in *.
 destruct (nth_error env n) as [Hget |].
  inversion Hun ; inversion Hl ; apply (projT2 (projT2 Hget)).
  inversion Hl.
 destruct (comp_rseq r env) as [vn |] ; [| inversion Hun] ;
  destruct (comp_limit r env) as [lo |] ; [| inversion Hl] ;
  inversion Hun ; inversion Hl.
  apply rseq_limit_opp_is_limit, IHr ; reflexivity.
 destruct (comp_rseq r1 env) as [vn |] ; [| inversion Hun] ;
  destruct (comp_limit r1 env) as [ll |] ; [| inversion Hl] ;
  destruct (comp_rseq r2 env) as [wn |] ; [| inversion Hun] ;
  destruct (comp_limit r2 env) as [lr |] ; [| inversion Hl].
   destruct ll ; destruct lr ; inversion Hun ; inversion Hl ;
   subst.
    apply Rseq_cv_neg_infty_plus_compat ; fold_is_limit ;
     [apply IHr1 | apply IHr2] ; reflexivity.
    eapply Rseq_cv_finite_plus_neg_infty_l ; fold_is_limit ;
     [apply IHr1 | apply IHr2] ; reflexivity.
    eapply Rseq_cv_finite_plus_neg_infty_r ; fold_is_limit ;
     [apply IHr1 | apply IHr2] ; reflexivity.
    eapply Rseq_cv_plus_compat ; fold_is_limit ;
     [apply IHr1 | apply IHr2] ; reflexivity.
    eapply Rseq_cv_finite_plus_pos_infty_r ; fold_is_limit ;
     [apply IHr1 | apply IHr2] ; reflexivity.
    eapply Rseq_cv_finite_plus_pos_infty_l ; fold_is_limit ;
     [apply IHr1 | apply IHr2] ; reflexivity.
    apply Rseq_cv_pos_infty_plus_compat ; fold_is_limit ;
     [apply IHr1 | apply IHr2] ; reflexivity.
Qed.

Definition rseq_precondition r env un l :=
match comp_rseq r env with
  | None    => False
  | Some vn =>
  match comp_limit r env with
    | None => False
    | Some v => (un == vn) /\ (l = v)
  end
end.

Lemma tactic_correctness : forall r env un l,
   rseq_precondition r env un l ->
   is_limit un l.
Proof.
unfold rseq_precondition ; intros r env un l ;
 destruct_eq (comp_rseq r env) ;
 destruct_eq (comp_limit r env) ;
 intros [].
 intros ; eapply is_limit_ext ;
  [ eapply comp_rseq_limit_compat | |] ;
  symmetry ; eassumption.
Qed.