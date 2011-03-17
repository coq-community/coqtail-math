Require Import Reals.
Require Import Fourier.
Require Import C_n_def.
Require Import Cauchy_lipschitz. (* TODO on importe des trucs qui parlent de Cn *)
Require Import Rextensionality.
Open Scope R_scope.

Definition derivable_on_interval a b (Hab : a < b) f :=
  forall x, open_interval a b x -> derivable_pt f x.

Section FirstGenHopital.

Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : derivable f) (Dg : derivable g).
Hypotheses (Zf : limit1_in f (D_x no_cond a) 0 a).
Hypotheses (Zg : limit1_in g (D_x no_cond a) 0 a).
Hypothesis (g_not_0 : forall x, open_interval a b x -> derive g Dg x <> 0 /\ g x <> 0).
Hypothesis (Hlimder : limit1_in (fun x => derive f Df x / derive g Dg x) (open_interval a b) L a).

Lemma f_a_zero : f a = 0.
Proof.
assert (continuity f). apply derivable_continuous. apply Df. 
unfold continuity in H. unfold continuity_pt in H. unfold continue_in in H.
specialize (H a).
eapply single_limit; [ | apply H | apply Zf ].
unfold adhDa. intros. exists (a + alp / 2).
split.
constructor. constructor.
intro. fourier.
unfold R_dist. ring_simplify (a + alp / 2 - a).
rewrite Rabs_right; fourier.
Qed.

Lemma g_a_zero : g a = 0.
assert (continuity g). apply derivable_continuous. apply Dg. 
unfold continuity in H. unfold continuity_pt in H. unfold continue_in in H.
specialize (H a).
eapply single_limit; [ | apply H | apply Zg ].
unfold adhDa. intros. exists (a + alp / 2).
split.
constructor. constructor.
intro. fourier.
unfold R_dist. ring_simplify (a + alp / 2 - a).
rewrite Rabs_right; fourier.
Qed.

(*
Lemma Rabs_div2 : forall a b c e, e > 0 ->
  Rabs (a - b) < e / 2 ->
  Rabs (b - c) < e / 2 ->
    Rabs (a - c) < e.
Proof.
  intros x y z e epos Hxy Hyz.
  replace (x - z) with ((x - y) + (y - z)) by ring.
  replace e with (e / 2 + e / 2) by field.
  eapply Rle_lt_trans.
    apply Rabs_triang.
    fourier.
Qed.
*)

Theorem Hopital_finite_zero_weak : limit1_in (fun x => f x / g x) (open_interval a b) L a.
Proof.
unfold limit1_in, limit_in.
intros.
unfold limit1_in, limit_in in Hlimder.
specialize (Hlimder eps H).
destruct Hlimder as [alp [Halp Hlim]].
exists alp. split. assumption.
intros.
assert (Hacc2 : forall x, open_interval a b x -> exists c, f x / g x = derive f Df c / derive g Dg c /\ a < c < x).
generalize MVT.
intros.
specialize (H1 f g a x0).
assert (forall c, a < c < x0 -> derivable_pt f c). intros. apply Df.
assert (forall c, a < c < x0 -> derivable_pt g c). intros. apply Dg.
specialize (H1 H3 H4).
assert (a < x0); unfold open_interval in H2; intuition.
assert (forall c : R, a <= c <= x0 -> continuity_pt f c).
intros. apply (derivable_continuous _ Df).
assert (forall c, a <= c <= x0 -> continuity_pt g c).
intros. apply (derivable_continuous _ Dg).
specialize (H2 H1 H9).
destruct H2 as [c [P H2]].
exists c. split.
rewrite g_a_zero in H2. rewrite f_a_zero in H2. do 2 rewrite Rminus_0_r in H2.
unfold derive.
apply (Rmult_eq_reg_l (g x0)).
rewrite (pr_nu f c _ (H3 c P)). unfold Rdiv. do 2 rewrite <- Rmult_assoc.
rewrite H2. rewrite (pr_nu g c _ (Dg c)).
field. generalize (g_not_0 c). generalize (g_not_0 x0).
intros H01 H02.
unfold open_interval in H01, H02.
unfold derive in H01, H02.
assert (c < b). eapply Rlt_trans with x0; intuition. destruct P; assumption.
destruct P;
intuition.
specialize (g_not_0 x0). 
unfold open_interval in g_not_0. intuition.
apply P.

destruct H0.
specialize (Hacc2 x H0).
destruct Hacc2 as (c, Haccc).
specialize (Hlim c). simpl in *. unfold R_dist in *.
assert (open_interval a b c /\ Rabs (c - a) < alp).
split.
unfold open_interval. split; intuition. apply Rlt_trans with x; intuition. apply H0.
destruct Haccc. destruct H3.
rewrite Rabs_right. rewrite Rabs_right in H1.
fourier. fourier. fourier.
specialize (Hlim H2).
destruct Haccc.
rewrite H3. apply Hlim.
Qed.

End FirstGenHopital.


Section VerySimplHopital.

Variables f g : R -> R.
Variables a b c L : R.

Hypothesis Hab : c < a < b.
Hypotheses (Cf : C 1 f) (Cg : C 1 g).
Definition Df := C_Sn_derivable f O Cf.
Definition Dg := C_Sn_derivable g O Cg.

(* Hypothesis (Zf : limit1_in f (D_x no_cond a) 0 a) (Zg : limit1_in g (D_x no_cond a) 0 a). *)
Hypothesis f_a_zero : f a = 0.
Hypothesis g_a_zero : g a = 0.
Hypothesis g_not_zero : forall x, g x <> 0.
Hypothesis (Hg_not_0 : derive g Dg a <> 0).

Hypothesis (Hlimder : limit1_in (fun x => derive f Df x / derive g Dg x) (D_x no_cond a) L a).


Lemma f'a_lim : limit1_in (derive f Df) (D_x no_cond a) (derive f Df a) a.
Proof.
 assert (continuity (derive f Df)).
  inversion Cf. inversion H0. apply continuity_ext with (derive f pr).
   intro. apply derive_ext. intro. reflexivity.

   apply H1.

  apply H.
Qed.

Lemma g'a_lim : limit1_in (derive g Dg) (D_x no_cond a) (derive g Dg a) a. Proof.
Proof.
 assert (continuity (derive g Dg)).
  inversion Cg. inversion H0. apply continuity_ext with (derive g pr).
   intro. apply derive_ext. intro. reflexivity.

   apply H1.

  apply H.
Qed.

Lemma L_decomp : L = derive f Df a / derive g Dg a. Proof.
 assert (limit1_in (fun x => derive f Df x / derive g Dg x) (D_x no_cond a) (derive f Df a / derive g Dg a) a).
  unfold Rdiv. apply limit_mul.
   apply f'a_lim.

   apply limit_inv.
    apply g'a_lim.

    apply Hg_not_0.

   eapply single_limit with (fun x => derive f Df x / derive g Dg x) (D_x no_cond a) a.
    intros alp Halp. exists (a + alp / 2). split.
     constructor.
      constructor.

      intro. fourier.

     unfold R_dist. ring_simplify (a + alp / 2 - a). apply Rle_lt_trans with (alp / 2).
      assert (alp / 2 > 0).
       fourier.
      
       rewrite Rabs_right. 
        intuition. 
        
        fourier.
        
        fourier.
        
        assumption.
        
        assumption.
Qed.


Theorem Hopital_finite_zero_weak' : limit1_in (fun x => f x / g x) (D_x no_cond a) L a.
Proof.
 assert (Hder' : limit1_in (fun x : R => derive f Df x / derive g Dg x)
      (D_x no_cond a) (derive f Df a / derive g Dg a) a).
  apply limit_mul.
   apply f'a_lim.

   apply limit_inv.
    apply g'a_lim.

    apply Hg_not_0.

   rewrite L_decomp. apply limit1_ext with (fun x : R => ((f x - f a) / (x - a)) * ((x - a) / (g x - g a))).
    intros x (Hax, Hxb).
      rewrite f_a_zero, g_a_zero. unfold Rdiv. rewrite <- Rmult_assoc. rewrite (Rmult_assoc (f x - R0)).
      replace (/ (x - a) * (x - a)) with 1.
      rewrite Rminus_0_r.
     rewrite Rminus_0_r. ring.

     intuition.

    apply limit_mul.
     (* f'(a) *)
        generalize (Df a); intros (l, Hl).
        intros e epos.
        destruct (Hl e epos) as (d, dpos).
        exists d; split.
          apply d.
          intros x (Hxab, Hxd).
          assert (Nxa : x - a <> 0). destruct Hxab. intro. apply H0. intuition.
          unfold dist in Hxd; simpl in Hxd; unfold R_dist in Hxd.
          specialize (dpos (x - a) Nxa Hxd).
          simpl.
          assert (Hdl : derive f Df a = l).
            unfold derive, derive_pt.
            destruct (Df a). simpl. unfold derivable_pt_abs in *. apply uniqueness_limite with f a; assumption. 
          
          rewrite Hdl.
          ring_simplify (a + (x - a)) in dpos.
          apply dpos.
        
        (* g'(a) *)
        apply limit1_ext with (fun x : R => / ((g x - g a) / (x - a))).
          intros x (Hax, Hxb).
          apply Rinv_Rdiv. 
          rewrite g_a_zero.
          rewrite Rminus_0_r.
          apply g_not_zero; intuition.
          intuition.

          apply limit_inv.
            generalize (Dg a); intros (l, Hl).
        intros e epos.
        destruct (Hl e epos) as (d, dpos).
        exists d; split.
          apply d.
          intros x (Hxab, Hxd).
          assert (Nxa : x - a <> 0). destruct Hxab. intro. apply H0. intuition.
          unfold dist in Hxd; simpl in Hxd; unfold R_dist in Hxd.
          specialize (dpos (x - a) Nxa Hxd).
          simpl.
          assert (Hdl : derive g Dg a = l).
            unfold derive, derive_pt.
            destruct (Dg a). simpl. unfold derivable_pt_abs in *. apply uniqueness_limite with g a; assumption. 
          
          rewrite Hdl.
          ring_simplify (a + (x - a)) in dpos.
          apply dpos.
          apply Hg_not_0.
Qed.

End VerySimplHopital.

(*
Section SimplHopital.

Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
(* Hypotheses (Df : derivable f) (Dg : derivable g). *)
Hypotheses (Cf : C 1 f) (Cg : C 1 g).
Hypotheses g_not_zero : forall x, x <> a -> g x <> 0.
Definition Df := C_Sn_derivable f O Cf.
Definition Dg := C_Sn_derivable g O Cg.
Hypotheses (Zf : limit1_in f no_cond 0 a).
Hypotheses (Zg : limit1_in g no_cond 0 a).
Hypothesis (Hlimder : limit1_in (fun x => derive f Df x / derive g Dg x) no_cond L a).

Lemma f_a_zero : f a = 0.
Proof.
symmetry. eapply tech_limit; [ | apply Zf].
constructor.
Qed.

Lemma g_a_zero : g a = 0.
Proof.
symmetry. eapply tech_limit; [ | apply Zg].
constructor.
Qed.

Lemma g'a_not_zero : derive g Dg a <> 0.
Proof.
 intro.
unfold derive, derive_pt, Dg in H.
destruct (C_Sn_derivable g 0 Cg a).
simpl in H. subst.



Admitted.

(*
Lemma g_not_zero : { c | a < c /\ forall x, a < x <= c -> g x <> 0 }.
Admitted.

Definition c := projT1 g_not_zero.
Definition Hc : a < c /\ forall x, a < x <= c -> g x <> 0 := projT2 g_not_zero.
*)

Lemma f'a_lim : limit1_in (derive f Df) (D_x no_cond a) (derive f Df a) a.
Proof.
assert (continuity (derive f Df)).
 inversion Cf. inversion H0. 
 apply continuity_ext with (derive f pr).
 intro. apply derive_ext.
 intro. reflexivity.
  unfold derive, derive_pt, Df. simpl. simpl. admit.
 apply H.
Qed.

Lemma g'a_lim : limit1_in (derive g Dg) (D_x no_cond a) (derive g Dg a) a.
Proof.
assert (continuity (derive g Dg)).
 admit.
 apply H.
Qed.

Lemma L_decomp : L = derive f Df a / derive g Dg a.
Admitted.

Theorem Hopital_finite_zero_weak : limit1_in (fun x => f x / g x) (D_x no_cond a) L a.
Proof.
  assert (Hder' : limit1_in (fun x : R => derive f Df x / derive g Dg x)
      (D_x no_cond a) (derive f Df a / derive g Dg a) a).
    apply limit_mul.
      apply f'a_lim.
      apply limit_inv.
        apply g'a_lim.
        apply g'a_not_zero.
    
    rewrite L_decomp.
    
    apply limit1_ext with (fun x : R => ((f x - f a) / (x - a)) * ((x - a) / (g x - g a))).
      intros x (Hax, Hxb).
      rewrite f_a_zero, g_a_zero.
      field; split.
        
        apply g_not_zero. intro; intuition.
        intuition.
      
      apply limit_mul.
        (* f'(a) *)
        generalize (Df a); intros (l, Hl).
        intros e epos.
        destruct (Hl e epos) as (d, dpos).
        exists d; split.
          apply d.
          intros x (Hxab, Hxd).
          assert (Nxa : x - a <> 0). destruct Hxab. intro. apply H0. intuition.
          unfold dist in Hxd; simpl in Hxd; unfold R_dist in Hxd.
          specialize (dpos (x - a) Nxa Hxd).
          simpl.
          assert (Hdl : derive f Df a = l).
            unfold derive, derive_pt.
            admit (* blabla ~ Hl *).
          
          rewrite Hdl.
          ring_simplify (a + (x - a)) in dpos.
          apply dpos.
        
        (* g'(a) *)
        apply limit1_ext with (fun x : R => / ((g x - g a) / (x - a))).
          intros x (Hax, Hxb).
          field.
          split; [ | intro; intuition ].
          rewrite g_a_zero.
          rewrite Rminus_0_r.
          apply g_not_zero; intuition.
          
          apply limit_inv.
            admit. (* même chose que pour f'(a) : remplir le blabla ~ Hl d'abord *)
            apply g'a_not_zero.
Qed.



End SimplHopital.
*)
(*
Section Hopital.

Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : derivable f) (Dg : derivable g).
Hypotheses (Zf : limit1_in f (open_interval a b) 0 a).
Hypotheses (Zg : limit1_in g (open_interval a b) 0 a).
Hypothesis (Hlimder : limit1_in (fun x => derive f Df x / derive g Dg x) (open_interval a b) L a).

Lemma f_a_zero : f a = 0.
Proof.
Admitted.

Lemma g_a_zero : g a = 0.
Admitted.

Lemma g'a_not_zero : derive g Dg a <> 0.
Admitted.

Lemma g_not_zero : { c | a < c /\ forall x, a < x <= c -> g x <> 0 }.
Admitted.

Definition c := projT1 g_not_zero.
Definition Hc : a < c /\ forall x, a < x <= c -> g x <> 0 := projT2 g_not_zero.

Lemma Rabs_div2 : forall a b c e, e > 0 ->
  Rabs (a - b) < e / 2 ->
  Rabs (b - c) < e / 2 ->
    Rabs (a - c) < e.
Proof.
  intros x y z e epos Hxy Hyz.
  replace (x - z) with ((x - y) + (y - z)) by ring.
  replace e with (e / 2 + e / 2) by field.
  eapply Rle_lt_trans.
    apply Rabs_triang.
    fourier.
Qed.

Lemma f'a_lim : limit1_in (derive f Df) (open_interval a b) (derive f Df a) a.
Proof.
  intros e epos.
  pose (e' := e / 2).
  assert (e'pos : e' > 0) by admit.
  unfold derive, derive_pt.
  
  (* Distance between fx-fa/x-a and f'a *)
  remember (Df a) as Dfa.
  destruct Dfa as (f'a, Hf'a).
  simpl.
  generalize (Hf'a e' e'pos); intros Hffa.
  destruct Hffa as (d1, Hd1).
  
  unfold dist; simpl; unfold R_dist.
  
  exists (d1 / 8); split.
    admit (* OK *).
    
    intros x ((Hax, Hxb), Hxd).
    apply Rabs_div2 with ((f x - f a) / (x - a)).
      apply epos.
      
      (* faire ça avec x ... appliquer la compatibilité de la limite avec un truc compliqué ? *)
      (* ou juste du découpage de epsilon ? *)
      admit (* difficult part *).
      
      assert (Nax : x - a <> 0) by (intro; fourier).
      assert (Hxdw : Rabs (x - a) < d1) by admit.
      specialize (Hd1 (x - a) Nax Hxdw).
      replace (a + (x - a)) with x in Hd1 by ring.
      apply Hd1.
Qed.

Lemma g'a_lim : limit1_in (derive g Dg) (open_interval a b) (derive g Dg a) a.
Admitted.

Lemma L_decomp : L = derive f Df a / derive g Dg a.
Admitted.

Theorem Hopital_finite_zero_weak : limit1_in (fun x => f x / g x) (open_interval a c) L a.
Proof.
  assert (Hder' : limit1_in (fun x : R => derive f Df x / derive g Dg x)
      (open_interval a b) (derive f Df a / derive g Dg a) a).
    apply limit_mul.
      apply f'a_lim.
      apply limit_inv.
        apply g'a_lim.
        apply g'a_not_zero.
    
    rewrite L_decomp.
    
    apply limit1_ext with (fun x : R => ((f x - f a) / (x - a)) * ((x - a) / (g x - g a))).
      intros x (Hax, Hxb).
      rewrite f_a_zero, g_a_zero.
      field; split.
        apply Hc; split; fourier.
        intro; fourier.
      
      apply limit_mul.
        (* f'(a) *)
        generalize (Df a); intros (l, Hl).
        intros e epos.
        destruct (Hl e epos) as (d, dpos).
        exists d; split.
          apply d.
          intros x (Hxab, Hxd).
          assert (Nxa : x - a <> 0) by (intro; destruct Hxab; fourier).
          unfold dist in Hxd; simpl in Hxd; unfold R_dist in Hxd.
          specialize (dpos (x - a) Nxa Hxd).
          simpl.
          assert (Hdl : derive f Df a = l).
            unfold derive, derive_pt.
            admit (* blabla ~ Hl *).
          
          rewrite Hdl.
          ring_simplify (a + (x - a)) in dpos.
          apply dpos.
        
        (* g'(a) *)
        apply limit1_ext with (fun x : R => / ((g x - g a) / (x - a))).
          intros x (Hax, Hxb).
          field.
          split; [ | intro; fourier ].
          rewrite g_a_zero.
          rewrite Rminus_0_r.
          apply Hc; split; fourier.
          
          apply limit_inv.
            admit. (* même chose que pour f'(a) : remplir le blabla ~ Hl d'abord *)
            apply g'a_not_zero.
Qed.

Definition pderive a b (Hab : a < b) f
  (Df : derivable_on_interval a b Hab f) x :=
    match Rlt_le_dec a x with
    | left Hax =>
        match Rlt_le_dec x b with
        | left Hxb => derive_pt f x (Df x (conj Hax Hxb))
        | right _ => 0
        end
    | right _ => 0
    end.

Theorem Hopital_finite_zero :
  forall f g c b (Hcb : c < b) L
    (Df : derivable_on_interval c b Hcb f)
    (Dg : derivable_on_interval c b Hcb g),
    limit1_in f (open_interval c b) 0 c -> 
    limit1_in g (open_interval c b) 0 c -> 
    limit1_in (fun x => pderive c b Hcb f Df x / pderive c b Hcb g Dg x) (open_interval c b) L c ->
      limit1_in (fun x => f x / g x) (open_interval c b) L c.
Admitted.
*)
