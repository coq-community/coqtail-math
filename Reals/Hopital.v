Require Import Reals.
Require Import Fourier.
Open Scope R_scope.

Definition derivable_on_interval a b (Hab : a < b) f :=
  forall x, open_interval a b x -> derivable_pt f x.

Section Hopital.

Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : derivable f) (Dg : derivable g).
Hypotheses (Zf : limit1_in f (open_interval a b) 0 a).
Hypotheses (Zg : limit1_in g (open_interval a b) 0 a).
Hypothesis (Hlimder : limit1_in (fun x => derive f Df x / derive g Dg x) (open_interval a b) L a).

Lemma f_a_zero : f a = 0.
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


