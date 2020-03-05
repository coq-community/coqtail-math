Require Import Reals.
Require Import Lra.
Require Import Rfunction_classes_def.
Require Import Cauchy_lipschitz. (* TODO on importe des trucs qui parlent de Cn *)
Require Import Rextensionality.
Open Scope R_scope.

(*
TODO check, rename, indent, and comment
*)

(* 
This file contains a proof of the Hopital's rule.
Due to the huge number of different cases we provide the user with some lemmas corresponding to
the cases of the Hopital's rule

How to use this file ?
There are 4 parameters: 
- The limit can be when x -> a+(the lemmas has a suffix : _right) or when x -> a- (the lemmas have a suffix : _left)
(* TODO change the names accordingly *)
- The limit of g is either + infinity, -infinity or 0
- The limit L of (f' / g') is either finite, +infinity or -infinity

********Not supported*********
If you want to reason about limits like x -> + infinity or x -> - infinity, we suggest that you change the variable
x -> 1 / t and then use this file with limits: t -> 0+ or t -> 0- 
******************************


So, an example of a specification can be : 

"Theorem Hopital_g0_Lfin_right :

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zf: lim_{x -> a+} f = 0
Zg: lim_{x -> a+} g = 0
g_not_0: \forall x \in ]a; b[, g' x <> 0 /\ g x <> 0
Hlimder: lim_{x -> a+} f' / g' = L    (with L \in R)
-----------------------------------------------------
lim_{x -> a+} f / g = L"



Exhaustive lemmas usable:
- Hopital_g0_Lfin_right
- Hopital_g0_Lpinf_right
- Hopital_g0_Lninf_right
- Hopital_gpinf_Lfin_right
- Hopital_gpinf_Lpinf_right
- Hopital_gpinf_Lninf_right
- Hopital_gninf_Lfin_right
- Hopital_gninf_Lpinf_right
- Hopital_gninf_Lninf_right
- Hopital_g0_Lfin_left
- Hopital_g0_Lpinf_left
- Hopital_g0_Lninf_left
- Hopital_gpinf_Lfin_left
- Hopital_gpinf_Lpinf_left
- Hopital_gpinf_Lninf_left
- Hopital_gninf_Lfin_left
- Hopital_gninf_Lpinf_left
- Hopital_gninf_Lninf_left


*)



Definition derivable_on_interval a b (Hab : a < b) f :=
  forall x, open_interval a b x -> derivable_pt f x.

Section Definitions.

Definition limit_div_pos f (I : R -> Prop) a := forall m, m > 0 -> 
  exists alp, alp > 0 /\
    forall x, I x -> R_dist x a < alp -> m < f x.

Definition limit_div_neg f (I : R -> Prop) a := forall m, m > 0 -> 
  exists alp, alp > 0 /\ 
    forall x, I x -> R_dist x a < alp -> -m > f x.

Lemma limit_div_Ropp : forall a b g, a < b -> 
  limit_div_neg g (open_interval a b) a -> 
    limit_div_pos (fun x : R => - g x) (open_interval a b) a.
Proof.
  intros. unfold limit_div_pos, limit_div_neg in *. intros. specialize (H0 m H1).
  destruct H0. exists x. split.
   now intuition.
   
   intros. destruct H0. specialize (H4 x0 H2 H3). lra.
Qed.

Lemma limit_div_pos_inv : forall f a b, limit_div_neg (fun x => - f x) (open_interval a b) a ->
   limit_div_pos f (open_interval a b) a.
Proof.
intros.
unfold limit_div_pos, limit_div_neg in *.
intros m Hm. specialize (H m Hm).
destruct H as [alp [Halp Hsolve]].
exists alp. split. assumption.
intros. specialize (Hsolve x H H0).
lra.
Qed.

Lemma limit_div_neg_inv : forall f a b, limit_div_pos (fun x => - f x) (open_interval a b) a ->
   limit_div_neg f (open_interval a b) a.
Proof.
intros.
unfold limit_div_pos, limit_div_neg in *.
intros m Hm. specialize (H m Hm).
destruct H as [alp [Halp Hsolve]].
exists alp. split. assumption.
intros. specialize (Hsolve x H H0).
lra.
Qed.

Lemma limit_div_neg_ext : forall f g (I : R -> Prop) a, (forall x, I x -> f x = g x) ->
  limit_div_neg f I a -> limit_div_neg g I a.
Proof.
intros.
unfold limit_div_neg in *.
intros m Hm. specialize (H0 m Hm).
destruct H0 as [alp [Halp Hsolve]].
exists alp. split. assumption.
intros. specialize (Hsolve x H0 H1).
rewrite <- H. apply Hsolve.
apply H0.
Qed.

Lemma limit_div_pos_ext : forall f g (I : R -> Prop) a, (forall x, I x -> f x = g x) ->
  limit_div_pos f I a -> limit_div_pos g I a.
Proof.
intros.
unfold limit_div_neg in *.
intros m Hm. specialize (H0 m Hm).
destruct H0 as [alp [Halp Hsolve]].
exists alp. split. assumption.
intros. specialize (Hsolve x H0 H1).
rewrite <- H. apply Hsolve.
apply H0.
Qed.


Lemma limit_div_pos_open : forall a b b' f, 
  open_interval a b b' -> limit_div_pos f (open_interval a b') a -> limit_div_pos f (open_interval a b) a.
Proof.
intros.
unfold limit_div_pos in *. intros m Hm.
destruct (H0 m Hm) as [alp [Halp Hsolve]].
exists (Rmin alp (b' - a)). split. apply Rmin_Rgt_r. split; destruct H; lra. 
intros. assert (x < b').
unfold R_dist in H2. rewrite Rabs_right in H2. replace b' with ((b' - a) + a) by ring.
assert (x - a < b' - a). apply Rlt_le_trans with (Rmin alp (b'- a)). apply H2.
apply Rmin_r. lra. destruct H1; lra.
apply Hsolve. split. apply H1. apply H3. apply Rlt_le_trans with (Rmin alp (b'-a)).
apply H2. apply Rmin_l.
Qed.

Lemma limit_div_neg_open : forall a b b' f, 
  open_interval a b b' -> limit_div_neg f (open_interval a b') a -> limit_div_neg f (open_interval a b) a.
Proof.
intros.
unfold limit_div_neg in *. intros m Hm.
destruct (H0 m Hm) as [alp [Halp Hsolve]].
exists (Rmin alp (b' - a)). split. apply Rmin_Rgt_r. split; destruct H; lra. 
intros. assert (x < b').
unfold R_dist in H2. rewrite Rabs_right in H2. replace b' with ((b' - a) + a) by ring.
assert (x - a < b' - a). apply Rlt_le_trans with (Rmin alp (b'- a)). apply H2.
apply Rmin_r. lra. destruct H1; lra.
apply Hsolve. split. apply H1. apply H3. apply Rlt_le_trans with (Rmin alp (b'-a)).
apply H2. apply Rmin_l.
Qed.

Lemma limit_div_pos_opp : forall a b g, limit_div_pos g (open_interval a b) b -> 
  limit_div_pos (fun x : R => g (- x)) (open_interval (- b) (- a)) (- b). 
Proof.
intros.
unfold limit_div_pos in *.
intros m Hm. destruct (H m Hm) as [alp [Halp Hsolve]].
exists alp. split. apply Halp. intros.
assert (Hopen : open_interval a b (-x)). split; destruct H0; lra.
assert (Hdist : R_dist (-x) b < alp). unfold R_dist in *.
replace (-x - b) with (- (x + b)) by ring.
rewrite Rabs_Ropp. ring_simplify (x -- b) in H1. apply H1.
specialize (Hsolve (-x) Hopen Hdist).
apply Hsolve.
Qed.

Lemma limit_div_neg_opp : forall a b g, limit_div_neg g (open_interval a b) b -> 
  limit_div_neg (fun x : R => g (- x)) (open_interval (- b) (- a)) (- b). 
Proof.
intros.
unfold limit_div_neg in *.
intros m Hm. destruct (H m Hm) as [alp [Halp Hsolve]].
exists alp. split. apply Halp. intros.
assert (Hopen : open_interval a b (-x)). split; destruct H0; lra.
assert (Hdist : R_dist (-x) b < alp). unfold R_dist in *.
replace (-x - b) with (- (x + b)) by ring.
rewrite Rabs_Ropp. ring_simplify (x -- b) in H1. apply H1.
specialize (Hsolve (-x) Hopen Hdist).
apply Hsolve.
Qed.

Lemma limit_div_pos_imp :
forall (f : R -> R) (D D1 : R -> Prop) (l : R),
  (forall x0 : R, D1 x0 -> D x0) -> limit_div_pos f D l -> limit_div_pos f D1 l.
Proof.
intros.
unfold limit_div_pos in *.
intros m Hm.
specialize (H0 m Hm).
destruct H0 as [alp [Halp Hsolve]].
exists alp. split.
apply Halp.
intros. assert (D x).
intuition.
specialize (Hsolve x H2 H1). apply Hsolve.
Qed.

Lemma limit_div_neg_imp :
forall (f : R -> R) (D D1 : R -> Prop) (l : R),
  (forall x0 : R, D1 x0 -> D x0) -> limit_div_neg f D l -> limit_div_neg f D1 l.
Proof.
intros.
intros m Hm.
specialize (H0 m Hm).
destruct H0 as [alp [Halp Hsolve]].
exists alp. split.
apply Halp.
intros. assert (D x).
intuition.
specialize (Hsolve x H2 H1). apply Hsolve.
Qed.


Lemma limit_div_pos_comp_Ropp : 
  forall (g : R -> R) (a b : R),
    limit_div_pos g (open_interval (-a) (-b)) (-a) -> 
      limit_div_pos (comp g (fun x => -x)) (open_interval b a) a.
Proof.
intros.
intros m Hm.
specialize (H m Hm).
destruct H as [alp [Halp Hsolve]].
exists alp. split. apply Halp.
intros. specialize (Hsolve (-x)).
apply Hsolve. split; destruct H; lra.
unfold R_dist in *. replace (- x - - a) with (- (x - a)) by ring.
rewrite Rabs_Ropp. apply H0.
Qed.

Lemma limit_div_pos_comp_Ropp_l : 
  forall (g : R -> R) (a b : R),
    limit_div_pos g (open_interval (-a) (-b)) (-b) -> 
      limit_div_pos (comp g (fun x => -x)) (open_interval b a) b.
Proof.
intros.
intros m Hm.
specialize (H m Hm).
destruct H as [alp [Halp Hsolve]].
exists alp. split. apply Halp.
intros. specialize (Hsolve (-x)).
apply Hsolve. split; destruct H; lra.
unfold R_dist in *. replace (- x - - b) with (- (x - b)) by ring.
rewrite Rabs_Ropp. apply H0.
Qed.

Lemma limit_div_neg_comp_Ropp : 
  forall (g : R -> R) (a b : R),
    limit_div_neg g (open_interval (-a) (-b)) (-a) -> 
      limit_div_neg (comp g (fun x => -x)) (open_interval b a) a.
Proof.
intros.
intros m Hm.
specialize (H m Hm).
destruct H as [alp [Halp Hsolve]].
exists alp. split. apply Halp.
intros. specialize (Hsolve (-x)).
apply Hsolve. split; destruct H; lra.
unfold R_dist in *. replace (- x - - a) with (- (x - a)) by ring.
rewrite Rabs_Ropp. apply H0.
Qed.

Lemma limit_div_neg_comp_Ropp_l : 
  forall (g : R -> R) (a b : R),
    limit_div_neg g (open_interval (-a) (-b)) (-b) -> 
      limit_div_neg (comp g (fun x => -x)) (open_interval b a) b.
Proof.
intros.
intros m Hm.
specialize (H m Hm).
destruct H as [alp [Halp Hsolve]].
exists alp. split. apply Halp.
intros. specialize (Hsolve (-x)).
apply Hsolve. split; destruct H; lra.
unfold R_dist in *. replace (- x - - b) with (- (x - b)) by ring.
rewrite Rabs_Ropp. apply H0.
Qed.

End Definitions.

Lemma derive_pt_comp_Ropp : forall a b f x (Df : forall x, open_interval a b x -> derivable_pt f x) 
(Df' : forall x, open_interval (-b) (-a) x -> derivable_pt (fun x0 => f (- x0)) x) 
  (H1 : open_interval (-b) (-a) x) (H2 : open_interval a b (-x)), - derive_pt f (- x) (Df (- x) H2) =
   derive_pt (fun x0 : R => f (- x0)) x (Df' x H1).
Proof.
intros.
assert (derivable_pt (comp f (fun x=> Ropp x)) x). reg. apply derivable_pt_opp. reg. 
apply Df. apply H2.

assert (Heq : forall x, (fun x0 => f (-x0)) x = (comp f (fun x => Ropp x)) x).
intros. reflexivity.

rewrite (derive_pt_ext (fun x0 => f (-x0)) (comp f (fun x => Ropp x)) Heq x (Df' (x) H1) H). 
assert (derivable_pt (fun x => (-x)) x). reg.
assert (derivable_pt f ((fun x => -x) x)). apply Df. apply H2.
pose (p := derivable_pt_comp (fun x => (-x)) f x H0 H3).
rewrite (pr_nu_var _ _ _ H p).
unfold p.
rewrite derive_pt_comp. replace (derive_pt (fun x0 : R => (- x0)%R) x H0) with (-(1%R)).
ring_simplify. apply Ropp_eq_compat. apply pr_nu.
rewrite <- derive_pt_id with x. rewrite <- derive_pt_opp.
unfold id. apply pr_nu.
reflexivity.
Qed.

Section FirstGenHopital.

(*
Theorem Hopital_g0_Lfin_right :

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zf: lim_{x -> a+} f = 0
Zg: lim_{x -> a+} g = 0
g_not_0: \forall x \in ]a; b[, g' x <> 0 /\ g x <> 0
Hlimder: lim_{x -> a+} f' / g' = L    (with L \in R)
-----------------------------------------------------
lim_{x -> a+} f / g = L

*)

Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).
Hypothesis (Zf : limit1_in f (open_interval a b) 0 a).
Hypothesis (Zg : limit1_in g (open_interval a b) 0 a).


Hypothesis (g_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0 /\ g x <> 0).
Hypothesis (Hlimder : forall eps, eps > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      R_dist (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)) L < eps)).


Lemma limit_open : forall f a b, 
  limit1_in f (D_x no_cond a) (f a) a -> limit1_in f (open_interval a b) (f a) a.
Proof.
  clear Hlimder Zf Zg. unfold limit1_in in *. unfold limit_in in *. intros. specialize (H eps H0).
  destruct H as [alp [Halp H2]]. exists alp. split.
   now apply Halp.
   
   intros. apply H2. destruct H. split.
    constructor.
     now constructor.
     
     unfold open_interval in H. now intro; destruct H; lra.
  
  apply H1.
Qed.

Lemma f_a_zero : f a = 0.
Proof.
  assert (forall x (Hclose : a <= x <= b), continuity_pt f x).
   intros. apply Cf. now apply Hclose.

   unfold continuity_pt in H. unfold continue_in in H. specialize (H a). assert (a <= a <= b) by intuition. 
   apply H in H0. apply (limit_open f a b) in H0. eapply single_limit; [ | apply H0 | apply Zf ]. unfold adhDa. 
   intros. exists (a + Rmin ((b - a) / 2) (alp / 2)). assert (H6 : alp / 2 > 0) by lra. 
   assert ((b - a) > 0) by lra. assert ((b-a) /2 > 0).
    apply (Rmult_gt_0_compat (/2)) in H2.
     now lra.

     now lra.

  split.
   unfold open_interval. split.
    assert (Rmin ((b - a) /2) (alp/2) > 0).
     apply Rmin_Rgt_r. now intuition.

     now lra.

   apply Rle_lt_trans with (a + (b-a) / 2).
    apply Rplus_le_compat.
     now intuition.

     now apply Rmin_l.

   assert (b - a - (b - a) / 2 > 0).
    field_simplify. now lra.

    now lra.

  unfold R_dist. rewrite Rabs_right.
   ring_simplify. apply Rle_lt_trans with (alp / 2).
    now apply Rmin_r.

    now lra.

  ring_simplify. apply Rle_ge. apply Rmin_glb; intuition.       
Qed.

Lemma g_a_zero : g a = 0. 
Proof.
  assert (forall x (Hclose : a <= x <= b), continuity_pt g x).
   intros. apply Cg. now apply Hclose.
   
   unfold continuity_pt in H. unfold continue_in in H. specialize (H a). assert (a <= a <= b) by intuition.
   apply H in H0. apply (limit_open g a b) in H0. eapply single_limit; [ | apply H0 | apply Zg ].
   unfold adhDa. intros. exists (a + Rmin ((b - a) / 2) (alp / 2)). assert (H6 : alp / 2 > 0) by lra.
   assert ((b - a) > 0) by lra. assert ((b-a) /2 > 0).
    apply (Rmult_gt_0_compat (/2)) in H2.
     now lra.
     
     now lra.
  
  split.
   unfold open_interval. split.
    assert (Rmin ((b - a) /2) (alp/2) > 0).
     apply Rmin_Rgt_r. now intuition.
     
     now lra.
   
   apply Rle_lt_trans with (a + (b-a) / 2).
    apply Rplus_le_compat.
     now intuition.
     
     now apply Rmin_l.
   
   assert (b - a - (b - a) / 2 > 0).
    field_simplify. now lra.
    
    now lra.
  
  unfold R_dist. rewrite Rabs_right.
   ring_simplify. apply Rle_lt_trans with (alp / 2).
    now apply Rmin_r.
    
    now lra.
  
  ring_simplify. apply Rle_ge. apply Rmin_glb; intuition.
Qed.

Theorem Hopital_g0_Lfin_right : limit1_in (fun x => f x / g x) (open_interval a b) L a.
Proof.
  unfold limit1_in, limit_in. intros. specialize (Hlimder eps H). destruct Hlimder as [alp [Halp Hlim]].
  exists alp. split.
   now assumption.
   
   intros. assert (Hacc2 : forall x, open_interval a b x ->  
     exists c, exists Hopenc, f x / g x = derive_pt f c (Df c Hopenc) / derive_pt g c (Dg c Hopenc) /\ a < c < x).
    generalize MVT. intros. specialize (H1 f g a x0). assert (forall c, a < c < x0 -> derivable_pt f c).
     intros. apply Df. unfold open_interval. split.
      now intuition.
      
      now apply Rlt_trans with x0; unfold open_interval in H2; intuition.
    
    assert (forall c, a < c < x0 -> derivable_pt g c).
     intros. apply Dg. unfold open_interval. split.
      now intuition.
      
      now apply Rlt_trans with x0; unfold open_interval in H2; intuition.
    
    specialize (H1 H3 H4). assert (a < x0) by (unfold open_interval in H2; intuition).
    assert (forall c : R, a <= c <= x0 -> continuity_pt f c).
     intros. apply Cf. split.
      now intuition.
      
      unfold open_interval in H2. now apply Rle_trans with x0; intuition.
    
    assert (forall c, a <= c <= x0 -> continuity_pt g c).
     intros. apply Cg. split.
      now intuition.
      
      unfold open_interval in H2. now apply Rle_trans with x0; intuition.
    
    specialize (H1 H5 H6 H7). destruct H1 as [c [P Hold2]]. exists c. assert (Hopenc : open_interval a b c).
     unfold open_interval in *. split.
      now apply P.
      
      apply Rlt_trans with x0.
       now apply P.
       
       now apply H2.
    
    exists Hopenc. split.
     rewrite g_a_zero in Hold2. rewrite f_a_zero in Hold2. do 2 rewrite Rminus_0_r in Hold2.
     apply (Rmult_eq_reg_l (g x0)).
      rewrite (pr_nu f c _ (H3 c P)). unfold Rdiv. do 2 rewrite <- Rmult_assoc. rewrite Hold2.
      rewrite (pr_nu g c _ (Dg c Hopenc)). field. generalize (g_not_0 c Hopenc). generalize (g_not_0 x0 H2).
      intros H01 H02. assert (c < b).
       now unfold open_interval in Hopenc; destruct Hopenc; assumption.
       
       split.
        now apply H02.
        
        now apply H01.
     
     apply g_not_0. now apply H2.
     
     now apply P.
  
  destruct H0. specialize (Hacc2 x H0). destruct Hacc2 as [c [Hopenc Haccc]]. specialize (Hlim c).
  simpl in *. unfold R_dist in *. assert (open_interval a b c /\ Rabs (c - a) < alp).
   split.
    now apply Hopenc.
    
    destruct Haccc. destruct H3. rewrite Rabs_right.
     rewrite Rabs_right in H1.
      now lra.
      
      now lra.
   
   now lra.
   
   specialize (Hlim Hopenc). destruct H2. specialize (Hlim H3). destruct Haccc. rewrite H4.
   apply Hlim.
Qed.

End FirstGenHopital.

Section FirstGenHopital_left.

(*
Theorem Hopital_g0_Lfin_left :

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zf: lim_{x -> b-} f = 0
Zg: lim_{x -> b-} g = 0
g_not_0: \forall x \in ]a; b[, g' x <> 0 /\ g x <> 0
Hlimder: lim_{x -> b-} f' / g' = L    (with L \in R)
-----------------------------------------------------
lim_{x -> b-} f / g = L

*)

Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).
Hypothesis (Zf : limit1_in f (open_interval a b) 0 b).
Hypothesis (Zg : limit1_in g (open_interval a b) 0 b).

Hypothesis (g_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0 /\ g x <> 0).
Hypothesis (Hlimder : forall eps, eps > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x b < alp -> 
      R_dist (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)) L < eps)).

Theorem Hopital_g0_Lfin_left : limit1_in (fun x => f x / g x) (open_interval a b) L b.
Proof.
  apply limit1_ext with (comp (fun x => f (-x) / g (-x)) (fun x => -x)).
   intros. unfold comp. ring_simplify (--x). now reflexivity.
   
   apply limit1_imp with (Dgf (open_interval a b) (open_interval (-b) (-a)) (fun x => - x)).
    intros. unfold Dgf. split.
     now apply H.
     
     now destruct H; split; lra.
  
  apply (limit_comp (fun x => - x) (fun x : R => f (- x) / g (- x)) _ _ (-b)).
   unfold limit1_in, limit_in. intros. exists eps. split.
    now assumption.
    
    intros. destruct H0. unfold dist in *. simpl in *. destruct H0. unfold R_dist in *.
    replace (- x -- b) with (- (x - b)) by ring. rewrite Rabs_Ropp. now apply H1.
  
  assert (Df': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => f (- x)) x).
   intros. reg. apply Df. now destruct H; split; lra.
   
   assert (Dg': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => g (- x)) x).
    intros. reg. apply Dg. now destruct H; split; lra.
    
    apply Hopital_g0_Lfin_right with Df' Dg'.
     now intuition.
     
     intros. reg. apply Cf. now destruct H; split; lra.
     
     intros. reg. apply Cg. now destruct H; split; lra.
     
     unfold limit1_in, limit_in in *. intros eps Heps. specialize (Zf eps Heps). destruct Zf as [alp [Halp Hsolve]].
     exists alp. split.
      now assumption.
      
      intros x H. specialize (Hsolve (-x)). assert (H1 : open_interval a b (- x) /\ dist R_met (- x) b < alp).
       split.
        destruct H. now destruct H; split; lra.
        
        unfold dist in *. simpl in *. destruct H. unfold R_dist in *. replace (-x - b) with (- (x -- b)) by ring.
        rewrite Rabs_Ropp. now apply H0.
     
     apply Hsolve. now apply H1.
     
     unfold limit1_in, limit_in in *. intros eps Heps. specialize (Zg eps Heps). destruct Zg as [alp [Halp Hsolve]].
     exists alp. split.
      now assumption.
      
      intros x H. specialize (Hsolve (-x)). assert (H1 : open_interval a b (- x) /\ dist R_met (- x) b < alp).
       split.
        destruct H. now destruct H; split; lra.
        
        unfold dist in *. simpl in *. destruct H. unfold R_dist in *. replace (-x - b) with (- (x -- b)) by ring.
        rewrite Rabs_Ropp. now apply H0.
     
     apply Hsolve. now apply H1.
     
     intros. assert (Hopen2: open_interval a b (-x)).
      now destruct Hopen; split; lra.
      
      destruct (g_not_0 (-x) Hopen2). split.
       assert (derive_pt (fun x0 : R => g (- x0)) x (Dg' x Hopen) = - derive_pt g (- x) (Dg (- x) Hopen2)).
        reg.
         apply Ropp_eq_compat. now apply pr_nu.
         
         apply Dg. now apply Hopen2.
       
       rewrite H1. intro. apply H. replace 0 with (-0) in H2 by ring. apply Ropp_eq_compat in H2.
       ring_simplify in H2. now apply H2.
       
       now apply H0.
  
  intros eps Heps. specialize (Hlimder eps Heps). destruct Hlimder as [alp [Halp Hsolve]].
  exists alp. split.
   now assumption.
   
   intros. assert (open_interval a b (-x)).
    now destruct Hopen; split; lra.
    
    assert (R_dist (-x) b < alp).
     unfold R_dist in *. replace (- x - b) with (- (x -- b)) by ring. rewrite Rabs_Ropp.
     now apply H.
     
     specialize (Hsolve (-x) H0 H1). assert (derive_pt (fun x0 : R => f (- x0)) x (Df' x Hopen) = - derive_pt f (- x) (Df (- x) H0) ).
      reg.
       apply Ropp_eq_compat. now apply pr_nu.
       
       apply Df. now destruct Hopen; split; lra.
  
  assert (derive_pt (fun x0 : R => g (- x0)) x (Dg' x Hopen) = - derive_pt g (- x) (Dg (- x) H0) ).
   reg.
    apply Ropp_eq_compat. now apply pr_nu.
    
    apply Dg. now destruct Hopen; split; lra.
  
  rewrite H2. rewrite H3. replace (- derive_pt f (- x) (Df (- x) H0) / - derive_pt g (- x) (Dg (- x) H0)) with
 (derive_pt f (- x) (Df (- x) H0) / derive_pt g (- x) (Dg (- x) H0)).
   now apply Hsolve.
   
   field. apply g_not_0.
Qed.

End FirstGenHopital_left.

Section SndGenHopital.

(*
Theoreme Hopital_gpinf_Lfin_right: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> a+} g = +infinity
Hlimder: lim_{x -> a+} f' / g' = L    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> a+} f / g = L


*)
Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_pos g (open_interval a b) a).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall eps, eps > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      R_dist (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)) L < eps)).

Lemma open_lemma : forall a b c, a < b -> c > 0 -> open_interval a b (a + Rmin ((b - a) /2) c).
Proof.
  intros. assert ((b0 - a0) > 0) by lra. assert ((b0-a0) /2 > 0).
   apply (Rmult_gt_0_compat (/2)) in H1.
    now lra.
    
    now lra.
  
  split.
   assert (Rmin ((b0-a0) /2) c > 0).
    now apply Rmin_glb_lt; assumption.
    
    now lra.
  
  apply Rle_lt_trans with (a0 + (b0-a0) /2).
   apply Rplus_le_compat_l. now apply Rmin_l.
   
   assert (b0 - a0 - (b0-a0) /2 > 0).
    field_simplify. now lra.
    
    lra.
Qed.


Lemma g_not_zero : exists a', open_interval a b a' /\ forall x, open_interval a a' x -> g x <> 0.
Proof.
  unfold limit_div_pos in Zg. assert (1 > 0) by lra. specialize (Zg 1 H). destruct Zg as [alp [Halp H3]].
  exists (a + Rmin ((b - a) / 2) (alp / 2)). assert (H6 : alp / 2 > 0) by lra.
  assert ((b - a) > 0) by lra. assert ((b-a) /2 > 0).
   apply (Rmult_gt_0_compat (/2)) in H0.
    now lra.
    
    now lra.
  
  split.
   unfold open_interval. split.
    assert (Rmin ((b-a) /2) (alp / 2) > 0).
     now apply Rmin_glb_lt; assumption.
     
     now lra.
   
   apply Rle_lt_trans with (a + (b-a) /2).
    apply Rplus_le_compat_l. now apply Rmin_l.
    
    assert (b - a - (b-a) /2 > 0).
     field_simplify. now lra.
     
     now lra.
  
  intros. unfold open_interval in H0. assert (g x > 1).
   apply H3.
    unfold open_interval. unfold open_interval in H2. split.
     now apply H2.
     
     apply Rlt_trans with (a + Rmin ((b-a)/2) (alp /2)).
      now apply H2.
      
      apply Rle_lt_trans with (a + (b-a) /2).
       apply Rplus_le_compat_l. now apply Rmin_l.
       
       assert (b - a - (b-a) /2 > 0).
        field_simplify. now lra.
        
        now lra.
   
   unfold R_dist. unfold open_interval in H2. destruct H2. apply Rlt_trans with (alp/2).
    apply Rlt_le_trans with (Rmin ((b-a) / 2) (alp /2)).
     now rewrite Rabs_right; lra.
     
     now apply Rmin_r.
   
   now lra.
   
   intro. lra.
Qed.

Lemma MVT_unusable : forall a', open_interval a b a' -> 
          forall x y : R,
          open_interval a a' x ->
          open_interval a a' y ->
          x < y ->
          exists c : R,
            exists Hopenc : open_interval a b c,
              (f y - f x) * derive_pt g c (Dg c Hopenc) =
              derive_pt f c (Df c Hopenc) * (g y - g x) /\ 
              x < c < y. 
Proof.
  intros a' Hopennew. generalize MVT. intros. specialize (H f g x y). assert (forall c, x < c < y -> derivable_pt f c).
   intros. apply Df. unfold open_interval in *. split.
    now apply Rlt_trans with x ; intuition.
    
    apply Rlt_trans with y ; intuition. now apply Rlt_trans with a'; intuition.
  
  assert (forall c, x < c < y -> derivable_pt g c).
   intros. apply Dg. unfold open_interval in *. split.
    now apply Rlt_trans with x ; intuition.
    
    apply Rlt_trans with y ; intuition. now apply Rlt_trans with a'; intuition.
  
  specialize (H H3 H4 H2). assert (forall c : R, x <= c <= y -> continuity_pt f c).
   intros. apply Cf. unfold open_interval in *. split.
    now apply Rle_trans with x; intuition.
    
    apply Rle_trans with y; intuition. now apply Rle_trans with a'; intuition.
  
  assert (forall c : R, x <= c <= y -> continuity_pt g c).
   intros. apply Cg. unfold open_interval in *. split.
    now apply Rle_trans with x; intuition.
    
    apply Rle_trans with y; intuition. now apply Rle_trans with a'; intuition.
  
  specialize (H H5 H6). destruct H as [c [P Hold2]]. exists c. assert (Hopenc : open_interval a b c).
   unfold open_interval in *. destruct P; split.
    now apply Rlt_trans with x; intuition.
    
    apply Rlt_trans with y; intuition. now apply Rlt_trans with a'; intuition.
  
  exists Hopenc. split.
   rewrite (pr_nu f c _ (H3 c P)). rewrite (pr_nu g c _ (H4 c P)). rewrite <- Hold2.
   now ring.
   
   apply P.
Qed.


Theorem Hopital_gpinf_Lfin_right : limit1_in (fun x => f x / g x) (open_interval a b) L a.
Proof.
  destruct g_not_zero as [a' [H1 Ha']]. unfold limit1_in, limit_in. intros. assert (Hacc2' : forall x y, open_interval a a' x -> open_interval a a' y -> x < y -> 
     exists c, exists Hopenc, f x / g x = (1 - (g y / g x)) * 
                     derive_pt f c (Df c Hopenc) / derive_pt g c (Dg c Hopenc) + (f y / g x) /\ x < c < y).
   intros. assert (open_interval a b x).
    split.
     now apply H0.
     
     apply Rlt_trans with a'.
      now apply H0.
      
      now apply H1.
   
   assert (open_interval a b y).
    split.
     now apply H2.
     
     apply Rlt_trans with a'.
      now apply H2.
      
      now apply H1.
   
   generalize (MVT_unusable a' H1 x y H0 H2 H3). intros Hacc2'. destruct Hacc2' as [c [Hopenc [Hacc2' H7]]].
   exists c. exists Hopenc. split; [ | now intuition]. apply (Rplus_eq_reg_l (- (f y / g x))).
   ring_simplify. apply (Rmult_eq_reg_l (g x)).
    apply (Rmult_eq_reg_l (derive_pt g c (Dg c Hopenc))).
     apply (Rmult_eq_reg_l (-1)).
      field_simplify.
       field_simplify in Hacc2'. replace (derive_pt g c (Dg c Hopenc) * f y - derive_pt g c (Dg c Hopenc) * f x)
           with (f y * derive_pt g c (Dg c Hopenc) - f x * derive_pt g c (Dg c Hopenc)) by ring.
       rewrite Hacc2'. now field.
       
       split.
        apply Ha'. now apply H0.
        
        now apply (g'_not_0 c Hopenc).
      
      now apply Ha'; assumption.
      
      intro. now lra.
    
    now apply g'_not_0.
    
    now apply Ha'; assumption.
  
  assert (H0: forall eps, eps > 0 -> 
         exists y, open_interval a a' y /\ forall c (Hopen : open_interval a y c) (Hopenc : open_interval a b c),
           R_dist (derive_pt f c (Df c Hopenc) / derive_pt g c (Dg c Hopenc)) L < eps).
   intros eps0 Heps0. specialize (Hlimder eps0 Heps0). destruct Hlimder as [alp [Halp Hlimder1]].
   exists (a + Rmin ((a'-a) / 2) alp). split.
    apply open_lemma.
     now apply H1.
     
     now apply Halp.
   
   intros. specialize (Hlimder1 c Hopenc). unfold R_dist in *. apply Hlimder1. destruct Hopen.
   apply Rlt_le_trans with (Rmin ((a' - a) / 2) alp).
    now rewrite Rabs_right; lra.
    
    now apply Rmin_r.
  
  assert (H15 : forall A eps, eps > 0 -> exists alp, 
           alp > 0 /\ forall x, open_interval a b x -> R_dist x a < alp -> Rabs (A / g x) < eps).
   intros. unfold limit_div_pos in Zg. destruct (Req_dec A 0) as [eq_dec1 | eq_dec2].
    subst. exists 1. intuition. unfold Rdiv. rewrite Rmult_0_l. rewrite Rabs_R0. now assumption.
    
    specialize (Zg (Rabs A / eps0)). assert (Rabs A /eps0 > 0).
     assert (Rabs A > 0).
      apply Rabs_pos_lt. now assumption.
      
      unfold Rdiv. assert (/eps0 > 0).
       now apply Rinv_0_lt_compat; assumption.
       
       now apply Rmult_lt_0_compat; assumption.
   
   specialize (Zg H3). destruct Zg as [alp [Halp Zg3]]. exists alp. intuition. unfold Rdiv.
   rewrite Rabs_mult. specialize (Zg3 x H4 H5). assert (g x > 0).
    apply Rlt_trans with (Rabs A / eps0).
     now assumption.
     
     now assumption.
   
   rewrite Rabs_Rinv.
    rewrite (Rabs_right (g x)).
     apply (Rmult_lt_reg_l (g x)).
      now assumption.
      
      apply (Rmult_lt_reg_l (/eps0)).
       apply Rinv_0_lt_compat. now apply H2.
       
       field_simplify.
        unfold Rdiv. try rewrite Rinv_1. try rewrite Rmult_1_r. now apply Zg3.
        
        intro. now lra.
        
        split.
         intro. now lra.
         
         intro. now lra.
    
    now lra.
    
    intro. now lra.
  
  assert (Heps4 : eps / 4 > 0) by lra. assert (bizarre : forall eps L, L >= 0 -> eps > 0 ->
                   exists eps1, eps1 > 0 /\  eps1 * (L + eps) < eps / 2).
   intros. exists (/2 * ((eps0 / 2) * / (L0 + eps0))). split.
    apply Rmult_lt_0_compat.
     now lra.
     
     apply Rmult_lt_0_compat.
      now lra.
      
      apply Rinv_0_lt_compat. now lra.
   
   field_simplify.
    now lra.
    
    intro. now lra.
  
  specialize (H0 (eps/4) Heps4). destruct H0 as [y [open H0]]. specialize (Hlimder eps H).
  destruct Hlimder as [alp1 [Halp1 Hlim2]]. generalize (H15 (f y) (eps/4) Heps4).
  intros H16. destruct H16 as [alp2 [Halp2 Hlim3]]. specialize (bizarre eps (Rabs L)).
  assert (Hb1: Rabs L >= 0) by (apply Rle_ge; apply Rabs_pos). specialize (bizarre Hb1 H).
  destruct bizarre as [eps1 [Heps1 HepsL4]]. specialize (H15 (g y) eps1 Heps1). destruct H15 as [alp3 [Halp3 Hlim4]].
  pose (alp_alp := Rmin (Rmin alp1 alp2) alp3). pose (alp := Rmin (Rmin alp_alp (a' - a)) (y - a)).
  exists alp. split.
   apply Rmin_pos.
    apply Rmin_pos.
     apply Rmin_pos.
      now apply Rmin_pos; assumption.
      
      now assumption.
    
    unfold open_interval in H1. destruct H1. now lra.
    
    unfold open_interval in open. destruct open. now lra.
  
  intros. specialize (Hacc2' x y). assert (open_interval a a' x).
   unfold dist in H2. simpl in H2. unfold R_dist in H2. split.
    now apply H2.
    
    assert (Rabs (x - a) < Rabs (a' - a)).
     rewrite (Rabs_right (a' - a)).
      unfold alp in H2. apply Rlt_le_trans with (Rmin (Rmin alp_alp (a' - a)) (y - a)).
       now intuition.
       
       apply Rle_trans with (Rmin alp_alp (a' - a)).
        now apply Rmin_l.
        
        now apply Rmin_r.
     
     destruct H1. now lra.
     
     do 2 rewrite Rabs_right in H3.
      now lra.
      
      now destruct H1; lra.
      
      destruct H2. now destruct H2; lra.
      
      destruct H2. now destruct H2; lra.
  
  assert (open_interval a a' y).
   now apply open.
   
   specialize (Hacc2' H3 H4). assert (x < y).
    unfold alp in H2. unfold dist in H2. simpl in H2. unfold R_dist in H2. assert (Rabs (x - a) < Rabs (y - a)).
     rewrite (Rabs_right (y - a)).
      unfold alp in H2. apply Rlt_le_trans with (Rmin (Rmin alp_alp (a' - a)) (y - a)).
       now intuition.
       
       now apply Rmin_r.
     
     destruct H4. now lra.
     
     do 2 rewrite Rabs_right in H5.
      now lra.
      
      now destruct H4; lra.
      
      now destruct H3; lra.
      
      now destruct H3; lra.
  
  specialize (Hacc2' H5). destruct Hacc2' as [c [Hopenc H10]]. destruct H10 as [H10 H100].
  rewrite H10. unfold dist. simpl. unfold R_dist. unfold Rdiv. ring_simplify (((1 - g y */ g x) * derive_pt f c (Df c Hopenc) */
                              derive_pt g c (Dg c Hopenc) + f y */ g x - L)). unfold Rminus.
  rewrite Rplus_assoc. rewrite Rplus_assoc. apply Rle_lt_trans with 
                              (Rabs  (- g y * / g x * derive_pt f c (Df c Hopenc) *
                                 / derive_pt g c (Dg c Hopenc)) + Rabs  (/ g x * f y + (
                                   derive_pt f c (Df c Hopenc) * / derive_pt g c (Dg c Hopenc) +- L))).
   now apply Rabs_triang.
   
   replace (- g y * / g x * derive_pt f c (Df c Hopenc) */ derive_pt g c (Dg c Hopenc)) 
                             with ((- g y * / g x) * (derive_pt f c (Df c Hopenc) */ derive_pt g c (Dg c Hopenc))) 
                             by ring. rewrite Rabs_mult. replace eps with (eps / 2 + eps / 2) by field.
   apply Rplus_lt_compat.
    apply Rle_lt_trans with (eps1 * (Rabs L + eps)).
     apply Rmult_le_compat.
      now apply Rabs_pos.
      
      now apply Rabs_pos.
      
      rewrite Ropp_mult_distr_l_reverse. rewrite Rabs_Ropp. apply Rlt_le. apply Hlim4.
       now apply H2.
       
       unfold alp in H2. unfold alp_alp in H2. apply Rlt_le_trans with ((Rmin (Rmin alp1 alp2) alp3)).
        apply Rlt_le_trans with (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)).
         apply Rlt_le_trans with (Rmin (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)) (y - a)).
          now apply H2.
          
          now apply Rmin_l.
        
        now apply Rmin_l.
        
        now apply Rmin_r.
     
     destruct H2. assert (R_dist x a < alp1).
      unfold alp in H6. unfold alp_alp in H6. apply Rlt_le_trans with (Rmin alp1 alp2).
       apply Rlt_le_trans with (Rmin (Rmin alp1 alp2) alp3).
        apply Rlt_le_trans with (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)).
         apply Rlt_le_trans with (Rmin (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)) (y - a)).
          now apply H6.
          
          now apply Rmin_l.
        
        now apply Rmin_l.
        
        now apply Rmin_l.
      
      now apply Rmin_l.
      
      assert (open_interval a y c).
       unfold open_interval. split.
        apply Rlt_trans with x.
         now apply H2.
         
         now apply H100.
       
       now apply H100.
       
       specialize (H0 c H8). specialize (H0 Hopenc). assert (Rabs (derive_pt f c (Df c Hopenc) / derive_pt g c (Dg c Hopenc)) - Rabs L <= eps).
        apply Rle_trans with  (R_dist (derive_pt f c (Df c Hopenc) / 
                                      derive_pt g c (Dg c Hopenc)) L).
         apply Rle_trans with  (Rabs (Rabs (derive_pt f c (Df c Hopenc) / 
                                       derive_pt g c (Dg c Hopenc)) - Rabs L)).
          now apply Rle_abs.
          
          unfold R_dist. now apply Rabs_triang_inv2.
        
        apply Rlt_le. apply Rlt_trans with (eps / 4).
         now apply H0.
         
         now lra.
     
     apply (Rplus_le_reg_l (- Rabs L)). ring_simplify. rewrite Rplus_comm. now apply H9.
     
     now apply HepsL4.
  
  replace (eps /2) with (eps / 4 + eps / 4) by field. apply Rle_lt_trans with (Rabs (/ g x * f y) + Rabs
                                     (derive_pt f c (Df c Hopenc) * / derive_pt g c (Dg c Hopenc) + - L)).
   now apply Rabs_triang.
   
   apply Rplus_lt_compat.
    rewrite Rmult_comm. apply Hlim3.
     now apply H2.
     
     destruct H2. unfold alp in H6. unfold alp_alp in H6. apply Rlt_le_trans with (Rmin alp1 alp2).
      apply Rlt_le_trans with ((Rmin (Rmin alp1 alp2) alp3)).
       apply Rlt_le_trans with (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)).
        apply Rlt_le_trans with (Rmin (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)) (y - a)).
         now apply H6.
         
         now apply Rmin_l.
       
       now apply Rmin_l.
       
       now apply Rmin_l.
    
    now apply Rmin_r.
    
    apply H0. unfold R_dist in Hlim2. unfold open_interval in *. split.
     now apply Hopenc.
     
     apply H100.
Qed.

End SndGenHopital.

Section SndGenHopital_left.

(*
Theoreme Hopital_gpinf_Lfin_left: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> b-} g = +infinity
Hlimder: lim_{x -> b-} f' / g' = L    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> b-} f / g = L


*)
Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_pos g (open_interval a b) b).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall eps, eps > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x b < alp -> 
      R_dist (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)) L < eps)).


Theorem Hopital_gpinf_Lfin_left : limit1_in (fun x => f x / g x) (open_interval a b) L b.
Proof.
  apply limit1_ext with (comp (fun x => f (-x) / g (-x)) (fun x => -x)).
   intros. unfold comp. ring_simplify (--x). now reflexivity.
   
   apply limit1_imp with (Dgf (open_interval a b) (open_interval (-b) (-a)) (fun x => - x)).
    intros. unfold Dgf. split.
     now apply H.
     
     now destruct H; split; lra.
  
  apply (limit_comp (fun x => - x) (fun x : R => f (- x) / g (- x)) _ _ (-b)).
   unfold limit1_in, limit_in. intros. exists eps. split.
    now assumption.
    
    intros. destruct H0. unfold dist in *. simpl in *. destruct H0. unfold R_dist in *.
    replace (- x -- b) with (- (x - b)) by ring. rewrite Rabs_Ropp. now apply H1.
  
  assert (Df': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => f (- x)) x).
   intros. reg. apply Df. now destruct H; split; lra.
   
   assert (Dg': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => g (- x)) x).
    intros. reg. apply Dg. now destruct H; split; lra.
    
    apply Hopital_gpinf_Lfin_right with Df' Dg'.
     now intuition.
     
     intros. reg. apply Cf. now destruct H; split; lra.
     
     intros. reg. apply Cg. now destruct H; split; lra.

     apply limit_div_pos_opp. apply Zg.

     intros.
     
     intros. assert (Hopen2: open_interval a b (-x)).
      now destruct Hopen; split; lra.

      intro. destruct (g'_not_0 (-x) Hopen2).
       assert (derive_pt (fun x0 : R => g (- x0)) x (Dg' x Hopen) = - derive_pt g (- x) (Dg (- x) Hopen2)).
        reg.
         apply Ropp_eq_compat. now apply pr_nu.
         
         apply Dg. now apply Hopen2.
       
       rewrite <- Ropp_involutive. symmetry. rewrite <- Ropp_involutive.
       replace 0 with (- 0) in H by ring. 
       apply Ropp_eq_compat. rewrite <- H. rewrite H0. reflexivity. 

intros eps Heps. specialize (Hlimder eps Heps).
destruct Hlimder as [alp [Halp Hsolve]].
exists alp. split. apply Halp.
intros.
assert (Hopenx : open_interval a b (-x)). split; destruct Hopen; lra.
assert (R_dist (-x) b < alp). unfold R_dist in *.
replace (- x - b) with (- (x + b)) by ring.
ring_simplify (x--b) in H.
rewrite Rabs_Ropp. apply H.
specialize (Hsolve (-x) Hopenx H0).
replace (derive_pt (fun x0 : R => f (- x0)) x (Df' x Hopen)) with 
  (- derive_pt f (- x) (Df (- x) Hopenx)).
replace (derive_pt (fun x0 : R => g (- x0)) x (Dg' x Hopen)) with 
  (- derive_pt g (- x) (Dg (- x) Hopenx)).
replace ((- derive_pt f (- x) (Df (- x) Hopenx) /
      - derive_pt g (- x) (Dg (- x) Hopenx))) with
((derive_pt f (- x) (Df (- x) Hopenx) /
      derive_pt g (- x) (Dg (- x) Hopenx))). apply Hsolve.

field. apply g'_not_0.

apply derive_pt_comp_Ropp.
apply derive_pt_comp_Ropp.
Qed.


End SndGenHopital_left.

Section SndGenHopitalposneg.

(*
Theoreme Hopital_gninf_Lfin_right: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> a+} g = -infinity
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
Hlimder: lim_{x -> a+} f' / g' = L    (with L \in R)
-----------------------------------------------------
lim_{x -> a+} f / g = L


*)


Lemma g_not_zero2 : forall g a b, b > a -> limit_div_neg g (open_interval a b) a -> 
  exists a', open_interval a b a' /\ forall x, open_interval a a' x -> g x <> 0.
Proof.
  intros g a b Hab Zg. unfold limit_div_neg in Zg. assert (1 > 0) by lra. specialize (Zg 1 H).
  destruct Zg as [alp [Halp H3]]. exists (a + Rmin ((b - a) / 2) (alp / 2)). assert (H6 : alp / 2 > 0) by lra.
  assert ((b - a) > 0) by lra. assert ((b-a) /2 > 0).
   apply (Rmult_gt_0_compat (/2)) in H0.
    now lra.
    
    now lra.
  
  split.
   unfold open_interval. split.
    assert (Rmin ((b-a) /2) (alp / 2) > 0).
     now apply Rmin_glb_lt; assumption.
     
     now lra.
   
   apply Rle_lt_trans with (a + (b-a) /2).
    apply Rplus_le_compat_l. now apply Rmin_l.
    
    assert (b - a - (b-a) /2 > 0).
     field_simplify. now lra.
     
     now lra.
  
  intros. unfold open_interval in H0. assert (g x < - 1).
   apply H3.
    unfold open_interval. unfold open_interval in H2. split.
     now apply H2.
     
     apply Rlt_trans with (a + Rmin ((b-a)/2) (alp /2)).
      now apply H2.
      
      apply Rle_lt_trans with (a + (b-a) /2).
       apply Rplus_le_compat_l. now apply Rmin_l.
       
       assert (b - a - (b-a) /2 > 0).
        field_simplify. now lra.
        
        now lra.
   
   unfold R_dist. unfold open_interval in H2. destruct H2. apply Rlt_trans with (alp/2).
    apply Rlt_le_trans with (Rmin ((b-a) / 2) (alp /2)).
     now rewrite Rabs_right; lra.
     
     now apply Rmin_r.
   
   now lra.
   
   intro. lra.
Qed.

Lemma limit1_in_open : forall f L a b c, open_interval a b c -> 
  limit1_in f (open_interval a c) L a ->
    limit1_in f (open_interval a b) L a.
Proof.
  intros. unfold limit1_in in *. unfold limit_in in *. intros. specialize (H0 eps H1).
  destruct H0 as [alp [Halp Hlim]]. exists (Rmin alp (c - a)). split.
   apply Rmin_glb_lt.
    now assumption.
    
    now destruct H; lra.
  
  intros. apply Hlim. destruct H0. unfold dist in *. simpl in *. unfold R_dist in *.
  split.
   split.
    now destruct H0; assumption.
    
    assert (Rabs (x - a) < c - a).
     apply Rlt_le_trans with (Rmin alp (c - a)).
      now apply H2.
      
      now apply Rmin_r.
   
   now rewrite Rabs_right in H3; destruct H0; lra.
   
   apply Rlt_le_trans with (Rmin alp (c - a)).
    now apply H2.
    
    apply Rmin_l.
Qed.

Lemma limit_div_neg_open1 : forall f a b c, open_interval a b c -> 
  limit_div_neg f (open_interval a b) a ->
    limit_div_neg f (open_interval a c) a. 
Proof.
  intros. unfold limit_div_neg in *. intros. specialize (H0 m H1). destruct H0 as [alp [Halp Hlim]].
  exists alp. intuition. apply Hlim.
   now destruct H; destruct H0; split; lra.
   
   apply H2.
Qed.

Lemma Hopital_gninf_Lfin_right
     : forall (f g : R -> R) (a b L : R),
       a < b ->
       forall (Df : forall x : R, open_interval a b x -> derivable_pt f x)
         (Dg : forall x : R, open_interval a b x -> derivable_pt g x),
       (forall x : R, a <= x <= b -> continuity_pt f x) ->
       (forall x : R, a <= x <= b -> continuity_pt g x) ->
       limit_div_neg g (open_interval a b) a ->
       (forall (x : R) (Hopen : open_interval a b x),
        derive_pt g x (Dg x Hopen) <> 0) ->
       (forall eps : R,
        eps > 0 ->
        exists alp : R,
          alp > 0 /\
          (forall (x : R) (Hopen : open_interval a b x),
           R_dist x a < alp ->
           R_dist (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)) L <
           eps)) ->
       limit1_in (fun x : R => f x / g x) (open_interval a b) L a.
Proof.
  intros. destruct (g_not_zero2 g a b H H2) as [a' [Hopen Ha']]. apply limit1_in_open with a'.
   now apply Hopen.
   
   apply limit1_ext with (fun x => - ( f x / (- g x))).
    intros. field. apply Ha'. now apply H5.
    
    replace L with (- - L) by ring. apply limit_Ropp. assert (Dg' :  forall x : R, open_interval a a' x -> derivable_pt (- g) x).
     intros. reg. apply Dg. split.
      now apply H5.
      
      apply Rlt_trans with a'.
       now apply H5.
       
       now apply Hopen.
  
  assert (Df' :  forall x : R, open_interval a a' x -> derivable_pt f x).
   intros. apply Df. split.
    now apply H5.
    
    apply Rlt_trans with a'.
     now apply H5.
     
     now apply Hopen.
  
  apply Hopital_gpinf_Lfin_right with Df' Dg'.
   now apply Hopen.
   
   intros. apply H0. split.
    now apply H5.
    
    apply Rle_trans with a'.
     now apply H5.
     
     apply Rlt_le. now apply Hopen.
   
   intros. reg. apply H1. split.
    now apply H5.
    
    apply Rle_trans with a'.
     now apply H5.
     
     apply Rlt_le. now apply Hopen.
   
   apply limit_div_Ropp.
    now apply Hopen.
    
    apply limit_div_neg_open1 with b.
     now assumption.
     
     now apply H2.
   
   intros. assert (Dg'' : forall x, open_interval a a' x -> derivable_pt g x).
    intros. apply Dg. split.
     now apply H5.
     
     apply Rlt_trans with a'.
      now apply H5.
      
      now apply Hopen.
   
   rewrite (pr_nu (-g)%F x _ (derivable_pt_opp g x (Dg'' x Hopen0))). rewrite derive_pt_opp.
   apply Ropp_neq_0_compat. assert (Hder : open_interval a b x).
    unfold open_interval in *. split.
     now apply Hopen0.
     
     now destruct Hopen, Hopen0; lra.
   
   rewrite (pr_nu g x _ (Dg x Hder)). now apply H3.
   
   intros. specialize (H4 eps H5). destruct H4 as [alp [Halp H10]]. exists alp. split.
    now assumption.
    
    intros. assert (Hder : open_interval a b x).
     unfold open_interval in *. split.
      now apply Hopen0.
      
      now destruct Hopen, Hopen0; lra.
  
  specialize (H10 x Hder H4). unfold R_dist in *. 
  replace (derive_pt (- g) x (Dg' x Hopen0)) with (- derive_pt g x (Dg x Hder)).
   replace (derive_pt f x (Df' x Hopen0)) with (derive_pt f x (Df x Hder)).
    replace (derive_pt f x (Df x Hder) / - derive_pt g x (Dg x Hder) - - L)
                    with (- (derive_pt f x (Df x Hder) / derive_pt g x (Dg x Hder) - L)).
     rewrite Rabs_Ropp. now assumption.
     
     field. now apply H3.
   
   now apply pr_nu.
   
   assert (Dg'' : forall x, open_interval a a' x -> derivable_pt g x).
    intros. apply Dg. split.
     now apply H6.
     
     apply Rlt_trans with a'.
      now apply H6.
      
      now apply Hopen.
  
  rewrite (pr_nu (-g)%F x _ (derivable_pt_opp g x (Dg'' x Hopen0))). rewrite derive_pt_opp.
  apply Ropp_eq_compat. apply pr_nu.
Qed.

End SndGenHopitalposneg.

Section SndGenHopitalposneg_left.


(*
Theoreme Hopital_gninf_Lfin_left: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> b-} g = -infinity
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
Hlimder: lim_{x -> b-} f' / g' = L    (with L \in R)
-----------------------------------------------------
lim_{x -> b-} f / g = L


*)

Lemma Hopital_gninf_Lfin_left
     : forall (f g : R -> R) (a b L : R),
       a < b ->
       forall (Df : forall x : R, open_interval a b x -> derivable_pt f x)
         (Dg : forall x : R, open_interval a b x -> derivable_pt g x),
       (forall x : R, a <= x <= b -> continuity_pt f x) ->
       (forall x : R, a <= x <= b -> continuity_pt g x) ->
       limit_div_neg g (open_interval a b) b ->
       (forall (x : R) (Hopen : open_interval a b x),
        derive_pt g x (Dg x Hopen) <> 0) ->
       (forall eps : R,
        eps > 0 ->
        exists alp : R,
          alp > 0 /\
          (forall (x : R) (Hopen : open_interval a b x),
           R_dist x b < alp ->
           R_dist (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)) L <
           eps)) ->
       limit1_in (fun x : R => f x / g x) (open_interval a b) L b.
Proof.
intros f g a b L Hab Df Dg Cf Cg Hdiv_neg g'_not_0 Hlimder.
  apply limit1_ext with (comp (fun x => f (-x) / g (-x)) (fun x => -x)).
   intros. unfold comp. ring_simplify (--x). now reflexivity.
   
   apply limit1_imp with (Dgf (open_interval a b) (open_interval (-b) (-a)) (fun x => - x)).
    intros. unfold Dgf. split.
     now apply H.
     
     now destruct H; split; lra.
  
  apply (limit_comp (fun x => - x) (fun x : R => f (- x) / g (- x)) _ _ (-b)).
   unfold limit1_in, limit_in. intros. exists eps. split.
    now assumption.
    
    intros. destruct H0. unfold dist in *. simpl in *. destruct H0. unfold R_dist in *.
    replace (- x -- b) with (- (x - b)) by ring. rewrite Rabs_Ropp. now apply H1.
  
  assert (Df': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => f (- x)) x).
   intros. reg. apply Df. now destruct H; split; lra.
   
   assert (Dg': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => g (- x)) x).
    intros. reg. apply Dg. now destruct H; split; lra.
    
    apply Hopital_gninf_Lfin_right with Df' Dg'.
     now intuition.
     
     intros. reg. apply Cf. now destruct H; split; lra.
     
     intros. reg. apply Cg. now destruct H; split; lra.

     apply limit_div_neg_opp. apply Hdiv_neg.

     intros.
     
     intros. assert (Hopen2: open_interval a b (-x)).
      now destruct Hopen; split; lra.
      
      intro. destruct (g'_not_0 (-x) Hopen2).
       assert (derive_pt (fun x0 : R => g (- x0)) x (Dg' x Hopen) = - derive_pt g (- x) (Dg (- x) Hopen2)).
        reg.
         apply Ropp_eq_compat. now apply pr_nu.
         
         apply Dg. now apply Hopen2.
       
       rewrite <- Ropp_involutive. symmetry. rewrite <- Ropp_involutive.
       replace 0 with (- 0) in H by ring. 
       apply Ropp_eq_compat. rewrite <- H. rewrite H0. reflexivity. 

intros eps Heps. specialize (Hlimder eps Heps).
destruct Hlimder as [alp [Halp Hsolve]].
exists alp. split. apply Halp.
intros.
assert (Hopenx : open_interval a b (-x)). split; destruct Hopen; lra.
assert (R_dist (-x) b < alp). unfold R_dist in *.
replace (- x - b) with (- (x + b)) by ring.
ring_simplify (x--b) in H.
rewrite Rabs_Ropp. apply H.
specialize (Hsolve (-x) Hopenx H0).
replace (derive_pt (fun x0 : R => f (- x0)) x (Df' x Hopen)) with 
  (- derive_pt f (- x) (Df (- x) Hopenx)).
replace (derive_pt (fun x0 : R => g (- x0)) x (Dg' x Hopen)) with 
  (- derive_pt g (- x) (Dg (- x) Hopenx)).
replace ((- derive_pt f (- x) (Df (- x) Hopenx) /
      - derive_pt g (- x) (Dg (- x) Hopenx))) with
((derive_pt f (- x) (Df (- x) Hopenx) /
      derive_pt g (- x) (Dg (- x) Hopenx))). apply Hsolve.

field. apply g'_not_0.

apply derive_pt_comp_Ropp.
apply derive_pt_comp_Ropp.
Qed.


End SndGenHopitalposneg_left.

Section InfiniteLimiteHopital_pos.

(*
Theorem Hopital_g0_Lpinf_right: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zf: lim_{x -> a+} f = 0
Zg: lim_{x -> a+} g = 0
Hlimder: lim_{x -> a+} f' / g' = +infinity
-----------------------------------------------------
lim_{x -> a+} f / g = +infinity

*)

Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).
Hypothesis (Zf : limit1_in f (open_interval a b) 0 a).
Hypothesis (Zg : limit1_in g (open_interval a b) 0 a).

Hypothesis (g_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0 /\ g x <> 0).
Hypothesis (Hlimder : forall m, m > 0 -> 
  exists alp,
    alp > 0 /\ 
      (forall x (Hopen: open_interval a b x), R_dist x a < alp ->
        m < (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)))).

Lemma Hopital_g0_Lpinf_right : forall m, m > 0 -> 
  exists alp,
    alp > 0 /\ 
      (forall x (Hopen: open_interval a b x), R_dist x a < alp ->
        m < (f x) / (g x)).
Proof.
  intros m Hm. specialize (Hlimder m Hm). destruct Hlimder as [alp [Halp Hlim]].
  exists alp. split.
   now assumption.
   
   intros. assert (Hacc2 : forall x, open_interval a b x ->  
     exists c, exists Hopenc, f x / g x = derive_pt f c (Df c Hopenc) / derive_pt g c (Dg c Hopenc) /\ a < c < x).
    generalize MVT. intros. specialize (H0 f g a x0). assert (forall c, a < c < x0 -> derivable_pt f c).
     intros. apply Df. unfold open_interval. split.
      now intuition.
      
      now apply Rlt_trans with x0; unfold open_interval in H1; intuition.
    
    assert (forall c, a < c < x0 -> derivable_pt g c).
     intros. apply Dg. unfold open_interval. split.
      now intuition.
      
      now apply Rlt_trans with x0; unfold open_interval in H1; intuition.
    
    specialize (H0 H2 H3). assert (a < x0) by (unfold open_interval in H1; intuition).
    assert (forall c : R, a <= c <= x0 -> continuity_pt f c).
     intros. apply Cf. split.
      now intuition.
      
      unfold open_interval in H1. now apply Rle_trans with x0; intuition.
    
    assert (forall c, a <= c <= x0 -> continuity_pt g c).
     intros. apply Cg. split.
      now intuition.
      
      unfold open_interval in H1. now apply Rle_trans with x0; intuition.
    
    specialize (H0 H4 H5 H6). destruct H0 as [c [P Hold2]]. exists c. assert (Hopenc : open_interval a b c).
     unfold open_interval in *. split.
      now apply P.
      
      apply Rlt_trans with x0.
       now apply P.
       
       now apply H1.
    
    exists Hopenc. split.
     rewrite (g_a_zero g a b) in Hold2. rewrite (f_a_zero f a b) in Hold2. do 2 rewrite Rminus_0_r in Hold2.
     apply (Rmult_eq_reg_l (g x0)).
      rewrite (pr_nu f c _ (H2 c P)). unfold Rdiv. do 2 rewrite <- Rmult_assoc. rewrite Hold2.
      rewrite (pr_nu g c _ (Dg c Hopenc)). field. generalize (g_not_0 c Hopenc). generalize (g_not_0 x0 H1).
      intros H01 H02. assert (c < b).
       now unfold open_interval in Hopenc; destruct Hopenc; assumption.
       
       split.
        now apply H02.
        
        now apply H01.
     
     apply g_not_0. now apply H1.
     
     apply Hab. apply Cf. apply Zf. apply Hab. apply Cg. apply Zg.
     now apply P.
  
  (* destruct H0.*) specialize (Hacc2 x Hopen). destruct Hacc2 as [c [Hopenc Haccc]]. specialize (Hlim c Hopenc).
  
  (*simpl in *.*) unfold R_dist in *. assert (open_interval a b c /\ Rabs (c - a) < alp).
   split.
    now apply Hopenc.
    
    destruct Haccc. destruct H1. rewrite Rabs_right.
     rewrite Rabs_right in H.
      now lra.
      
      now lra.
   
   now lra.
   
   destruct H0. specialize (Hlim H1). destruct Haccc. rewrite H2.
   apply Hlim.
Qed.


End InfiniteLimiteHopital_pos.

Section InfiniteLimiteHopital_pos_left.


(*
Theorem Hopital_g0_Lpinf_left: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zf: lim_{x -> b-} f = 0
Zg: lim_{x -> b-} g = 0
Hlimder: lim_{x -> b-} f' / g' = +infinity
-----------------------------------------------------
lim_{x -> b-} f / g = +infinity

*)

Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).
Hypothesis (Zf : limit1_in f (open_interval a b) 0 b).
Hypothesis (Zg : limit1_in g (open_interval a b) 0 b).


Hypothesis (g_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0 /\ g x <> 0).
Hypothesis (Hlimder : forall m, m > 0 -> 
  exists alp,
    alp > 0 /\ 
      (forall x (Hopen: open_interval a b x), R_dist x b < alp ->
        m < (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)))).

Lemma Hopital_g0_Lpinf_left : limit_div_pos (fun x => f x / g x) (open_interval a b) b.
Proof.
apply limit_div_pos_ext with (comp (fun x => f (- x) / g (- x)) (fun x => -x)). 
intros. unfold comp. ring_simplify (--x). reflexivity.
apply limit_div_pos_comp_Ropp.
  assert (Df': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => f (- x)) x).
   intros. reg. apply Df. now destruct H; split; lra.
   
   assert (Dg': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => g (- x)) x).
    intros. reg. apply Dg. now destruct H; split; lra.
    intros m Hm.
    apply Hopital_g0_Lpinf_right with Df' Dg'.
     now intuition.
     
     intros. reg. apply Cf. now destruct H; split; lra.
     
     intros. reg. apply Cg. now destruct H; split; lra.

     apply limit1_ext with (comp f (fun x => -x)). intros. reflexivity.
     apply limit1_imp with  (Dgf (open_interval (-b) (-a)) (open_interval a b) (fun x => - x)).
     intros. split. apply H. destruct H; split; lra.
     apply (limit_comp _ f _ _ b). unfold limit1_in, limit_in.
     intros. exists eps. split. intuition. intros. simpl in *. unfold R_dist in *.
     ring_simplify (x -- b) in H0. replace (- x - b) with (- (x + b)) by ring. rewrite Rabs_Ropp.
     apply H0. apply Zf.

     apply limit1_ext with (comp g (fun x => -x)). intros. reflexivity.
     apply limit1_imp with  (Dgf (open_interval (-b) (-a)) (open_interval a b) (fun x => - x)).
     intros. split. apply H. destruct H; split; lra.
     apply (limit_comp _ g _ _ b). unfold limit1_in, limit_in.
     intros. exists eps. split. intuition. intros. simpl in *. unfold R_dist in *.
     ring_simplify (x -- b) in H0. replace (- x - b) with (- (x + b)) by ring. rewrite Rabs_Ropp.
     apply H0. apply Zg.

     intros. split.
     assert (Hopen' : open_interval a b (-x)).  split; destruct Hopen; lra.
     generalize (g_not_0 (-x) Hopen'). intros. intro. destruct H. destruct H.
     erewrite <- (derive_pt_comp_Ropp a b g x Dg Dg' _ Hopen') in H0. replace 0 with (-0) by ring. 
     rewrite <- H0. ring.

     apply g_not_0. split; destruct Hopen; lra.
 
     intros m1 Hm1. specialize (Hlimder m1 Hm1).
     destruct Hlimder as [alp [Halp Hsolve1]].
     exists alp. split. apply Halp.
     intros. 
assert (Hopenx : open_interval a b (-x)). destruct Hopen; split; lra.
replace (derive_pt (fun x0 : R => f (- x0)) x (Df' x Hopen)) with 
  (- derive_pt f (- x) (Df (- x) Hopenx)).
replace (derive_pt (fun x0 : R => g (- x0)) x (Dg' x Hopen)) with 
  (- derive_pt g (- x) (Dg (- x) Hopenx)).
replace ((- derive_pt f (- x) (Df (- x) Hopenx) /
      - derive_pt g (- x) (Dg (- x) Hopenx))) with
((derive_pt f (- x) (Df (- x) Hopenx) /
      derive_pt g (- x) (Dg (- x) Hopenx))). 
apply Hsolve1. unfold R_dist in *.
replace (- x - b) with (- (x + b)) by ring. ring_simplify (x -- b) in H.
rewrite Rabs_Ropp. apply H.
field. apply g_not_0.
apply derive_pt_comp_Ropp.
apply derive_pt_comp_Ropp.
apply Hm.
Qed.


End InfiniteLimiteHopital_pos_left.

Section InfiniteLimiteHopital_neg.

(*
Theorem Hopital_g0_Lninf_right: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zf: lim_{x -> a+} f = 0
Zg: lim_{x -> a+} g = 0
Hlimder: lim_{x -> a+} f' / g' = -infinity
-----------------------------------------------------
lim_{x -> a+} f / g = -infinity

*)

Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).
Hypothesis (Zf : limit1_in f (open_interval a b) 0 a).
Hypothesis (Zg : limit1_in g (open_interval a b) 0 a).

Hypothesis (g_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0 /\ g x <> 0).
Hypothesis (Hlimder : forall m, m < 0 -> 
  exists alp,
    alp > 0 /\ 
      (forall x (Hopen: open_interval a b x), R_dist x a < alp ->
        m > (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)))).

Lemma Hopital_g0_Lninf_right : forall m, m < 0 -> 
  exists alp,
    alp > 0 /\ 
      (forall x (Hopen: open_interval a b x), R_dist x a < alp ->
        m > (f x) / (g x)).
Proof.
  intros m Hm. specialize (Hlimder m Hm). destruct Hlimder as [alp [Halp Hlim]].
  exists alp. split.
   now assumption.
   
   intros. assert (Hacc2 : forall x, open_interval a b x ->  
     exists c, exists Hopenc, f x / g x = derive_pt f c (Df c Hopenc) / derive_pt g c (Dg c Hopenc) /\ a < c < x).
    generalize MVT. intros. specialize (H0 f g a x0). assert (forall c, a < c < x0 -> derivable_pt f c).
     intros. apply Df. unfold open_interval. split.
      now intuition.
      
      now apply Rlt_trans with x0; unfold open_interval in H1; intuition.
    
    assert (forall c, a < c < x0 -> derivable_pt g c).
     intros. apply Dg. unfold open_interval. split.
      now intuition.
      
      now apply Rlt_trans with x0; unfold open_interval in H1; intuition.
    
    specialize (H0 H2 H3). assert (a < x0) by (unfold open_interval in H1; intuition).
    assert (forall c : R, a <= c <= x0 -> continuity_pt f c).
     intros. apply Cf. split.
      now intuition.
      
      unfold open_interval in H1. now apply Rle_trans with x0; intuition.
    
    assert (forall c, a <= c <= x0 -> continuity_pt g c).
     intros. apply Cg. split.
      now intuition.
      
      unfold open_interval in H1. now apply Rle_trans with x0; intuition.
    
    specialize (H0 H4 H5 H6). destruct H0 as [c [P Hold2]]. exists c. assert (Hopenc : open_interval a b c).
     unfold open_interval in *. split.
      now apply P.
      
      apply Rlt_trans with x0.
       now apply P.
       
       now apply H1.
    
    exists Hopenc. split.
     rewrite (g_a_zero g a b) in Hold2. rewrite (f_a_zero f a b) in Hold2. do 2 rewrite Rminus_0_r in Hold2.
     apply (Rmult_eq_reg_l (g x0)).
      rewrite (pr_nu f c _ (H2 c P)). unfold Rdiv. do 2 rewrite <- Rmult_assoc. rewrite Hold2.
      rewrite (pr_nu g c _ (Dg c Hopenc)). field. generalize (g_not_0 c Hopenc). generalize (g_not_0 x0 H1).
      intros H01 H02. assert (c < b).
       now unfold open_interval in Hopenc; destruct Hopenc; assumption.
       
       split.
        now apply H02.
        
        now apply H01.
     
     apply g_not_0. now apply H1.
     
     apply Hab. apply Cf. apply Zf. apply Hab. apply Cg. apply Zg.
     now apply P.
  
  (* destruct H0.*) specialize (Hacc2 x Hopen). destruct Hacc2 as [c [Hopenc Haccc]]. specialize (Hlim c Hopenc).
  
  (*simpl in *.*) unfold R_dist in *. assert (open_interval a b c /\ Rabs (c - a) < alp).
   split.
    now apply Hopenc.
    
    destruct Haccc. destruct H1. rewrite Rabs_right.
     rewrite Rabs_right in H.
      now lra.
      
      now lra.
   
   now lra.
   
   destruct H0. specialize (Hlim H1). destruct Haccc. rewrite H2.
   apply Hlim.
Qed.


End InfiniteLimiteHopital_neg.


Section InfiniteLimiteHopital_neg_left.

(*
Theorem Hopital_g0_Lninf_left: 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zf: lim_{x -> b-} f = 0
Zg: lim_{x -> b-} g = 0
Hlimder: lim_{x -> b-} f' / g' = -infinity
-----------------------------------------------------
lim_{x -> b-} f / g = -infinity

*)

Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).
Hypothesis (Zf : limit1_in f (open_interval a b) 0 b).
Hypothesis (Zg : limit1_in g (open_interval a b) 0 b).

Hypothesis (g_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0 /\ g x <> 0).
Hypothesis (Hlimder : forall m, m < 0 -> 
  exists alp,
    alp > 0 /\ 
      (forall x (Hopen: open_interval a b x), R_dist x b < alp ->
        m > (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)))).

Lemma Hopital_g0_Lninf_left : limit_div_neg (fun x => f x / g x) (open_interval a b) b.
Proof.
apply limit_div_neg_ext with (comp (fun x => f (- x) / g (- x)) (fun x => -x)). 
intros. unfold comp. ring_simplify (--x). reflexivity.
apply limit_div_neg_comp_Ropp.
  assert (Df': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => f (- x)) x).
   intros. reg. apply Df. now destruct H; split; lra.
   
   assert (Dg': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => g (- x)) x).
    intros. reg. apply Dg. now destruct H; split; lra.
    intros m Hm.
    apply Hopital_g0_Lninf_right with Df' Dg'.
     now intuition.
     
     intros. reg. apply Cf. now destruct H; split; lra.
     
     intros. reg. apply Cg. now destruct H; split; lra.

     apply limit1_ext with (comp f (fun x => -x)). intros. reflexivity.
     apply limit1_imp with  (Dgf (open_interval (-b) (-a)) (open_interval a b) (fun x => - x)).
     intros. split. apply H. destruct H; split; lra.
     apply (limit_comp _ f _ _ b). unfold limit1_in, limit_in.
     intros. exists eps. split. intuition. intros. simpl in *. unfold R_dist in *.
     ring_simplify (x -- b) in H0. replace (- x - b) with (- (x + b)) by ring. rewrite Rabs_Ropp.
     apply H0. apply Zf.

     apply limit1_ext with (comp g (fun x => -x)). intros. reflexivity.
     apply limit1_imp with  (Dgf (open_interval (-b) (-a)) (open_interval a b) (fun x => - x)).
     intros. split. apply H. destruct H; split; lra.
     apply (limit_comp _ g _ _ b). unfold limit1_in, limit_in.
     intros. exists eps. split. intuition. intros. simpl in *. unfold R_dist in *.
     ring_simplify (x -- b) in H0. replace (- x - b) with (- (x + b)) by ring. rewrite Rabs_Ropp.
     apply H0. apply Zg.

     intros. split.
     assert (Hopen' : open_interval a b (-x)).  split; destruct Hopen; lra.
     generalize (g_not_0 (-x) Hopen'). intros. intro. destruct H. destruct H.
     erewrite <- (derive_pt_comp_Ropp a b g x Dg Dg' _ Hopen') in H0. replace 0 with (-0) by ring. 
     rewrite <- H0. ring.

     apply g_not_0. split; destruct Hopen; lra.
 
     intros m1 Hm1. specialize (Hlimder m1 Hm1).
     destruct Hlimder as [alp [Halp Hsolve1]].
     exists alp. split. apply Halp.
     intros. 
assert (Hopenx : open_interval a b (-x)). destruct Hopen; split; lra.
replace (derive_pt (fun x0 : R => f (- x0)) x (Df' x Hopen)) with 
  (- derive_pt f (- x) (Df (- x) Hopenx)).
replace (derive_pt (fun x0 : R => g (- x0)) x (Dg' x Hopen)) with 
  (- derive_pt g (- x) (Dg (- x) Hopenx)).
replace ((- derive_pt f (- x) (Df (- x) Hopenx) /
      - derive_pt g (- x) (Dg (- x) Hopenx))) with
((derive_pt f (- x) (Df (- x) Hopenx) /
      derive_pt g (- x) (Dg (- x) Hopenx))). 
apply Hsolve1. unfold R_dist in *.
replace (- x - b) with (- (x + b)) by ring. ring_simplify (x -- b) in H.
rewrite Rabs_Ropp. apply H.
field. apply g_not_0.
apply derive_pt_comp_Ropp.
apply derive_pt_comp_Ropp.
lra.
Qed.

End InfiniteLimiteHopital_neg_left.

Section Hopital_infinite_pos.

(*
Theoreme Hopital_gpinf_Lpinf_right : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> a+} g = +infinity
Hlimder: lim_{x -> a+} f' / g' = +infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> a+} f / g = +infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_pos g (open_interval a b) a).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) > m))).

Theorem Hopital_gpinf_Lpinf_right : limit_div_pos (fun x => f x / g x) (open_interval a b) a.
Proof.
  destruct (g_not_zero g a b Hab Zg) as [a' [H1 Ha']]. unfold limit_div_pos. intros eps H. assert (Hacc2' : forall x y, open_interval a a' x -> open_interval a a' y -> x < y -> 
     exists c, exists Hopenc, f x / g x = (1 - (g y / g x)) * 
                     derive_pt f c (Df c Hopenc) / derive_pt g c (Dg c Hopenc) + (f y / g x) /\ x < c < y).
   intros. assert (open_interval a b x).
    split.
     now apply H0.
     
     apply Rlt_trans with a'.
      now apply H0.
      
      now apply H1.
   
   assert (open_interval a b y).
    split.
     now apply H2.
     
     apply Rlt_trans with a'.
      now apply H2.
      
      now apply H1.
   
   generalize (MVT_unusable f g a b Df Dg Cf Cg a' H1 x y H0 H2 H3). intros Hacc2'. destruct Hacc2' as [c [Hopenc [Hacc2' H7]]].
   exists c. exists Hopenc. split; [ | now intuition]. apply (Rplus_eq_reg_l (- (f y / g x))).
   ring_simplify. apply (Rmult_eq_reg_l (g x)).
    apply (Rmult_eq_reg_l (derive_pt g c (Dg c Hopenc))).
     apply (Rmult_eq_reg_l (-1)).
      field_simplify.
       field_simplify in Hacc2'. replace (derive_pt g c (Dg c Hopenc) * f y - derive_pt g c (Dg c Hopenc) * f x)
           with (f y * derive_pt g c (Dg c Hopenc) - f x * derive_pt g c (Dg c Hopenc)) by ring.
       rewrite Hacc2'. now field.
       
       split.
        apply Ha'. now apply H0.
        
        now apply (g'_not_0 c Hopenc).
      
      now apply Ha'; assumption.
      
      intro. now lra.
    
    now apply g'_not_0.
    
    now apply Ha'; assumption.

   assert (H0: forall eps, eps > 0 -> 
         exists y, open_interval a a' y /\ forall c (Hopen : open_interval a y c) (Hopenc : open_interval a b c),
           (derive_pt f c (Df c Hopenc) / derive_pt g c (Dg c Hopenc)) > 2 * eps + 2).
   intros eps0 Heps0. assert (Hdeb4: 2 * eps0 + 2 > 0) by lra. specialize (Hlimder (2 * eps0 + 2) Hdeb4). destruct Hlimder as [alp [Halp Hlimder1]].
   exists (a + Rmin ((a'-a) / 2) alp). split.
    apply open_lemma.
     now apply H1.
     
     now apply Halp.
   
   intros. specialize (Hlimder1 c Hopenc). unfold R_dist in *. apply Hlimder1. destruct Hopen.
   apply Rlt_le_trans with (Rmin ((a' - a) / 2) alp).
    now rewrite Rabs_right; lra.
    
    now apply Rmin_r.
  
  assert (H15 : forall A eps, eps > 0 -> exists alp, 
           alp > 0 /\ forall x, open_interval a b x -> R_dist x a < alp -> Rabs (A / g x) < eps).
   intros. unfold limit_div_pos in Zg. destruct (Req_dec A 0) as [eq_dec1 | eq_dec2].
    subst. exists 1. intuition. unfold Rdiv. rewrite Rmult_0_l. rewrite Rabs_R0. now assumption.
    
    specialize (Zg (Rabs A / eps0)). assert (Rabs A /eps0 > 0).
     assert (Rabs A > 0).
      apply Rabs_pos_lt. now assumption.
      
      unfold Rdiv. assert (/eps0 > 0).
       now apply Rinv_0_lt_compat; assumption.
       
       now apply Rmult_lt_0_compat; assumption.
   
   specialize (Zg H3). destruct Zg as [alp [Halp Zg3]]. exists alp. intuition. unfold Rdiv.
   rewrite Rabs_mult. specialize (Zg3 x H4 H5). assert (g x > 0).
    apply Rlt_trans with (Rabs A / eps0).
     now assumption.
     
     now assumption.
   
   rewrite Rabs_Rinv.
    rewrite (Rabs_right (g x)).
     apply (Rmult_lt_reg_l (g x)).
      now assumption.
      
      apply (Rmult_lt_reg_l (/eps0)).
       apply Rinv_0_lt_compat. now apply H2.
       
       field_simplify.
        unfold Rdiv. try rewrite Rinv_1. try rewrite Rmult_1_r. now apply Zg3.
        
        intro. now lra.
        
        split.
         intro. now lra.
         
         intro. now lra.
    
    now lra.
    
    intro. now lra.
    
  specialize (H0 (eps) H). destruct H0 as [y [open H0]]. assert (Hdeb3 : 2 * eps  + 2> 0) by lra.
  specialize (Hlimder (2 * eps + 2) Hdeb3).
  destruct Hlimder as [alp1 [Halp1 Hlim2]]. assert (Hdeb : 1 > 0) by lra. generalize (H15 (f y) (1) Hdeb).
  intros H16. destruct H16 as [alp2 [Halp2 Hlim3]].
  assert (Hdeb2 : 1 / 2 > 0) by lra.
  generalize (H15 (g y) (1/2) Hdeb2). intros H16. destruct H16 as [alp3 [Halp3 Hlim4]].

  pose (alp_alp := Rmin (Rmin alp1 alp2) alp3). pose (alp := Rmin (Rmin alp_alp (a' - a)) (y - a)).
  exists alp. split.
   apply Rmin_pos.
    apply Rmin_pos.
     apply Rmin_pos.
     apply Rmin_pos; assumption.
      
    
    unfold open_interval in H1. destruct H1. now lra.
    
    unfold open_interval in open. destruct open. now lra.
    destruct open; lra.
  
  intros. specialize (Hacc2' x y). assert (open_interval a a' x).
   unfold dist in H2. simpl in H2. unfold R_dist in H2. split.
    now apply H2.
    
    assert (Rabs (x - a) < Rabs (a' - a)).
     rewrite (Rabs_right (a' - a)).
      unfold alp in H2. apply Rlt_le_trans with (Rmin (Rmin alp_alp (a' - a)) (y - a)).
       now intuition.
       
       apply Rle_trans with (Rmin alp_alp (a' - a)).
        now apply Rmin_l.
        
        now apply Rmin_r.
     
     destruct H1. now lra.
     
     do 2 rewrite Rabs_right in H4.
      now lra.
      
      now destruct H1; lra.
      
      destruct H2. lra. destruct H2; lra.
  
  assert (open_interval a a' y).
   now apply open.
   
   specialize (Hacc2' H4 H5). assert (x < y).
    unfold alp in H2. unfold dist in H2. simpl in H2. unfold R_dist in H2. assert (Rabs (x - a) < Rabs (y - a)).
     rewrite (Rabs_right (y - a)).
      unfold alp in H2. apply Rlt_le_trans with (Rmin (Rmin alp_alp (a' - a)) (y - a)).
       now intuition.
       
       now apply Rmin_r.
     
     destruct H5. now lra.
     
     do 2 rewrite Rabs_right in H6.
      now lra.
      
      now destruct H5; lra.
      
      now destruct H4; lra.
      
      now destruct H4; lra.
  
  specialize (Hacc2' H6). destruct Hacc2' as [c [Hopenc H10]]. destruct H10 as [H10 H100].
  rewrite H10.
  

 unfold Rdiv. 
 apply Rlt_trans with ((1 - g y * / g x) * derive_pt f c (Df c Hopenc) *
   / derive_pt g c (Dg c Hopenc) - 1).
 
 rewrite Rmult_assoc.
 apply Rle_lt_trans with ((1 / 2) * (2 * eps + 2) - 1).
 replace (1 / 2 * (2 * eps + 2) - 1) with eps. intuition.
 field.
 unfold Rminus.
 apply Rplus_lt_compat_r.
 apply Rlt_trans with (1 / 2 *(derive_pt f c (Df c Hopenc) * / derive_pt g c (Dg c Hopenc)) ).
 apply Rmult_lt_compat_l. lra.
 apply H0.
 split. apply Hopenc. apply H100.

 apply Rmult_lt_compat_r. apply Rlt_trans with (2 * eps + 2). lra.
apply H0.
 split. apply Hopenc. apply H100.
 
 assert (HH : R_dist x a < alp3).
 apply Rlt_le_trans with (Rmin (Rmin alp1 alp2) alp3).
 apply Rlt_le_trans with (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)).
         apply Rlt_le_trans with (Rmin (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)) (y - a)).
          now apply H3.
          
          now apply Rmin_l.
        
        now apply Rmin_l.
        
        now apply Rmin_r.
      
 specialize (Hlim4 x H2 HH). apply Rabs_def2 in Hlim4. 
 apply Rle_lt_trans with (1 - 1/2). lra. unfold Rminus. 
 apply Rplus_lt_compat_l. destruct Hlim4. intuition.
 apply Rplus_lt_compat_l.  
assert (HH : R_dist x a < alp2).
apply Rlt_le_trans with (Rmin alp1 alp2).
 apply Rlt_le_trans with (Rmin (Rmin alp1 alp2) alp3).
 apply Rlt_le_trans with (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)).
         apply Rlt_le_trans with (Rmin (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)) (y - a)).
          now apply H3.
          
          now apply Rmin_l.
        
        now apply Rmin_l. now apply Rmin_l.
        
        now apply Rmin_r. specialize (Hlim3 x H2 HH).
  apply Rabs_def2 in Hlim3. intuition.
Qed.

End Hopital_infinite_pos.

Section Hopital_infinite_pos_left.

(*
Theoreme Hopital_gpinf_Lpinf_left : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> b-} g = +infinity
Hlimder: lim_{x -> b-} f' / g' = +infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> b-} f / g = +infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_pos g (open_interval a b) b).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x b < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) > m))).

Theorem Hopital_gpinf_Lpinf_left : limit_div_pos (fun x => f x / g x) (open_interval a b) b.
Proof.
apply limit_div_pos_ext with (comp (fun x => f (- x) / g (- x)) (fun x => -x)). 
intros. unfold comp. ring_simplify (--x). reflexivity.
apply limit_div_pos_comp_Ropp.
  assert (Df': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => f (- x)) x).
   intros. reg. apply Df. now destruct H; split; lra.
   
   assert (Dg': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => g (- x)) x).
    intros. reg. apply Dg. now destruct H; split; lra.
    intros m Hm.
    apply Hopital_gpinf_Lpinf_right with Df' Dg'.
     now intuition.
     
     intros. reg. apply Cf. now destruct H; split; lra.
     
     intros. reg. apply Cg. now destruct H; split; lra.

     apply limit_div_pos_ext with (comp g (fun x => -x)). intros. reflexivity.
     apply limit_div_pos_comp_Ropp_l. do 2  rewrite Ropp_involutive.
     apply Zg.
     
     intros. assert (Hopen' : open_interval a b (-x)). 
     destruct Hopen; split; lra.
     rewrite <- (derive_pt_comp_Ropp _ _ _ _ Dg _ _ Hopen'). replace 0 with (-0) by ring. 
     intro. apply Ropp_eq_compat in H. do 2 rewrite Ropp_involutive in H. 
     apply g'_not_0 in H. apply H.
     
     intros m1 Hm1. specialize (Hlimder m1 Hm1).
     destruct Hlimder as [alp [Halp Hsolve1]].
     exists alp. split. apply Halp.
     intros. 
assert (Hopenx : open_interval a b (-x)). destruct Hopen; split; lra.
replace (derive_pt (fun x0 : R => f (- x0)) x (Df' x Hopen)) with 
  (- derive_pt f (- x) (Df (- x) Hopenx)).
replace (derive_pt (fun x0 : R => g (- x0)) x (Dg' x Hopen)) with 
  (- derive_pt g (- x) (Dg (- x) Hopenx)).
replace ((- derive_pt f (- x) (Df (- x) Hopenx) /
      - derive_pt g (- x) (Dg (- x) Hopenx))) with
((derive_pt f (- x) (Df (- x) Hopenx) /
      derive_pt g (- x) (Dg (- x) Hopenx))). 
apply Hsolve1. unfold R_dist in *.
replace (- x - b) with (- (x + b)) by ring. ring_simplify (x -- b) in H.
rewrite Rabs_Ropp. apply H.
field. apply g'_not_0.
apply derive_pt_comp_Ropp.
apply derive_pt_comp_Ropp.
lra.
Qed.

End Hopital_infinite_pos_left.


Section Hopital_infinite_neg.

(*
Theoreme Hopital_gpinf_Lninf_right : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> a+} g = +infinity
Hlimder: lim_{x -> a+} f' / g' = -infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> a+} f / g = -infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_pos g (open_interval a b) a).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) < -m))).

Theorem Hopital_gpinf_Lninf_right : limit_div_neg (fun x => f x / g x) (open_interval a b) a.
Proof.
  destruct (g_not_zero g a b Hab Zg) as [a' [H1 Ha']]. unfold limit_div_neg. intros eps H. assert (Hacc2' : forall x y, open_interval a a' x -> open_interval a a' y -> x < y -> 
     exists c, exists Hopenc, f x / g x = (1 - (g y / g x)) * 
                     derive_pt f c (Df c Hopenc) / derive_pt g c (Dg c Hopenc) + (f y / g x) /\ x < c < y).
   intros. assert (open_interval a b x).
    split.
     now apply H0.
     
     apply Rlt_trans with a'.
      now apply H0.
      
      now apply H1.
   
   assert (open_interval a b y).
    split.
     now apply H2.
     
     apply Rlt_trans with a'.
      now apply H2.
      
      now apply H1.
   
   generalize (MVT_unusable f g a b Df Dg Cf Cg a' H1 x y H0 H2 H3). intros Hacc2'. destruct Hacc2' as [c [Hopenc [Hacc2' H7]]].
   exists c. exists Hopenc. split; [ | now intuition]. apply (Rplus_eq_reg_l (- (f y / g x))).
   ring_simplify. apply (Rmult_eq_reg_l (g x)).
    apply (Rmult_eq_reg_l (derive_pt g c (Dg c Hopenc))).
     apply (Rmult_eq_reg_l (-1)).
      field_simplify.
       field_simplify in Hacc2'. replace (derive_pt g c (Dg c Hopenc) * f y - derive_pt g c (Dg c Hopenc) * f x)
           with (f y * derive_pt g c (Dg c Hopenc) - f x * derive_pt g c (Dg c Hopenc)) by ring.
       rewrite Hacc2'. now field.
       
       split.
        apply Ha'. now apply H0.
        
        now apply (g'_not_0 c Hopenc).
      
      now apply Ha'; assumption.
      
      intro. now lra.
    
    now apply g'_not_0.
    
    now apply Ha'; assumption.

   assert (H0: forall eps, eps > 0 -> 
         exists y, open_interval a a' y /\ forall c (Hopen : open_interval a y c) (Hopenc : open_interval a b c),
           (derive_pt f c (Df c Hopenc) / derive_pt g c (Dg c Hopenc)) < - (2 * eps + 2)).
   intros eps0 Heps0. assert (Hdeb4: 2 * eps0 + 2 > 0) by lra. specialize (Hlimder (2 * eps0 + 2) Hdeb4). destruct Hlimder as [alp [Halp Hlimder1]].
   exists (a + Rmin ((a'-a) / 2) alp). split.
    apply open_lemma.
     now apply H1.
     
     now apply Halp.
   
   intros. specialize (Hlimder1 c Hopenc). unfold R_dist in *. apply Hlimder1. destruct Hopen.
   apply Rlt_le_trans with (Rmin ((a' - a) / 2) alp).
    now rewrite Rabs_right; lra.
    
    now apply Rmin_r.
  
  assert (H15 : forall A eps, eps > 0 -> exists alp, 
           alp > 0 /\ forall x, open_interval a b x -> R_dist x a < alp -> Rabs (A / g x) < eps).
   intros. unfold limit_div_pos in Zg. destruct (Req_dec A 0) as [eq_dec1 | eq_dec2].
    subst. exists 1. intuition. unfold Rdiv. rewrite Rmult_0_l. rewrite Rabs_R0. now assumption.
    
    specialize (Zg (Rabs A / eps0)). assert (Rabs A /eps0 > 0).
     assert (Rabs A > 0).
      apply Rabs_pos_lt. now assumption.
      
      unfold Rdiv. assert (/eps0 > 0).
       now apply Rinv_0_lt_compat; assumption.
       
       now apply Rmult_lt_0_compat; assumption.
   
   specialize (Zg H3). destruct Zg as [alp [Halp Zg3]]. exists alp. intuition. unfold Rdiv.
   rewrite Rabs_mult. specialize (Zg3 x H4 H5). assert (g x > 0).
    apply Rlt_trans with (Rabs A / eps0).
     now assumption.
     
     now assumption.
   
   rewrite Rabs_Rinv.
    rewrite (Rabs_right (g x)).
     apply (Rmult_lt_reg_l (g x)).
      now assumption.
      
      apply (Rmult_lt_reg_l (/eps0)).
       apply Rinv_0_lt_compat. now apply H2.
       
       field_simplify.
        unfold Rdiv. try rewrite Rinv_1. try rewrite Rmult_1_r. now apply Zg3.
        
        intro. now lra.
        
        split.
         intro. now lra.
         
         intro. now lra.
    
    now lra.
    
    intro. now lra.
  
  specialize (H0 (eps) H). destruct H0 as [y [open H0]]. assert (Hdeb3 : 2 * eps  + 2> 0) by lra.
  specialize (Hlimder (2 * eps + 2) Hdeb3).
  destruct Hlimder as [alp1 [Halp1 Hlim2]]. assert (Hdeb : 1 > 0) by lra. generalize (H15 (f y) (1) Hdeb).
  intros H16. destruct H16 as [alp2 [Halp2 Hlim3]].
  assert (Hdeb2 : 1 / 2 > 0) by lra.
  generalize (H15 (g y) (1/2) Hdeb2). intros H16. destruct H16 as [alp3 [Halp3 Hlim4]].

  pose (alp_alp := Rmin (Rmin alp1 alp2) alp3). pose (alp := Rmin (Rmin alp_alp (a' - a)) (y - a)).
  exists alp. split.
   apply Rmin_pos.
    apply Rmin_pos.
     apply Rmin_pos.
     apply Rmin_pos; assumption.
      
    
    unfold open_interval in H1. destruct H1. now lra.
    
    unfold open_interval in open. destruct open. now lra.
    destruct open; lra.
  
  intros. specialize (Hacc2' x y). assert (open_interval a a' x).
   unfold dist in H2. simpl in H2. unfold R_dist in H2. split.
    now apply H2.
    
    assert (Rabs (x - a) < Rabs (a' - a)).
     rewrite (Rabs_right (a' - a)).
      unfold alp in H2. apply Rlt_le_trans with (Rmin (Rmin alp_alp (a' - a)) (y - a)).
       now intuition.
       
       apply Rle_trans with (Rmin alp_alp (a' - a)).
        now apply Rmin_l.
        
        now apply Rmin_r.
     
     destruct H1. now lra.
     
     do 2 rewrite Rabs_right in H4.
      now lra.
      
      now destruct H1; lra.
      
      destruct H2. lra. destruct H2; lra.
  
  assert (open_interval a a' y).
   now apply open.
   
   specialize (Hacc2' H4 H5). assert (x < y).
    unfold alp in H3. unfold dist in H3. simpl in H3. unfold R_dist in H3. assert (Rabs (x - a) < Rabs (y - a)).
     rewrite (Rabs_right (y - a)).
      unfold alp in H3. apply Rlt_le_trans with (Rmin (Rmin alp_alp (a' - a)) (y - a)).
       now intuition.
       
       now apply Rmin_r.
     
     destruct H5. now lra.
     
     do 2 rewrite Rabs_right in H6.
      now lra.
      
      now destruct H5; lra.
      
      now destruct H4; lra.
      
      now destruct H4; lra.
  
  specialize (Hacc2' H6). destruct Hacc2' as [c [Hopenc H10]]. destruct H10 as [H10 H100].
  rewrite H10.
  

 unfold Rdiv. 
 apply Rlt_trans with ((1 - g y * / g x) * derive_pt f c (Df c Hopenc) *
   / derive_pt g c (Dg c Hopenc) + 1).
 
 rewrite Rmult_assoc.
 apply Rplus_lt_compat_l. specialize (Hlim3 x H2).
 assert (R_dist x a < alp2). 
apply Rlt_le_trans with (Rmin alp1 alp2).
 apply Rlt_le_trans with (Rmin (Rmin alp1 alp2) alp3).
 apply Rlt_le_trans with (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)).
         apply Rlt_le_trans with (Rmin (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)) (y - a)).
          now apply H3.
          
          now apply Rmin_l.
        
        now apply Rmin_l. now apply Rmin_l.
        
        now apply Rmin_r.
 specialize (Hlim3 H7). apply Rabs_def2 in Hlim3. apply Hlim3.
 apply Rlt_le_trans with (1 / 2 * (- (2 * eps + 2)) + 1).
 apply Rplus_lt_compat_r. 
 apply Rlt_trans with ((1 - g y * / g x) * (- (2 * eps + 2))).
 rewrite Rmult_assoc. apply Rmult_lt_compat_l. 
 replace 0 with (1 - 1). apply Rplus_lt_compat_l.
 apply Ropp_gt_lt_contravar. apply Rlt_trans with (1 / 2).
 assert (R_dist x a < alp3). 
 apply Rlt_le_trans with (Rmin (Rmin alp1 alp2) alp3).
 apply Rlt_le_trans with (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)).
 apply Rlt_le_trans with (Rmin (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)) (y - a)).
 apply H3. apply Rmin_l. apply Rmin_l. apply Rmin_r.
 specialize (Hlim4 x H2 H7). apply Rabs_def2. apply Hlim4.
 lra. ring.
 apply H0. 
 split. apply Hopenc. apply H100.

 do 2 rewrite Ropp_mult_distr_r_reverse. 
 apply Ropp_gt_lt_contravar. apply Rmult_lt_compat_r. intuition.
 replace (1 /2) with (1 - 1/ 2) by field.
 apply Rplus_lt_compat_l. apply Ropp_gt_lt_contravar.
 specialize (Hlim4 x H2). assert (R_dist x a < alp3).
 apply Rlt_le_trans with (Rmin (Rmin alp1 alp2) alp3).
 apply Rlt_le_trans with (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)).
 apply Rlt_le_trans with (Rmin (Rmin (Rmin (Rmin alp1 alp2) alp3) (a' - a)) (y - a)).
 apply H3. apply Rmin_l. apply Rmin_l. apply Rmin_r.

 specialize (Hlim4 H7). apply Rabs_def2 in Hlim4. apply Hlim4.

 apply Req_le. field.
Qed.
 
End Hopital_infinite_neg.

Section Hopital_infinite_neg_left.


(*
Theoreme Hopital_gpinf_Lninf_left : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> b-} g = +infinity
Hlimder: lim_{x -> b-} f' / g' = -infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> b-} f / g = -infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_pos g (open_interval a b) b).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x b < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) < -m))).

Theorem Hopital_gpinf_Lninf_left : limit_div_neg (fun x => f x / g x) (open_interval a b) b.
Proof.
apply limit_div_neg_ext with (comp (fun x => f (- x) / g (- x)) (fun x => -x)). 
intros. unfold comp. ring_simplify (--x). reflexivity.
apply limit_div_neg_comp_Ropp.
  assert (Df': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => f (- x)) x).
   intros. reg. apply Df. now destruct H; split; lra.
   
   assert (Dg': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => g (- x)) x).
    intros. reg. apply Dg. now destruct H; split; lra.
    intros m Hm.
    apply Hopital_gpinf_Lninf_right with Df' Dg'.
     now intuition.
     
     intros. reg. apply Cf. now destruct H; split; lra.
     
     intros. reg. apply Cg. now destruct H; split; lra.

     apply limit_div_pos_ext with (comp g (fun x => -x)). intros. reflexivity.
     apply limit_div_pos_comp_Ropp_l. do 2  rewrite Ropp_involutive.
     apply Zg.
     
     intros. assert (Hopen' : open_interval a b (-x)). 
     destruct Hopen; split; lra.
     rewrite <- (derive_pt_comp_Ropp _ _ _ _ Dg _ _ Hopen'). replace 0 with (-0) by ring. 
     intro. apply Ropp_eq_compat in H. do 2 rewrite Ropp_involutive in H. 
     apply g'_not_0 in H. apply H.
     
     intros m1 Hm1. specialize (Hlimder m1 Hm1).
     destruct Hlimder as [alp [Halp Hsolve1]].
     exists alp. split. apply Halp.
     intros. 
assert (Hopenx : open_interval a b (-x)). destruct Hopen; split; lra.
replace (derive_pt (fun x0 : R => f (- x0)) x (Df' x Hopen)) with 
  (- derive_pt f (- x) (Df (- x) Hopenx)).
replace (derive_pt (fun x0 : R => g (- x0)) x (Dg' x Hopen)) with 
  (- derive_pt g (- x) (Dg (- x) Hopenx)).
replace ((- derive_pt f (- x) (Df (- x) Hopenx) /
      - derive_pt g (- x) (Dg (- x) Hopenx))) with
((derive_pt f (- x) (Df (- x) Hopenx) /
      derive_pt g (- x) (Dg (- x) Hopenx))). 
apply Hsolve1. unfold R_dist in *.
replace (- x - b) with (- (x + b)) by ring. ring_simplify (x -- b) in H.
rewrite Rabs_Ropp. apply H.
field. apply g'_not_0.
apply derive_pt_comp_Ropp.
apply derive_pt_comp_Ropp.
lra.
Qed.

End Hopital_infinite_neg_left.

Section Useless.

(*
Theoreme Hopital_infinite_pos : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> a+} g = -infinity
Hlimder: lim_{x -> a+} f' / g' = +infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
g_not_zero : \forall x \in ]a ; b[, g x <> 0
-----------------------------------------------------
lim_{x -> a+} f / g = +infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_neg g (open_interval a b) a).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) > m))).

Hypothesis (g_not_0 : forall x (Hopen: open_interval a b x), g x <> 0).

Theorem Hopital_infinite_inf_neg_lpos_useless : limit_div_pos (fun x => f x / g x) (open_interval a b) a.
Proof.
apply limit_div_pos_inv.
apply limit_div_neg_ext with (fun x => (f x) / (- g x)).
intros. field. apply g_not_0. apply H.
assert (Dg' : forall x, open_interval a b x -> derivable_pt (- g) x). intros. reg. apply Dg; intuition.
apply Hopital_gpinf_Lninf_right with Df Dg'; try assumption; try reg; try (now intuition). apply limit_div_pos_inv. 
apply limit_div_neg_ext with g. intros. unfold opp_fct. ring. apply Zg.
intros. intro. apply g'_not_0 with x Hopen. rewrite (pr_nu _ _ _ (derivable_pt_opp g x (Dg x Hopen))) in H.
rewrite  derive_pt_opp in H. apply Ropp_eq_0_compat in H. rewrite <- H. ring.
intros m Hm. destruct (Hlimder m Hm) as [alp [Halp Hsolve]]. 
exists alp. split. assumption.
intros. specialize (Hsolve x Hopen H).
replace (derive_pt f x (Df x Hopen) / derive_pt (- g) x (Dg' x Hopen)) with (-  (derive_pt f x (Df x Hopen) / derive_pt (g) x (Dg x Hopen))).
apply Ropp_gt_lt_contravar. apply Hsolve.
unfold Rdiv. rewrite (pr_nu _ _ _ (derivable_pt_opp g x (Dg x Hopen))). rewrite derive_pt_opp.
field. apply g'_not_0.
Qed.

End Useless.

Section Hopital_infinite_neg_pos.

(*
Theoreme Hopital_gninf_Lpinf_right : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> a+} g = -infinity
Hlimder: lim_{x -> a+} f' / g' = +infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> a+} f / g = +infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_neg g (open_interval a b) a).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) > m))).

Lemma new_bound : exists b', (forall x, open_interval a b' x -> g x <> 0) /\ open_interval a b b'.
Proof.
unfold limit_div_neg in Zg.
assert (1 > 0) by lra. destruct (Zg 1 H) as [alp [Halp Hsolve]].
exists (Rmin (a + alp) ((b + a) / 2)). split. intros. specialize (Hsolve x).
assert (H3 : open_interval a b x).
split. apply H0. destruct H0. apply Rlt_le_trans with (Rmin (a + alp) ((b + a) / 2)).
apply H1. apply Rle_trans with ((b + a)/ 2). apply Rmin_r. 
apply Rle_trans with ((b + b) /2). assert (b + a <= b + b) by lra. unfold Rdiv. apply Rmult_le_compat_r. 
lra. apply H2. apply Req_le. field.
 specialize (Hsolve H3).
assert (R_dist x a < alp). destruct H0. assert (x < a + alp).
apply Rlt_le_trans with (Rmin (a + alp) ((b + a) /2)). apply H1.
apply Rmin_l. unfold R_dist. rewrite Rabs_right. lra.
lra. specialize (Hsolve H1). intro. lra.
split. apply Rmin_glb_lt. lra. apply Rle_lt_trans with ((a +a) / 2). apply Req_le. field. 
unfold Rdiv. apply Rmult_lt_compat_r. lra. intuition.
apply Rle_lt_trans with ((b + a) / 2). apply Rmin_r.
apply Rlt_le_trans with ((b + b) / 2). unfold Rdiv. apply Rmult_lt_compat_r. lra. intuition. 
apply Req_le. field.
Qed.

Theorem Hopital_gninf_Lpinf_right : limit_div_pos (fun x => f x / g x) (open_interval a b) a.
Proof.
destruct new_bound as (b', H0).
apply limit_div_pos_open with b'. intuition.
assert (Df' : forall x, open_interval a b' x -> derivable_pt f x). intros. apply Df. 
destruct H; split; destruct H0 as [H5  [H2  H4]]; lra.
assert (Dg' : forall x, open_interval a b' x -> derivable_pt g x). 
intros. apply Dg.
destruct H; split; destruct H0 as [H5  [H2  H4]]; lra. 
destruct H0. destruct H0.
apply Hopital_infinite_inf_neg_lpos_useless with Df' Dg'.
apply H0.
intros. apply Cf. intuition. lra.
intros. apply Cg; intuition; lra.
apply (limit_div_neg_open1 g a b b'). split; assumption.  (* TODO remove limit_div_neg_open1 et remettre limit_div_neg_open a la place *) apply Zg.
intros. assert (Hopen2 : open_interval a b x). destruct Hopen; split. 
apply H2. lra. rewrite (pr_nu _ _ _ (Dg x Hopen2)). apply g'_not_0.
intros m Hm. specialize (Hlimder m Hm). destruct Hlimder as [alp [Halp Hsolve]].
exists alp. split. assumption. intros. assert (Hopen2 : open_interval a b x).
split; destruct Hopen; lra. specialize (Hsolve x Hopen2 H2).
replace (derive_pt f x (Df' x Hopen)) with (derive_pt f x (Df x Hopen2)) by (apply pr_nu).
replace (derive_pt g x (Dg' x Hopen)) with (derive_pt g x (Dg x Hopen2)) by (apply pr_nu).
apply Hsolve.
intuition.
Qed.


End Hopital_infinite_neg_pos.

Section Hopital_infinite_neg_pos_left.
(*
Theoreme Hopital_gninf_Lpinf_left : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> b-} g = -infinity
Hlimder: lim_{x -> b-} f' / g' = +infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> b-} f / g = +infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_neg g (open_interval a b) b).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x b < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) > m))).

Theorem Hopital_gninf_Lpinf_left : limit_div_pos (fun x => f x / g x) (open_interval a b) b.
Proof.
apply limit_div_pos_ext with (comp (fun x => f (- x) / g (- x)) (fun x => -x)).
intros. unfold comp. ring_simplify (--x). reflexivity.
apply limit_div_pos_comp_Ropp.
  assert (Df': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => f (- x)) x).
   intros. reg. apply Df. now destruct H; split; lra.
   
   assert (Dg': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => g (- x)) x).
    intros. reg. apply Dg. now destruct H; split; lra.
    intros m Hm.
    apply Hopital_gninf_Lpinf_right with Df' Dg'.
     now intuition.
     
     intros. reg. apply Cf. now destruct H; split; lra.
     
     intros. reg. apply Cg. now destruct H; split; lra.

     apply limit_div_neg_ext with (comp g (fun x => -x)). intros. reflexivity.
     apply limit_div_neg_comp_Ropp_l. do 2  rewrite Ropp_involutive.
     apply Zg.
     
     intros. assert (Hopen' : open_interval a b (-x)). 
     destruct Hopen; split; lra.
     rewrite <- (derive_pt_comp_Ropp _ _ _ _ Dg _ _ Hopen'). replace 0 with (-0) by ring. 
     intro. apply Ropp_eq_compat in H. do 2 rewrite Ropp_involutive in H. 
     apply g'_not_0 in H. apply H.
     
     intros m1 Hm1. specialize (Hlimder m1 Hm1).
     destruct Hlimder as [alp [Halp Hsolve1]].
     exists alp. split. apply Halp.
     intros. 
assert (Hopenx : open_interval a b (-x)). destruct Hopen; split; lra.
replace (derive_pt (fun x0 : R => f (- x0)) x (Df' x Hopen)) with 
  (- derive_pt f (- x) (Df (- x) Hopenx)).
replace (derive_pt (fun x0 : R => g (- x0)) x (Dg' x Hopen)) with 
  (- derive_pt g (- x) (Dg (- x) Hopenx)).
replace ((- derive_pt f (- x) (Df (- x) Hopenx) /
      - derive_pt g (- x) (Dg (- x) Hopenx))) with
((derive_pt f (- x) (Df (- x) Hopenx) /
      derive_pt g (- x) (Dg (- x) Hopenx))). 
apply Hsolve1. unfold R_dist in *.
replace (- x - b) with (- (x + b)) by ring. ring_simplify (x -- b) in H.
rewrite Rabs_Ropp. apply H.
field. apply g'_not_0.
apply derive_pt_comp_Ropp.
apply derive_pt_comp_Ropp.
lra.
Qed.

End Hopital_infinite_neg_pos_left.

Section Hopital_infinite_pos_g.

(*
Theoreme Hopital_gninf_Lninf_right : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> a+} g = -infinity
Hlimder: lim_{x -> a+} f' / g' = -infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> a+} f / g = -infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_neg g (open_interval a b) a).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m < 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) < m))).

Theorem Hopital_gninf_Lninf_right : limit_div_neg (fun x => f x / g x) (open_interval a b) a.
Proof.
apply limit_div_neg_inv.
apply limit_div_pos_ext with (fun x => (- f x) / g x).
intros. unfold Rdiv. ring.
assert (Df' : forall x : R, open_interval a b x -> derivable_pt (-f) x).
intros. reg. apply Df. apply H.
apply Hopital_gninf_Lpinf_right with Df' Dg; try assumption.
intros. reg. apply Cf. apply H.
intros m Hm. assert (Hm' : - m < 0) by lra. destruct (Hlimder (-m) Hm') as [alp [Halp Hsolve]].
exists alp. split. assumption. intros. specialize (Hsolve x Hopen H).
rewrite (pr_nu _ _ _ (derivable_pt_opp f x (Df x Hopen))). rewrite derive_pt_opp.
replace m with (--m) by ring.
unfold Rdiv.
rewrite Ropp_mult_distr_l_reverse. apply Ropp_gt_lt_contravar.
apply Hsolve.
Qed.


End Hopital_infinite_pos_g.

Section Hopital_infinite_pos_g_left.

(*
Theoreme Hopital_gninf_Lninf_left : 

a, b \in R, 
Hab: a < b
Cf, Cg: f and g continue on [a; b], 
Df, Dg: f and g derivable on ]a; b[
Zg: lim_{x -> b-} g = -infinity
Hlimder: lim_{x -> b-} f' / g' = -infinity    (with L \in R)
g'_not_zero: \forall x \in ]a; b[, g' (x) <> 0
-----------------------------------------------------
lim_{x -> b-} f / g = -infinity

*)

Variables f g : R -> R.
Variables a b : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).

Hypothesis (Zg : limit_div_neg g (open_interval a b) b).

Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall m, m < 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x b < alp -> 
      (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen) < m))).

Theorem Hopital_gninf_Lninf_left : limit_div_neg (fun x => f x / g x) (open_interval a b) b.
Proof.
apply limit_div_neg_ext with (comp (fun x => f (- x) / g (- x)) (fun x => -x)). 
intros. unfold comp. ring_simplify (--x). reflexivity.
apply limit_div_neg_comp_Ropp.
  assert (Df': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => f (- x)) x).
   intros. reg. apply Df. now destruct H; split; lra.
   
   assert (Dg': forall x, open_interval (-b) (-a) x -> derivable_pt (fun x => g (- x)) x).
    intros. reg. apply Dg. now destruct H; split; lra.
    intros m Hm.
    apply Hopital_gninf_Lninf_right with Df' Dg'.
     now intuition.
     
     intros. reg. apply Cf. now destruct H; split; lra.
     
     intros. reg. apply Cg. now destruct H; split; lra.

     apply limit_div_neg_ext with (comp g (fun x => -x)). intros. reflexivity.
     apply limit_div_neg_comp_Ropp_l. do 2  rewrite Ropp_involutive.
     apply Zg.
     
     intros. assert (Hopen' : open_interval a b (-x)). 
     destruct Hopen; split; lra.
     rewrite <- (derive_pt_comp_Ropp _ _ _ _ Dg _ _ Hopen'). replace 0 with (-0) by ring. 
     intro. apply Ropp_eq_compat in H. do 2 rewrite Ropp_involutive in H. 
     apply g'_not_0 in H. apply H.
     
     intros m1 Hm1. specialize (Hlimder m1 Hm1).
     destruct Hlimder as [alp [Halp Hsolve1]].
     exists alp. split. apply Halp.
     intros. 
assert (Hopenx : open_interval a b (-x)). destruct Hopen; split; lra.
replace (derive_pt (fun x0 : R => f (- x0)) x (Df' x Hopen)) with 
  (- derive_pt f (- x) (Df (- x) Hopenx)).
replace (derive_pt (fun x0 : R => g (- x0)) x (Dg' x Hopen)) with 
  (- derive_pt g (- x) (Dg (- x) Hopenx)).
replace ((- derive_pt f (- x) (Df (- x) Hopenx) /
      - derive_pt g (- x) (Dg (- x) Hopenx))) with
((derive_pt f (- x) (Df (- x) Hopenx) /
      derive_pt g (- x) (Dg (- x) Hopenx))). 
apply Hsolve1. unfold R_dist in *.
replace (- x - b) with (- (x + b)) by ring. ring_simplify (x -- b) in H.
rewrite Rabs_Ropp. apply H.
field. apply g'_not_0.
apply derive_pt_comp_Ropp.
apply derive_pt_comp_Ropp.
lra.
Qed.


End Hopital_infinite_pos_g_left.
