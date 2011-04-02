Require Import Reals.
Require Import Fourier.
Require Import C_n_def.
Require Import Cauchy_lipschitz. (* TODO on importe des trucs qui parlent de Cn *)
Require Import Rextensionality.
Open Scope R_scope.

Definition derivable_on_interval a b (Hab : a < b) f :=
  forall x, open_interval a b x -> derivable_pt f x.

Section FirstGenHopital.

(*
Theorem Hopital_finite_zero_weak :

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
Hypothesis (Zf : limit1_in f (open_interval a b) 0 a). (* TODO en a t on vraiment besoin ? *)
Hypothesis (Zg : limit1_in g (open_interval a b) 0 a).

(* TODO on a besoin de l'hypothese en g car g' n'est pas continue. *)
Hypothesis (g_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0 /\ g x <> 0).
Hypothesis (Hlimder : forall eps, eps > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      R_dist (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)) L < eps)).

(* Ancienne hypothese :
limit1_in (fun x => derive_pt f Df x / derive g Dg x) (open_interval a b) L a).*)

Lemma limit_open : forall f a b, 
  limit1_in f (D_x no_cond a) (f a) a -> limit1_in f (open_interval a b) (f a) a.
Proof.
  clear Hlimder Zf Zg. unfold limit1_in in *. unfold limit_in in *. intros. specialize (H eps H0).
  destruct H as [alp [Halp H2]]. exists alp. split.
   now apply Halp.
   
   intros. apply H2. destruct H. split.
    constructor.
     now constructor.
     
     unfold open_interval in H. now intro; destruct H; fourier.
  
  apply H1.
Qed.

Lemma f_a_zero : f a = 0.
Proof.
  assert (forall x (Hclose : a <= x <= b), continuity_pt f x).
   intros. apply Cf. now apply Hclose.

   unfold continuity_pt in H. unfold continue_in in H. specialize (H a). assert (a <= a <= b) by intuition. 
   apply H in H0. apply (limit_open f a b) in H0. eapply single_limit; [ | apply H0 | apply Zf ]. unfold adhDa. 
   intros. exists (a + Rmin ((b - a) / 2) (alp / 2)). assert (H6 : alp / 2 > 0) by fourier. 
   assert ((b - a) > 0) by fourier. assert ((b-a) /2 > 0).
    apply (Rmult_gt_0_compat (/2)) in H2.
     now fourier.

     now fourier.

  split.
   unfold open_interval. split.
    assert (Rmin ((b - a) /2) (alp/2) > 0).
     apply Rmin_Rgt_r. now intuition.

     now fourier.

   apply Rle_lt_trans with (a + (b-a) / 2).
    apply Rplus_le_compat.
     now intuition.

     now apply Rmin_l.

   assert (b - a - (b - a) / 2 > 0).
    field_simplify. now fourier.

    now fourier.

  unfold R_dist. rewrite Rabs_right.
   ring_simplify. apply Rle_lt_trans with (alp / 2).
    now apply Rmin_r.

    now fourier.

  ring_simplify. apply Rle_ge. apply Rmin_glb; intuition.       
Qed.

Lemma g_a_zero : g a = 0. 
Proof.
  assert (forall x (Hclose : a <= x <= b), continuity_pt g x).
   intros. apply Cg. now apply Hclose.
   
   unfold continuity_pt in H. unfold continue_in in H. specialize (H a). assert (a <= a <= b) by intuition.
   apply H in H0. apply (limit_open g a b) in H0. eapply single_limit; [ | apply H0 | apply Zg ].
   unfold adhDa. intros. exists (a + Rmin ((b - a) / 2) (alp / 2)). assert (H6 : alp / 2 > 0) by fourier.
   assert ((b - a) > 0) by fourier. assert ((b-a) /2 > 0).
    apply (Rmult_gt_0_compat (/2)) in H2.
     now fourier.
     
     now fourier.
  
  split.
   unfold open_interval. split.
    assert (Rmin ((b - a) /2) (alp/2) > 0).
     apply Rmin_Rgt_r. now intuition.
     
     now fourier.
   
   apply Rle_lt_trans with (a + (b-a) / 2).
    apply Rplus_le_compat.
     now intuition.
     
     now apply Rmin_l.
   
   assert (b - a - (b - a) / 2 > 0).
    field_simplify. now fourier.
    
    now fourier.
  
  unfold R_dist. rewrite Rabs_right.
   ring_simplify. apply Rle_lt_trans with (alp / 2).
    now apply Rmin_r.
    
    now fourier.
  
  ring_simplify. apply Rle_ge. apply Rmin_glb; intuition.
Qed.

Theorem Hopital_finite_zero_weak : limit1_in (fun x => f x / g x) (open_interval a b) L a.
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
      now fourier.
      
      now fourier.
   
   now fourier.
   
   specialize (Hlim Hopenc). destruct H2. specialize (Hlim H3). destruct Haccc. rewrite H4.
   apply Hlim.
Qed.

End FirstGenHopital.

Definition limit_div_pos f (I : R -> Prop) a := forall m, m > 0 -> 
  exists alp, alp > 0 /\
    forall x, I x -> R_dist x a < alp -> m < f x.

Definition limit_div_neg f (I : R -> Prop) a := forall m, m > 0 -> 
  exists alp, alp > 0 /\ 
    forall x, I x -> R_dist x a < alp -> -m > f x.

Section SndGenHopital.

(*
Theoreme Hopital_infinite: 

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

(* TODO oulala... ca doit etre un gros craquage ca... *)
(* Hypothesis (Zf : limit_div_pos f (open_interval a b) a).*)

Hypothesis (Zg : limit_div_pos g (open_interval a b) a).

(* TODO on a besoin de l'hypothese en g car g' n'est pas continue. *)
Hypothesis (g'_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0).
Hypothesis (Hlimder : forall eps, eps > 0 ->
  exists alp, 
    alp > 0 /\
    (forall x (Hopen : open_interval a b x), R_dist x a < alp -> 
      R_dist (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)) L < eps)).

Lemma open_lemma : forall a b c, a < b -> c > 0 -> open_interval a b (a + Rmin ((b - a) /2) c).
Proof.
  intros. assert ((b0 - a0) > 0) by fourier. assert ((b0-a0) /2 > 0).
   apply (Rmult_gt_0_compat (/2)) in H1.
    now fourier.
    
    now fourier.
  
  split.
   assert (Rmin ((b0-a0) /2) c > 0).
    now apply Rmin_glb_lt; assumption.
    
    now fourier.
  
  apply Rle_lt_trans with (a0 + (b0-a0) /2).
   apply Rplus_le_compat_l. now apply Rmin_l.
   
   assert (b0 - a0 - (b0-a0) /2 > 0).
    field_simplify. now fourier.
    
    fourier.
Qed.

(* TODO reecrire cette preuve un peu partout *)  
Lemma g_not_zero : exists a', open_interval a b a' /\ forall x, open_interval a a' x -> g x <> 0.
Proof.
  unfold limit_div_pos in Zg. assert (1 > 0) by fourier. specialize (Zg 1 H). destruct Zg as [alp [Halp H3]].
  exists (a + Rmin ((b - a) / 2) (alp / 2)). assert (H6 : alp / 2 > 0) by fourier.
  assert ((b - a) > 0) by fourier. assert ((b-a) /2 > 0).
   apply (Rmult_gt_0_compat (/2)) in H0.
    now fourier.
    
    now fourier.
  
  split.
   unfold open_interval. split.
    assert (Rmin ((b-a) /2) (alp / 2) > 0).
     now apply Rmin_glb_lt; assumption.
     
     now fourier.
   
   apply Rle_lt_trans with (a + (b-a) /2).
    apply Rplus_le_compat_l. now apply Rmin_l.
    
    assert (b - a - (b-a) /2 > 0).
     field_simplify. now fourier.
     
     now fourier.
  
  intros. unfold open_interval in H0. assert (g x > 1).
   apply H3.
    unfold open_interval. unfold open_interval in H2. split.
     now apply H2.
     
     apply Rlt_trans with (a + Rmin ((b-a)/2) (alp /2)).
      now apply H2.
      
      apply Rle_lt_trans with (a + (b-a) /2).
       apply Rplus_le_compat_l. now apply Rmin_l.
       
       assert (b - a - (b-a) /2 > 0).
        field_simplify. now fourier.
        
        now fourier.
   
   unfold R_dist. unfold open_interval in H2. destruct H2. apply Rlt_trans with (alp/2).
    apply Rlt_le_trans with (Rmin ((b-a) / 2) (alp /2)).
     now rewrite Rabs_right; fourier.
     
     now apply Rmin_r.
   
   now fourier.
   
   intro. fourier.
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

(*
Lemma open_interval_min : forall a b x c, 
  c > 0 -> a < b -> a < x ->  R_dist x a < Rmin ((b- a) / 2) c -> open_interval a b x. Proof.
intros.
unfold R_dist in H2.
split. apply H1.
rewrite Rabs_right in H2.
assert (x - a0 < (b0 - a0) / 2).
admit.


Qed.
*)
(* TODO constructif si on sait si L <> 0 ou L = 0 je crois...
Faire les deux cas... 
Si on ne sait pas, la preuve ne l'est pas *)

Theorem Hopital_infinite : limit1_in (fun x => f x / g x) (open_interval a b) L a.
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
      
      intro. now fourier.
    
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
    now rewrite Rabs_right; fourier.
    
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
        unfold Rdiv. rewrite Rinv_1. rewrite Rmult_1_r. now apply Zg3.
        
        intro. now fourier.
        
        split.
         intro. now fourier.
         
         intro. now fourier.
    
    now fourier.
    
    intro. now fourier.
  
  assert (Heps4 : eps / 4 > 0) by fourier. assert (bizarre : forall eps L, L >= 0 -> eps > 0 ->
                   exists eps1, eps1 > 0 /\  eps1 * (L + eps) < eps / 2).
   intros. exists (/2 * ((eps0 / 2) * / (L0 + eps0))). split.
    apply Rmult_lt_0_compat.
     now fourier.
     
     apply Rmult_lt_0_compat.
      now fourier.
      
      apply Rinv_0_lt_compat. now fourier.
   
   field_simplify.
    now fourier.
    
    intro. now fourier.
  
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
    
    unfold open_interval in H1. destruct H1. now fourier.
    
    unfold open_interval in open. destruct open. now fourier.
  
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
     
     destruct H1. now fourier.
     
     do 2 rewrite Rabs_right in H3.
      now fourier.
      
      now destruct H1; fourier.
      
      destruct H2. now destruct H2; fourier.
      
      destruct H2. now destruct H2; fourier.
  
  assert (open_interval a a' y).
   now apply open.
   
   specialize (Hacc2' H3 H4). assert (x < y).
    unfold alp in H2. unfold dist in H2. simpl in H2. unfold R_dist in H2. assert (Rabs (x - a) < Rabs (y - a)).
     rewrite (Rabs_right (y - a)).
      unfold alp in H2. apply Rlt_le_trans with (Rmin (Rmin alp_alp (a' - a)) (y - a)).
       now intuition.
       
       now apply Rmin_r.
     
     destruct H4. now fourier.
     
     do 2 rewrite Rabs_right in H5.
      now fourier.
      
      now destruct H4; fourier.
      
      now destruct H3; fourier.
      
      now destruct H3; fourier.
  
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
         
         now fourier.
     
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

Section SndGenHopitalposneg.

(*
Theoreme Hopital_infinite_neg: 

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
  intros g a b Hab Zg. unfold limit_div_neg in Zg. assert (1 > 0) by fourier. specialize (Zg 1 H).
  destruct Zg as [alp [Halp H3]]. exists (a + Rmin ((b - a) / 2) (alp / 2)). assert (H6 : alp / 2 > 0) by fourier.
  assert ((b - a) > 0) by fourier. assert ((b-a) /2 > 0).
   apply (Rmult_gt_0_compat (/2)) in H0.
    now fourier.
    
    now fourier.
  
  split.
   unfold open_interval. split.
    assert (Rmin ((b-a) /2) (alp / 2) > 0).
     now apply Rmin_glb_lt; assumption.
     
     now fourier.
   
   apply Rle_lt_trans with (a + (b-a) /2).
    apply Rplus_le_compat_l. now apply Rmin_l.
    
    assert (b - a - (b-a) /2 > 0).
     field_simplify. now fourier.
     
     now fourier.
  
  intros. unfold open_interval in H0. assert (g x < - 1).
   apply H3.
    unfold open_interval. unfold open_interval in H2. split.
     now apply H2.
     
     apply Rlt_trans with (a + Rmin ((b-a)/2) (alp /2)).
      now apply H2.
      
      apply Rle_lt_trans with (a + (b-a) /2).
       apply Rplus_le_compat_l. now apply Rmin_l.
       
       assert (b - a - (b-a) /2 > 0).
        field_simplify. now fourier.
        
        now fourier.
   
   unfold R_dist. unfold open_interval in H2. destruct H2. apply Rlt_trans with (alp/2).
    apply Rlt_le_trans with (Rmin ((b-a) / 2) (alp /2)).
     now rewrite Rabs_right; fourier.
     
     now apply Rmin_r.
   
   now fourier.
   
   intro. fourier.
Qed.

Lemma limit_div_Ropp : forall a b g, a < b -> 
  limit_div_neg g (open_interval a b) a -> 
    limit_div_pos (fun x : R => - g x) (open_interval a b) a.
Proof.
  intros. unfold limit_div_pos, limit_div_neg in *. intros. specialize (H0 m H1).
  destruct H0. exists x. split.
   now intuition.
   
   intros. destruct H0. specialize (H4 x0 H2 H3). fourier.
Qed.

Lemma limit1_in_open : forall f L a b c, open_interval a b c -> 
  limit1_in f (open_interval a c) L a ->
    limit1_in f (open_interval a b) L a.
Proof.
  intros. unfold limit1_in in *. unfold limit_in in *. intros. specialize (H0 eps H1).
  destruct H0 as [alp [Halp Hlim]]. exists (Rmin alp (c - a)). split.
   apply Rmin_glb_lt.
    now assumption.
    
    now destruct H; fourier.
  
  intros. apply Hlim. destruct H0. unfold dist in *. simpl in *. unfold R_dist in *.
  split.
   split.
    now destruct H0; assumption.
    
    assert (Rabs (x - a) < c - a).
     apply Rlt_le_trans with (Rmin alp (c - a)).
      now apply H2.
      
      now apply Rmin_r.
   
   now rewrite Rabs_right in H3; destruct H0; fourier.
   
   apply Rlt_le_trans with (Rmin alp (c - a)).
    now apply H2.
    
    apply Rmin_l.
Qed.

Lemma limit_div_neg_open : forall f a b c, open_interval a b c -> 
  limit_div_neg f (open_interval a b) a ->
    limit_div_neg f (open_interval a c) a. 
Proof.
  intros. unfold limit_div_neg in *. intros. specialize (H0 m H1). destruct H0 as [alp [Halp Hlim]].
  exists alp. intuition. apply Hlim.
   now destruct H; destruct H0; split; fourier.
   
   apply H2.
Qed.

Lemma Hopital_infinite_neg
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
  
  apply Hopital_infinite with Df' Dg'.
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
    
    apply limit_div_neg_open with b.
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
     
     now destruct Hopen, Hopen0; fourier.
   
   rewrite (pr_nu g x _ (Dg x Hder)). now apply H3.
   
   intros. specialize (H4 eps H5). destruct H4 as [alp [Halp H10]]. exists alp. split.
    now assumption.
    
    intros. assert (Hder : open_interval a b x).
     unfold open_interval in *. split.
      now apply Hopen0.
      
      now destruct Hopen, Hopen0; fourier.
  
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

Section InfiniteLimiteHopital.

(*
Theorem Infinite_Limit_Hopital: 

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

(* TODO this proof has been done following the scheme of the first one... Maybe not optimal *)

Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : forall x, open_interval a b x -> derivable_pt f x) 
           (Dg : forall x, open_interval a b x -> derivable_pt g x).
Hypotheses (Cf : forall x, a <= x <= b -> continuity_pt f x)
           (Cg : forall x, a <= x <= b -> continuity_pt g x).
Hypothesis (Zf : limit1_in f (open_interval a b) 0 a). (* TODO en a t on vraiment besoin ? *)
Hypothesis (Zg : limit1_in g (open_interval a b) 0 a).

(* TODO on a besoin de l'hypothese en g car g' n'est pas continue. *)
Hypothesis (g_not_0 : forall x (Hopen: open_interval a b x),  derive_pt g x (Dg x Hopen) <> 0 /\ g x <> 0).
Hypothesis (Hlimder : forall m, m > 0 -> 
  exists alp,
    alp > 0 /\ 
      (forall x (Hopen: open_interval a b x), R_dist x a < alp ->
        m < (derive_pt f x (Df x Hopen) / derive_pt g x (Dg x Hopen)))).

Lemma Infinite_Limit_Hopital : forall m, m > 0 -> 
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
      now fourier.
      
      now fourier.
   
   now fourier.
   
   destruct H0. specialize (Hlim H1). destruct Haccc. rewrite H2.
   apply Hlim.
Qed.


End InfiniteLimiteHopital.


(*
 Section FirstGenHopital.

Variables f g : R -> R.
Variables a b L : R.

Hypothesis Hab : a < b.
Hypotheses (Df : derivable f) (Dg : derivable g).
Hypotheses (Zf : limit1_in f (D_x no_cond a) 0 a).
Hypotheses (Zg : limit1_in g (D_x no_cond a) 0 a).
(* TODO on a besoin de l'hypothese en g car g' n'est pas continue. *)
Hypothesis (g_not_0 : forall x, open_interval a b x -> derive g Dg x <> 0 /\ g x <> 0).
Hypothesis (Hlimder : limit1_in (fun x => derive f Df x / derive g Dg x) (open_interval a b) L a).

Lemma f_a_zero : f a = 0.
Proof.
 assert (continuity f).
  apply derivable_continuous. apply Df.

  unfold continuity in H. unfold continuity_pt in H. unfold continue_in in H. specialize (H a).
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
*)

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
