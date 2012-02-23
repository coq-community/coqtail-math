Require Import ZArith NArith Arith Omega MyNat Div2.
Require Import Natsets.

Definition foursquare (n : Z) : Type :=
  sigT (fun a => sigT (fun b => sigT (fun c => sig (fun d =>
    (n = a * a + b * b + c * c + d * d)%Z)))).


(** Euler's identity, compatibility of the 4-square property wrt. multiplication *)

Lemma euler's_identity : forall a b c d w x y z : Z,
  (let s z := z * z in
  (a * a + b * b + c * c + d * d) * (w * w + x * x + y * y + z * z) =
  s (a*w + b*x + c*y + d*z) +
  s (a*x - b*w - c*z + d*y) +
  s (a*y + b*z - c*w - d*x) +
  s (a*z - b*y + c*x - d*w))%Z.
Proof.
  intros.
  unfold s.
  ring.
Qed.

(*
Lemma euler's_identity_N : forall a b c d w x y z : N,
  (let s n := n * n in
  let Ndiff a b := Zabs_N (Z_of_N a - Z_of_N b) in
  (s a + s b + s c + s d) * (s w + s x + s y + s z) =
  s (a*w + b*x + c*y + d*z) +
  s (Ndiff (a*x + d*y) (b*w + c*z)) +
  s (Ndiff (a*y + b*z) (c*w + d*x)) +
  s (Ndiff (a*z + c*x) (b*y + d*w)))%N.
Proof.
  intros.
  apply Z_of_N_eq_rev.
  unfold s, Ndiff; clear s Ndiff.
  repeat rewrite Z_of_N_mult, Z_of_N_plus.
  repeat rewrite Z_of_N_mult.
  repeat rewrite Z_of_N_abs.
  repeat rewrite Zabs_square.
  repeat rewrite Z_of_N_plus.
  ring.
Qed.
*)

Lemma mult_foursquare_compat : forall n m : Z,
  foursquare n -> foursquare m -> foursquare (n * m)%Z.
Proof.
  intros n m (a, (b, (c, (d, Hn)))) (x, (y, (z, (t, Hm)))); subst.
  rewrite euler's_identity.
  repeat eexists.
Qed.


(** Properties on prime numbers *)

(*
Definition prime (n : N) := Znumtheory.prime (Z_of_N n).

(* TODO : pas vraiment besoin d'un gros résultat de factorisation, 
sauf s'il est rapide : on a juste besoin de décider si un nombre est premier 
ou sinon, donner deux nombres premiers *)

Variable prime_ge_2 : forall n, prime n -> (2 <= n)%N.

Fixpoint Nprod n f :=
  match n with
  | O => 1%N
  | S n => (f n * Nprod n f)%N
  end.

Definition bforall n {X} P (xs : nat -> X) : Type :=
  forall i, lt i n -> P (xs i).

Variable factorisation : forall x, (x <> 0)%N ->
  sigT (fun n => sigT (fun ps =>
    (bforall n prime ps * (Nprod n ps = x))%type)).

Lemma factor_not_zero : forall n ps, bforall n prime ps -> Nprod n ps <> 0%N.
Proof.
  intros n; induction n; intros ps Pps; simpl; dumb.
  remember (ps n) as psn; remember (Nprod n ps) as pps; destruct psn; destruct pps;
    try (exfalso; simpl; eapply IHn; [ | eauto ]; intros i Hi; solve [eauto]).
    
    exfalso.
    pose proof (prime_ge_2 (ps n) (Pps _ (le_refl _))).
    rewrite <- Heqpsn in *; compute in H; tauto.
    
    simpl; intros I; inversion I.
Qed.

Lemma prime_ind_l : forall P,
  ((P 0) ->
  (P 1) ->
  (forall p, prime p -> P p) ->
  (forall p n, prime p -> P n -> P (p * n)) ->
    forall n, P n)%N.
Proof.
  intros P H0 H1 Hp Hpn x.
  destruct x as [ | x ]; [ auto | ].
  destruct (factorisation (Npos x)) as (n, (ps, (Pps, Hpsx))); [ dumb | ].
  generalize x Hpsx; clear Hpsx x.
  induction n.
    simpl; intros x Ex1; rewrite <- Ex1; assumption.
    
    simpl; intros x Ex; rewrite <- Ex.
    apply Hpn.
      apply Pps; auto.
      remember (Nprod n ps) as psn; destruct psn as [ | psn].
        eauto.
        apply IHn.
          intros i Hi; eauto.
          auto.
Qed.

Lemma prime_ind : forall P,
  ((P 0) ->
  (P 1) ->
  (forall n, prime n -> P n) ->
  (forall a b, P a -> P b -> P (a * b)) ->
    forall n, P n)%N.
Proof.
  intros; apply prime_ind_l; eauto.
Qed.
*)

Require Import Znumtheory.

Lemma Z_prime_ind : forall P : Z -> Prop,
  ((P 0) ->
  (P 1) ->
  (forall n, prime n -> P n) ->
  (forall a b, P a -> P b -> P (a * b)) ->
    forall n, P n)%Z.
Admitted.

Lemma Z_prime_rect : forall P : Z -> Type,
  ((P 0) ->
  (P 1) ->
  (forall n, prime n -> P n) ->
  (forall a b, P a -> P b -> P (a * b)) ->
    forall n, P n)%Z.
Admitted.

Lemma Z_pZ_mult_injective : forall p n, prime p -> Zmod n p <> 0%Z ->
  forall x y, Zmod (x * n) p = Zmod (y * n) p -> Zmod x p = Zmod y p.
Proof.
  intros p n Pp Nn x y E.
  cut (Zdivide p (x - y)).
    intros (k, Hk).
    rewrite <- (Z_mod_plus_full y k).
    rewrite <- Hk.
    f_equal; ring.
  
  cut (Zdivide p (n * (x - y))).
    intros D.
    destruct (prime_mult _ Pp _ _ D) as [D1|D2]; [ | exact D2 ].
    apply Zdivide_mod in D1.
    tauto.
  
  apply Zmod_divide.
    destruct Pp; omega.
    
    rewrite Zmult_minus_distr_l, Zminus_mod.
    rewrite <- (Zmod_0_l p); f_equal.
    do 2 rewrite (Zmult_comm n); rewrite <- E.
    ring.
Qed.

Lemma Z_pZ_inverse : forall p x, prime p -> x mod p <> 0 -> { y | Zmod (x * y) p = 1%Z }.
Proof.
  (* preuve : (Zmod x p) et (p) sont copremiers, donc par bézout
     1 = u * p + v * Zmod x p  et avec y = v ou Zmod v p on est bon. *)
Admitted.

(* Declare Z/pZ as a field somewhere ? With what operation ? *)

Lemma Zmod_eq_minus : forall p a b, a mod p = b mod p <-> (a - b) mod p = 0.
Proof.
  intros p a b; split; intros E.
    rewrite Zminus_mod, E, <- (Zmod_0_l p).
    f_equal; ring.
    
    replace a with (b + (a - b)) by ring.
    rewrite Zplus_mod, E, <- (Zmod_mod b).
    f_equal; rewrite Zmod_mod; ring.
Qed.

Lemma Zmod_sqrt_eq_compat : forall p i j, Znumtheory.prime p ->
  (0 <= i -> 0 <= j -> 2 * i < p -> 2 * j < p ->
  (i * i) mod p = (j * j) mod p -> i = j)%Z.
Proof.
  intros p i j Pp Pi Pj Bi Bj ES.
  destruct (Z_eq_dec ((i + j) mod p) 0) as [ E | E ].
    cut (i + j = 0); [ omega | ].
    cut (i + j < p); [ intros H | omega ].
    rewrite <- E; symmetry; apply Zmod_small.
    omega.
  
  destruct (Z_pZ_inverse _ _ Pp E) as (a, Ha).
  cut (((i - j) * 1) mod p = 0).
    rewrite Zmult_1_r, Zminus_mod; intros HE.
    rewrite <- Zmod_eq_minus in HE.
    do 2 rewrite (Zmod_small i p), (Zmod_small j p) in HE; try omega.
  
  rewrite <- Ha.
  clear -ES.
  rewrite Zmod_eq_minus in ES.
  rewrite Zmult_mod_idemp_r, Zmult_assoc.
  rewrite Zmult_mod, <- (Zmod_0_l p); f_equal.
  apply Z_eq_mult.
  rewrite <- ES; f_equal; ring.
Qed.

Lemma Zabs_nat_inj : forall a b, 0 <= a -> 0 <= b -> Zabs_nat a = Zabs_nat b -> a = b.
Proof.
  intros a b Pa Pb E.
  rewrite <- (Zabs_eq a), <- (Zabs_eq b); eauto.
  do 2 rewrite <- inj_Zabs_nat.
  auto.
Qed.

Lemma lt_div_2 : forall a b, 0 <= a -> a < b / 2 -> 2 * a < b.
Proof.
  intros a b P L.
  apply Zlt_le_trans with (2 * (b / 2)).
    apply Zmult_gt_0_lt_compat_l; eauto.
    reflexivity.
    
  apply Z_mult_div_ge; reflexivity.
Qed.

Lemma Z_mult_div_mod : forall a b, b <> 0 -> b * (a / b) = a - a mod b.
Proof.
  intros a b N.
  pose proof Z_div_mod_eq_full a b N; omega.
Qed.

Lemma Z_mult_div_bounds : forall a b, 0 < b -> a - b < b * (a / b) <= a.
Proof.
  intros a b N; split.
    pose proof Z_mod_lt a b.
    rewrite Z_mult_div_mod; omega.
    
    apply Z_mult_div_ge; omega.
Qed.

Definition odd p := p mod 2 = 1.

Lemma prime_odd : forall p, 2 <> p -> prime p -> odd p.
Proof.
  intros p N2 Pp; unfold odd.
  rem (p mod 2) r Er.
  pose proof Z_mod_lt p 2 as help_omega.
  cut (r <> 0).
    omega.
    
    clear help_omega; intros Rn; subst.
    apply Zmod_divide in Rn; [ | omega ].
    refine (N2 (prime_div_prime _ _ _ _ _)); auto.
    apply prime_2.
Qed.

Lemma odd_bound_1 : forall p i, odd p -> i < Zsucc (p / 2) -> 2 * i < p.
Proof.
  intros p i Op Bi.
  unfold Zsucc in Bi.
  apply Zle_lt_trans with (2 * (p / 2)).
    omega.
    
    rewrite Z_mult_div_mod; [ | auto with * ].
    rewrite Op; auto with *.
Qed.


(** 4-square property on prime numbers (the interesting part) *)

Lemma prime_dividing_sum_of_two_squares_plus_one : forall p,
  prime p -> 3 <= p ->	
    sigT (fun l => sigT (fun m => sig (fun k =>
      p * k = 1 + l * l + m * m /\
      2 * m < p /\  2 * l < p /\ 0 < k /\ 0 <= l /\ 0 <= m /\ (0 < l \/ 0 < m)))).
Proof.
  intros p Pp Op.
  
  pose (np := Zabs_nat p).
  
  assert (p_odd : odd p) by (apply prime_odd; auto || omega).
  
  pose (s := fun x : Z => x * x).
  assert (s_pos : forall x, 0 <= s x).
    intros; unfold s; rewrite <- Zabs_square.
    apply Zmult_le_0_compat; auto with *.
  
  assert (mod_pos : forall x, 0 <= x mod p).
    intros; apply Z_mod_lt; destruct Pp; omega.
  
  assert (hp_pos : 0 <= p / 2) by (apply Z_div_pos; omega).
  
  assert (autobound : forall i, (i < S (Zabs_nat (p / 2)))%nat -> 2 * Z_of_nat i < p).
    intros i Li.
    apply inj_lt in Li.
    rewrite inj_S, inj_Zabs_nat, Zabs_eq in Li; auto.
    apply odd_bound_1; auto.
  
  pose (FL := fun l => Zabs_nat (s (Z_of_nat l) mod p)).
  pose (FM := fun m => Zabs_nat ((-1 - s (Z_of_nat m)) mod p)).
  assert (IFL : injective (S (Zabs_nat (p / 2))) FL).
    intros i j Li Lj E.
    unfold FL in E.
    apply Zabs_nat_inj in E; eauto.
    apply inj_eq_rev.
    apply (Zmod_sqrt_eq_compat p (Z_of_nat i) (Z_of_nat j)); auto with *.
  
  assert (IFM : injective (S (Zabs_nat (p / 2))) FM).
    intros i j Li Lj E.
    unfold FM in E.
    apply inj_eq_rev.
    apply (Zmod_sqrt_eq_compat p (Z_of_nat i) (Z_of_nat j)); auto with *.
    
    apply Zabs_nat_inj in E; eauto.
    rewrite Zmod_eq_minus in E.
    symmetry.
    apply Zmod_eq_minus.
    rewrite <- E; f_equal.
    unfold s; ring.
  
  assert (BFL : bounded (S (Zabs_nat (p / 2))) (Zabs_nat p) FL).
    intros i _.
    unfold FL.
    apply inj_lt_rev; do 2 rewrite inj_Zabs_nat.
    repeat rewrite Zabs_eq; auto with *.
      apply Z_mod_lt; auto with *.
  
  assert (BFM : bounded (S (Zabs_nat (p / 2))) (Zabs_nat p) FM).
    intros i _.
    unfold FM.
    apply inj_lt_rev; do 2 rewrite inj_Zabs_nat.
    repeat rewrite Zabs_eq; auto with *.
    apply Z_mod_lt; auto with *.
  
  assert (CL := count_image_injective (S (Zabs_nat (p / 2))) np FL IFL BFL).
  assert (CM := count_image_injective (S (Zabs_nat (p / 2))) np FM IFM BFM).
  
  remember (image FL (S (Zabs_nat (p / 2)))) as L.
  remember (image FM (S (Zabs_nat (p / 2)))) as M.
  
  destruct (count_drawers L M np) as (i, (Bi, (Li, Mi))).
    rewrite CL, CM.
    apply inj_lt_rev.
    rewrite inj_plus, inj_S, inj_Zabs_nat.
    rewrite Zabs_eq; auto.
    unfold np; rewrite inj_Zabs_nat, Zabs_eq; auto with *.
    unfold Zsucc.
    ring_simplify.
    pose proof Z_mult_div_bounds p 2.
    omega.
  
  rewrite HeqL in Li; rewrite HeqM in Mi.
  destruct (image_true _ _ _ Li) as (l, (Bl, Hl)).
  destruct (image_true _ _ _ Mi) as (m, (Bm, Hm)).
  exists (Z_of_nat l); exists (Z_of_nat m).
  unfold FL in Hl; unfold FM in Hm.
  clear HeqL CL HeqM CM Li Mi IFL IFM BFL BFM FL FM.
  subst.
  apply inj_eq in Hm; do 2 rewrite inj_Zabs_nat in Hm.
  do 2 rewrite Zabs_eq in Hm; auto.
  symmetry in Hm; rewrite Zmod_eq_minus in Hm.
  apply Zmod_divide in Hm; [ | omega ].
  (* merci la stdlib qui fait ça dans prop *)
  assert (Hm' : {k | s (Z_of_nat l) - (-1 - s (Z_of_nat m)) = k * p}).
    clear -Hm.
    admit.
  pose proof s_pos (Z_of_nat l).
  pose proof s_pos (Z_of_nat m).
  destruct Hm' as (k, Hk); exists k.
  assert (0 < k * p) by omega.
  assert (0 < k) by (apply Zmult_lt_0_reg_r with p; assumption || omega).
  assert (3 <= k * p).
    (* TODO Zle transitif dans MyZ *)
    replace 3 with (1 * 3) by reflexivity.
    apply Zmult_le_compat; omega.
  repeat split; auto with *.
    rewrite Zmult_comm, <- Hk.
    unfold s; ring.
    
    rem (Z_of_nat l) lz Elz.
    rem (Z_of_nat m) mz Emz.
    cut (0 <> lz \/ 0 <> mz); [ omega | ].
    cut (0 <> s lz \/ 0 <> s mz).
      cut (forall a, 0 <> s a -> 0 <> a). (* TODO : MyZ (?) *)
        intros Hyp [?|?]; [left|right]; apply Hyp; auto.
        clear; intros [] H; tauto || zify; auto with *.
      omega.
Qed.

Lemma foursquare_prime_factor_decreasing :
  forall p, prime p -> forall m, (1 < m /\ m < p)%Z ->
    foursquare (m * p) ->
      sigT (fun n => ((0 < n /\ n < m)%Z * foursquare (n * p))%type).
Proof.
  (* Arithmétique modulaire ET avec des majorations. *)
Admitted.


(* Ça devrait être quelque part, mais je n'ai pas trouvé. Peut-être aussi qu'on
   peut utiliser un induction scheme au lieu d'utiliser ce résultat ? *)
Definition lt_wf_rect :=
  fun p (P : nat -> Type) F =>
    well_founded_induction_type
      (well_founded_ltof nat (fun m => m)) P F p.

Lemma foursquare_prime : forall p, prime p -> foursquare p.
Proof.
  intros p Pp.
  
  destruct (Z_eq_dec p 2) as [E | E].
    (* Case p = 2 *)
    do 2 exists 1%Z; do 2 exists 0%Z; auto.
    
    (* Case p >= 3 *)
    
    assert (3 <= p) as Op by
      (pose proof (prime_ge_2 p Pp); zify; omega); clear E.
    
    (* We prove : ∃m>0 FS(kp) *)
    pose (fs_mult := fun p m =>
      prod (foursquare (Z_of_nat (S m) * p))
        (Z_of_nat (S m) < p)).
    assert (sigT (fs_mult p)) as Hm.
      (* .. using the previous lemma *)
      destruct (prime_dividing_sum_of_two_squares_plus_one p Pp Op) as
        (l, (m, (k, (Ep, (Bm, (Bl, (Pk, Plm))))))).
      assert (tech1 : Z_of_nat (S (Zabs_nat (k - 1))) = k).
        rewrite inj_S, inj_Zabs_nat, Zabs_eq; [ | omega ]; auto with *.
      exists (Zabs_nat (k - 1)); split.
        (* FS(kp) *)
        exists 0%Z; exists 1%Z; exists l; exists m.
        transitivity (p * k).
          rewrite tech1; ring.
          rewrite Ep; auto.
        
        (* k<p *)
        rewrite tech1; clear tech1.
        apply Zmult_lt_reg_r with (4 * p); [ auto with * | ].
        replace (p * (4 * p)) with (2 * (p * p) + 2 * (p * p)) by ring.
        replace (k * (4 * p)) with (4 * (p * k)) by ring.
        rewrite Ep.
        assert (tech2 : forall a b, 0 < a -> 2 * a < b -> 4 * a * a + 4 < b * b). 
          clear; intros a b Pa LT.
          assert (LE : 2 * a + 1 <= b) by omega.
          assert (Pda : 0 <= 2 * a + 1) by omega.
          assert (LE2 := Zmult_le_compat _ _ _ _ LE LE Pda Pda).
          eapply Zlt_le_trans; [ | apply LE2 ].
          ring_simplify.
          omega.
        
        assert (tech3 : forall a b, 0 <= a -> 2 * a < b -> 4 * a * a < b * b). 
          clear; intros a b Pa LT.
          assert (LE : 2 * a + 1 <= b) by omega.
          assert (Pda : 0 <= 2 * a + 1) by omega.
          assert (LE2 := Zmult_le_compat _ _ _ _ LE LE Pda Pda).
          eapply Zlt_le_trans; [ | apply LE2 ].
          ring_simplify.
          omega.
        
        assert (p2_pos : 0 < p * p).
          transitivity (1 * p).
            omega.
            apply Zmult_lt_compat_r; omega.
        
        rem (l * l) ll Ell.
        rem (m * m) mm Emm.
        rem (p * p) pp Epp.
        destruct Plm as (NNl, (NNm, [Pl | Pm])).
          specialize (tech2 _ p Pl Bl).
          specialize (tech3 _ p NNm Bm).
          rewrite <- Zmult_assoc, Ell, Emm, Epp in *.
          clear -tech2 tech3 p2_pos.
          ring_simplify.
          omega.
          
          specialize (tech2 _ p Pm Bm).
          specialize (tech3 _ p NNl Bl).
          rewrite <- Zmult_assoc, Ell, Emm, Epp in *.
          clear -tech2 tech3 p2_pos.
          ring_simplify.
          omega.
          
          (* De "k<p" à ici : majoration beaucoup trop fine ! (2p² au
          lieu de 4p²) Donc partie potentiellement beaucoup plus courte
          et rapide à exécuter. *)
    
    (* To prove FS(p) we can prove ∀m>0 (FS(mp) -> FS(p)) *)
    clear Op.
    destruct Hm as (m, Hm).
    generalize p Pp m Hm; clear Hm m Pp p.
    intros p Pp m.
    refine (lt_wf_rect m (fun n => fs_mult p n -> foursquare p) _); clear m.
    intros [|m] IH (FSm, UBm).
      (* m=1 *)
      destruct p; assumption.
      
      (* m>1 *)
      assert (LBm : 1 < Z_of_nat (S (S m))) by (zify; omega).
      destruct (foursquare_prime_factor_decreasing p Pp _ (conj LBm UBm) FSm) as (n, ((LBn, UBn), FSn)).
        apply IH with (Zabs_nat (n - 1)).
          unfold ltof.
          zify; omega.
          
          unfold fs_mult.
          rewrite inj_S, inj_Zabs_nat, Zabs_eq; auto with *; unfold Zsucc.
          replace (n - 1 + 1) with n by ring.
          split; auto; omega.
Qed.


(** Trivial application of the previous lemma and euler's identity *)

Theorem lagrange_4_square_theorem : forall n, foursquare n.
Proof.
  intros n; eapply Z_prime_rect.
    repeat (exists 0); auto.
    
    exists 1; repeat (exists 0); auto.
    
    apply foursquare_prime.
    
    apply mult_foursquare_compat.
Qed.

(*
http://planetmath.org/encyclopedia/ProofOfLagrangesFourSquareTheorem.html
(le site est down le 13 février 2012 à 19h)
*)

