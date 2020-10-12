Require Import ZArith Lia Znumtheory.
Require Import Natsets MyNat Ztools Zeqm Znumfacts.

(** Definition of the predicate : being the sum of four squares *)

Definition foursquare (n : Z) : Type :=
  {a : _ & { b: _ & { c : _ & { d |
    n = a * a + b * b + c * c + d * d
  }}}}.


(** Euler's identity and compatibility of the 4-square property wrt. multiplication *)

Lemma euler's_identity : forall a b c d w x y z : Z,
  let s z := z * z in
  (a * a + b * b + c * c + d * d) * (w * w + x * x + y * y + z * z) =
  s (a*w + b*x + c*y + d*z) +
  s (a*x - b*w - c*z + d*y) +
  s (a*y + b*z - c*w - d*x) +
  s (a*z - b*y + c*x - d*w).
Proof.
  intros; unfold s.
  ring.
Qed.

Lemma mult_foursquare_compat : forall n m : Z,
  foursquare n -> foursquare m -> foursquare (n * m)%Z.
Proof.
  intros n m (a, (b, (c, (d, Hn)))) (x, (y, (z, (t, Hm)))); subst.
  rewrite euler's_identity.
  repeat eexists.
Defined.

Lemma Zmod_sqrt_eq_compat : forall p i j, prime p ->
  (0 <= i -> 0 <= j -> 2 * i < p -> 2 * j < p ->
  i * i ≡ j * j [p] -> i = j)%Z.
Proof.
  intros p i j Pp Pi Pj Bi Bj ES.
  destruct (Z.eq_dec ((i + j) mod p) 0) as [ E | E ].
    cut (i + j = 0); [ lia | ].
    cut (i + j < p); [ intros H | lia ].
    rewrite <- E; symmetry; apply Zmod_small.
    lia.
  
  destruct (modular_inverse _ _ Pp E) as (a, Ha).
  
  cut (i ≡ j [p]).
    intros M; red in M.
    rewrite (Zmod_small i p), (Zmod_small j p) in M; lia.
  
  apply eqm_minus_0.
  replace (i - j) with ((i - j) * 1) by ring.
  rewrite <- Ha.
  apply eqm_minus_0 in ES.
  replace 0 with (0 * a) by ring.
  rewrite <- ES.
  apply eq_eqm; ring.
Qed.

Lemma prime_odd : forall p, 2 <> p -> prime p -> p mod 2 = 1.
Proof.
  intros p N2 Pp.
  rem (p mod 2) r Er.
  pose proof Z_mod_lt p 2 as help_lia.
  cut (r <> 0).
    lia.
    
    clear help_lia; intros Rn; subst.
    apply Zmod_divide in Rn; [ | lia ].
    refine (N2 (prime_div_prime _ _ _ _ _)); auto.
    apply prime_2.
Qed.

Lemma odd_bound_1 : forall p i, p mod 2 = 1 -> i < Z.succ (p / 2) -> 2 * i < p.
Proof.
  intros p i Op Bi.
  unfold Z.succ in Bi.
  apply Z.le_lt_trans with (2 * (p / 2)).
    lia.
    
    rewrite Z_mult_div_mod; [ | auto with * ].
    rewrite Op; auto with *.
Qed.


(** [modsym x m] is the unique y congruent to x such that -m/2≤x<m/2 *)

Definition modsym x m := (x + m / 2) mod m - m / 2.

Lemma modsym_bounds : forall x m, 0 < m -> - m <= 2 * modsym x m < m.
Proof.
  intros x m Pm; unfold modsym.
  pose proof Z_mod_lt (x + m / 2) m.
  pose proof Z_mod_lt m 2.
  split; ring_simplify; rewrite Z_mult_div_mod; lia.
Qed.

Lemma modsym_mod_compat : forall x m, (modsym x m) mod m = x mod m.
Proof.
  intros x m; unfold modsym.
  rewrite Zminus_mod_idemp_l.
  f_equal; ring.
Qed.

Lemma mod_modsym_compat : forall x m, modsym (x mod m) m = modsym x m.
Proof.
  intros x m; unfold modsym.
  rewrite Zplus_mod_idemp_l; auto.
Qed.

Lemma modsym_mod_diff : forall x m, 0 < m -> { k | modsym x m = x mod m + m * k }.
Proof.
  intros x m.
  exists ((modsym x m - x mod m) / m).
  rewrite Z_mult_div_mod; [ | auto with * ].
  rewrite Zminus_mod, modsym_mod_compat.
  rewrite Zminus_mod_idemp_l.
  do 2 rewrite Zminus_mod_idemp_r.
  rewrite Zminus_diag, Zmod_0_l.
  ring.
Qed.

Lemma modsym_eqm : forall x m, modsym x m ≡ x [ m ].
Proof.
  intros x m.
  apply modsym_mod_compat.
Qed.

Lemma prime_div_false : forall a p, prime p -> (a | p) -> 1 < a < p -> False.
Proof.
  intros a p Pp D Bp.
  destruct (prime_divisors p Pp a D) as [|[|[|]]]; lia.
Qed.

Lemma Zbounding_square : forall x m, 0 < m -> -m <= x <= m -> x ^ 2 <= m ^ 2.
Proof.
  intros x m Pm Bx.
  simpl; unfold Zpower_pos; simpl.
  rewrite Zmult_assoc.
  rewrite <- Z.abs_square.
  apply Z.le_trans with (Z.abs x * m).
    rewrite <- Zmult_assoc.
    apply Zmult_le_compat_l; lia.
    
    rewrite Zmult_comm.
    apply Zmult_le_compat_l; lia.
Qed.


(** All prime numbers divides some [1+l²+m²] (plus convenient conditions on [l,m]) *)

Lemma prime_dividing_sum_of_two_squares_plus_one : forall p,
  prime p -> 3 <= p ->	
    {l : _ & {m : _ & { k |
      p * k = 1 + l * l + m * m /\
      2 * m < p /\  2 * l < p /\ 0 < k /\ 0 <= l /\ 0 <= m /\ (0 < l \/ 0 < m)}}}.
Proof.
  intros p Pp Op.
  
  pose (np := Z.abs_nat p).
  
  assert (p_odd : p mod 2 = 1) by (apply prime_odd; auto || lia).
  
  pose (s := fun x : Z => x * x).
  assert (s_pos : forall x, 0 <= s x).
    intros; unfold s; rewrite <- Z.abs_square.
    apply Zmult_le_0_compat; auto with *.
  
  assert (mod_pos : forall x, 0 <= x mod p).
    intros; apply Z_mod_lt; destruct Pp; lia.
  
  assert (hp_pos : 0 <= p / 2) by (apply Z_div_pos; lia).
  
  assert (autobound : forall i, (i < S (Z.abs_nat (p / 2)))%nat -> 2 * Z_of_nat i < p).
    intros i Li.
    apply inj_lt in Li.
    rewrite inj_S, inj_Zabs_nat, Z.abs_eq in Li; auto.
    apply odd_bound_1; auto.
  
  pose (FL := fun l => Z.abs_nat (s (Z_of_nat l) mod p)).
  pose (FM := fun m => Z.abs_nat ((-1 - s (Z_of_nat m)) mod p)).
  assert (IFL : injective (S (Z.abs_nat (p / 2))) FL).
    intros i j Li Lj E.
    unfold FL in E.
    apply Zabs_nat_inj in E; eauto.
    apply inj_eq_rev.
    apply (Zmod_sqrt_eq_compat p (Z_of_nat i) (Z_of_nat j)); auto with *.
  
  assert (IFM : injective (S (Z.abs_nat (p / 2))) FM).
    intros i j Li Lj E.
    unfold FM in E.
    apply inj_eq_rev.
    apply (Zmod_sqrt_eq_compat p (Z_of_nat i) (Z_of_nat j)); auto with *.
    
    apply Zabs_nat_inj in E; eauto.
    symmetry; apply eqm_minus_0.
    apply eqm_minus_0 in E.
    rewrite <- E.
    apply eq_eqm; unfold s; ring.
  
  assert (BFL : bounded (S (Z.abs_nat (p / 2))) (Z.abs_nat p) FL).
    intros i _.
    unfold FL.
    apply inj_lt_rev; do 2 rewrite inj_Zabs_nat.
    repeat rewrite Z.abs_eq; auto with *.
      apply Z_mod_lt; auto with *.
  
  assert (BFM : bounded (S (Z.abs_nat (p / 2))) (Z.abs_nat p) FM).
    intros i _.
    unfold FM.
    apply inj_lt_rev; do 2 rewrite inj_Zabs_nat.
    repeat rewrite Z.abs_eq; auto with *.
    apply Z_mod_lt; auto with *.
  
  assert (CL := count_image_injective (S (Z.abs_nat (p / 2))) np FL IFL BFL).
  assert (CM := count_image_injective (S (Z.abs_nat (p / 2))) np FM IFM BFM).
  
  remember (image FL (S (Z.abs_nat (p / 2)))) as L.
  remember (image FM (S (Z.abs_nat (p / 2)))) as M.
  
  destruct (count_drawers L M np) as (i, (Bi, (Li, Mi))).
    rewrite CL, CM.
    apply inj_lt_rev.
    rewrite inj_plus, inj_S, inj_Zabs_nat.
    rewrite Z.abs_eq; auto.
    unfold np; rewrite inj_Zabs_nat, Z.abs_eq; auto with *.
    unfold Z.succ.
    ring_simplify.
    pose proof Z_mult_div_bounds p 2.
    lia.
  
  rewrite HeqL in Li; rewrite HeqM in Mi.
  destruct (image_true _ _ _ Li) as (l, (Bl, Hl)).
  destruct (image_true _ _ _ Mi) as (m, (Bm, Hm)).
  exists (Z_of_nat l); exists (Z_of_nat m).
  unfold FL in Hl; unfold FM in Hm.
  clear HeqL CL HeqM CM Li Mi IFL IFM BFL BFM FL FM.
  subst.
  apply inj_eq in Hm; do 2 rewrite inj_Zabs_nat in Hm.
  do 2 rewrite Z.abs_eq in Hm; auto.
  symmetry in Hm; apply eqm_minus_0 in Hm.
  rewrite divide_eqm in Hm; notzero.
  pose proof s_pos (Z_of_nat l).
  pose proof s_pos (Z_of_nat m).
  destruct (Zdivide_inf _ _ Hm) as (k, Hk).
  exists k.
  assert (0 < k * p) by lia.
  assert (0 < k) by (apply Zmult_lt_0_reg_r with p; assumption || lia).
  assert (3 <= k * p).
    (* TODO Zle transitif dans MyZ *)
    replace 3 with (1 * 3) by reflexivity.
    apply Zmult_le_compat; lia.
  repeat split; auto with *.
    rewrite Zmult_comm, <- Hk.
    unfold s; ring.
    
    rem (Z_of_nat l) lz Elz.
    rem (Z_of_nat m) mz Emz.
    cut (0 <> lz \/ 0 <> mz); [ lia | ].
    cut (0 <> s lz \/ 0 <> s mz).
      cut (forall a, 0 <> s a -> 0 <> a). (* TODO : MyZ (?) *)
        intros Hyp [?|?]; [left|right]; apply Hyp; auto.
        clear; intros [] H; tauto || zify; auto with *.
      lia.
Defined.


(** Building bounds to prove things like x1²+x2²+x3²+x4²=m² /\ -m/2≤xi<m/2 => xi=-m/2 *)

Lemma egality_case_sum_of_four : forall a b c d M,
  a <= M -> b <= M -> c <= M -> d <= M ->
  a + b + c + d = 4 * M -> ((a = M) /\ (b = M)) /\ ((c = M) /\ (d = M)).
Proof.
  intros.
  lia.
Qed.

Lemma square_bound_equality_case : forall a M,
  -M <= a < M -> M * M <= a * a -> a = - M.
Proof.
  intros a M Bounds Bsqr.
  destruct (Z_le_dec 0 M); [ | lia ].
  cut (Z.abs M <= Z.abs a).
    intro; lia.
    
    rewrite <- (Z.abs_square M), <- (Z.abs_square a) in Bsqr.
    apply sqrt_le_compat; auto with *.
Qed.

Lemma square_bound : forall x m, -m <= x <= m -> x * x <= m * m.
Proof.
  intros x m Bx.
  assert (Pm : 0 <= m) by lia.
  rewrite <- Z.abs_square.
  apply Z.le_trans with (Z.abs x * m).
    apply Zmult_le_compat_l; auto with *; try lia.

    apply Zmult_le_compat_r; auto with *; try lia.
Qed.

Lemma square_bound_opp : forall x m, m <= x <= -m -> x * x <= m * m.
Proof.
  intros x m Bx.
  rewrite <- (Zmult_opp_opp m m).
  apply square_bound; auto with *.
Qed.

Lemma egality_case_sum_of_four_squares : forall a b c d M,
  -M <= a < M -> -M <= b < M -> -M <= c < M -> -M <= d < M ->
  a * a + b * b + c * c + d * d = 4 * (M * M) ->
    ((a = -M) /\ (b = -M)) /\ ((c = -M) /\ (d = -M)).
Proof.
  intros a b c d m Ba Bb Bc Bd E.
  assert (P : forall x, -m <= x < m -> -m <= x <= m) by (intros; lia).
  pose proof square_bound _ _ (P _ Ba).
  pose proof square_bound _ _ (P _ Bb).
  pose proof square_bound _ _ (P _ Bc).
  pose proof square_bound _ _ (P _ Bd).
  assert (Pm : 0 < m) by lia.
  cut ((Z.abs a = m /\ Z.abs b = m) /\ (Z.abs c = m /\ Z.abs d = m)).
    intros; lia.
    
    split; split; (rewrite <- (Z.abs_eq m); [ | auto with * ]);
      apply sqrt_eq_compat_abs;
      lia.
Qed.


(** If [mp] is the sum of four squares, then so is [np] for a smaller [n] *)

Lemma foursquare_prime_factor_decreasing :
  forall p, prime p -> forall m, (1 < m /\ m < p)%Z ->
    foursquare (m * p) ->
      sigT (fun n => ((0 < n /\ n < m)%Z * foursquare (n * p))%type).
Proof.
  intros p Pp m (LBm, UBm) FSmp.
  assert (help0 : m <> 0); auto with *.
  assert (help1 : 0 < m); auto with *.
  destruct FSmp as (x1, (x2, (x3, (x4, Hx)))).
  pose (y1 := modsym x1 m).
  pose (y2 := modsym x2 m).
  pose (y3 := modsym x3 m).
  pose (y4 := modsym x4 m).
  assert (eqm1 : y1 ≡ x1 [m]) by apply modsym_eqm.
  assert (eqm2 : y2 ≡ x2 [m]) by apply modsym_eqm.
  assert (eqm3 : y3 ≡ x3 [m]) by apply modsym_eqm.
  assert (eqm4 : y4 ≡ x4 [m]) by apply modsym_eqm.
  
  assert (Dm : (m | y1 * y1 + y2 * y2 + y3 * y3 + y4 * y4)).
    apply divide_eqm; auto.
    rewrite eqm1, eqm2, eqm3, eqm4.
    rewrite <-Hx, divide_eqm; auto.
    apply Z.divide_factor_l.
  
  assert (Dmp : ~ (m | p)).
    intros D.
    eapply prime_div_false; eauto.
  
  destruct (Zdivide_inf _ _ Dm) as (r, Hr).
  exists r.
  split.
    (* Bounds for the new r *)
    assert (Pr : 0 <= r).
      apply Zmult_le_0_reg_r with m; auto with *.
      rewrite <- Hr.
      pose proof Zle_0_square y1.
      pose proof Zle_0_square y2.
      pose proof Zle_0_square y3.
      pose proof Zle_0_square y4.
      lia.
    
    assert (Nr : 0 <> r).
      (* otherwise yi=0  ⇒  m|xi  ⇒  m²|xi²  ⇒  m²|mp  ⇒  m|p  ⇒  baad *)
      intros Zr; subst.
      
      (* yi = 0 *)
      ring_simplify (0 * m) in Hr.
      assert (y0 : (y1 = 0 /\ y2 = 0) /\ (y3 = 0 /\ y4 = 0)).
        pose proof Zle_0_square y1.
        pose proof Zeq_0_square y1.
        pose proof Zle_0_square y2.
        pose proof Zeq_0_square y2.
        pose proof Zle_0_square y3.
        pose proof Zeq_0_square y3.
        pose proof Zle_0_square y4.
        pose proof Zeq_0_square y4.
        lia.
      
      apply Dmp.
      apply Zmult_divide_compat_rev_l with m; auto.
      rewrite Hx.
      repeat apply Zdivide_plus_r;
        apply Zdivide_square, divide_eqm; auto.
          rewrite <- eqm1; apply eq_eqm; tauto.
          rewrite <- eqm2; apply eq_eqm; tauto.
          rewrite <- eqm3; apply eq_eqm; tauto.
          rewrite <- eqm4; apply eq_eqm; tauto.
    
    assert (Lrm : r <= m).
      (* -m≤2*yi<m  ⇒  4yi²≤m²  ⇒  4rm≤4m²  ⇒ r≤m *)
      apply Zmult_le_reg_r with m; auto with *.
      rewrite <- Hr.
      apply Zmult_le_reg_r with 4; auto with *.
      ring_simplify.
      clear -help1 LBm.
      assert (B : forall x, 4 * (modsym x m) ^ 2 <= m ^2).
        clear -help1; intros x.
        pose proof modsym_bounds x m help1 as Bms.
        set (y := modsym x m); fold y in Bms; clearbody y.
        replace (4 * y ^ 2) with ((2 * y) ^ 2) by ring.
        apply Zbounding_square; auto.
        now auto with *.
      
      pose proof B x1 as Ey1; fold y1 in Ey1.
      pose proof B x2 as Ey2; fold y2 in Ey2.
      pose proof B x3 as Ey3; fold y3 in Ey3.
      pose proof B x4 as Ey4; fold y4 in Ey4.
      lia.
    
    assert (Nmr : r <> m).
      (* like for 0 <> r but harder : yi=-m/2 → xi≡m²/4 [m²] → m²|m*p*)
      intros Emr; subst.
      assert (Eyi : (2 * - y1 = m /\ 2 * - y2 = m) /\ (2 * - y3 = m /\ 2 * - y4 = m)).
        (* -m/2≤yi<m/2 donc |yi|≤m/2 mais Σyi²=m² donc |yi|=m/2 donc yi=-m/2 *)
        assert (Eyi : (2 * y1 = - m /\ 2 * y2 = - m) /\ (2 * y3 = - m /\ 2 * y4 = - m)).
          apply egality_case_sum_of_four_squares;
            try (apply modsym_bounds; notzero).
          rewrite <- Hr; ring.
        lia.
        
        destruct Eyi as ((Ey1, Ey2), (Ey3, Ey4)).
        apply Dmp.
        apply Zmult_divide_compat_rev_l with m; auto.
        rewrite Hx.
        apply Zmult_divide_compat_rev_l with 4; notzero.
        rewrite <- divide_eqm; notzero.
        ring_simplify.
        assert (REW : forall x, 4 * x ^ 2 = (2 * x) * (2 * x)) by (intros; ring).
        repeat rewrite REW; clear REW.
        transitivity (m * m + m * m + m * m + m * m).
          cut (forall x y, 2 * -y = m -> y ≡ x [m] ->
              (2 * x) * (2 * x) ≡ m * m [4 * (m * m)]).
            intros HYP.
            repeat apply Zplus_eqm;
              (eapply HYP; [ | eassumption ]; eassumption).
            
            intros x y Ey Mxy.
            apply eqm_square_half; notzero.
            rewrite <- Ey at 2.
            apply eqm_mult_compat_l.
            rewrite <- Mxy.
            replace (- y) with (y + 2 * - y) by ring.
            rewrite Ey.
            rewrite eqm_minus_0.
            apply divide_eqm; notzero.
            exists (- 1); ring.
          
          apply divide_eqm; notzero.
          exists 1; ring.
    
    lia.
    
    (* FS(r*p) *)
    assert (Erpm : (r * p) * (m * m) = (r * m) * (m * p)) by ring.
    rewrite Hx, <-Hr in Erpm.
    rewrite euler's_identity in Erpm.
    rem (y1 * x1 + y2 * x2 + y3 * x3 + y4 * x4) t1 Et1.
    rem (y1 * x2 - y2 * x1 - y3 * x4 + y4 * x3) t2 Et2.
    rem (y1 * x3 + y2 * x4 - y3 * x1 - y4 * x2) t3 Et3.
    rem (y1 * x4 - y2 * x3 + y3 * x2 - y4 * x1) t4 Et4.
    
    assert (D1 : (m | t1)).
      rewrite <- divide_eqm; auto; rewrite Et1.
      unfold y1, y2, y3, y4; repeat rewrite modsym_eqm.
      rewrite <-Hx, divide_eqm; auto.
      apply Z.divide_factor_l.
    
    assert (D2 : (m | t2)).
      rewrite <- divide_eqm; auto; rewrite Et2.
      unfold y1, y2, y3, y4; repeat rewrite modsym_eqm.
      try ring (* :-( :-( :-( *).
      red; f_equal; ring.
    
    assert (D3 : (m | t3)).
      rewrite <- divide_eqm; auto; rewrite Et3.
      unfold y1, y2, y3, y4; repeat rewrite modsym_eqm.
      red; f_equal; ring.
    
    assert (D4 : (m | t4)).
      rewrite <- divide_eqm; auto; rewrite Et4.
      unfold y1, y2, y3, y4; repeat rewrite modsym_eqm.
      red; f_equal; ring.
    
    exists (t1 / m); exists (t2 / m); exists (t3 / m); exists (t4 / m).
    apply Zmult_reg_r with (m * m).
      clear -help0; destruct m; auto; intro H; inversion H.
      rewrite Erpm.
      ring_simplify.
      cut (forall a, (m | a) -> (a / m) ^ 2 * m ^ 2 = a ^ 2).
        intros Q.
        do 4 (rewrite Q; auto).
        
        clear -help0.
        intros a D.
        destruct (Zdivide_inf m a D) as (k, E); subst.
        rewrite Z_div_mult_full; auto.
        ring.
Defined.


(** Induction scheme to use the previous lemma *)
(* TODO déplacer ça ? *)
Definition lt_wf_rect :=
  fun p (P : nat -> Type) F =>
    well_founded_induction_type
      (well_founded_ltof nat (fun m => m)) P F p.


(** Using the previous lemma, one can decrease [mp] into [np] to eventually get [p] *)

Lemma foursquare_prime : forall p, prime p -> foursquare p.
Proof.
  intros p Pp.
  
  destruct (Z.eq_dec p 2) as [E | E].
    (* Case p = 2 *)
    do 2 exists 1%Z; do 2 exists 0%Z; auto.
    
    (* Case p >= 3 *)
    
    assert (3 <= p) as Op by
      (pose proof (prime_ge_2 p Pp); lia); clear E.
    
    (* We prove : ∃m>0 FS(kp) *)
    pose (fs_mult := fun p m =>
      prod (foursquare (Z_of_nat (S m) * p))
        (Z_of_nat (S m) < p)).
    assert (sigT (fs_mult p)) as Hm.
      (* .. using the previous lemma *)
      destruct (prime_dividing_sum_of_two_squares_plus_one p Pp Op) as
        (l, (m, (k, (Ep, (Bm, (Bl, (Pk, Plm))))))).
      assert (tech1 : Z_of_nat (S (Z.abs_nat (k - 1))) = k).
        rewrite inj_S, inj_Zabs_nat, Z.abs_eq; [ | lia ]; auto with *.
      exists (Z.abs_nat (k - 1)); split.
        (* FS(kp) *)
        exists 0%Z; exists 1%Z; exists l; exists m.
        transitivity (p * k).
          rewrite tech1; ring.
          rewrite Ep; auto.
        
        (* Big part, the bound: k<p *)
        rewrite tech1; clear tech1.
        apply Zmult_lt_reg_r with (4 * p); [ auto with * | ].
        replace (p * (4 * p)) with (2 * (p * p) + 2 * (p * p)) by ring.
        replace (k * (4 * p)) with (4 * (p * k)) by ring.
        rewrite Ep.
        assert (tech2 : forall a b, 0 < a -> 2 * a < b -> 4 * a * a + 4 < b * b). 
          clear; intros a b Pa LT.
          assert (LE : 2 * a + 1 <= b) by lia.
          assert (Pda : 0 <= 2 * a + 1) by lia.
          assert (LE2 := Zmult_le_compat _ _ _ _ LE LE Pda Pda).
          eapply Z.lt_le_trans; [ | apply LE2 ].
          ring_simplify.
          lia.
        
        assert (tech3 : forall a b, 0 <= a -> 2 * a < b -> 4 * a * a < b * b). 
          clear; intros a b Pa LT.
          assert (LE : 2 * a + 1 <= b) by lia.
          assert (Pda : 0 <= 2 * a + 1) by lia.
          assert (LE2 := Zmult_le_compat _ _ _ _ LE LE Pda Pda).
          eapply Z.lt_le_trans; [ | apply LE2 ].
          ring_simplify.
          lia.
        
        assert (p2_pos : 0 < p * p).
          transitivity (1 * p).
            lia.
            apply Zmult_lt_compat_r; lia.
        
        rem (l * l) ll Ell.
        rem (m * m) mm Emm.
        rem (p * p) pp Epp.
        destruct Plm as (NNl, (NNm, [Pl | Pm])).
          specialize (tech2 _ p Pl Bl).
          specialize (tech3 _ p NNm Bm).
          rewrite <- Zmult_assoc, <-Ell, <-Emm, <-Epp in *.
          clear -tech2 tech3 p2_pos.
          ring_simplify.
          lia.
          
          specialize (tech2 _ p Pm Bm).
          specialize (tech3 _ p NNl Bl).
          rewrite <- Zmult_assoc, <-Ell, <-Emm, <-Epp in *.
          clear -tech2 tech3 p2_pos.
          ring_simplify.
          lia.
          
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
      assert (LBm : 1 < Z_of_nat (S (S m))) by lia.
      destruct (foursquare_prime_factor_decreasing p Pp _ (conj LBm UBm) FSm) as (n, ((LBn, UBn), FSn)).
        apply IH with (Z.abs_nat (n - 1)).
          unfold ltof.
          lia.
          
          unfold fs_mult.
          rewrite inj_S, inj_Zabs_nat, Z.abs_eq; auto with *; unfold Z.succ.
          replace (n - 1 + 1) with n by ring.
          split; auto; lia.
Defined.


(** Trivial application of the previous lemma and euler's identity *)

Theorem lagrange_4_square_theorem : forall n, 0 <= n -> foursquare n.
Proof.
  intros n; eapply Z_prime_rect; auto.
    repeat (exists 0); auto.
    
    exists 1; repeat (exists 0); auto.
    
    apply foursquare_prime.
    
    apply mult_foursquare_compat.
Defined.


Definition lagrange_fun (n : Z) : (Z * Z) * (Z * Z) :=
  let (a, ha) := lagrange_4_square_theorem (Z.abs n) (Zabs_pos n) in
  let (b, hb) := ha in
  let (c, hc) := hb in
  let (d, _ ) := hc in
  ((a, b), (c, d)).

Lemma lagrange_fun_spec (n : Z) :
  (let (ab, cd) := lagrange_fun n in let (a, b) := ab in let (c, d) := cd in
  Z.abs n = a * a + b * b + c * c + d * d).
Proof.
  unfold lagrange_fun.
  destruct (lagrange_4_square_theorem (Z.abs n) (Zabs_pos n)) as (a, (b, (c, (d, pr)))).
  exact pr.
Qed.

(*
Require Extraction.
Extraction "Lagrange_four_square.ml" lagrange_fun.
*)

(*
Eval compute in lagrange_fun 0.

Print Opaque Dependencies lagrange_4_square_theorem.
*)
