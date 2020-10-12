Require Import ZArith Znumtheory Lia Zpow_facts MyZ.
Require Import Hurwitz_def.

Section basic_lemmas.

Variable h1 h2 h3 : Hurwitz.

(* eq *)

Lemma Hurwitz_dec : { h1 = h2 } + { h1 <> h2 }.
Proof.
repeat decide equality.
Qed.

(* hopp *)

Lemma hopp_invol : h- (h- h1) = h1.
Proof.
destruct h1 ; simpl ; f_equal ; ring.
Qed.

Lemma hopp_hadd_distrib : h- (h1 h+ h2) = h- h1 h+ h- h2.
Proof.
destruct h1, h2, h3 ; simpl ; f_equal ; ring.
Qed.

Lemma hopp_hadd_hminus : h- h1 h+ h2 = h2 h- h1.
Proof.
destruct h1, h2 ; simpl ; f_equal ; ring.
Qed.

(* hadd *)

Lemma hadd_comm : h1 h+ h2 = h2 h+ h1.
Proof.
destruct h1, h2 ; simpl ; f_equal ; ring.
Qed.

Lemma hadd_assoc : h1 h+ h2 h+ h3 = h1 h+ (h2 h+ h3).
Proof.
destruct h1, h2, h3 ; simpl ; f_equal ; ring.
Qed.

(* hmul *)

Lemma hmul_assoc : forall a b c, hmul a (hmul b c) = hmul (hmul a b) c.
Proof.
intros [] [] []; intros.
 unfold hmul ; f_equal ; ring.
Qed.

Lemma hmul_1_l : hmul (IZH 1) h1 = h1.
Proof.
destruct h1 ; intros.
unfold hmul, IZH.
f_equal; ring.
Qed.

Lemma hmul_1_r : hmul h1 (IZH 1) = h1.
Proof.
destruct h1 ; intros.
unfold hmul, IZH.
f_equal; ring.
Qed.

(* conjugate *)

Lemma hconj_invol : hconj (hconj h1) = h1.
Proof.
destruct h1 ; intros ; unfold hconj ; f_equal ; ring.
Qed.

Lemma hconj_hopp : hconj (h- h1) = h- (hconj h1).
unfold hconj, hopp ; destruct h1 ; intros ; f_equal ; ring.
Qed.

Lemma hconj_hadd : hconj (h1 h+ h2) = hconj h1 h+ hconj h2.
Proof.
unfold hconj, hadd ; destruct h1, h2 ; intros ; f_equal ; ring.
Qed.

Lemma hconj_hminus : hconj (h1 h- h2) = (hconj h1) h- (hconj h2).
Proof.
unfold hminus, hadd, hopp, hconj ; destruct h1, h2 ; intros ; f_equal ; ring.
Qed.

Lemma hconj_hmul : hconj (h1 h* h2) = (hconj h2) h* (hconj h1).
Proof.
unfold hmul, hconj ; destruct h1, h2 ; f_equal ; ring.
Qed.

(* norm *)

Lemma hnorm2_IZH : forall z, hnorm2 (IZH z) = z ^ 2.
Proof.
intro z ; unfold hnorm2, hconj, IZH, hmul, i ; ring.
Qed.

Lemma hnorm2_hconj : hnorm2 (hconj h1) = hnorm2 h1.
Proof.
destruct h1 ; intros ; unfold hnorm2 , hconj , hmul, Hurwitz_def.i ;
 ring.
Qed.

Lemma hnorm2_hmul : hnorm2 (h1 h* h2) = hnorm2 h1 * hnorm2 h2.
Proof.
destruct h1, h2 ; unfold hnorm2, hconj, hmul, Hurwitz_def.i ;
 ring.
Qed.

Lemma real_hnorm2 : is_real (hmul h1 (hconj h1)).
Proof.
destruct h1 ; intros; unfold hmul, hconj.
repeat split;
  cbv delta [Hurwitz_def.h Hurwitz_def.i Hurwitz_def.j Hurwitz_def.k];
  cbv iota beta;
  ring.
Qed.

Lemma Zmult_le_reg_l : forall m n p, 0 < p -> p * m <= p * n -> m <= n.
Proof.
intros m n p p_pos ; do 2 rewrite (Zmult_comm p) ;
 apply Zmult_le_reg_r, Z.lt_gt ; assumption.
Qed.

Lemma hnorm2_pos : 0 <= hnorm2 h1.
Proof.
destruct h1 ; intros ; unfold hnorm2, hmul, hconj.
 cbv delta [Hurwitz_def.i] ; cbv beta iota.
 ring_simplify.
 apply Zmult_le_reg_l with 4 ; [lia |].
 transitivity ((h + 2 * i) ^ 2 + (h + 2 * j) ^ 2 + (h + 2 * k) ^ 2 + h ^ 2).
 do 4 rewrite Zpower_2 ; repeat apply Zplus_le_0_compat ; apply Z.ge_le, sqr_pos.
 apply eq_Zle ; ring.
Qed.

Lemma h_Zle_hnorm2 : (h h1) ^ 2 <= 4 * hnorm2 h1.
Proof.
destruct h1 ; intros ; unfold hnorm2, hmul, hconj.
 cbv delta [Hurwitz_def.h Hurwitz_def.i] ; cbv beta iota.
 apply Zle_0_minus_le ; ring_simplify.
 transitivity ((h + 2 * i) ^ 2 + (h + 2 * j) ^ 2 + (h + 2 * k) ^ 2).
 do 3 rewrite Zpower_2 ; repeat apply Zplus_le_0_compat ; apply Z.ge_le, sqr_pos.
 apply eq_Zle ; ring.
Qed.

End basic_lemmas.

(* units *)

Lemma H_unit_is_unit : forall x, H_unit x -> is_H_unit x.
Proof.
  intros x Ux.
  exists (hconj x).
  destruct Ux as [[]|[]|[]|[]|[] [] [] []]; auto.
Qed.

Lemma is_H_unit_hnorm2_1 : forall x, is_H_unit x -> hnorm2 x = 1.
Proof.
intros x (y, Ixy).
 assert (H : hnorm2 x  * hnorm2 y = 1).
  etransitivity ; [symmetry ; eapply hnorm2_hmul |].
  rewrite Ixy ; apply hnorm2_IZH.
 eapply Zmult_one ; [apply Z.le_ge, hnorm2_pos | eassumption].
Qed.

Lemma H_unit_dec : forall x, H_unit x + (H_unit x -> False).
Proof.
intro h ; pose (np := Z_of_Z_unit Z_one) ; pose (nn := Z_of_Z_unit Z_mone).
 destruct (Hurwitz_dec h (mkHurwitz (2 * np) (- np) (- np) (- np))) as [e | Hnp_1].
  left ; subst ; apply H_unit_1.
 destruct (Hurwitz_dec h (mkHurwitz (2 * nn) (- nn) (- nn) (- nn))) as [e | Hnn_1].
  left ; subst ; apply H_unit_1.
 destruct (Hurwitz_dec h (mkHurwitz 0 np 0 0)) as [e | Hnp_i].
  left ; subst ; apply H_unit_i.
 destruct (Hurwitz_dec h (mkHurwitz 0 nn 0 0)) as [e | Hnn_i].
  left ; subst ; apply H_unit_i.
 destruct (Hurwitz_dec h (mkHurwitz 0 0 np 0)) as [e | Hnp_j].
  left ; subst ; apply H_unit_j.
 destruct (Hurwitz_dec h (mkHurwitz 0 0 nn 0)) as [e | Hnn_j].
  left ; subst ; apply H_unit_j.
 destruct (Hurwitz_dec h (mkHurwitz 0 0 0 np)) as [e | Hnp_k].
  left ; subst ; apply H_unit_k.
 destruct (Hurwitz_dec h (mkHurwitz 0 0 0 nn)) as [e | Hnn_k].
  left ; subst ; apply H_unit_k.
 pose (hpp := halfsub Z_one Z_one) ; pose (hpn := halfsub Z_one Z_mone) ;
 pose (hnp := halfsub Z_mone Z_one) ; pose (hnn := halfsub Z_mone Z_mone).
 destruct (Hurwitz_dec h (mkHurwitz np hpp hpp hpp)) as [e | Hh_0].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz np hpp hpp hnp)) as [e | Hh_1].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz np hpp hnp hpp)) as [e | Hh_2].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz np hpp hnp hnp)) as [e | Hh_3].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz np hnp hpp hpp)) as [e | Hh_4].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz np hnp hpp hnp)) as [e | Hh_5].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz np hnp hnp hpp)) as [e | Hh_6].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz np hnp hnp hnp)) as [e | Hh_7].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz nn hpn hpn hpn)) as [e | Hh_8].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz nn hpn hpn hnn)) as [e | Hh_9].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz nn hpn hnn hpn)) as [e | Hh_A].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz nn hpn hnn hnn)) as [e | Hh_B].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz nn hnn hpn hpn)) as [e | Hh_C].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz nn hnn hpn hnn)) as [e | Hh_D].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz nn hnn hnn hpn)) as [e | Hh_E].
  left ; subst ; apply H_unit_h.
 destruct (Hurwitz_dec h (mkHurwitz nn hnn hnn hnn)) as [e | Hh_F].
  left ; subst ; apply H_unit_h.
 right ; intros Hf ; inversion Hf.
  destruct u ; [apply Hnp_1 | apply Hnn_1] ; auto.
  destruct u ; [apply Hnp_i | apply Hnn_i] ; auto.
  destruct u ; [apply Hnp_j | apply Hnn_j] ; auto.
  destruct u ; [apply Hnp_k | apply Hnn_k] ; auto.
  destruct u ; destruct v ; destruct w ; destruct z ;
  [ apply Hh_0 | apply Hh_1 | apply Hh_2 | apply Hh_3 | apply Hh_4 |
    apply Hh_5 | apply Hh_6 | apply Hh_7 | apply Hh_8 | apply Hh_9 |
    apply Hh_A | apply Hh_B | apply Hh_C | apply Hh_D | apply Hh_E |
    apply Hh_F ] ; auto.
Qed.
  

Lemma H_unit_characterization : forall x, is_H_unit x -> H_unit x.
Proof.
intros x Hx ; assert (Nx := is_H_unit_hnorm2_1 _ Hx) ; destruct Hx as [y Ixy].
 assert (Ny : hnorm2 y = 1).
  apply Zmult_reg_l with 1 ; [lia |] ; rewrite <- Zpower_2,
   <- hnorm2_IZH, <- Ixy, <- Nx ; symmetry ; apply hnorm2_hmul.

  (* Une fois qu'on a ça, c'est pas si facile. Chez les quaternions
  on peut borner |a+bi+cj+dk|>=|a|+|b|+|c|+|d| mais comme le changement
  est dans une base pas trop orthonormée, c'est moins facile, mais c'est
  possible quand même. *)
  (*intros [[|p|p] [|q|q] [|r|r] [|s|s]] (y, Uxy).*)
  
  (* idée : on peut énumérer les x, y de norme bornée (par 1), et après
  on peut vérifier que si xy=1 c'est que H_unit x. Peut-être avoir la 
  décidabilité de H_unit aidera. *)
Abort.

