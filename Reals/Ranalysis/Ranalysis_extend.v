(*
(C) Copyright 2010--2014, COQTAIL team

Project Info: http://sourceforge.net/projects/coqtail/

This library is free software; you can redistribute it and/or modify it
under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation; either version 2.1 of the License, or
(at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301,
USA.
*)

Require Import Rinterval Ranalysis_def Ranalysis_def_simpl Ranalysis_continuity.
Require Import Ranalysis_derivability Ranalysis_usual Ranalysis_facts.
Require Import Rbase MyRIneq MyR_dist Rfunctions Lra.

Open Scope R_scope.

Definition extend_continuously (f : R -> R) (a b : R) (x : R) : R.
destruct (Rlt_le_dec x a).
 + exact (f a).
 + destruct (Rle_lt_dec x b).
   - exact (f x).
   - exact (f b).
Defined.


Lemma extend_continuously_continuous : forall a b f,
  a <= b ->
  Ranalysis_def.continuity_interval a b f ->
  Ranalysis1.continuity (extend_continuously f a b).
Proof.
intros a b f aleb f_cont x ; destruct (Rlt_le_dec x a) as [xlta | alex].
{ exists ((a - x) / 2)%R ; split.
  + eapply dist_2_pos ; assumption.
  + intros h [_ h_bd] ; simpl ; unfold R_dist, extend_continuously.
    destruct (Rlt_le_dec x a) as [_ | hf].
    {
      destruct (Rlt_le_dec h a) as [_ | hf].
      + unfold Rminus ; rewrite Rplus_opp_r, Rabs_R0 ; assumption.
      + simpl in h_bd ; unfold R_dist in h_bd.
        destruct (Rlt_irrefl x) ; apply (Rlt_le_trans x a) ; [assumption |].
        transitivity (h + h - a)%R.
        - apply Rminus_le_compat_r, Rplus_le_compat ; assumption.
        - left. apply Rlt_minus_swap, Rminus_lt_compat_rev with (c := x).
          apply Rle_lt_trans with (2 * (h - x))%R ; [right ; ring |].
          apply Rmult_Rdiv_lt_compat_l_rev ; [lra |].
          rewrite <- Rabs_right at 1 ; [assumption | lra].
    }
    destruct (Rlt_irrefl x) ; apply Rlt_le_trans with a ; assumption.
}
destruct (Rle_lt_dec x b) as [xleb | bltx].
assert (x_in : interval a b x).
{
  unfold interval ; split ; assumption.
}
{
  intros eps eps_pos ; destruct (f_cont x x_in _ eps_pos) as [delta [delta_pos Hdelta]].
  exists delta ; split.
  + assumption.
  + intros h [_ h_bd] ; simpl ; unfold R_dist, extend_continuously.
    destruct (Rlt_le_dec h a) as [hlta | aleh].
    {
      destruct (Rlt_le_dec x a) as [_ | _].
      + unfold Rminus ; rewrite Rplus_opp_r, Rabs_R0 ; assumption.
      + destruct (Rle_lt_dec x b) as [_ | hf].
        {
          apply Hdelta ; split.
          + split ; [reflexivity | transitivity x ; assumption].
          + simpl ; rewrite R_dist_sym ; transitivity (R_dist x h).
            - apply Rlt_le_Rdist_compat ; assumption.
            - rewrite R_dist_sym ; assumption.
        }
        destruct (Rlt_irrefl x) ; apply Rle_lt_trans with b ; assumption.
    }
    {
      destruct (Rle_lt_dec h b) as [hleb | blth].
      {
        destruct (Rlt_le_dec x a) as [hf | _].
        + destruct (Rlt_irrefl x) ; apply Rlt_le_trans with a ; assumption.
        + destruct (Rle_lt_dec x b) as [_ | hf].
          - apply Hdelta ; repeat split ; assumption.
          - destruct (Rlt_irrefl b) ; apply Rlt_le_trans with x ; assumption.
      }
      {
        destruct (Rlt_le_dec x a) as [hf | _].
        + destruct (Rlt_irrefl x) ; apply Rlt_le_trans with a ; assumption.
        + destruct (Rle_lt_dec x b) as [_ | hf].
          {
            apply Hdelta ; split.
            + split ; [transitivity x ; assumption | reflexivity].
            + simpl ; transitivity (R_dist h x).
            - apply Rle_lt_Rdist_compat ; assumption.
            - assumption.
          }
          destruct (Rlt_irrefl x) ; apply Rle_lt_trans with b ; assumption.
      }
   }
}
{ exists ((x - b) / 2)%R ; split.
  + eapply dist_2_pos ; assumption.
  + intros h [_ h_bd] ; simpl ; unfold R_dist, extend_continuously.
    destruct (Rlt_le_dec x a) as [hf | _].
    - destruct (Rlt_irrefl a) ; apply Rle_lt_trans with x ; assumption.
    - destruct (Rle_lt_dec x b) as [hf |_].
      destruct (Rlt_irrefl b) ; apply Rlt_le_trans with x ; assumption.
      {
        destruct (Rlt_le_dec h a) as [hlta | aleh].
        + simpl in h_bd ; unfold R_dist in h_bd.
          destruct (Rlt_irrefl a) ; apply (Rle_lt_trans a h) ; [| assumption].
          transitivity b ; [assumption |].
          left ; apply Rmult_lt_reg_l with 2 ; [lra |].
          transitivity (x + b)%R.
          - replace (2 * b)%R with (b + b)%R by ring ; apply Rplus_lt_compat_r.
            assumption.
          - apply Rlt_minus_sort3, Rplus_lt_reg_r with x.
            apply Rle_lt_trans with (2 * (x - h))%R ; [right ; ring |].
            apply Rmult_Rdiv_lt_compat_l_rev ; [lra |].
            rewrite <- Rabs_right at 1 ; [| lra].
            rewrite Rabs_minus_sym, Rplus_comm. assumption.
          + destruct (Rle_lt_dec h b) as [hleb | blth].
            - destruct (Rlt_irrefl b) ; apply Rlt_le_trans with h ; [| assumption].
              apply Rmult_lt_reg_l with 2 ; [lra |].
              transitivity (x + b)%R.
              * replace (2 * b)%R with (b + b)%R by ring ; apply Rplus_lt_compat_r.
                assumption.
              * apply Rlt_minus_sort3, Rplus_lt_reg_r with x.
                apply Rle_lt_trans with (2 * (x - h))%R ; [right ; ring |].
                apply Rmult_Rdiv_lt_compat_l_rev ; [lra |].
                rewrite <- Rabs_right at 1 ; [| lra].
                rewrite Rabs_minus_sym, Rplus_comm ; assumption.
            - unfold Rminus ; rewrite Rplus_opp_r, Rabs_R0 ; assumption.
      }
}
Qed.

Lemma extend_continuously_extends_open_interval : forall a b f x,
 Rinterval.open_interval a b x -> f x = extend_continuously f a b x.
Proof.
intros a b f x [alex xleb] ; unfold extend_continuously.
 destruct (Rlt_le_dec x a).
  + destruct (Rlt_irrefl x) ; transitivity a ; assumption.
  + destruct (Rle_lt_dec x b).
    - reflexivity.
    - destruct (Rlt_irrefl x) ; transitivity b ; assumption.
Qed.

Lemma extend_continuously_extends_interval : forall a b f x,
 Rinterval.interval a b x -> f x = extend_continuously f a b x.
Proof.
intros a b f x [alex xleb] ; unfold extend_continuously.
 destruct (Rlt_le_dec x a).
  + destruct (Rlt_irrefl x) ; apply Rlt_le_trans with a ; assumption.
  + destruct (Rle_lt_dec x b).
    - reflexivity.
    - destruct (Rlt_irrefl x) ; apply Rle_lt_trans with b ; assumption.
Qed.

Lemma extend_continuously_derivable_open_interval : forall a b f,
  Ranalysis_def.derivable_open_interval a b f ->
  Ranalysis_def.derivable_open_interval a b (extend_continuously f a b).
Proof.
intros a b f f_deriv x x_in ;
 eapply derivable_pt_in_ext_strong, f_deriv ; try assumption.
 apply extend_continuously_extends_open_interval.
Qed.

Lemma extend_continuously_derive_open_interval :
  forall a b f fext_deriv f_deriv c,
  (derive_open_interval a b (extend_continuously f a b) fext_deriv c =
  derive_open_interval a b f f_deriv c)%R.
Proof.
intros a b f fext_deriv f_deriv c ; unfold derive_open_interval ;
 destruct (in_open_interval_dec a b c) as [c_in | c_out].
 + apply derive_pt_in_ext_strong.
   - apply dense_open_interval.
     * transitivity c ; apply c_in.
     * apply open_interval_interval ; assumption.
   - assumption.
   - intros ; symmetry ; eapply extend_continuously_extends_open_interval ; assumption.
 + reflexivity.
Qed.
