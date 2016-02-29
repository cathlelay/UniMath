(** * Analysis in real numbers *)
(** Catherine Lelay. Feb 2016 *)

Require Export UniMath.Dedekind.NonnegativeReals_analysis.
Require Export UniMath.Dedekind.Reals.
Require Import UniMath.Bourbaki.NormedSpace.
Require Import UniMath.Bourbaki.Filters.
Require Export UniMath.Dedekind.Complements.

(** ** NonnegativeReals is an absrng *)

Unset Printing Notations.

Definition R_absrng : absrng NR_NonnegativeRig.
Proof.
  exists Reals.
  simple refine (tpair _ _ _).
  { simple refine (tpair _ _ _).
    apply Rap.
    repeat split.
    - intros x.
      now apply isirrefl_Rap.
    - intros x y.
      now apply issymm_Rap.
    - intros x y z.
      now apply iscotrans_Rap.
    - intros x y.
      now apply istight_Rap. }
  exists hr_abs.
  split ; [split | repeat split].
  - intros a b c.
    exact (pr2 (Rplus_apcompat_r c a b)).
  - intros a b c.
    exact (pr2 (Rplus_apcompat_l c a b)).
  - intros H.
    change (0 < Rabs x)%NR.
    simpl in H.
    destruct (pr1 (hr_NR_ap_0 x (pr1 (hr_to_NR x)) (pr1 (pr2 (hr_to_NR x)))) H) as [H0 | H0] ;
    apply ispositive_apNonnegativeReals in H0 ;
    eapply istrans_lt_le_ltNonnegativeReals.
    apply H0.
    eapply istrans_leNonnegativeReals, maxNonnegativeReals_le_r.
    apply minusNonnegativeReals_le.
    apply H0.
    eapply istrans_leNonnegativeReals, Dcuts_max_le_l.
    apply Dcuts_minus_le.
  - apply hinhuniv.
    intros (r,(_)).
    apply hinhuniv.
    intros H.
    simple refine (pr2 (hr_NR_ap_0 _ _ _) _).
    apply (pr1 (hr_to_NR x)).
    apply (pr1 (pr2 (hr_to_NR x))).
    destruct (hr_to_NR x) as (X,(Hx,Hle)) ; simpl pr1 in H |- *.
    destruct H as [Hr | Hr].
    + right.
      apply_pr2 ispositive_apNonnegativeReals.
      eapply istrans_lt_le_ltNonnegativeReals.
      apply hinhpr.
      exists r.
      split.
      apply Dcuts_zero_empty.
      apply Hr.
      simple refine (pr1 (Hle (((pr1 X) - (pr2 X))%NR ,, ((pr2 X) - (pr1 X))%NR) _)).
      revert Hx.
      apply hr_inside_carac'.
      simpl pr1 ; simpl pr2.
      rewrite iscomm_plusNonnegativeReals, !Dcuts_minus_plus_max.
      apply iscomm_Dcuts_max.
    + left.
      apply_pr2 ispositive_apNonnegativeReals.
      eapply istrans_lt_le_ltNonnegativeReals.
      apply hinhpr.
      exists r.
      split.
      apply Dcuts_zero_empty.
      apply Hr.
      simple refine (pr2 (Hle (((pr1 X) - (pr2 X))%NR ,, ((pr2 X) - (pr1 X))%NR) _)).
      revert Hx.
      apply hr_inside_carac'.
      simpl pr1 ; simpl pr2.
      rewrite iscomm_plusNonnegativeReals, !Dcuts_minus_plus_max.
      apply iscomm_Dcuts_max.
  - rewrite hr_abs_opp.
    change (@rngunel2 Reals) with Rone.
    change (hr_abs Rone) with (maxNonnegativeReals (pr1 (RtoNRNR Rone)) (pr2 (RtoNRNR Rone))).
    rewrite <- NRNRtoR_one.
    rewrite RtoNRNR_NRNRtoR ; simpl pr1 ; simpl pr2.
    rewrite <- (minusNonnegativeReals_correct_l _ _ 1%NR).
    rewrite minusNonnegativeReals_eq_zero.
    rewrite maxNonnegativeReals_carac_l.
    reflexivity.
    apply isnonnegative_NonnegativeReals.
    apply isnonnegative_NonnegativeReals.
    apply pathsinv0, islunit_zero_plusNonnegativeReals.
  - intros x y.
    apply istriangle_Rabs.
  - intros x y.
    apply Rabs_submult.
Defined.

Definition R_NormedModule : NormedModule R_absrng
  := absrng_to_NormedModule R_absrng.

Definition is_Rfilter_lim (F : Filter) (x : Reals) :=
  is_filter_lim (X := R_NormedModule) F x.
Definition ex_Rfilter_lim (F : Filter) :=
  ex_filter_lim (X := R_NormedModule) F.

Definition is_Rlim {X : UU} (f : X -> Reals) (F : Filter) (l : Reals) :=
  is_lim (V := R_NormedModule) f F l.
Definition ex_Rlim {X : UU} (f : X -> Reals) (F : Filter) :=
  ex_lim (V := R_NormedModule) f F.
