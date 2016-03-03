(** * Analysis in real numbers *)
(** Catherine Lelay. Feb 2016 *)

Require Export UniMath.Dedekind.NonnegativeReals_analysis.
Require Export UniMath.Dedekind.Reals.
Require Import UniMath.Bourbaki.NormedSpace.
Require Import UniMath.Bourbaki.Filters.
Require Export UniMath.Dedekind.Complements.

(** ** NonnegativeReals is an absrng *)

Lemma issepp_hr_abs :
  ∀ x : hr_commrng, hr_ap_rel x 0%rng <-> (0 < hr_abs x)%NR.
Proof.
  intros x.
  split ; intros H.
  - apply hr_ap_lt in H.
    destruct H as [H | H].
    + apply_pr2_in hr_to_NR_negative H.
      unfold Rabs, hr_abs.
      rewrite (pr1 H), maxNonnegativeReals_carac_r.
      apply ispositive_apNonnegativeReals, (pr2 H).
      now apply isnonnegative_NonnegativeReals.
    + apply_pr2_in hr_to_NR_positive H.
      unfold Rabs, hr_abs.
      rewrite (pr2 H), maxNonnegativeReals_carac_l.
      apply ispositive_apNonnegativeReals, (pr1 H).
      now apply isnonnegative_NonnegativeReals.
  - apply maxNonnegativeReals_lt' in H.
    revert H.
    apply hinhuniv.
    intros [H | H].
    + rewrite <- (hr_to_NR_bij x), <- (hr_to_NR_bij 0%rng), hr_to_NR_zero.
      apply NR_to_hr_ap.
      change ((hr_to_NRpos x) + 0 ≠ 0 + (hr_to_NRneg x))%NR.
      rewrite hr_to_NRposneg_zero.
      rewrite !isrunit_zero_plusNonnegativeReals.
      now apply_pr2 ispositive_apNonnegativeReals.
      exact H.
    + rewrite <- (hr_to_NR_bij x), <- (hr_to_NR_bij 0%rng), hr_to_NR_zero.
      apply NR_to_hr_ap.
      change ((hr_to_NRpos x) + 0 ≠ 0 + (hr_to_NRneg x))%NR.
      rewrite hr_to_NRnegpos_zero.
      rewrite !islunit_zero_plusNonnegativeReals.
      apply issymm_apNonnegativeReals.
      now apply_pr2 ispositive_apNonnegativeReals.
      exact H.
Qed.

Lemma hr_abs_one :
  hr_abs (1%rng : hr_commrng) = 1%NR.
Proof.
  unfold hr_abs, hr_to_NRpos, hr_to_NRneg.
  rewrite hr_to_NR_one.
  rewrite maxNonnegativeReals_carac_l.
  reflexivity.
  apply isnonnegative_NonnegativeReals.
Qed.

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
  - now apply issepp_hr_abs.
  - now apply_pr2 issepp_hr_abs.
  - rewrite hr_abs_opp.
    exact hr_abs_one.
  - intros x y.
    apply istriangle_Rabs.
  - intros x y.
    rewrite Rabs_Rmult.
    apply isrefl_leNonnegativeReals.
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
