(** * Analysis in nonnegative real numbers *)
(** Catherine Lelay. Feb 2016 *)

Require Export UniMath.Dedekind.NonnegativeReals.
Require Export UniMath.Dedekind.NonnegativeRationals.
Require Import UniMath.Bourbaki.MetricSpace.
Require Import UniMath.Bourbaki.NormedSpace.
Require Export UniMath.Dedekind.Complements.

(** ** NonnegativeReals is a NonnegativeRig *)

Lemma isldistr_minus_multNonnegativeReals :
  ∀ x y z : NonnegativeReals, x * (y - z) = x * y - x * z.
Proof.
  intros x y z.
  apply (plusNonnegativeReals_eqcompat_l (x * z)).
  rewrite <- isldistr_plus_multNonnegativeReals.
  rewrite !Dcuts_minus_plus_max.
  apply Dcuts_eq_is_eq.
  intros r.
  split.
  - apply hinhuniv.
    intros ((rx,ryz)) ; simpl ; intros (->,(Xr)).
    apply hinhfun.
    intros [Yr | Zr].
    + left.
      apply hinhpr.
      now exists (rx,ryz).
    + right.
      apply hinhpr.
      now exists (rx,ryz).
  - apply hinhuniv.
    intros [ | ].
    + apply hinhuniv.
      intros ((rx,ry)) ; simpl ; intros (->,(Xr,Yr)).
      apply hinhpr.
      exists (rx,ry).
      repeat split.
      exact Xr.
      apply hinhpr.
      now left.
    + apply hinhuniv.
      intros ((rx,rz)) ; simpl ; intros (->,(Xr,Zr)).
      apply hinhpr.
      exists (rx,rz).
      repeat split.
      exact Xr.
      apply hinhpr.
      now right.
Qed.
Lemma isrdistr_minus_multNonnegativeReals :
  ∀ x y z : NonnegativeReals, (x - y) * z = x * z - y * z.
Proof.
  intros x y z.
  now rewrite iscomm_multNonnegativeReals, isldistr_minus_multNonnegativeReals, !(iscomm_multNonnegativeReals z).
Qed.

Definition minNonnegativeReals (x y : NonnegativeReals) : NonnegativeReals.
Proof.
  intros x y.
  exists (λ r, r ∈ x ∧ r ∈ y).
  repeat split.
  - now apply is_Dcuts_bot with (1 := pr1 X).
  - now apply is_Dcuts_bot with (1 := pr2 X).
  - intros r (Xr,Yr).
    generalize (is_Dcuts_open _ _ Xr) (is_Dcuts_open _ _ Yr).
    apply hinhfun2.
    intros (rx,(Xrx,Hrx)) (ry,(Yry,Hry)).
    destruct (isdecrel_ltNonnegativeRationals rx ry).
    + exists rx ; repeat split.
      exact Xrx.
      apply is_Dcuts_bot with (1 := Yry).
      now apply lt_leNonnegativeRationals.
      exact Hrx.
    + exists ry ; repeat split.
      apply is_Dcuts_bot with (1 := Xrx).
      now apply notlt_geNonnegativeRationals.
      exact Yry.
      exact Hry.
  - intros c Hc.
    generalize (is_Dcuts_error x c Hc).
    apply hinhuniv.
    intros [nXc | (qx,(Xq,nXq))].
    + apply hinhpr.
      left.
      intro H ; apply nXc.
      now apply (pr1 H).
    + generalize (is_Dcuts_error y c Hc).
      apply hinhuniv.
      intros [nYc | (qy,(Yq,nYq))].
      * apply hinhpr.
        left.
        intro H ; apply nYc.
        now apply (pr2 H).
      * apply hinhpr.
        right.
        destruct (isdecrel_ltNonnegativeRationals qx qy) as [Hq | Hq].
        exists qx ; repeat split.
        exact Xq.
        apply is_Dcuts_bot with (1 := Yq).
        now apply lt_leNonnegativeRationals.
        intro H ; apply nXq.
        exact (pr1 H).
        exists qy ; repeat split.
        apply is_Dcuts_bot with (1 := Xq).
        now apply notlt_geNonnegativeRationals.
        exact Yq.
        intro H ; apply nYq.
        exact (pr2 H).
Defined.

Transparent EffectivelyOrdered_NonnegativeReals.

Lemma minNonnegativeReals_le_l :
  ∀ x y : NonnegativeReals, minNonnegativeReals x y <= x.
Proof.
  now intros x y r (Xr,Yr).
Qed.
Lemma minNonnegativeReals_le_r :
  ∀ x y : NonnegativeReals, minNonnegativeReals x y <= y.
Proof.
  now intros x y r (Xr,Yr).
Qed.
Lemma minNonnegativeReals_gtcompat :
  ∀ x y z : NonnegativeReals, z < x -> z < y -> z < minNonnegativeReals x y.
Proof.
  intros x y z.
  apply hinhfun2.
  intros (rx,(nZx,Xr)) (ry,(nZy,Yr)).
  case (isdecrel_ltNonnegativeRationals rx ry) ; intro Hr.
  - exists rx.
    split.
    exact nZx.
    split.
    exact Xr.
    apply is_Dcuts_bot with (1 := Yr).
    now apply lt_leNonnegativeRationals.
  - exists ry.
    split.
    exact nZy.
    split.
    apply is_Dcuts_bot with (1 := Xr).
    now apply notlt_geNonnegativeRationals.
    exact Yr.
Qed.
Lemma ispositive_minNonnegativeReals :
  ∀ x y : NonnegativeReals, 0 < x -> 0 < y -> 0 < minNonnegativeReals x y.
Proof.
  intros x y.
  apply hinhfun2.
  intros (rx,(_,Xr)) (ry,(_,Yr)).
  destruct (isdecrel_ltNonnegativeRationals rx ry) as [Hr | Hr].
  - exists rx ; repeat split.
    apply Dcuts_zero_empty.
    exact Xr.
    apply is_Dcuts_bot with (1 := Yr).
    now apply lt_leNonnegativeRationals.
  - exists ry ; repeat split.
    apply Dcuts_zero_empty.
    apply is_Dcuts_bot with (1 := Xr).
    now apply notlt_geNonnegativeRationals.
    exact Yr.
Qed.

Definition NR_NonnegativeRig : NonnegativeRig.
Proof.
  exists (commrigtorig (pr1 NonnegativeReals)).
  exists apNonnegativeReals, (pr1 geNonnegativeReals), (pr1 gtNonnegativeReals).
  split ; [split ; [ | split ; [ | split]] | repeat split].
  - exact (pr2 (pr2 Dcuts)).
  - exact iseo_Dcuts_ge_gt_rel.
  - intros x y Hle Hge.
    apply isantisymm_leNonnegativeReals.
    split.
    exact Hge.
    exact Hle.
  - intros x y.
    split ; intros [H | H].
    now right.
    now left.
    now right.
    now left.
  - intros a b c ; apply plusNonnegativeReals_ltcompat_r.
  - intros a b c ; apply plusNonnegativeReals_ltcompat_l.
  - intros a b c d.
    change (b < a -> d < c -> (a * d + b * c) < (a * c + b * d)).
    intros Hab Hcd.
    rewrite (minusNonnegativeReals_plus_r (a - b) a b).
    2: now apply Dcuts_lt_le, Hab.
    2: reflexivity.
    rewrite !isrdistr_plus_multNonnegativeReals, !isassoc_plusNonnegativeReals.
    rewrite (iscomm_plusNonnegativeReals (b * d)).
    apply plusNonnegativeReals_ltcompat_l.
    apply multNonnegativeReals_ltcompat_r.
    now apply ispositive_minusNonnegativeReals.
    exact Hcd.
  - intros x.
    apply (isnonnegative_NonnegativeReals x).
  - apply NonnegativeRationals_to_NonnegativeReals_lt, ispositive_oneNonnegativeRationals.
  - intros x y.
    apply hinhpr.
    exists (minNonnegativeReals x y) ; repeat split.
    now apply minNonnegativeReals_le_l.
    now apply minNonnegativeReals_le_r.
    intros z.
    now apply minNonnegativeReals_gtcompat.
  - intros x y H.
    apply hinhpr.
    exists (minusNonnegativeReals x y) ; split.
    now apply ispositive_minusNonnegativeReals.
    rewrite iscomm_plusNonnegativeReals.
    apply minusNonnegativeReals_plus_r.
    apply Dcuts_lt_le, H.
    reflexivity.
Defined.

Definition NR_MetricSpace : MetricSet (NR := NonnegativeRig_to_NonnegativeAddMonoid NR_NonnegativeRig).
Proof.
  simple refine (tpair _ _ _).
  exact Dcuts.
  simple refine (tpair _ _ _).
  intros x y.
  apply maxNonnegativeReals.
  exact (x - y).
  exact (y - x).
  repeat split.
  - intros x y.
    apply iscomm_Dcuts_max.
  - intros [H | H].
    eapply istrans_lt_le_ltNonnegativeReals.
    apply ispositive_minusNonnegativeReals, H.
    apply Dcuts_max_le_r.
    eapply istrans_lt_le_ltNonnegativeReals.
    apply ispositive_minusNonnegativeReals, H.
    apply Dcuts_max_le_l.
  - apply hinhuniv ; intros (r,(_)).
    apply hinhuniv.
    intros [H | H].
    + right.
      apply_pr2 ispositive_minusNonnegativeReals.
      apply hinhpr.
      exists r ; split.
      apply Dcuts_zero_empty.
      exact H.
    + left.
      apply_pr2 ispositive_minusNonnegativeReals.
      apply hinhpr.
      exists r ; split.
      apply Dcuts_zero_empty.
      exact H.
  - intros x y z.
    change (maxNonnegativeReals (x - z) (z - x) <= maxNonnegativeReals (x - y) (y - x) + maxNonnegativeReals (y - z) (z - y)).
    apply Dcuts_max_le.
    + eapply istrans_leNonnegativeReals.
      2: apply plusNonnegativeReals_lecompat_r, Dcuts_max_le_l.
      eapply istrans_leNonnegativeReals.
      2: apply plusNonnegativeReals_lecompat_l, Dcuts_max_le_l.
      apply_pr2 (plusNonnegativeReals_lecompat_l z).
      rewrite isassoc_plusNonnegativeReals, !Dcuts_minus_plus_max.
      apply Dcuts_max_le.
      * eapply istrans_leNonnegativeReals.
        2: apply plusNonnegativeReals_lecompat_r, Dcuts_max_le_l.
        rewrite Dcuts_minus_plus_max.
        apply Dcuts_max_le_l.
      * eapply istrans_leNonnegativeReals.
        2: apply plusNonnegativeReals_lecompat_r, Dcuts_max_le_r.
        apply Dcuts_plus_le_r.
    + eapply istrans_leNonnegativeReals.
      2: apply plusNonnegativeReals_lecompat_r, Dcuts_max_le_r.
      eapply istrans_leNonnegativeReals.
      2: apply plusNonnegativeReals_lecompat_l, Dcuts_max_le_r.
      rewrite iscomm_plusNonnegativeReals.
      apply_pr2 (plusNonnegativeReals_lecompat_l x).
      rewrite isassoc_plusNonnegativeReals, !Dcuts_minus_plus_max.
      apply Dcuts_max_le.
      * eapply istrans_leNonnegativeReals.
        2: apply plusNonnegativeReals_lecompat_r, Dcuts_max_le_l.
        rewrite Dcuts_minus_plus_max.
        apply Dcuts_max_le_l.
      * eapply istrans_leNonnegativeReals.
        2: apply plusNonnegativeReals_lecompat_r, Dcuts_max_le_r.
        apply Dcuts_plus_le_r.
Defined.
