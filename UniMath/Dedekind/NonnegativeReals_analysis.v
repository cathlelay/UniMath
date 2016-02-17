(** * Analysis in nonnegative real numbers *)
(** Catherine Lelay. Feb 2016 *)

Require Export UniMath.Dedekind.NonnegativeReals.
Require Export UniMath.Dedekind.NonnegativeRationals.
Require Import UniMath.Bourbaki.MetricSpace.
Require Import UniMath.Bourbaki.NormedSpace.
Require Import UniMath.Bourbaki.Filters.
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

Definition ball (x eps y : NonnegativeReals) :=
  x < y + eps ∧ y < x + eps.

Lemma ball_correct :
  ∀ x eps y : NonnegativeReals,
    0 < eps ->
    (ball x eps y <-> MetricSpace.ball (M := NR_MetricSpace) x eps y).
Proof.
  intros x eps y.
  split.
  - intros (Hxy,Hyx).
    apply Dcuts_max_lt.
    + apply_pr2 (plusNonnegativeReals_ltcompat_l y).
      rewrite Dcuts_minus_plus_max, iscomm_plusNonnegativeReals.
      apply Dcuts_max_lt.
      exact Hxy.
      now apply plusNonnegativeReals_lt_r.
    + apply_pr2 (plusNonnegativeReals_ltcompat_l x).
      rewrite Dcuts_minus_plus_max, iscomm_plusNonnegativeReals.
      apply Dcuts_max_lt.
      exact Hyx.
      now apply plusNonnegativeReals_lt_r.
  - intros Hxy.
    split.
    + eapply istrans_le_lt_ltNonnegativeReals, plusNonnegativeReals_ltcompat_r, Hxy.
      eapply istrans_leNonnegativeReals, plusNonnegativeReals_lecompat_r, Dcuts_max_le_l.
      rewrite iscomm_plusNonnegativeReals, Dcuts_minus_plus_max.
      now apply Dcuts_max_le_l.
    + eapply istrans_le_lt_ltNonnegativeReals, plusNonnegativeReals_ltcompat_r, Hxy.
      eapply istrans_leNonnegativeReals, plusNonnegativeReals_lecompat_r, Dcuts_max_le_r.
      rewrite iscomm_plusNonnegativeReals, Dcuts_minus_plus_max.
      apply Dcuts_max_le_l.
Qed.

Definition base_of_neighborhood_ball (x : NonnegativeReals) : Topology.base_of_neighborhood (T := metric_topology (M := NR_MetricSpace)) x.
Proof.
  intros x.
  generalize (is_base_of_neighborhood_ball (M := NR_MetricSpace) x) ; intro is.
  simple refine (tpair _ _ _).
  intros A.
  apply (∃ eps : NonnegativeReals, 0 < eps × ∀ y : NonnegativeReals, A y <-> ball x eps y).
  split.
  - intros P HP.
    apply (pr1 is).
    revert HP.
    apply hinhfun.
    intros (e,(He,HP)).
    exists (e,,He).
    apply funextfun ; intros y.
    apply uahp.
    + intros Py.
      apply ball_correct.
      exact He.
      now apply HP.
    + intros H.
      apply_pr2 HP.
      apply_pr2 ball_correct.
      exact He.
      exact H.
  - intros P HP.
    generalize (pr2 is P HP).
    apply hinhfun.
    intros (Q,(HQ,H)).
    exists Q.
    split.
    + revert HQ.
      apply hinhfun.
      intros ((e,He),->).
      exists e.
      split.
      exact He.
      split.
      apply_pr2 ball_correct.
      exact He.
      apply ball_correct.
      exact He.
    + apply H.
Defined.
Definition locally (x : NonnegativeReals) : Filter (X := NonnegativeReals).
Proof.
  intros x.
  simple refine (Topology.locally_base (T := metric_topology (M := NR_MetricSpace)) _ _).
  apply x.
  apply base_of_neighborhood_ball.
Defined.

Definition is_filter_lim (F : Filter (X := NonnegativeReals)) (x : NonnegativeReals) :=
  Topology.is_filter_lim_base (T := metric_topology (M := NR_MetricSpace)) F x (base_of_neighborhood_ball x).

Definition is_lim {X : UU} (f : X -> NonnegativeReals) (F : Filter) (x : NonnegativeReals) :=
  Topology.is_lim_base (T := metric_topology (M := NR_MetricSpace)) f F x (base_of_neighborhood_ball x).

Lemma is_lim_aux {X : UU} (f : X -> NonnegativeReals) (F : Filter) (x : NonnegativeReals) :
  is_lim f F x <->
  (∀ eps : NonnegativeReals, 0 < eps -> F (λ y : X, ball x eps (f y))).
Proof.
  intros X f F x.
  generalize (is_lim_aux (M := NR_MetricSpace) f F x).
  intro H.
  split.
  - intros Hf e He.
    eapply filter_imply.
    intros y Hy.
    refine (pr2 (ball_correct _ _ _ _) _).
    exact He.
    apply Hy.
    refine (pr1 H _ (e,,He)).
    apply (pr2 (Topology.is_lim_base_correct _ _ _ _)).
    eapply (pr1 (Topology.is_lim_base_correct _ _ _ _)).
    apply Hf.
  - intros Hf.
    refine (pr2 (Topology.is_lim_base_correct _ _ _ _) _).
    eapply (pr1 (Topology.is_lim_base_correct _ _ _ _)).
    apply (pr2 H).
    intros (e,He).
    eapply filter_imply.
    intros y Hy.
    refine (pr1 (ball_correct _ _ _ _) _).
    exact He.
    apply Hy.
    apply Hf.
    exact He.
Qed.

Lemma is_lim_unique_aux {X : UU} (f : X -> NonnegativeReals) (F : Filter) (l l' : NonnegativeReals) :
  is_lim f F l -> is_lim f F l' -> l < l' -> empty.
Proof.
  intros X f F l l' Hl Hl' Hlt.
  assert (Hlt0 : 0 < l' - l).
  { now apply ispositive_minusNonnegativeReals. }
  assert (Hlt0' : 0 < (l' - l) / 2).
  { now apply ispositive_Dcuts_half. }
  apply (filter_notempty F).
  generalize (filter_and _ _ _ (pr1 (is_lim_aux _ _ _) Hl _ Hlt0') (pr1 (is_lim_aux _ _ _) Hl' _ Hlt0')).
  apply filter_imply.
  unfold ball.
  intros x ((_,H),(H0,_)).
  apply (isirrefl_Dcuts_gt_rel ((l + l') / 2)).
  apply istrans_Dcuts_gt_rel with (f x).
  - rewrite (minusNonnegativeReals_plus_r (l' - l) l' l), (iscomm_plusNonnegativeReals _ l), <- isassoc_plusNonnegativeReals, !isdistr_Dcuts_half_plus, <-double_Dcuts_half.
    exact H.
    now apply Dcuts_lt_le.
    reflexivity.
  - apply_pr2 (plusNonnegativeReals_ltcompat_l ((l' - l) / 2)).
    rewrite <- isdistr_Dcuts_half_plus.
    rewrite (iscomm_plusNonnegativeReals l), isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals l).
    rewrite <- (minusNonnegativeReals_plus_r (l' - l) l' l), isdistr_Dcuts_half_plus, <- double_Dcuts_half.
    exact H0.
    now apply Dcuts_lt_le.
    reflexivity.
Qed.

Lemma is_lim_unique {X : UU} (f : X -> NonnegativeReals) (F : Filter) (l l' : NonnegativeReals) :
  is_lim f F l -> is_lim f F l' -> l = l'.
Proof.
  intros X f F l l' Hl Hl'.
  apply istight_apNonnegativeReals.
  intros [ | ].
  - now apply (is_lim_unique_aux f F).
  - now apply (is_lim_unique_aux f F).
Qed.

Lemma isaprop_ex_lim {X : UU} :
  ∀ (f : X -> NonnegativeReals) (F : Filter), isaprop (Σ l : NonnegativeReals, is_lim f F l).
Proof.
  intros X f F.
  apply isaproptotal2'.
  apply pr2.
  intros l.
  apply impred_isaprop ; intro P.
  apply isapropimpl.
  apply pr2.
  apply is_lim_unique.
Qed.
Definition ex_lim {X : UU} (f : X -> NonnegativeReals) (F : Filter) : hProp
  := hProppair (Σ l : NonnegativeReals, is_lim f F l) (isaprop_ex_lim f F).
Definition Lim_seq {X : UU} (f : X -> NonnegativeReals) (F : Filter) (Lu : ex_lim f F) : NonnegativeReals
  := pr1 Lu.

Lemma is_lim_seq_equiv :
  ∀ (f : nat -> NonnegativeReals) (l : NonnegativeReals),
    is_lim f filter_nat l <-> is_lim_seq f l.
Proof.
  intros f l.
  split.
  - intros H e He.
    generalize (pr1 (is_lim_aux _ _ _) H e He).
    apply hinhfun.
    intros (N,Hf).
    exists N.
    intros n Hn.
    split.
    now apply_pr2 Hf.
    now apply Hf.
  - intros H.
    apply (pr2 (is_lim_aux _ _ _)).
    intros e He.
    generalize (H e He).
    apply hinhfun.
    intros (N,Hf).
    exists N.
    intros n Hn.
    split.
    now apply_pr2 Hf.
    now apply Hf.
Qed.