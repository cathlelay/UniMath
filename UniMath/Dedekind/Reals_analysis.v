(** * Analysis in real numbers *)
(** Catherine Lelay. Feb 2016 *)

Require Export UniMath.Dedekind.NonnegativeReals_analysis.
Require Export UniMath.Dedekind.Reals.
Require Import UniMath.Bourbaki.NormedSpace.
Require Import UniMath.Bourbaki.Filters.
Require Export UniMath.Dedekind.Complements.

(** ** Reals *)

Local Notation Reals := hr_ConstructiveField.

Definition hr_ap : tightap Reals :=
  hr_ap_rel,,istightap_hr_ap.

Definition hr_zero : Reals := CFzero (X := Reals).
Definition hr_one : Reals := CFone (X := Reals).

Definition hr_plus : binop Reals := CFplus.
Definition hr_opp : unop Reals := CFopp.
Definition hr_minus : binop Reals := CFminus.
Definition hr_mult : binop Reals := CFmult.
Definition hr_inv : ∀ x : Reals, (hr_ap x hr_zero) -> Reals := CFinv.
Definition hr_div : Reals -> ∀ y : Reals, (hr_ap y hr_zero) -> Reals := CFdiv (X := Reals).

Lemma israpbinop_hr_plus :
  ∀ x y z : Reals,
   hr_ap (hr_plus x y) (hr_plus x z) -> hr_ap y z.
Proof.
  simpl.
  intros x y z H.
  apply (israpbinop_plus x).
  apply H.
Qed.
Lemma islapbinop_hr_plus :
  ∀ x y z : Reals,
   hr_ap (hr_plus y x) (hr_plus z x) -> hr_ap y z.
Proof.
  simpl.
  intros x y z H.
  apply (islapbinop_plus x).
  apply H.
Qed.

Lemma isassoc_hr_plus : isassoc hr_plus.
Proof.
  intros x y z.
  apply isassoc_CFplus.
Qed.

Lemma islinv_hr_opp :
  ∀ x : Reals, (hr_plus (hr_opp x) x) = hr_zero.
Proof.
  apply islinv_CFopp.
Qed.
Lemma isrinv_hr_opp :
  ∀ x : Reals, (hr_plus x (hr_opp x)) = hr_zero.
Proof.
  apply isrinv_CFopp.
Qed.

Lemma islunit_hr_zero_plus :
  ∀ (x : Reals), (hr_plus hr_zero x) = x.
Proof.
  apply islunit_CFzero_CFplus.
Qed.
Lemma isrunit_hr_zero_plus :
  ∀ (x : Reals), (hr_plus x hr_zero) = x.
Proof.
  apply isrunit_CFzero_CFplus.
Qed.

Transparent EffectivelyOrdered_NonnegativeReals.

Lemma hr_to_NR_NR_to_hr :
  ∀ x : NonnegativeReals × NonnegativeReals, pr1 (hr_to_NR (NR_to_hr x)) = (pr1 x - pr2 x,,pr2 x - pr1 x).
Proof.
  intros x.
  destruct (hr_to_NR _) as (X,(Hx,Hle)).
  apply dirprodeq ; simpl ;
  apply isantisymm_leNonnegativeReals ;
  split.
  - apply (Hle (pr1 x - pr2 x,,pr2 x - pr1 x)).
    apply hinhpr.
    exists 0 ; simpl.
    rewrite (iscomm_plusNonnegativeReals (pr1 x)).
    now rewrite !Dcuts_minus_plus_max, iscomm_Dcuts_max.
  - revert Hx.
    apply hinhuniv.
    intros (c,Hc).
    apply plusNonnegativeReals_eqcompat_l in Hc ; clear c.
    apply_pr2 (plusNonnegativeReals_lecompat_l (pr2 x)).
    rewrite Dcuts_minus_plus_max.
    apply Dcuts_max_le.
    revert Hc.
    change ((pr1 x + pr2 X) = (pr1 X + pr2 x) ->
   pr1 x <= pr1 X + pr2 x).
    intros <-.
    apply Dcuts_plus_le_l.
    apply Dcuts_plus_le_r.
  - apply_pr2 (Hle (pr1 x - pr2 x,,pr2 x - pr1 x)).
    apply hinhpr.
    exists 0 ; simpl.
    rewrite (iscomm_plusNonnegativeReals (pr1 x)).
    now rewrite !Dcuts_minus_plus_max, iscomm_Dcuts_max.
  - revert Hx.
    apply hinhuniv.
    intros (c,Hc).
    apply plusNonnegativeReals_eqcompat_l in Hc ; clear c.
    apply_pr2 (plusNonnegativeReals_lecompat_r (pr1 x)).
    rewrite iscomm_plusNonnegativeReals, Dcuts_minus_plus_max.
    apply Dcuts_max_le.
    revert Hc.
    change ((pr1 x + pr2 X) = (pr1 X + pr2 x) ->
   pr2 x <= pr1 x + pr2 X).
    intros ->.
    apply Dcuts_plus_le_r.
    apply Dcuts_plus_le_l.
Qed.

Lemma isldistr_max_plus :
  ∀ x y z : NonnegativeReals, x + Dcuts_max y z = Dcuts_max (x + y) (x + z).
Proof.
  intros x y z.
  apply Dcuts_eq_is_eq.
  intros r ; split.
  - apply hinhuniv ; intros [ | ] ; apply hinhuniv ; [intros [Xr | ] | intros ((rx,ryz)) ; simpl ; intros (->,(Xr))].
    + apply hinhpr.
      left.
      apply hinhpr.
      left.
      apply hinhpr.
      left.
      exact Xr.
    + apply hinhfun.
      intros [Yr | Zr].
      * left.
        apply hinhpr.
        left.
        apply hinhpr.
        right.
        exact Yr.
      * right.
        apply hinhpr.
        left.
        apply hinhpr.
        right.
        exact Zr.
    + apply hinhfun.
      intros [Yr | Zr].
      * left.
        apply hinhpr.
        right.
        apply hinhpr.
        exists (rx,ryz).
        repeat split.
        exact Xr.
        exact Yr.
      * right.
        apply hinhpr.
        right.
        apply hinhpr.
        exists (rx,ryz).
        repeat split.
        exact Xr.
        exact Zr.
  - apply hinhuniv ; intros [ | ].
    + apply hinhuniv ; intros [ | ] ; apply hinhfun ; [intros [Xr | Yr] | intros ((rx,ry)) ; simpl ; intros (->,(Xr,Yr))].
      * left.
        apply hinhpr.
        left.
        exact Xr.
      * left.
        apply hinhpr.
        right.
        apply hinhpr.
        left.
        exact Yr.
      * right.
        apply hinhpr.
        exists (rx,ry) ; repeat split.
        exact Xr.
        apply hinhpr.
        left.
        exact Yr.
    + apply hinhuniv ; intros [ | ] ; apply hinhfun ; [intros [Xr | Zr] | intros ((rx,rz)) ; simpl ; intros (->,(Xr,Zr))].
      * left.
        apply hinhpr.
        left.
        exact Xr.
      * left.
        apply hinhpr.
        right.
        apply hinhpr.
        right.
        exact Zr.
      * right.
        apply hinhpr.
        exists (rx,rz) ; repeat split.
        exact Xr.
        apply hinhpr.
        right.
        exact Zr.
Qed.
Lemma isrdistr_max_plus :
  ∀ x y z : NonnegativeReals, Dcuts_max y z + x = Dcuts_max (y + x) (z + x).
Proof.
  intros x y z.
  rewrite !(iscomm_plusNonnegativeReals _ x).
  apply isldistr_max_plus.
Qed.

Lemma hr_to_NR_plus_1 :
  ∀ x y : Reals, pr1 (pr1 (hr_to_NR (hr_plus x y))) <= pr1 (pr1 (hr_to_NR x)) + pr1 (pr1 (hr_to_NR y)).
Proof.
  intros x y.
  destruct (hr_to_NR _) as (z,(Hz,Hle)).
  simpl pr1.
  refine (pr1 (Hle (pr1 (pr1 (hr_to_NR x)) + pr1 (pr1 (hr_to_NR y)) ,, pr2 (pr1 (hr_to_NR x)) + pr2 (pr1 (hr_to_NR y))) _)).
  pattern x at 1.
  rewrite <- (setquotl0 _ x (pr1 (hr_to_NR x),,pr1 (pr2 (hr_to_NR x)))).
  pattern y at 1.
  rewrite <- (setquotl0 _ y (pr1 (hr_to_NR y),,pr1 (pr2 (hr_to_NR y)))).
  apply hinhpr.
  simpl pr1 ; simpl pr2.
  exists 0.
  reflexivity.
Qed.
Lemma hr_to_NR_plus_2 :
  ∀ x y : Reals, pr2 (pr1 (hr_to_NR (hr_plus x y))) <= pr2 (pr1 (hr_to_NR x)) + pr2 (pr1 (hr_to_NR y)).
Proof.
  intros x y.
  destruct (hr_to_NR _) as (z,(Hz,Hle)).
  simpl pr1.
  refine (pr2 (Hle (pr1 (pr1 (hr_to_NR x)) + pr1 (pr1 (hr_to_NR y)) ,, pr2 (pr1 (hr_to_NR x)) + pr2 (pr1 (hr_to_NR y))) _)).
  pattern x at 1.
  rewrite <- (setquotl0 _ x (pr1 (hr_to_NR x),,pr1 (pr2 (hr_to_NR x)))).
  pattern y at 1.
  rewrite <- (setquotl0 _ y (pr1 (hr_to_NR y),,pr1 (pr2 (hr_to_NR y)))).
  apply hinhpr.
  simpl pr1 ; simpl pr2.
  exists 0.
  reflexivity.
Qed.

(** ** NonnegativeReals is an absrng *)

Unset Printing Notations.

Definition R_absrng : absrng (NR := NR_NonnegativeRig).
Proof.
  exists Reals.
  exists hr_ap.
  exists hr_abs.
  split ; [ split | repeat split].
  - intros a b c H.
    change (hr_ap (hr_plus c a) (hr_plus c b)).
    apply (israpbinop_hr_plus (hr_opp c)).
    rewrite <- !isassoc_hr_plus.
    rewrite islinv_hr_opp.
    rewrite !islunit_hr_zero_plus.
    exact H.
  - intros a b c H.
    change (hr_ap (hr_plus a c) (hr_plus b c)).
    apply (islapbinop_hr_plus (hr_opp c)).
    rewrite !isassoc_hr_plus.
    rewrite isrinv_hr_opp.
    rewrite !isrunit_hr_zero_plus.
    exact H.
  - intros H.
    change (0 < hr_abs x).
    destruct (pr1 (hr_NR_ap_0 x (pr1 (hr_to_NR x)) (pr1 (pr2 (hr_to_NR x)))) H) as [H0 | H0] ;
    apply ispositive_apNonnegativeReals in H0 ;
    eapply istrans_lt_le_ltNonnegativeReals.
    apply H0.
    unfold hr_abs.
    eapply istrans_leNonnegativeReals, Dcuts_max_le_r.
    apply Dcuts_minus_le.
    apply H0.
    unfold hr_abs.
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
    unfold hr_abs.
    change (@rngunel2 hr_ConstructiveField) with hr_one.
    change hr_one with (NR_to_hr (1,,0)).
    rewrite hr_to_NR_NR_to_hr ; simpl pr1 ; simpl pr2.
    rewrite <- (Dcuts_minus_correct_l _ _ 1).
    rewrite Dcuts_minus_eq_zero.
    rewrite Dcuts_max_carac_l.
    reflexivity.
    apply isnonnegative_NonnegativeReals.
    apply isnonnegative_NonnegativeReals.
    apply pathsinv0, islunit_zero_plusNonnegativeReals.
  - intros x y.
    apply Dcuts_max_le.
    + unfold hr_abs.
      rewrite isldistr_max_plus, !isrdistr_max_plus.
      eapply istrans_leNonnegativeReals, Dcuts_max_le_l.
      eapply istrans_leNonnegativeReals, Dcuts_max_le_l.
      apply hr_to_NR_plus_1.

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