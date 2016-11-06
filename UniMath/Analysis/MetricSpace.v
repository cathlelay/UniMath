(** * Results about Metric Spaces *)
(** Author: Catherine LELAY. Jan 2016 - *)

Require Export UniMath.Foundations.Algebra.Lattice.
Require Import UniMath.Topology.Prelim.
Require Export UniMath.Topology.Filters.
Require Import UniMath.Topology.Topology.
Require Import UniMath.Topology.UniformSpace.
Require Import UniMath.RealNumbers.Sets.
Require Import UniMath.Foundations.Algebra.Apartness.

Set Default Timeout 10.

(** ** Lattice *)

Definition apfromlt {X : hSet} (lt : StrongOrder X) : aprel X.
Proof.
  intros X lt.
  mkpair.
  - intros x y.
    simple refine (hProppair _ _).
    apply (coprod (lt x y) (lt y x)).
    apply isapropcoprod.
    apply propproperty.
    apply propproperty.
    intros Hxy Hyx.
    apply (isirrefl_StrongOrder lt x).
    now apply (istrans_StrongOrder lt _ y).
  - repeat split.
    + intros x H ; revert H ; apply sumofmaps ;
      apply isirrefl_StrongOrder.
    + intros x y ; apply sumofmaps ; [intros Hxy | intros Hyx].
      now right.
      now left.
    + intros x y z ; apply sumofmaps ; intros H ;
      generalize (iscotrans_StrongOrder lt _ y _ H) ;
      apply hinhfun ; apply sumofmaps ;
      intros H'.
      now left ; left.
      now right ; left.
      now right ; right.
      now left ; right.
Defined.

Definition tightapfromlt {X : hSet} (lt : StrongOrder X) (le : hrel X)
           (Hnltle : Π x y, (¬ lt x y) <-> le y x) (Hle : isantisymm le) : tightap X.
Proof.
  intros X lt le Hnltle Hle.
  refine (tpair _ _ _).
  split.
  apply (pr2 (apfromlt lt)).
  intros x y Hlt.
  apply Hle ; apply (pr1 (Hnltle _ _)) ; intro H ; apply Hlt.
  now right.
  now left.
Defined.

Open Scope addmonoid_scope.

Section truncminus_lt.

Context {X : abmonoid}
        {is : islatticewithlt X}
        (Hlt : isbinophrel (Llt is))
        (Hlt' : isinvbinophrel (Llt is))
        (minus : binop X)
        (is0 : istruncminus is minus).

Lemma truncminus_pos :
  Π x y : X, Llt is 0 (minus x y) -> Llt is y x.
Proof.
  intros x y H0.
  apply (pr2 Hlt _ _ y) in H0.
  rewrite lunax, is0 in H0.
  rewrite <- (Lmax_eq_l is x y).
  exact H0.
  apply notLlt_Lle.
  intros H ; revert H0.
  apply (pr2 (notLlt_Lle _ _ _)).
  rewrite Lmax_eq_r.
  apply isrefl_Lle.
  now apply Llt_Lle.
Qed.
Lemma minus_lt_pos :
  Π x y : X, Llt is y x -> Llt is 0 (minus x y).
Proof.
  intros x y H0.
  apply (pr2 Hlt' _ _ y).
  rewrite lunax, is0.
  rewrite (Lmax_eq_l _ x y).
  exact H0.
  now apply Llt_Lle.
Qed.

End truncminus_lt.

(** ** Nonnegative Monoid *)

Definition isNonnegativeMonoid {X : abmonoid} (is : islatticewithlt X) :=
  (extruncminus is)
    × isbinophrel (Llt is)
    × isinvbinophrel (Llt is)
    × (Π x : X, Lle is 0 x)
    × (∃ x0, Llt is 0 x0)
    × (Π x y : X, Llt is x y → ∃ z : X, Llt is x z × Llt is z y).

Definition NonnegativeMonoid :=
  Σ (X : abmonoid) (is : islatticewithlt X), isNonnegativeMonoid is.

Definition pr1NonnegativeMonoid : NonnegativeMonoid -> abmonoid := pr1.
Coercion pr1NonnegativeMonoid : NonnegativeMonoid >-> abmonoid.


Section NnM_pr.

Context (X : NonnegativeMonoid).

Definition islatticewithlt_NonnegativeMonoid : islatticewithlt X :=
  pr1 (pr2 X).
Definition NnMlt : StrongOrder X :=
  Llt islatticewithlt_NonnegativeMonoid.
Definition NnMle : PartialOrder X.
Proof.
  mkpair.
  apply (Lle islatticewithlt_NonnegativeMonoid).
  repeat split.
  - apply istrans_Lle.
  - apply isrefl_Lle.
  - apply isantisymm_Lle.
Defined.
Definition NnMap : tightap X.
Proof.
  simple refine (tightapfromlt _ _ _ _).
  - apply NnMlt.
  - apply (pr1 NnMle).
  - apply (pr2 (pr2 (pr1 (pr2 X)))).
  - apply isantisymm_Lle.
Defined.

End NnM_pr.

Local Notation "0" := (0%addmonoid).
Local Notation "x + y" := ((x + y)%addmonoid).
Local Notation "x ≠ y" := (NnMap _ x y).
Local Notation "x < y" :=  (NnMlt _ x y).
Local Notation "x <= y" :=  (NnMle _ x y).

Section NnM_pty.

Context {X : NonnegativeMonoid}.

Definition NnMmin : binop X := Lmin (islatticewithlt_NonnegativeMonoid X).
Definition NnMmax : binop X := Lmax (islatticewithlt_NonnegativeMonoid X).
Definition NnMminus : binop X := (pr1 (pr1 (pr2 (pr2 X)))).

Local Notation "x - y" := (NnMminus x y).

Lemma istight_NnMap : istight (NnMap X).
Proof.
  exact (pr2 (pr2 (NnMap X))).
Qed.
Lemma isirrefl_NnMap : isirrefl (NnMap X).
Proof.
  exact (pr1 (pr1 (pr2 (NnMap X)))).
Qed.
Lemma istotal_NnMlt :
  Π x y : X, x ≠ y <-> (x < y) ⨿ (y < x).
Proof.
  easy.
Qed.

Lemma notNnMlt_le :
  Π x y : X, (¬ (x < y)) <-> (y <= x).
Proof.
  apply notLlt_Lle.
Qed.
Lemma isirrefl_NnMlt :
  Π x : X, ¬ (x < x).
Proof.
  apply isirrefl_StrongOrder.
Qed.
Lemma istrans_NnMlt :
  Π x y z : X, x < y -> y < z -> x < z.
Proof.
  apply istrans_StrongOrder.
Qed.
Lemma iscotrans_NnMlt :
  Π x y z : X, x < z -> x < y ∨ y < z.
Proof.
  apply iscotrans_StrongOrder.
Qed.

Lemma NnMlt_le :
  Π x y : X, x < y -> x <= y.
Proof.
  apply Llt_Lle.
Qed.

Lemma isrefl_NnMle :
  Π x : X, (x <= x).
Proof.
  apply isrefl_Lle.
Qed.

Lemma istrans_NnMlt_le :
  Π x y z : X, x < y -> y <= z -> x < z.
Proof.
  intros x y z Hxy Hyz.
  generalize (iscotrans_NnMlt x z y Hxy).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  exact H.
  now apply (pr2 (notNnMlt_le _ _)) in Hyz.
Qed.

Lemma istrans_NnMle_lt :
  Π x y z : X, x <= y -> y < z -> x < z.
Proof.
  intros x y z Hxy Hyz.
  generalize (iscotrans_NnMlt y x z Hyz).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  now apply (pr2 (notNnMlt_le _ _)) in Hxy.
  exact H.
Qed.

Lemma isnonnegative_NnM :
  Π x : X, 0 <= x.
Proof.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
Qed.
Lemma isnonnegative_NnM' :
  Π x : X, ¬ (x < 0).
Proof.
  intros x.
  apply (pr2 (notNnMlt_le _ _)).
  now apply isnonnegative_NnM.
Qed.

Lemma NnMplus_lt_l :
  Π k x y : X, x < y -> k + x < k + y.
Proof.
  intros k x y.
  apply (pr1 (pr1 (pr2 (pr2 (pr2 X))))).
Qed.
Lemma NnMplus_lt_r :
  Π k x y : X, x < y -> x + k < y + k.
Proof.
  intros k x y.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 X))))).
Qed.

Lemma NnMap_lt_0 :
  Π x : X, x ≠ 0 -> 0 < x.
Proof.
  intros x Hx.
  apply istotal_NnMlt in Hx.
  induction Hx as [Hx | Hx].
  apply fromempty.
  revert Hx.
  now apply isnonnegative_NnM'.
  exact Hx.
Qed.
Lemma NnMlt_ap :
  Π x y : X, x < y -> x ≠ y.
Proof.
  intros x y H.
  apply (pr2 (istotal_NnMlt _ _)).
  now left.
Qed.

Lemma NnM_nottrivial :
  ∃ x0 : X, 0 < x0.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.

Lemma NnMmin_le_l :
  Π x y : X, NnMmin x y <= x.
Proof.
  apply Lmin_le_l.
Qed.
Lemma NnMmin_le_r :
  Π x y : X, NnMmin x y <= y.
Proof.
  apply Lmin_le_r.
Qed.
Lemma NnMmin_gt :
  Π x y z : X, z < x -> z < y -> z < NnMmin x y.
Proof.
  apply Lmin_Llt.
Qed.

Lemma NnMmax_ge_l  :
  Π x y : X, x <= NnMmax x y.
Proof.
  apply Lmax_ge_l.
Qed.
Lemma NnMmax_ge_r  :
  Π x y : X, y <= NnMmax x y.
Proof.
  apply Lmax_ge_r.
Qed.
Lemma NnMmax_lt :
  Π x y z : X, x < z -> y < z -> NnMmax x y < z.
Proof.
  apply Lmax_lt.
Qed.

Lemma iscomm_NnMmin :
  iscomm NnMmin.
Proof.
  apply iscomm_Lmin.
Qed.
Lemma isassoc_NnMmin :
  isassoc NnMmin.
Proof.
  apply isassoc_Lmin.
Qed.

Lemma iscomm_NnMmax :
  iscomm NnMmax.
Proof.
  apply iscomm_Lmax.
Qed.
Lemma isassoc_NnMmax :
  isassoc NnMmax.
Proof.
  apply isassoc_Lmax.
Qed.

Lemma NnMmin_eq_l :
  Π (x y : X), x <= y → NnMmin x y = x.
Proof.
  apply Lmin_eq_l.
Qed.
Lemma NnMmin_eq_r :
  Π (x y : X), y <= x → NnMmin x y = y.
Proof.
  apply Lmin_eq_r.
Qed.
Lemma NnMmax_eq_l :
  Π (x y : X), y <= x → NnMmax x y = x.
Proof.
  apply Lmax_eq_l.
Qed.
Lemma NnMmax_eq_r :
  Π (x y : X), x <= y → NnMmax x y = y.
Proof.
  apply Lmax_eq_r.
Qed.

Lemma NnMminus_plus :
  Π x y : X, (x - y) + y = NnMmax x y.
Proof.
  exact (pr2 (pr1 (pr2 (pr2 X)))).
Qed.

Lemma NnMminus_lt_pos :
  Π x y : X, y < x -> 0 < NnMminus x y.
Proof.
  apply minus_lt_pos.
  apply (pr1 (pr2 (pr2 (pr2 (pr2  X))))).
  exact NnMminus_plus.
Qed.

Lemma NnM_dense :
  Π x y : X, x < y → ∃ z : X, x < z × z < y.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.
Lemma NnM_cut :
  Π x : X, 0 < x → ∃ y z : X, x = y + z × 0 < y × 0 < z.
Proof.
  intros x Hx.
  generalize (NnM_dense _ _ Hx).
  apply hinhfun.
  intros z.
  exists (x - pr1 z), (pr1 z).
  repeat split.
  - rewrite NnMminus_plus.
    apply pathsinv0, NnMmax_eq_l.
    apply NnMlt_le, (pr2 (pr2 z)).
  - apply NnMminus_lt_pos, (pr2 (pr2 z)).
  - apply (pr1 (pr2 z)).
Qed.

End NnM_pty.

(** ** Definition of metric spaces *)

Section MetricSet.

Context {NR : NonnegativeMonoid}.
Context {X : tightapSet}.
Context (dist : X -> X -> NR).

Definition issymm_isdist : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (Π x y : X, dist x y = dist y x).
  apply impred_isaprop ; intro x.
  apply impred_isaprop ; intro y.
  apply (pr2 (pr1 (pr1 (pr1 NR)))).
Defined.

Definition issepp_isdist : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (Π x y : X, (x ≠ y)%tap <-> (0 < (dist x y))).
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply isapropdirprod.
  apply isapropimpl.
  apply propproperty.
  apply isapropimpl.
  apply propproperty.
Defined.

Definition istriangle_isdist : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (Π x y z : X,  (dist x z) <= (dist x y + dist y z)%addmonoid).
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply impred_isaprop ; intros z.
  apply propproperty.
Defined.

End MetricSet.

Definition isdist {NR : NonnegativeMonoid} {X : tightapSet} (dist : X -> X -> NR) : hProp :=
  issymm_isdist dist ∧ issepp_isdist dist ∧ istriangle_isdist dist.

Definition MetricSet (NR : NonnegativeMonoid) :=
  Σ (X : tightapSet) (dist : X -> X -> NR), isdist dist.

Definition pr1MetricSet {NR : NonnegativeMonoid} : MetricSet NR -> tightapSet := pr1.
Coercion pr1MetricSet : MetricSet >-> tightapSet.

Definition dist {NR : NonnegativeMonoid} {X : MetricSet NR} : (X -> X -> NR) := pr1 (pr2 X).

Lemma issymm_dist {NR : NonnegativeMonoid} {X : MetricSet NR} :
  Π x y : X, dist x y = dist y x.
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 X))).
Qed.
Lemma issepp_dist {NR : NonnegativeMonoid} {X : MetricSet NR} :
  Π x y : X, (x ≠ y)%tap <-> (0 < (dist x y)).
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 (pr2 X)))).
Qed.
Lemma istriangle_dist {NR : NonnegativeMonoid} {X : MetricSet NR} :
  Π x y z : X, (dist x z) <= (dist x y + dist y z).
Proof.
  intros.
  now apply (pr2 (pr2 (pr2 (pr2 X)))).
Qed.

Lemma dist_0 {NR : NonnegativeMonoid} {X : MetricSet NR} :
  Π x : X, dist x x = 0.
Proof.
  intros.
  apply istight_NnMap.
  intro H.
  apply NnMap_lt_0, (pr2 (issepp_dist _ _)) in H.
  revert H.
  apply isirrefltightapSet.
Qed.

(** ** Topology on metric spaces *)

Section Balls.

Context {NR : NonnegativeMonoid}.
Context {M : MetricSet NR}.

Definition ball (x : M) (eps : NR) (y : M) : hProp :=
  (dist x y < eps).

Lemma ball_center :
  Π (x : M) (eps : NR), 0 < eps -> ball x eps x.
Proof.
  intros x eps He.
  unfold ball.
  now rewrite dist_0.
Qed.
Lemma ball_le :
  Π x e e' y, e <= e' -> ball x e y -> ball x e' y.
Proof.
  intros x e e' y H H'.
  refine (istrans_NnMlt_le _ _ _ _ _).
  apply H'.
  apply H.
Qed.
Lemma ball_recenter :
  Π (x y : M) (eps : NR), ball y eps x -> Σ eps' : NR, 0 < eps' × Π z : M, ball x eps' z -> ball y eps z.
Proof.
  intros x y eps Hy.
  exists (NnMminus eps (dist y x)).
  split.
  apply NnMminus_lt_pos, Hy.
  intros z Hz.
  unfold ball.
  eapply istrans_NnMle_lt, istrans_NnMlt_le.
  rewrite issymm_dist.
  eapply istriangle_dist.
  apply NnMplus_lt_r.
  rewrite issymm_dist.
  apply Hz.
  rewrite issymm_dist.
  rewrite NnMminus_plus.
  rewrite NnMmax_eq_l.
  apply isrefl_Lle.
  rewrite issymm_dist.
  apply NnMlt_le, Hy.
Qed.

Lemma ball_symm :
  Π (x y : M) (eps : NR), ball x eps y -> ball y eps x.
Proof.
  intros x y eps.
  unfold ball.
  now rewrite issymm_dist.
Qed.

Definition metricUniformStructure : UniformStructure M.
Proof.
  simple refine (mkUniformStructure _ _ _ _ _ _ _).
  - intros A.
    apply (∃ e : NR, 0 < e × Π x y : M, ball x e y -> A (x,,y)).
  - intros A B H.
    apply hinhfun.
    intros e.
    exists (pr1 e) ; split.
    exact (pr1 (pr2 e)).
    intros x y Hxy.
    now apply H, (pr2 (pr2 e)).
  - generalize (NnM_nottrivial (X := NR)).
    apply hinhfun.
    intros e.
    now exists (pr1 e), (pr2 e).
  - intros A B.
    apply hinhfun2.
    intros ea eb.
    exists (NnMmin (pr1 ea) (pr1 eb)).
    split.
    apply NnMmin_gt.
    exact (pr1 (pr2 ea)).
    exact (pr1 (pr2 eb)).
    intros x y He.
    split.
    apply (pr2 (pr2 ea)).
    eapply istrans_NnMlt_le, NnMmin_le_l.
    exact He.
    apply (pr2 (pr2 eb)).
    eapply istrans_NnMlt_le, NnMmin_le_r.
    exact He.
  - intros A Ha x.
    revert Ha.
    apply hinhuniv.
    intros e.
    apply (pr2 (pr2 e)).
    apply ball_center.
    exact (pr1 (pr2 e)).
  - intros A.
    apply hinhfun.
    intros e.
    exists (pr1 e) ; split.
    exact (pr1 (pr2 e)).
    intros x y H.
    apply (pr2 (pr2 e)).
    now apply ball_symm.
  - intros A.
    apply hinhuniv.
    intros e.
    generalize (NnM_cut (pr1 e) (pr1 (pr2 e))).
    apply hinhfun.
    intros e'.
    mkpair.
    intros x.
    apply (ball (pr1 x) (NnMmin (pr1 e') (pr1 (pr2 e'))) (pr2 x)).
    split.
    apply hinhpr.
    exists (NnMmin (pr1 e') (pr1 (pr2 e'))).
    split.
    apply NnMmin_gt.
    apply (pr1 (pr2 (pr2 (pr2 e')))).
    apply (pr2 (pr2 (pr2 (pr2 e')))).
    easy.
    intros xy.
    apply hinhuniv.
    intros z.
    rewrite (tppr xy) ; apply (pr2 (pr2 e)).
    eapply istrans_NnMle_lt, istrans_NnMlt_le.
    eapply istriangle_dist.
    eapply istrans_NnMlt.
    apply NnMplus_lt_l.
    eapply istrans_NnMlt_le.
    apply (pr2 (pr2 z)).
    apply NnMmin_le_r.
    apply NnMplus_lt_r.
    eapply istrans_NnMlt_le.
    apply (pr1 (pr2 z)).
    apply NnMmin_le_l.
    rewrite <- (pr1 (pr2 (pr2 e'))).
    apply isrefl_NnMle.
Defined.

End Balls.

(** ** Limits in a Metric Space *)

Section MSlocally.

Context {NR : NonnegativeMonoid} {M : MetricSet NR}.

Definition MSneighborhood (x : M) (A : M -> hProp) :=
  ∃ e : NR, 0 < e × Π y, ball x e y -> A y.

Lemma MSneighborhood_equiv :
  Π x A, USneighborhood metricUniformStructure x A <-> MSneighborhood x A.
Proof.
  split.
  - apply hinhuniv ; intros U.
    generalize (pr1 (pr2 U)).
    apply hinhfun.
    intros e.
    exists (pr1 e) ; split.
    exact (pr1 (pr2 e)).
    intros y Hy.
    apply (pr2 (pr2 U)), (pr2 (pr2 e)), Hy.
  - apply hinhfun.
    intros e.
    exists (λ z, ball (pr1 z) (pr1 e) (pr2 z)).
    split.
    apply hinhpr.
    now exists (pr1 e), (pr1 (pr2 e)).
    apply (pr2 (pr2 e)).
Qed.

Lemma MSneighborhood_imply :
  Π x : M, isfilter_imply (MSneighborhood x).
Proof.
  intros x A B H Ha.
  apply MSneighborhood_equiv.
  apply USneighborhood_imply with (1 := H).
  apply_pr2 MSneighborhood_equiv.
  exact Ha.
Qed.

Lemma MSneighborhood_htrue :
  Π x : M, isfilter_htrue (MSneighborhood x).
Proof.
  intros x.
  apply MSneighborhood_equiv.
  apply USneighborhood_htrue.
Qed.
Lemma MSneighborhood_and :
  Π x : M, isfilter_and (MSneighborhood x).
Proof.
  intros x A B Ha Hb.
  apply MSneighborhood_equiv.
  apply USneighborhood_and.
  apply_pr2 MSneighborhood_equiv.
  exact Ha.
  apply_pr2 MSneighborhood_equiv.
  exact Hb.
Qed.
Lemma MSneighborhood_point :
  Π (x : M) (P : M → hProp), MSneighborhood x P → P x.
Proof.
  intros x P Hp.
  simple refine (USneighborhood_point _ _ _ _).
  apply metricUniformStructure.
  apply_pr2 MSneighborhood_equiv.
  exact Hp.
Qed.
Lemma MSneighborhood_neighborhood :
  Π (x : M) (P : M → hProp),
    MSneighborhood x P
    → ∃ Q : M → hProp, MSneighborhood x Q × (Π y : M, Q y → MSneighborhood y P).
Proof.
  intros x P Hp.
  apply_pr2_in MSneighborhood_equiv Hp.
  generalize (USneighborhood_neighborhood _ _ _ Hp).
  apply hinhfun.
  intros Q.
  exists (pr1 Q).
  split.
  apply MSneighborhood_equiv.
  exact (pr1 (pr2 Q)).
  intros y Hy.
  apply MSneighborhood_equiv.
  apply (pr2 (pr2 Q)), Hy.
Qed.

Lemma isNeighborhood_MSneighborhood :
  isNeighborhood MSneighborhood.
Proof.
  repeat split.
  - exact MSneighborhood_imply.
  - exact MSneighborhood_htrue.
  - exact MSneighborhood_and.
  - exact MSneighborhood_point.
  - exact MSneighborhood_neighborhood.
Qed.

End MSlocally.

Definition MSlocally {NR : NonnegativeMonoid} {M : MetricSet NR} (x : M) : Filter M.
Proof.
  intros NR M x.
  exists (MSneighborhood x).
  revert x.
  apply isNeighborhood_isFilter.
  apply isNeighborhood_MSneighborhood.
Defined.

Lemma MSlocally_ball {NR : NonnegativeMonoid} {M : MetricSet NR} (x : M) :
  Π e : NR, 0 < e -> MSlocally x (ball x e).
Proof.
  intros NR M x e He.
  apply hinhpr.
  now exists e.
Qed.

Definition MSlocally2d {NR : NonnegativeMonoid} {X Y : MetricSet NR} (x : X) (y : Y) :=
  FilterDirprod (MSlocally x) (MSlocally y).

(** *** Limit of a filter *)

Definition is_filter_MSlim {NR : NonnegativeMonoid} {M : MetricSet NR} (F : Filter M) (x : M) :=
  filter_le F (MSlocally x).
Definition ex_filter_MSlim {NR : NonnegativeMonoid} {M : MetricSet NR} (F : Filter M) :=
  ∃ (x : M), is_filter_MSlim F x.

(** *** Limit of a function *)

Definition is_MSlim {X : UU} {NR : NonnegativeMonoid} {M : MetricSet NR} (f : X -> M) (F : Filter X) (x : M) :=
  filterlim f F (MSlocally x).
Definition ex_MSlim {X : UU} {NR : NonnegativeMonoid} {M : MetricSet NR} (f : X -> M) (F : Filter X) :=
  ∃ (x : M), is_MSlim f F x.

Lemma is_MSlim_correct :
  Π {X : UU} {NR : NonnegativeMonoid} {M : MetricSet NR} (f : X -> M) (F : Filter X) (x : M),
    is_USlim (Y := _ ,, metricUniformStructure (M := M)) f F x <-> is_MSlim f F x.
Proof.
  split ; intros H P Hp.
  - apply H ; revert Hp.
    refine (pr2 (MSneighborhood_equiv _ _)).
  - apply H ; revert Hp.
    refine (pr1 (MSneighborhood_equiv _ _)).
Qed.

Lemma is_MSlim_aux {X : UU} {NR : NonnegativeMonoid} {M : MetricSet NR} (f : X -> M) (F : Filter X) (x : M) :
  is_MSlim f F x <->
  (Π eps : NR, 0 < eps -> F (λ y, ball x eps (f y))).
Proof.
  intros X NR M f F x.
  split.
  - intros H e He.
    apply H.
    apply MSlocally_ball, He.
  - intros H P.
    apply hinhuniv.
    intros e.
    eapply (Filter_imply F).
    intros y Hy.
    apply (pr2 (pr2 e)).
    apply Hy.
    apply H, (pr1 (pr2 e)).
Qed.

(** *** Continuity *)

Definition MScontinuous_at {NR : NonnegativeMonoid} {U V : MetricSet NR} (f : U -> V) (x : U) :=
  is_MSlim f (MSlocally x) (f x).
Definition MScontinuous_on {NR : NonnegativeMonoid} {U V : MetricSet NR} (dom : U -> hProp) (f : Π (x : U), dom x -> V) :=
  Π (x : U) (Hx : dom x),
  ∃ H,
  is_MSlim (λ y, f (pr1 y) (pr2 y))
  (FilterSubtype (MSlocally x) dom H) (f x Hx).
Definition MScontinuous {NR : NonnegativeMonoid} {U V : MetricSet NR} (f : U -> V) :=
  Π x : U, MScontinuous_at f x.

(** *** Continuity for 2 variable functions *)

Definition MScontinuous2d_at {NR : NonnegativeMonoid} {U V W : MetricSet NR} (f : U -> V -> W) (x : U) (y : V) :=
  is_MSlim (λ z : U × V, f (pr1 z) (pr2 z)) (MSlocally2d x y) (f x y).
Definition MScontinuous2d_on {NR : NonnegativeMonoid} {U V W : MetricSet NR} (dom : U → V -> hProp) (f : Π x y, dom x y -> V) :=
  Π x y (Hxy : dom x y),
  ∃ H,
    is_MSlim
      (λ y0,
       f (pr1 (pr1 y0)) (pr2 (pr1 y0)) (pr2 y0))
      (FilterSubtype (MSlocally2d x y) (λ z, dom (pr1 z) (pr2 z)) H)
      (f x y Hxy).
Definition MScontinuous2d {NR : NonnegativeMonoid} {U V W : MetricSet NR} (f : U -> V -> W) :=
  Π x y, MScontinuous2d_at f x y.

(** * NonnegativeMonoid is a MetricSet *)

Definition NnMtoMS (NR : NonnegativeMonoid)
           (is : Π x y z : NR, z < NnMmax x y -> coprod (z < x) (z < y))
           (is0 : isrdistr (@NnMmax NR) (λ x y : NR, x + y))
: MetricSet NR.
Proof.
  intros NR.
  intros Hmax Hdistr.
  mkpair.
  eexists ; exact (NnMap NR).
  mkpair.
  apply (λ x y : NR, NnMmax (NnMminus x y) (NnMminus y x)).
  repeat split.
  - intros x y.
    apply iscomm_NnMmax.
  - apply sumofmaps ; intros H.
    eapply istrans_NnMlt_le, NnMmax_ge_r.
    now apply NnMminus_lt_pos.
    eapply istrans_NnMlt_le, NnMmax_ge_l.
    now apply NnMminus_lt_pos.
  - intros H.
    generalize (Hmax _ _ _ H).
    clear H ; apply sumofmaps ; intros H.
    right.
    apply (NnMplus_lt_r y) in H.
    rewrite NnMminus_plus, lunax in H.
    generalize (Hmax _ _ _ H).
    clear H ; apply sumofmaps ; intros H.
    exact H.
    apply fromempty ; revert H.
    apply isirrefl_NnMlt.
    left.
    apply (NnMplus_lt_r x) in H.
    rewrite NnMminus_plus, lunax in H.
    generalize (Hmax _ _ _ H).
    clear H ; apply sumofmaps ; intros H.
    exact H.
    apply fromempty ; revert H.
    apply isirrefl_NnMlt.
  - intros x y z.
    change (NnMmax (NnMminus x z) (NnMminus z x) <=
            NnMmax (NnMminus x y) (NnMminus y x) + NnMmax (NnMminus y z) (NnMminus z y)).
    apply notNnMlt_le ; intros H.
    generalize (Hmax _ _ _ H).
    clear H ; apply sumofmaps ; intros H.
    apply (NnMplus_lt_r z) in H.
    rewrite assocax, !Hdistr, !NnMminus_plus in H.
    generalize (Hmax _ _ _ H).
    clear H ; apply sumofmaps ;
    apply_pr2 (notNnMlt_le (X := NR)).
    admit.
    admit.
    admit.
Admitted.
