(** * Results about Metric Spaces *)
(** Author: Catherine LELAY. Jan 2016 - *)

Require Export UniMath.Foundations.Algebra.Apartness.
Require Export UniMath.Bourbaki.Filters.
Require Import UniMath.Bourbaki.Topology.
Require Import UniMath.Dedekind.Sets.

(** ** Nonnegative Monoid *)

Definition is_min {X : UU} (ge gt : hrel X)
           (x y min : X) :=
  ge x min × ge y min
     × (∀ z : X, gt x z -> gt y z -> gt min z).
Definition is_minus {X : monoid} (gt : hrel X)
           (x y minus : X) (Hxy : gt x y) :=
  gt minus 0%addmonoid × x = (y + minus)%addmonoid.

Definition isNonnegativeMonoid {X : monoid} (ap ge gt : hrel X) :=
  isConstructiveTotalEffectiveOrder ap ge gt
  × isbinophrel gt
  × (∀ x : X, ge x 0%addmonoid)
  × (∃ x0, gt x0 0%addmonoid)
  × (∀ x y : X, ∃ min : X, is_min ge gt x y min)
  × (∀ (x y : X) is, ∃ minus : X, is_minus gt x y minus is).

Definition NonnegativeMonoid :=
  Σ (X : monoid) (ap ge gt : hrel X), isNonnegativeMonoid ap ge gt.

Definition pr1NonnegativeMonoid : NonnegativeMonoid -> monoid := pr1.
Coercion pr1NonnegativeMonoid : NonnegativeMonoid >-> monoid.

Definition NnMap (X : NonnegativeMonoid) : tightap X :=
  pr1 (pr2 X) ,, pr1 (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
Definition NnMge (X : NonnegativeMonoid) : PartialOrder X :=
  pr1 (pr2 (pr2 X)),,
      pr1 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X))))))),,
      pr1 (pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X))))))).
Definition NnMgt (X : NonnegativeMonoid) : StrongOrder X :=
  pr1 (pr2 (pr2 (pr2 X))) ,, pr1 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))).

Local Notation "0" := (0%addmonoid).
Local Notation "x + y" := ((x + y)%addmonoid).
Local Notation "x ≠ y" := (NnMap _ x y).
Local Notation "x >= y" :=  (NnMge _ x y).
Local Notation "x > y" :=  (NnMgt _ x y).

Lemma istight_NnMap {X : NonnegativeMonoid} : istight (NnMap X).
Proof.
  intros X.
  exact (pr2 (pr2 (NnMap X))).
Qed.
Lemma isirrefl_NnMap {X : NonnegativeMonoid} : isirrefl (NnMap X).
Proof.
  intros X.
  exact (pr1 (pr1 (pr2 (NnMap X)))).
Qed.
Lemma istotal_NnMgt {X : NonnegativeMonoid} :
  ∀ x y : X, x ≠ y <-> (x > y) ⨿ (y > x).
Proof.
  intros X.
  exact (pr2 (pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))).
Qed.

Lemma istrans_NnMgt {X : NonnegativeMonoid} :
  ∀ x y z : X, x > y -> y > z -> x > z.
Proof.
  intros X.
  apply istrans_StrongOrder.
Qed.
Lemma istrans_NnMge_gt {X : NonnegativeMonoid} :
  ∀ x y z : X, x >= y -> y > z -> x > z.
Proof.
  intros X.
  apply (pr2 (pr2 (pr2 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))))))).
Qed.
Lemma istrans_NnMgt_ge {X : NonnegativeMonoid} :
  ∀ x y z : X, x > y -> y >= z -> x > z.
Proof.
  intros X.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))))))).
Qed.
Lemma NnMgt_ge {X : NonnegativeMonoid} :
  ∀ x y : X, x > y -> x >= y.
Proof.
  intros X.
  exact (pr1 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))))).
Qed.

Lemma notNnMgt_ge {X : NonnegativeMonoid} :
  ∀ x y : X, (¬ (x > y)) <-> (y >= x).
Proof.
  intros X.
  exact (pr1 (pr2 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X))))))))))).
Qed.
Lemma isnonnegative_NnM {X : NonnegativeMonoid} :
  ∀ x : X, x >= 0.
Proof.
  intros X.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.
Lemma isnonnegative_NnM' {X : NonnegativeMonoid} :
  ∀ x : X, ¬ (0 > x).
Proof.
  intros X x.
  apply (pr2 (notNnMgt_ge _ _)).
  now apply isnonnegative_NnM.
Qed.

Lemma NnMplus_gt_l {X : NonnegativeMonoid} :
  ∀ k x y : X, x > y -> k + x > k + y.
Proof.
  intros X k x y.
  apply (pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.
Lemma NnMplus_gt_r {X : NonnegativeMonoid} :
  ∀ k x y : X, x > y -> x + k > y + k.
Proof.
  intros X k x y.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.

Lemma NnMap_gt_0 {X : NonnegativeMonoid} :
  ∀ x : X, x ≠ 0 -> x > 0.
Proof.
  intros X x Hx.
  apply istotal_NnMgt in Hx.
  destruct Hx as [Hx | Hx].
  exact Hx.
  apply fromempty.
  revert Hx.
  now apply isnonnegative_NnM'.
Qed.
Lemma NnMgt_ap {X : NonnegativeMonoid} :
  ∀ x y : X, x > y -> x ≠ y.
Proof.
  intros X x y H.
  apply (pr2 (istotal_NnMgt _ _)).
  now left.
Qed.

Lemma NnM_nottrivial (X : NonnegativeMonoid) :
  ∃ x0 : X, x0 > 0.
Proof.
  intros X.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))).
Qed.

Lemma NnMmin_carac {X : NonnegativeMonoid} :
  ∀ x y : X, ∃ min : X,
    x >= min × y >= min × (∀ z : X, x > z -> y > z -> min > z).
Proof.
  intros X.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))))).
Qed.

Lemma NnMminus_carac {X : NonnegativeMonoid} :
  ∀ (x y : X), x > y -> ∃ minus : X, minus > 0 × x = y + minus.
Proof.
  intros X.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))))).
Qed.

(** ** Definition of metric spaces *)

Section MetricSet.

Context {NR : NonnegativeMonoid}.
Context {X : tightapSet}.
Context (dist : X -> X -> NR).

Definition issymm_isdist : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ x y : X, dist x y = dist y x).
  apply impred_isaprop ; intro x.
  apply impred_isaprop ; intro y.
  apply (pr2 (pr1 (pr1 (pr1 NR)))).
Defined.

Definition issepp_isdist : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ x y : X, (x ≠ y)%tap <-> ((dist x y) > 0%addmonoid)).
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
  apply (∀ x y z : X, (dist x y + dist y z)%addmonoid >= (dist x z)).
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply impred_isaprop ; intros z.
  apply propproperty.
Defined.

End MetricSet.

Definition isdist {NR : NonnegativeMonoid} {X : tightapSet} (dist : X -> X -> NR) : hProp :=
  issymm_isdist dist ∧ issepp_isdist dist ∧ istriangle_isdist dist.

Definition MetricSet {NR : NonnegativeMonoid} :=
  Σ (X : tightapSet) (dist : X -> X -> NR), isdist dist.

Definition pr1MetricSet {NR : NonnegativeMonoid} : MetricSet (NR := NR) -> tightapSet := pr1.
Coercion pr1MetricSet : MetricSet >-> tightapSet.

Definition dist {NR : NonnegativeMonoid} {X : MetricSet (NR := NR)} : (X -> X -> NR) := pr1 (pr2 X).

Lemma issymm_dist {NR : NonnegativeMonoid} {X : MetricSet (NR := NR)} :
  ∀ x y : X, dist x y = dist y x.
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 X))).
Qed.
Lemma issepp_dist {NR : NonnegativeMonoid} {X : MetricSet (NR := NR)} :
  ∀ x y : X, (x ≠ y)%tap <-> ((dist x y) > 0).
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 (pr2 X)))).
Qed.
Lemma istriangle_dist {NR : NonnegativeMonoid} {X : MetricSet (NR := NR)} :
  ∀ x y z : X, (dist x y + dist y z) >= (dist x z).
Proof.
  intros.
  now apply (pr2 (pr2 (pr2 (pr2 X)))).
Qed.

Lemma dist_0 {NR : NonnegativeMonoid} {X : MetricSet (NR := NR)} :
  ∀ x : X, dist x x = 0.
Proof.
  intros.
  apply istight_NnMap.
  intro H.
  apply NnMap_gt_0, (pr2 (issepp_dist _ _)) in H.
  revert H.
  apply isirrefltightapSet.
Qed.

(** ** Topology on metric spaces *)

Section Balls.

Context {NR : NonnegativeMonoid}.
Context {M : MetricSet (NR := NR)}.

Definition ball (x : M) (eps : NR) (y : M) : hProp.
Proof.
  intros.
  apply (eps > dist x y).
Defined.

Lemma ball_center :
  ∀ (x : M) (eps : NR), eps > 0 -> ball x eps x.
Proof.
  intros x eps He.
  unfold ball.
  now rewrite dist_0.
Qed.
Lemma ball_ge :
  ∀ x e e' y, e >= e' -> ball x e' y -> ball x e y.
Proof.
  intros x e e' y H H'.
  refine (istrans_NnMge_gt _ _ _ _ _).
  apply H.
  apply H'.
Qed.
Lemma ball_recenter :
  ∀ (x y : M) (eps : NR), ball y eps x -> ∃ eps' : NR, eps' > 0 × ∀ z : M, ball x eps' z -> ball y eps z.
Proof.
  intros x y eps Hy.
  apply NnMminus_carac in Hy.
  revert Hy.
  apply hinhfun.
  intros (eps',(H,->)).
  exists eps'.
  split.
  exact H.
  intros z Hz.
  unfold ball.
  refine (istrans_NnMgt_ge _ _ _ _ _).
  apply NnMplus_gt_l.
  apply Hz.
  apply istriangle_dist.
Qed.

Lemma ball_symm :
  ∀ (x y : M) (eps : NR), ball x eps y -> ball y eps x.
Proof.
  intros x y eps.
  unfold ball.
  now rewrite issymm_dist.
Qed.

Definition metric_topology : TopologicalSet.
Proof.
  simple refine (generated_topology _).
  apply (pr1 (pr1 M)).
  intros A.
  apply (∃ (x : M) (eps : Σ e : NR, e > 0), A = ball x (pr1 eps)).
Defined.

Lemma isOpen_ball :
  ∀ (x : M) (eps : Σ e : NR, e > 0),
    isOpen (T := metric_topology) (ball x (pr1 eps)).
Proof.
  intros x eps.
  apply generated_topology_included.
  apply hinhpr.
  now exists x, eps.
Qed.

Lemma is_base_of_neighborhood_ball (x : M) :
  is_base_of_neighborhood (T := metric_topology) x
                          (λ A : M -> hProp, ∃ (eps : Σ e : NR, e > 0), A = ball x (pr1 eps)).
Proof.
  split.
  - intros P.
    apply hinhuniv.
    intros (eps, ->).
    apply (pr2 (neighborhood_isOpen _)).
    apply isOpen_ball.
    unfold ball.
    rewrite dist_0.
    now apply (pr2 eps).
  - intros P.
    apply hinhuniv.
    intros ((O,Ho),(Ox,Hp)).
    simpl in Ox, Hp.
    generalize (Ho x Ox) ; clear Ho.
    apply hinhuniv.
    intros (L,(Bl,Hl)).
    assert (∃ (eps : Σ e : NR, e > 0), ∀ y : M, ball x (pr1 eps) y -> finite_intersection L y).
    { clear -Bl.
      revert L Bl.
      apply (Sequence_rect (P := λ L : Sequence (pr1 (pr1 M) -> hProp), (∀ n : stn (length L), (∃ (x0 : M) (eps : Σ e : NR, e > 0), L n = ball x0 (pr1 eps)) × L n x) -> ∃ eps : Σ e : NR, e > 0, ∀ y : M, ball x (pr1 eps) y -> finite_intersection L y)).
      - intros _.
        generalize (NnM_nottrivial NR).
        apply hinhfun.
        intros eps.
        exists eps.
        now intros y _ (n,Hn).
      - intros L A IHl Hl.
        generalize (Hl (lastelement _)).
        intros (Ha,Ax).
        revert Ha.
        apply hinhuniv.
        intros (xa,(epsa,Ha)).
        simpl in Ax, Ha.
        rewrite append_fun_compute_2 in Ax, Ha.
        rewrite Ha in Hl, Ax |- * ; clear A Ha.
        apply ball_recenter in Ax.
        refine (hinhuniv2 _ _ _).
        2: apply Ax.
        2: apply IHl.
        intros (e0,(e0_pos,He0)) ((e1,e1_pos),He1).
        generalize (NnMmin_carac e0 e1).
        apply hinhfun.
        intros (min,(min_x,(min_y,min_pos))).
        simpl in He1.
        specialize (min_pos _ e0_pos e1_pos).
        exists (min ,, min_pos).
        intros y Hy.
        rewrite finite_intersection_append.
        split.
        apply He0.
        revert Hy.
        now apply ball_ge.
        intros n.
        apply He1.
        revert Hy.
        now apply ball_ge.
        intros n.
        generalize (Hl (dni_lastelement n)).
        intros (Hb,Bx).
        split.
        revert Hb.
        apply hinhuniv.
        intros (xb,(epsb,Hb)).
        simpl in Hb.
        rewrite append_fun_compute_1 in Hb.
        apply hinhpr.
        exists xb, epsb.
        apply Hb.
        simpl in Bx.
        rewrite append_fun_compute_1 in Bx.
        apply Bx. }
    revert X.
    apply hinhfun.
    intros (e,He).
    exists (ball x (pr1 e)).
    split.
    apply hinhpr.
    now exists e.
    intros t Ht.
    now apply Hp, Hl, He.
Qed.

End Balls.

(** ** Limits in a Metric Space *)

Definition locally {NR : NonnegativeMonoid} {M : MetricSet (NR := NR)} (x : M) : Filter (X := M) :=
  locally_base (T := metric_topology) x (_,,is_base_of_neighborhood_ball x).

Lemma locally_ball {NR : NonnegativeMonoid} {M : MetricSet (NR := NR)} (x : M) :
  ∀ e : NR, e > 0 -> locally x (ball x e).
Proof.
  intros NR M x e He.
  apply hinhpr.
  exists (ball x e).
  split.
  apply hinhpr.
  exists (e,,He).
  reflexivity.
  easy.
Qed.

(** *** Limit of a filter *)

Definition is_filter_lim {NR : NonnegativeMonoid} {M : MetricSet (NR := NR)} (F : Filter) (x : M) :=
  is_filter_lim_base (T := metric_topology) F x (_,,is_base_of_neighborhood_ball x).
Definition ex_filter_lim {NR : NonnegativeMonoid} {M : MetricSet (NR := NR)} (F : Filter) :=
  ∃ (x : M), is_filter_lim F x.

(** *** Limit of a function *)

Definition is_lim {X : UU} {NR : NonnegativeMonoid} {M : MetricSet (NR := NR)} (f : X -> M) (F : Filter) (x : M) :=
  is_lim_base (T := metric_topology) f F x (_,,is_base_of_neighborhood_ball x).
Definition ex_lim {X : UU} {NR : NonnegativeMonoid} {M : MetricSet (NR := NR)} (f : X -> M) (F : Filter) :=
  ∃ (x : M), is_lim f F x.

Lemma is_lim_aux {X : UU} {NR : NonnegativeMonoid} {M : MetricSet (NR := NR)} (f : X -> M) (F : Filter) (x : M) :
  is_lim f F x <->
  (∀ eps : (Σ e : NR, e > 0), F (λ y, ball x (pr1 eps) (f y))).
Proof.
  intros X NR M f F x.
  split.
  - intros H e.
    eapply filter_imply.
    2: apply H.
    intros y Hy.
    apply Hy.
    apply locally_ball.
    now apply (pr2 e).
  - intros H P.
    apply hinhuniv.
    intros (O,(Ho,Ho')).
    revert Ho.
    apply hinhuniv.
    intros (e,->).
    generalize (H e).
    apply (filter_imply F).
    intros y Hy.
    apply Ho'.
    apply Hy.
Qed.

(** *** Continuity *)

Definition continuous_at {NR : NonnegativeMonoid} {U V : MetricSet (NR := NR)} (f : U -> V) (x : U) :=
  continuous_base_at (U := metric_topology) (V := metric_topology) f x  (_,,is_base_of_neighborhood_ball x) (_,,is_base_of_neighborhood_ball (f x)).

Definition continuous_on {NR : NonnegativeMonoid} {U V : MetricSet (NR := NR)} (dom : U -> hProp) (f : U -> V) :=
  ∀ (x : U) (Hx : dom x) H,
    is_lim f (filter_dom (locally x) dom H) (f x).
Definition continuous_subtypes {NR : NonnegativeMonoid} {U V : MetricSet (NR := NR)} (dom : U -> hProp) (f : (Σ x : U, dom x) -> V) :=
  ∀ (x : Σ x : U, dom x) H,
    is_lim f (filter_subtypes (locally (pr1 x)) dom H) (f x).
Definition continuous {NR : NonnegativeMonoid} {U V : MetricSet (NR := NR)} (f : U -> V) :=
  ∀ x : U, continuous_at f x.

(** *** Continuity for 2 variable functions *)

Definition continuous2d_at {NR : NonnegativeMonoid} {U V W : MetricSet (NR := NR)} (f : U -> V -> W) (x : U) (y : V) :=
  continuous2d_base_at (U := metric_topology) (V := metric_topology) (W := metric_topology) f x y (_,,is_base_of_neighborhood_ball x) (_,,is_base_of_neighborhood_ball y) (_,,is_base_of_neighborhood_ball (f x y)).

Definition continuous2d {NR : NonnegativeMonoid} {U V W : MetricSet (NR := NR)} (f : U -> V -> W) :=
  ∀ (x : U) (y : V), continuous2d_at f x y.
