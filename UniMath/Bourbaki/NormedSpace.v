(** * Results about Normed Spaces *)
(** Author: Catherine LELAY. Jan 2016 - *)

Require Export UniMath.Bourbaki.Filters.
Require Export UniMath.Foundations.Algebra.Apartness.
Require Import UniMath.Bourbaki.Topology.
Require Import UniMath.Foundations.Algebra.DivisionRig.
Require Import UniMath.Foundations.Algebra.ConstructiveStructures.
Require Import UniMath.Dedekind.Sets.

(** ** Nonnegative Rig *)

Definition isNonnegativeRig {X : rig} (ap ge gt : hrel X) :=
  isConstructiveTotalEffectiveOrder ap ge gt
  × isbinophrel (X := rigaddabmonoid X) gt
  × isrigmultgt X gt
  × (∀ x : X, ge x 0%rig)
  × (gt 1%rig 0%rig).
(*  × (∀ x y : X, ∃ min : X, ge x min × ge y min × (gt x 0%addmonoid -> gt y 0%addmonoid -> gt min 0%addmonoid))
  × (∀ x y : X, gt x y -> ∃ minus : X, gt minus 0%addmonoid × x = (y + minus)%addmonoid).*)

Definition NonnegativeRig :=
  Σ (X : rig) (ap gt ge : hrel X), isNonnegativeRig ap gt ge.

Definition pr1NonnegativeRig : NonnegativeRig -> rig := pr1.
Coercion pr1NonnegativeRig : NonnegativeRig >-> rig.

Definition NnRap (X : NonnegativeRig) : tightap X :=
  pr1 (pr2 X) ,, pr1 (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
Definition NnRge (X : NonnegativeRig) : PartialOrder X :=
  pr1 (pr2 (pr2 X)),,
      pr1 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X))))))),,
      pr1 (pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X))))))).
Definition NnRgt (X : NonnegativeRig) : StrongOrder X :=
  pr1 (pr2 (pr2 (pr2 X))) ,, pr1 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))).

Local Notation "0" := (0%rig).
Local Notation "1" := (1%rig).
Local Notation "x + y" := ((x + y)%rig).
Local Notation "x * y" := ((x * y)%rig).
Local Notation "x ≠ y" := (NnRap _ x y).
Local Notation "x >= y" :=  (NnRge _ x y).
Local Notation "x > y" :=  (NnRgt _ x y).

Lemma istight_NnRap {X : NonnegativeRig} : istight (NnRap X).
Proof.
  intros X.
  exact (pr2 (pr2 (NnRap X))).
Qed.
Lemma isirrefl_NnRap {X : NonnegativeRig} : isirrefl (NnRap X).
Proof.
  intros X.
  exact (pr1 (pr1 (pr2 (NnRap X)))).
Qed.
Lemma istotal_NnRgt {X : NonnegativeRig} :
  ∀ x y : X, x ≠ y <-> (x > y) ⨿ (y > x).
Proof.
  intros X.
  exact (pr2 (pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))).
Qed.

Lemma istrans_NnRgt {X : NonnegativeRig} :
  ∀ x y z : X, x > y -> y > z -> x > z.
Proof.
  intros X.
  apply istrans_StrongOrder.
Qed.
Lemma istrans_NnRge_gt {X : NonnegativeRig} :
  ∀ x y z : X, x >= y -> y > z -> x > z.
Proof.
  intros X.
  apply (pr2 (pr2 (pr2 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))))))).
Qed.
Lemma istrans_NnRgt_ge {X : NonnegativeRig} :
  ∀ x y z : X, x > y -> y >= z -> x > z.
Proof.
  intros X.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))))))).
Qed.
Lemma NnRgt_ge {X : NonnegativeRig} :
  ∀ x y : X, x > y -> x >= y.
Proof.
  intros X.
  exact (pr1 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))))).
Qed.

Lemma notNnRgt_ge {X : NonnegativeRig} :
  ∀ x y : X, (¬ (x > y)) <-> (y >= x).
Proof.
  intros X.
  exact (pr1 (pr2 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X))))))))))).
Qed.
Lemma isnonnegative_NnR {X : NonnegativeRig} :
  ∀ x : X, x >= 0.
Proof.
  intros X.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))).
Qed.
Lemma isnonnegative_NnR' {X : NonnegativeRig} :
  ∀ x : X, ¬ (0 > x).
Proof.
  intros X x.
  apply (pr2 (notNnRgt_ge _ _)).
  now apply isnonnegative_NnR.
Qed.

Lemma NnRplus_gt_l {X : NonnegativeRig} :
  ∀ k x y : X, x > y -> k + x > k + y.
Proof.
  intros X k x y.
  apply (pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.
Lemma NnRplus_gt_r {X : NonnegativeRig} :
  ∀ k x y : X, x > y -> x + k > y + k.
Proof.
  intros X k x y.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.

Lemma NnRmult_gt {X : NonnegativeRig} :
  ∀ a b c d : X,
    a > b -> c > d -> ((a * c) + (b * d)) > ((a * d) + (b * c)).
Proof.
  intros X x y Hx Hy.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.
Lemma NnRmult_gt_0 {X : NonnegativeRig} :
  ∀ x y : X, x > 0 -> y > 0 -> x * y > 0.
Proof.
  intros X x y Hx Hy.
  generalize (NnRmult_gt _ _ _ _ Hx Hy).
  now rewrite !rigmult0x, rigmultx0, !rigrunax1.
Qed.
Lemma NnRmult_gt_l {X : NonnegativeRig} :
  ∀ k x y : X, k > 0 -> x > y -> k * x > k * y.
Proof.
  intros X k x y Hk H.
  generalize (NnRmult_gt _ _ _ _ Hk H).
  now rewrite !rigmult0x, !rigrunax1.
Qed.
Lemma NnRmult_gt_r {X : NonnegativeRig} :
  ∀ k x y : X, k > 0 -> x > y -> x * k > y * k.
Proof.
  intros X k x y Hk H.
  generalize (NnRmult_gt _ _ _ _ H Hk).
  now rewrite !rigmultx0, rigrunax1, riglunax1.
Qed.

Lemma NnRap_gt_0 {X : NonnegativeRig} :
  ∀ x : X, x ≠ 0 -> x > 0.
Proof.
  intros X x Hx.
  apply istotal_NnRgt in Hx.
  destruct Hx as [Hx | Hx].
  exact Hx.
  apply fromempty.
  revert Hx.
  now apply isnonnegative_NnR'.
Qed.
Lemma NnRgt_ap {X : NonnegativeRig} :
  ∀ x y : X, x > y -> x ≠ y.
Proof.
  intros X x y H.
  apply (pr2 (istotal_NnRgt _ _)).
  now left.
Qed.

Lemma NnR_nottrivial (X : NonnegativeRig) :
  1 > (0 : X).
Proof.
  intros X.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))).
Qed.

(*Lemma NnRmin_carac {X : NonnegativeRig} :
  ∀ x y : X, ∃ min : X,
    x >= min × y >= min × (x > 0 -> y > 0 -> min > 0).
Proof.
  intros X.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))))).
Qed.

Lemma NnRminus_carac {X : NonnegativeRig} :
  ∀ (x y : X), x > y -> ∃ minus : X, minus > 0 × x = y + minus.
Proof.
  intros X.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))))).
Qed.*)

(** ** Definition of module *)

Definition ismodule (K : rng) (X : gr) (scal : K -> X -> X) :=
  (∀ (a : K) (x y : X), scal a (x + y)%addmonoid = (scal a x + scal a y)%addmonoid)
  × (∀ (a b : K) (x : X), scal (a + b) x = (scal a x + scal b x)%addmonoid)
  × (∀ (a b : K) (x : X), scal (a * b) x = scal a (scal b x))
  × (∀ x : X, scal 1%rng x = x).
Definition module (K : rng) :=
  Σ (X : gr) (scal : K -> X -> X), ismodule K X scal.
Definition pr1module (K : rng) : (module K) -> gr := pr1.
Coercion pr1module : module >-> gr.

Definition scal {K : rng} {X : module K} : K -> X -> X :=
  pr1 (pr2 X).

(** ** Ring with absolute value *)

Definition isabsrng (NR : NonnegativeRig) (K : rng) (abs : K -> NR) :=
  (abs 0%rng = 0)
  × (abs 1%rng = 1)
  × (∀ (x y : K), abs x + abs y >= abs (x + y)%rng)
  × (∀ (x y : K), abs x * abs y >= abs (x * y)%rng).
Definition absrng {NR : NonnegativeRig} :=
  Σ  (K : rng) (abs : K -> NR), isabsrng NR K abs.

Definition absrngtorng {NR : NonnegativeRig} (K : absrng (NR := NR)) : rng := (pr1 K).
Coercion absrngtorng : absrng >-> rng.

(** ** Definition of normed module *)

Section NormedModule.

Context {NR : NonnegativeRig}.
Context {K : absrng (NR := NR)}.
Context {X : module K}.
Context (norm : X -> NR).

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
  apply (∀ x y : X, (x ≠ y)%tap <-> ((dist x y) ≠ 0%addrig)).
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
  apply (∀ x y z : X, (dist x y + dist y z)%addrig >= (dist x z)).
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply impred_isaprop ; intros z.
  apply propproperty.
Defined.

End MetricSet.

Definition isdist {NR : NonnegativeRig} {X : tightapSet} (dist : X -> X -> NR) : hProp :=
  issymm_isdist dist ∧ issepp_isdist dist ∧ istriangle_isdist dist.

Definition MetricSet {NR : NonnegativeRig} :=
  Σ (X : tightapSet) (dist : X -> X -> NR), isdist dist.

Definition pr1MetricSet {NR : NonnegativeRig} : MetricSet (NR := NR) -> tightapSet := pr1.
Coercion pr1MetricSet : MetricSet >-> tightapSet.

Definition dist {NR : NonnegativeRig} {X : MetricSet (NR := NR)} : (X -> X -> NR) := pr1 (pr2 X).

Lemma issymm_dist {NR : NonnegativeRig} {X : MetricSet (NR := NR)} :
  ∀ x y : X, dist x y = dist y x.
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 X))).
Qed.
Lemma issepp_dist {NR : NonnegativeRig} {X : MetricSet (NR := NR)} :
  ∀ x y : X, (x ≠ y)%tap <-> ((dist x y) ≠ 0).
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 (pr2 X)))).
Qed.
Lemma istriangle_dist {NR : NonnegativeRig} {X : MetricSet (NR := NR)} :
  ∀ x y z : X, (dist x y + dist y z) >= (dist x z).
Proof.
  intros.
  now apply (pr2 (pr2 (pr2 (pr2 X)))).
Qed.

Lemma dist_0 {NR : NonnegativeRig} {X : MetricSet (NR := NR)} :
  ∀ x : X, dist x x = 0.
Proof.
  intros.
  apply istight_NnRap.
  intro H.
  apply (pr2 (issepp_dist _ _)) in H.
  revert H.
  apply isirrefltightapSet.
Qed.

(** ** Topology on metric spaces *)

Section Balls.

Context {NR : NonnegativeRig}.
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
  refine (istrans_NnRge_gt _ _ _ _ _).
  apply H.
  apply H'.
Qed.
Lemma ball_recenter :
  ∀ (x y : M) (eps : NR), ball y eps x -> ∃ eps' : NR, eps' > 0 × ∀ z : M, ball x eps' z -> ball y eps z.
Proof.
  intros x y eps Hy.
  apply NnRminus_carac in Hy.
  revert Hy.
  apply hinhfun.
  intros (eps',(H,->)).
  exists eps'.
  split.
  exact H.
  intros z Hz.
  unfold ball.
  refine (istrans_NnRgt_ge _ _ _ _ _).
  apply NnRplus_gt_l.
  apply Hz.
  apply istriangle_dist.
Qed.

Definition metric_topology : TopologicalSet.
Proof.
  simple refine (generated_topology _).
  apply (pr1 (pr1 M)).
  intros A.
  apply (∃ (x : M) (eps : Σ e : NR, e ≠ 0), A = ball x (pr1 eps)).
Defined.

Lemma isOpen_ball :
  ∀ (x : M) (eps : Σ e : NR, e ≠ 0),
    isOpen (T := metric_topology) (ball x (pr1 eps)).
Proof.
  intros x eps.
  apply generated_topology_included.
  apply hinhpr.
  now exists x, eps.
Qed.

Lemma is_base_of_neighborhood_ball (x : M) :
  is_base_of_neighborhood (T := metric_topology) x
                          (λ A : M -> hProp, ∃ (eps : Σ e : NR, e ≠ 0), A = ball x (pr1 eps)).
Proof.
  split.
  - intros P.
    apply hinhuniv.
    intros (eps, ->).
    apply (pr2 (neighborhood_isOpen _)).
    apply isOpen_ball.
    unfold ball.
    rewrite dist_0.
    apply NnRap_gt_0.
    now apply (pr2 eps).
  - intros P.
    apply hinhuniv.
    intros ((O,Ho),(Ox,Hp)).
    simpl in Ox, Hp.
    generalize (Ho x Ox) ; clear Ho.
    apply hinhuniv.
    intros (L,(Bl,Hl)).
    assert (∃ (eps : Σ e : NR, e ≠ 0), ∀ y : M, ball x (pr1 eps) y -> finite_intersection L y).
    { clear -Bl.
      revert L Bl.
      apply (Sequence_rect (P := λ L : Sequence (pr1 (pr1 M) -> hProp), (∀ n : stn (length L), (∃ (x0 : M) (eps : Σ e : NR, e ≠ 0), L n = ball x0 (pr1 eps)) × L n x) -> ∃ eps : Σ e : NR, e ≠ 0, ∀ y : M, ball x (pr1 eps) y -> finite_intersection L y)).
      - intros _.
        generalize (NnR_nottrivial NR).
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
        generalize (NnRmin_carac e0 e1).
        apply hinhfun.
        intros (min,(min_x,(min_y,min_pos))).
        simpl in He1.
        apply NnRap_gt_0 in e1_pos.
        specialize (min_pos e0_pos e1_pos).
        apply NnRgt_ap in min_pos.
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
    exists (ball x (pr1 e) ,, isOpen_ball _ _).
    split.
    apply hinhpr.
    now exists e.
    intros t Ht.
    now apply Hp, Hl, He.
Qed.

End Balls.

(** ** Limits in a Metric Space *)

Definition locally {NR : NonnegativeRig} {M : MetricSet (NR := NR)} (x : M) : Filter (X := M).
Proof.
  intros NR M x.
  simple refine (mkFilter _ _ _ _ _).
  - apply (neighborhood' (T := metric_topology) x).
    refine (tpair _ _ _).
    apply is_base_of_neighborhood_ball.
  - intros A B.
    intros Himpl Ha.
    apply (pr2 (neighborhood_equiv _ _ _)).
    apply neighborhood_equiv in Ha.
    revert Ha.
    apply neighborhood_impl, Himpl.
  - apply (pr2 (neighborhood_equiv _ _ _)).
    apply (pr2 (neighborhood_isOpen _)).
    apply (isOpen_htrue (T := metric_topology)).
    apply tt.
  - intros A B Ha Hb.
    apply (pr2 (neighborhood_equiv _ _ _)).
    apply neighborhood_equiv in Ha.
    apply neighborhood_equiv in Hb.
    revert Ha Hb.
    apply neighborhood_and.
  - intros Hx.
    apply neighborhood_equiv in Hx.
    apply neighborhood_point in Hx.
    exact Hx.
Defined.

(** *** Limit of a filter *)

Definition is_filter_lim {NR : NonnegativeRig} {M : MetricSet (NR := NR)} (F : Filter) (x : M) :=
  filter_le (locally x) F.
Definition ex_filter_lim {NR : NonnegativeRig} {M : MetricSet (NR := NR)} (F : Filter) :=
  ∃ (x : M), is_filter_lim F x.

Lemma is_filter_lim_correct {NR : NonnegativeRig} {M : MetricSet (NR := NR)} (F : Filter) (x : M) :
  is_filter_lim F x <-> Topology.is_filter_lim (T := metric_topology) F x.
Proof.
  intros NR M F x.
  split.
  - intros H P Hp.
    apply H.
    revert Hp.
    apply (pr2 (neighborhood_equiv _ _ _)).
  - intros H P Hp.
    apply H.
    revert Hp.
    apply (pr1 (neighborhood_equiv _ _ _)).
Qed.
Lemma ex_filter_lim_correct {NR : NonnegativeRig} {M : MetricSet (NR := NR)} (F : Filter (X := M)) :
  ex_filter_lim F <-> Topology.ex_filter_lim (T := metric_topology) F.
Proof.
  intros NR M F.
  split.
  - apply hinhfun.
    intros (x,Hx).
    exists x.
    revert Hx.
    apply (pr1 (is_filter_lim_correct _ _)).
  - apply hinhfun.
    intros (x,Hx).
    exists x.
    revert Hx.
    apply (pr2 (is_filter_lim_correct _ _)).
Qed.

(** *** Limit of a function *)

Definition is_lim {X : UU} {NR : NonnegativeRig} {M : MetricSet (NR := NR)} (f : X -> M) (F : Filter (X := X)) (x : M) :=
  filterlim f F (locally x).
Definition ex_lim {X : UU} {NR : NonnegativeRig} {M : MetricSet (NR := NR)} (f : X -> M) (F : Filter (X := X)) :=
  ∃ (x : M), is_lim f F x.

Lemma is_lim_correct {X : UU} {NR : NonnegativeRig} {M : MetricSet (NR := NR)} (f : X -> M) (F : Filter (X := X)) (x : M) :
  is_lim f F x <-> Topology.is_lim (T := metric_topology) f F x.
Proof.
  intros.
  split.
  - intros Hx P HP.
    apply Hx in HP.
    revert HP.
    apply (pr1 (neighborhood_equiv _ _ _)).
  - intros Hx P HP.
    apply Hx in HP.
    revert HP.
    apply (pr2 (neighborhood_equiv _ _ _)).
Qed.
Lemma ex_lim_correct {X : UU} {NR : NonnegativeRig} {M : MetricSet (NR := NR)} (f : X -> M) (F : Filter (X := X)) :
  ex_lim f F <-> Topology.ex_lim (T := metric_topology) f F.
Proof.
  intros.
  split.
  - apply hinhfun.
    intros (x,Hx).
    exists x.
    revert Hx.
    apply (pr1 (is_lim_correct _ _ _)).
  - apply hinhfun.
    intros (x,Hx).
    exists x.
    revert Hx.
    apply (pr2 (is_lim_correct _ _ _)).
Qed.

(** *** Continuity *)

Definition continuous_at {NR : NonnegativeRig} {U V : MetricSet (NR := NR)} (f : U -> V) (x : U) :=
  is_lim f (locally x) (f x).
Definition continuous_on {NR : NonnegativeRig} {U V : MetricSet (NR := NR)} (dom : U -> hProp) (f : U -> V) :=
  ∀ (x : U) (Hx : dom x),
    is_lim f (filter_dom (locally x) dom (notempty_ex dom x Hx)) (f x).

Definition continuous_subtypes {NR : NonnegativeRig} {U V : MetricSet (NR := NR)} (dom : U -> hProp) (f : (Σ x : U, dom x) -> V) :=
  ∀ (x : Σ x : U, dom x),
    is_lim f (filter_subtypes (locally (pr1 x)) dom (notempty_ex dom (pr1 x) (pr2 x))) (f x).
Definition continuous {NR : NonnegativeRig} {U V : MetricSet (NR := NR)} (f : U -> V) :=
  ∀ x : U, continuous_at f x.

(** *** Continuity for 2 variable functions *)

Definition continuous2d_at {NR : NonnegativeRig} {U V W : MetricSet (NR := NR)} (f : U -> V -> W) (x : U) (y : V) :=
  is_lim (λ z : U × V, f (pr1 z) (pr2 z)) (filter_prod (locally x) (locally y)) (f x y).
Definition continuous2d {NR : NonnegativeRig} {U V W : MetricSet (NR := NR)} (f : U -> V -> W) :=
  ∀ (x : U) (y : V), continuous2d_at f x y.
