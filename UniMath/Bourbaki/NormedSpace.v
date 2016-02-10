(** * Results about Normed Spaces *)
(** Author: Catherine LELAY. Jan 2016 - *)

Require Export UniMath.Bourbaki.Filters.
Require Export UniMath.Foundations.Algebra.Apartness.
Require Import UniMath.Bourbaki.Topology.
Require Import UniMath.Bourbaki.MetricSpace.
Require Import UniMath.Foundations.Algebra.DivisionRig.
Require Import UniMath.Foundations.Algebra.ConstructiveStructures.
Require Import UniMath.Dedekind.Sets.

(** ** Nonnegative Rig *)

Definition isNonnegativeRig {X : rig} (ap ge gt : hrel X) :=
  isConstructiveTotalEffectiveOrder ap ge gt
  × isbinophrel (X := rigaddabmonoid X) gt
  × isrigmultgt X gt
  × (∀ x : X, ge x 0%rig)
  × (gt 1%rig 0%rig)
  × (∀ x y : X, ∃ min : X, ge x min × ge y min × (gt x 0%rig -> gt y 0%rig -> gt min 0%rig))
  × (∀ x y : X, gt x y -> ∃ minus : X, gt minus 0%rig × x = (y + minus)%rig).

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

Definition NonnegativeRig_to_NonnegativeAddMonoid (X : NonnegativeRig) : NonnegativeMonoid.
Proof.
  intro X.
  simple refine (tpair _ _ _).
  - apply (abmonoidtomonoid (rigaddabmonoid X)).
  - exists (NnRap X), (NnRge X), (NnRgt X).
    split.
    apply (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
    split.
    apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
    repeat split.
    apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))).
    apply hinhpr.
    exists 1.
    apply (pr1 (pr2  (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))))).
    apply (pr1 (pr2 (pr2  (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))))).
    apply (pr2 (pr2 (pr2  (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))))).
Defined.

Section NonnegativeRig_pty.

Context {X : NonnegativeRig}.

Lemma isirrefl_NnRap : isirrefl (NnRap X).
Proof.
  exact (pr1 (pr1 (pr2 (NnRap X)))).
Qed.

Lemma istight_NnRap : istight (NnRap X).
Proof.
  exact (pr2 (pr2 (NnRap X))).
Qed.
Lemma istotal_NnRgt :
  ∀ x y : X, x ≠ y <-> (x > y) ⨿ (y > x).
Proof.
  exact (pr2 (pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))).
Qed.

Lemma isrefl_NnRge :
  ∀ x : X, x >= x.
Proof.
  intros x.
  apply (pr2 (pr1 (pr2 (NnRge _)))).
Qed.

Lemma istrans_NnRgt :
  ∀ x y z : X, x > y -> y > z -> x > z.
Proof.
  apply istrans_StrongOrder.
Qed.
Lemma istrans_NnRge :
  ∀ x y z : X, x >= y -> y >= z -> x >= z.
Proof.
  exact (pr1 (pr1 (pr2 (NnRge _)))).
Qed.
Lemma istrans_NnRge_gt :
  ∀ x y z : X, x >= y -> y > z -> x > z.
Proof.
  apply (pr2 (pr2 (pr2 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))))))).
Qed.
Lemma istrans_NnRgt_ge :
  ∀ x y z : X, x > y -> y >= z -> x > z.
Proof.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))))))).
Qed.

Lemma NnRgt_ge :
  ∀ x y : X, x > y -> x >= y.
Proof.
  exact (pr1 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))))).
Qed.
Lemma notNnRgt_ge :
  ∀ x y : X, (¬ (x > y)) <-> (y >= x).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X))))))))))).
Qed.

Lemma isnonnegative_NnR :
  ∀ x : X, x >= 0.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))).
Qed.
Lemma isnonnegative_NnR' :
  ∀ x : X, ¬ (0 > x).
Proof.
  intros x.
  apply (pr2 (notNnRgt_ge _ _)).
  now apply isnonnegative_NnR.
Qed.

Lemma NnRplus_gt_l :
  ∀ k x y : X, x > y -> k + x > k + y.
Proof.
  intros k x y.
  apply (pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.
Lemma NnRplus_gt_r :
  ∀ k x y : X, x > y -> x + k > y + k.
Proof.
  intros k x y.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.

Lemma NnRmult_gt :
  ∀ a b c d : X,
    a > b -> c > d -> ((a * c) + (b * d)) > ((a * d) + (b * c)).
Proof.
  intros x y Hx Hy.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.
Lemma NnRmult_gt_0 :
  ∀ x y : X, x > 0 -> y > 0 -> x * y > 0.
Proof.
  intros x y Hx Hy.
  generalize (NnRmult_gt _ _ _ _ Hx Hy).
  now rewrite !rigmult0x, rigmultx0, !rigrunax1.
Qed.
Lemma NnRmult_gt_l :
  ∀ k x y : X, k > 0 -> x > y -> k * x > k * y.
Proof.
  intros k x y Hk H.
  generalize (NnRmult_gt _ _ _ _ Hk H).
  now rewrite !rigmult0x, !rigrunax1.
Qed.
Lemma NnRmult_gt_r :
  ∀ k x y : X, k > 0 -> x > y -> x * k > y * k.
Proof.
  intros k x y Hk H.
  generalize (NnRmult_gt _ _ _ _ H Hk).
  now rewrite !rigmultx0, rigrunax1, riglunax1.
Qed.

Lemma NnRap_gt_0 :
  ∀ x : X, x ≠ 0 -> x > 0.
Proof.
  intros x Hx.
  apply istotal_NnRgt in Hx.
  destruct Hx as [Hx | Hx].
  exact Hx.
  apply fromempty.
  revert Hx.
  now apply isnonnegative_NnR'.
Qed.
Lemma NnRgt_ap :
  ∀ x y : X, x > y -> x ≠ y.
Proof.
  intros x y H.
  apply (pr2 (istotal_NnRgt _ _)).
  now left.
Qed.

Lemma NnR_nottrivial :
  1 > (0 : X).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))))).
Qed.

Lemma NnRmin_carac :
  ∀ x y : X, ∃ min : X,
    x >= min × y >= min × (x > 0 -> y > 0 -> min > 0).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))))).
Qed.

Lemma NnRminus_carac :
  ∀ (x y : X), x > y -> ∃ minus : X, minus > 0 × x = y + minus.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))))).
Qed.

End NonnegativeRig_pty.

(** ** Definition of module *)

Definition ismodule (K : rng) (X : gr) (ap : tightap X) (scal : K -> X -> X) :=
  (∀ (a : K) (x y : X), scal a (x + y)%addmonoid = (scal a x + scal a y)%addmonoid)
  × (∀ (a b : K) (x : X), scal (a + b) x = (scal a x + scal b x)%addmonoid)
  × (∀ (a b : K) (x : X), scal (a * b) x = scal a (scal b x))
  × (∀ x : X, scal (- (1))%rng x = grinv _ x).
Definition module (K : rng) :=
  Σ (X : gr) (ap : tightap X) (scal : K -> X -> X), ismodule K X ap scal.
Definition pr1module (K : rng) : (module K) -> gr := pr1.
Coercion pr1module : module >-> gr.


Section Module_pty.

Context {K : rng} {X : module K}.

Definition Map : tightap X :=
  pr1 (pr2 X).
Definition scal : K -> X -> X :=
  pr1 (pr2 (pr2 X)).

Lemma isldistr_scal :
  ∀ (a : K) (x y : X), scal a (x + y)%addmonoid = (scal a x + scal a y)%addmonoid.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 X)))).
Qed.
Lemma isrdistr_scal :
  ∀ (a b : K) (x : X), scal (a + b) x = (scal a x + scal b x)%addmonoid.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
Qed.

Lemma isassoc_scal :
  ∀ (a b : K) (x : X), scal (a * b) x = scal a (scal b x).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
Qed.

Lemma scal_m1 :
  ∀ x : X, scal (- (1))%rng x = grinv _ x.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
Qed.

Lemma islunit_scal_1 :
  ∀ x : X, scal 1%rng x = x.
Proof.
  intros x.
  rewrite <- (rnglunax2 _ 1%rng).
  rewrite <- rngmultminusminus.
  rewrite isassoc_scal.
  rewrite !scal_m1.
  apply grinvinv.
Qed.

Lemma islabsorb_scal_0 :
  ∀ x : X, scal 0%rng x = 0%addmonoid.
Admitted.
Lemma israbsorb_scal_0 :
  ∀ k : K, scal k 0%addmonoid = 0%addmonoid.
Admitted.

End Module_pty.

(** ** Ring with absolute value *)

Definition isabsrng (NR : NonnegativeRig) (K : rng) (abs : K -> NR) :=
  (abs 0%rng = 0)
  × (abs 1%rng = 1)
  × (∀ (x y : K), abs x + abs y >= abs (x + y)%rng)
  × (∀ (x y : K), abs x * abs y >= abs (x * y)%rng).
Definition absrng {NR : NonnegativeRig} :=
  Σ (K : rng) (abs : K -> NR), isabsrng NR K abs.

Definition absrngtorng {NR : NonnegativeRig} (K : absrng (NR := NR)) : rng := (pr1 K).
Coercion absrngtorng : absrng >-> rng.

Definition abs {NR : NonnegativeRig} {K : absrng (NR := NR)} : K -> NR := (pr1 (pr2 K)).

(** ** Definition of normed module *)

Section NormedModule.

Context {NR : NonnegativeRig}.
Context {K : absrng (NR := NR)}.
Context {X : module K}.
Context (norm : X -> NR).

Definition issepp_isnorm : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ x : X, (Map x 0%addmonoid) <-> (norm x ≠ 0)).
  apply impred_isaprop ; intros x.
  apply isapropdirprod.
  apply isapropimpl.
  apply propproperty.
  apply isapropimpl.
  apply propproperty.
Defined.

Definition istriangle_isnorm : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ x y : X, (norm x + norm y) >= (norm (x + y)%addmonoid)).
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply propproperty.
Defined.

Definition issubmult_isnorm : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ (k : K) (x : X), (abs k * norm x) >= norm (scal k x)).
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply propproperty.
Defined.

End NormedModule.

Definition isnorm {NR : NonnegativeRig} {K : absrng (NR := NR)} {X : module K} (norm : X -> NR) : hProp :=
  issepp_isnorm norm ∧ istriangle_isnorm norm ∧ issubmult_isnorm norm.

Definition NormedModule {NR : NonnegativeRig} (K : absrng (NR := NR)) :=
  Σ (X : module K) (norm : X -> NR), isnorm norm.

Definition pr1NormedModule {NR : NonnegativeRig} (K : absrng (NR := NR)) : NormedModule K -> module K := pr1.
Coercion pr1NormedModule : NormedModule >-> module.

Definition norm {NR : NonnegativeRig} {K : absrng (NR := NR)} {X : NormedModule K} : (X -> NR) := pr1 (pr2 X).

Section NormedModule_pty.

Context {NR : NonnegativeRig}
        {K : absrng (NR := NR)}
        {X : NormedModule K}.

Lemma issepp_norm :
  ∀ x : X, (Map x 0%addmonoid) <-> (norm x ≠ 0).
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 X))).
Qed.
Lemma istriangle_norm :
  ∀ x y : X, (norm x + norm y) >= (norm (x + y)%addmonoid).
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 (pr2 X)))).
Qed.
Lemma issubmult_norm :
  ∀ (k : K) (x : X), (abs k * norm x) >= norm (scal k x).
Proof.
  intros.
  now apply (pr2 (pr2 (pr2 (pr2 X)))).
Qed.

Lemma norm_grinv :
  ∀ x : X, norm (grinv X x) = norm x.
Proof.
  assert (∀ x : X, norm x >= norm (grinv X x)).
  { intros x.
    rewrite <- scal_m1.
    eapply istrans_NnRge.
    2: apply issubmult_norm.
    rewrite abs_m1.
Qed.

End NormedModule_pty.

(** ** Metric space on Normed Modules *)

Section dist_norm.

Context {NR : NonnegativeRig}
        {K : absrng (NR := NR)}
        {X : NormedModule K}.

Definition metric_norm : MetricSet (NR := NonnegativeRig_to_NonnegativeAddMonoid NR).
Proof.
  simple refine (tpair _ _ _).
  simple refine (tpair _ _ _).
  apply (pr1 (pr1 (pr1 (pr1 X)))).
  apply Map.
  simple refine (tpair _ _ _).
  intros x y.
  apply (norm (X := X) (x + grinv _ y)%addmonoid).
  repeat split.
  - intros x y.

Defined.

End dist_norm.

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
