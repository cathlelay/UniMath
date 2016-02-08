(** * Results about Metric Spaces *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Export UniMath.Bourbaki.Filters.
Require Export UniMath.Foundations.Algebra.Apartness.
Require Import UniMath.Bourbaki.Topology.
Require Import UniMath.Foundations.Algebra.DivisionRig.
Require Import UniMath.Foundations.Algebra.ConstructiveStructures.
Require Import UniMath.Dedekind.Sets.

(** ** Nonnegative *)

Definition isNonnegativeMonoid {X : monoid} (ap ge gt : hrel X) :=
  isConstructiveTotalEffectiveOrder ap ge gt
  × isbinophrel gt
  × (∀ x : X, ge x 0%addmonoid).
Definition NonnegativeMonoid :=
  Σ (X : monoid) (ap gt ge : hrel X), isNonnegativeMonoid ap gt ge.

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
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
Qed.
Lemma isnonnegative_NnM' {X : NonnegativeMonoid} :
  ∀ x : X, ¬ (0 > x).
Proof.
  intros X x.
  apply (pr2 (notNnMgt_ge _ _)).
  now apply isnonnegative_NnM.
Qed.


Lemma NnMap_Nngt_0 {X : NonnegativeMonoid} :
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
  apply (∀ x y : X, (x ≠ y)%tap <-> ((dist x y) ≠ 0%addmonoid)).
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
  ∀ x y : X, (x ≠ y)%tap <-> ((dist x y) ≠ 0).
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
  apply (pr2 (issepp_dist _ _)) in H.
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
  intros x eps T H.
  apply H.
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
    apply NnMap_Nngt_0.
    now apply (pr2 eps).
  - intros P.
    apply hinhuniv.
Qed.

End Balls.