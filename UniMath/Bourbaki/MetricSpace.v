(** * Results about Metric Spaces *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Export UniMath.Bourbaki.Filters.
Require Export UniMath.Foundations.Algebra.Apartness.
Require Import UniMath.Bourbaki.Topology.
Require Import UniMath.Foundations.Algebra.DivisionRig.
Require Import UniMath.Foundations.Algebra.ConstructiveStructures.

(** ** Nonnegative *)

Definition isNonnegative_monoid (X : monoid) (R : PartialOrder X) :=
  (tightap X) × isbinophrel R × (∀ x : X, R 0%addmonoid x).
Definition Nonnegative_monoid :=
  Σ (X : monoid) (R : PartialOrder X), isNonnegative_monoid X R.

Definition pr1Nonnegative_monoid : Nonnegative_monoid -> monoid := pr1.
Coercion pr1Nonnegative_monoid : Nonnegative_monoid >-> monoid.

Definition apNonnegative_monoid : Nonnegative_monoid -> tightapSet.
Proof.
  intros.
  simple refine (tpair _ _ _).
  apply (pr1 (pr1 (pr1 X))).
  apply (pr1 (pr2 (pr2 X))).
Defined.

Definition poNonnegative_monoid (X : Nonnegative_monoid) : PartialOrder X :=
  pr1 (pr2 X).
Local Notation "x <= y" :=  (poNonnegative_monoid _ x y).

(** ** Definition of metric spaces *)

Section MetricSet.

Context {NR : Nonnegative_monoid}.
Context {X : tightapSet}.
Context (dist : X -> X -> NR).

Definition issymm_dist : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ x y : X, dist x y = dist y x).
  apply impred_isaprop ; intro x.
  apply impred_isaprop ; intro y.
  apply (pr2 (pr1 (pr1 (pr1 NR)))).
Defined.

Definition issepp_dist : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ x y : X, (x ≠ y)%tap <-> ((dist x y : apNonnegative_monoid NR) ≠ 0%addmonoid)%tap).
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply isapropdirprod.
  apply isapropimpl.
  apply propproperty.
  apply isapropimpl.
  apply propproperty.
Defined.

Definition istriangle_dist : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ x y z : X, (dist x z) <= (dist x y + dist y z)%addmonoid).
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply impred_isaprop ; intros z.
  apply propproperty.
Defined.

End MetricSet.

Definition isdist {NR : Nonnegative_monoid} {X : tightapSet} (dist : X -> X -> NR) : hProp :=
  issymm_dist dist ∧ issepp_dist dist ∧ istriangle_dist dist.

Definition MetricSet {NR : Nonnegative_monoid} :=
  Σ (X : tightapSet) (dist : X -> X -> NR), isdist dist.

Definition pr1MetricSet {NR : Nonnegative_monoid} : MetricSet (NR := NR) -> tightapSet := pr1.
Coercion pr1MetricSet : MetricSet >-> tightapSet.

Definition dist {NR : Nonnegative_monoid} {X : MetricSet (NR := NR)} : (X -> X -> NR) := pr1 (pr2 X).

(** ** Topology on metric spaces *)

Section Balls.

Context {NR : Nonnegative_monoid}.
Context {M : MetricSet (NR := NR)}.

Definition ball (x : M) (eps : NR) (y : M) : hProp.
Proof.
  simple refine (hneg _).
  apply (eps <= dist x y).
Defined.

Definition metric_topology : TopologicalSet.
Proof.
  simple refine (generated_topology _).
  apply (pr1 (pr1 M)).
  intros A.
  apply (∃ (x : M) (eps : Σ e : NR, ((e : apNonnegative_monoid NR) ≠ 0%addmonoid)%tap), A = ball x (pr1 eps)).
Defined.
Lemma isOpen_ball :
  ∀ (x : M) (eps : Σ e : NR, ((e : apNonnegative_monoid NR) ≠ 1%multmonoid)%tap),
    isOpen (T := metric_topology) (ball x (pr1 eps)).
Proof.
  intros x eps T H.
  apply H.
  apply hinhpr.
  now exists x, eps.
Qed.

Lemma is_base_of_neighborhood_ball (x : M) :
  is_base_of_neighborhood (T := metric_topology) x (λ A : M -> hProp, ∃ (eps : Σ e : NR, ((e : apNonnegative_monoid NR) ≠ 0%addmonoid)%tap), A = ball x (pr1 eps)).
Proof.
  split.
  - intros P.
    apply hinhuniv.
    intros (eps, ->).
    apply (pr2 (neighborhood_isOpen _)).
    apply isOpen_ball.
    intro H.

Qed.

End Balls.