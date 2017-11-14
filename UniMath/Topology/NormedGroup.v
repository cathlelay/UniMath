(** * Results about Metric Spaces *)
(** Author: Catherine LELAY. Jan 2017 - *)

Require Export UniMath.Algebra.Lattice.
Require Import UniMath.Topology.Prelim.
Require Export UniMath.Topology.Filters.
Require Import UniMath.Topology.Topology.
Require Import UniMath.Topology.UniformSpace.
Require Import UniMath.Algebra.Apartness.
Require Import UniMath.Topology.MetricSpace.

Unset Automatic Introduction.

Set Default Timeout 5.

(** * Normed Group *)

Local Open Scope addmonoid.

Section NormGr.

Context {NR : NonnegativeMonoid}
        {X : abgr}.
Context (ap : tightap X).

Definition istriangle1 (f : X → NR) : UU :=
  ∏ x y : X, NnMle NR (f (x + y)) (f x + f y).
Lemma isaprop_istriangle1 (f : X → NR) :
  isaprop (istriangle1 f).
Proof.
  intros f.
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply propproperty.
Qed.

Definition isseparated1 (f : X → NR) : UU :=
  ∏ x : X, ap x 0 <-> NnMgt NR (f x) 0.
Lemma isaprop_isseparated1 (f : X → NR) :
  isaprop (isseparated1 f).
Proof.
  intros f.
  apply impred_isaprop ; intros x.
  apply isapropdirprod ;
  apply isapropimpl, propproperty.
Qed.

Definition isnormgr (norm : X → NR) : UU :=
  (istriangle1 norm)
    × (isseparated1 norm)
    × (∏ x : X, norm (grinv X x) = norm x).
Lemma isaprop_isnormgr (norm : X → NR) :
  isaprop (isnormgr norm).
Proof.
  intros norm.
  apply isapropdirprod.
  apply isaprop_istriangle1.
  apply isapropdirprod.
  apply isaprop_isseparated1.
  apply impred_isaprop ; intros x.
  apply setproperty.
Qed.

End NormGr.

Definition normgr (NR : NonnegativeMonoid) (X : abgr) (ap : tightap X) : UU :=
  ∑ (norm : X → NR), isnormgr ap norm.


Definition normgrpr1 {NR : NonnegativeMonoid} {X : abgr} {ap : tightap X}
                     (norm : normgr NR X ap) : X → NR := pr1 norm.
Coercion normgrpr1 : normgr >-> Funclass.

Section NormGr_pty.

Context {NR : NonnegativeMonoid}
        {X : abgr}
        {ap : tightap X}
        (norm : normgr NR X ap).

Definition istriangle1_normgr : istriangle1 norm :=
  pr1 (pr2 norm).
Definition isseparated1_normgr : isseparated1 ap norm :=
  pr1 (pr2 (pr2 norm)).
Definition normgr_opp :
  ∏ x : X, norm (grinv X x) = norm x :=
  pr2 (pr2 (pr2 norm)).

Lemma isseparated1_normgr' :
  ∏ x : X, norm x = 0 → x = 0.
Proof.
  intros x Hx.
  apply (pr2 (pr2 ap)).
  intros Hx'.
  apply isseparated1_normgr in Hx'.
  revert Hx'.
  apply (pr2 (notNnMgt_le _ _)).
  rewrite Hx.
  apply isrefl_NnMle.
Qed.

Lemma istriangle1_normgr' :
  isrdistr (@NnMmax NR) (@NnMmin NR)
  → ∏ (x y : X),
  NnMle NR (NnMminus (norm x) (norm y)) (norm (x + grinv X y)).
Proof.
  intros H x y.
  apply (notLgt_Lle _ _).
  intros H1.
  apply (NnMplus_gt_r (norm y)) in H1.
  revert H1.
  apply Lle_notLgt.
  rewrite NnMminus_plus.
  apply Lmax_le_case.
  - exact H.
  - set (x' := x).
    change (NnMle NR (norm x) (norm (x' + grinv X y) + norm y)).
    rewrite <- (runax X x), <- (grlinvax X y), <- assocax.
    apply istriangle1_normgr.
  - set (y' := norm y).
    change (NnMle NR y' (norm (x + grinv X y) + norm y)).
    rewrite <- (lunax NR y').
    apply (notLgt_Lle _ _).
    intros H1.
    apply NnMplus_gt_r' in H1.
    revert H1.
    apply isnonnegative_NnM'.
Qed.

End NormGr_pty.

(** * A norm group is a metric space *)

Lemma grinv_opp_r (X : gr) :
  ∏ x y : X, grinv X (x + y) = grinv X y + grinv X x.
Proof.
  intros X x y.
  apply pathsinv0, grtopathsxy.
  rewrite grinvinv.
  rewrite (assocax X (grinv X y)), <- (assocax X (grinv X x)).
  rewrite grlinvax, lunax.
  apply grlinvax.
Qed.

Section NormGr_metric.

Context {NR : NonnegativeMonoid}
        {X : abgr}
        {ap : tightap X}
        (Hap : isbinophrel ap)
        (norm : normgr NR X ap).

Definition normgr_MetricSpace : MetricSet NR (pr1 (pr1 X),,ap).
Proof.
  exists (λ x y : X, norm  (x + (grinv X y))).
  - split ; [ | split].
    + intros x y.
      rewrite <- normgr_opp.
      rewrite (grinv_opp_r X), grinvinv.
      reflexivity.
    + intros x y.
      split.
      * intros H.
        apply (pr1 (isseparated1_normgr _ _)).
        rewrite <- (grrinvax X y).
        apply (pr2 Hap).
        apply H.
      * intros H.
        rewrite <- (runax X x), <- (grlinvax X y), <- assocax.
        set (y' := y).
        change (ap (x + grinv X y' + y') y)%tap.
        rewrite <- (lunax X y).
        apply (pr2 Hap).
        refine (pr2 (isseparated1_normgr _ _) _).
        apply H.
    + intros x y z.
      set (x' := x).
      change (NnMle NR (norm (x + grinv X z)) (norm (x' + grinv X y) + norm (y + grinv X z))).
      rewrite <- (runax X x), <- (grlinvax X y).
      rewrite (assocax X x), (assocax X (grinv X y)), <- (assocax X x).
      apply istriangle1_normgr.
Defined.

End NormGr_metric.

(** * Differentiability *)

Section DiffGr.

Context {NR : NonnegativeMonoid}
        {X Y : abgr}
        {apX : tightap X}
        {apY : tightap Y}
        (normX : normgr NR X apX)
        (normY : normgr NR Y apY)
        (predom : StrongOrder (X → NR)).

Definition isdiffgr (f : X → Y) (x : X) (df : monoidfun X Y) :=
  predom (λ y, normX (y + grinv X x))
         (λ y, normY (f y + grinv Y (f x) + grinv Y (df (y + grinv X x)))).

End DiffGr.