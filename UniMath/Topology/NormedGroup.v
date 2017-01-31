(** * Results about Metric Spaces *)
(** Author: Catherine LELAY. Jan 2017 - *)

Require Export UniMath.Algebra.Lattice.
Require Import UniMath.Topology.Prelim.
Require Export UniMath.Topology.Filters.
Require Import UniMath.Topology.Topology.
Require Import UniMath.Topology.UniformSpace.
Require Import UniMath.Algebra.Apartness.
Require Import UniMath.Topology.MetricSpace.

Set Default Timeout 5.

(** * Normed Group *)

Local Open Scope addmonoid.

Section NormGr.

Context {NR : NonnegativeMonoid}
        {X : abgr}.
Context (ap : tightap X).

Definition istriangle1 (f : X → NR) : UU :=
  Π x y : X, NnMle NR (f (x + y)) (f x + f y).
Lemma isaprop_istriangle1 (f : X → NR) :
  isaprop (istriangle1 f).
Proof.
  intros f.
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply propproperty.
Qed.

Definition isseparated1 (f : X → NR) : UU :=
  Π x : X, ap x 0 → NnMgt NR (f x) 0.
Lemma isaprop_isseparated1 (f : X → NR) :
  isaprop (isseparated1 f).
Proof.
  intros f.
  apply impred_isaprop ; intros x.
  apply isapropimpl.
  apply propproperty.
Qed.

Definition isnormgr (norm : X → NR) : UU :=
  (istriangle1 norm) × (isseparated1 norm).
Lemma isaprop_isnormgr (norm : X → NR) :
  isaprop (isnormgr norm).
Proof.
  intros norm.
  apply isapropdirprod.
  apply isaprop_istriangle1.
  apply isaprop_isseparated1.
Qed.

End NormGr.

Definition normgr (NR : NonnegativeMonoid) (X : abgr) (ap : tightap X) : UU :=
  Σ (norm : X → NR), isnormgr ap norm.


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
  pr2 (pr2 norm).

Lemma isseparated1_normgr' :
  Π x : X, norm x = 0 → x = 0.
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

End NormGr_pty.