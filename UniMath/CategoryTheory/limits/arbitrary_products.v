(*

Direct implementation of arbitrary products.

Written by: Anders Mörtberg 2016

*)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.ArbitraryProductPrecategory.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Section product_def.

Variable (I : UU) (C : precategory).

Definition isArbitraryProductCone (c : forall (i : I), C) (p : C)
  (pi : forall i, p --> c i) :=
  forall (a : C) (f : forall i, a --> c i),
    iscontr (total2 (fun (fap : a --> p) => forall i, fap ;; pi i = f i)).

Definition ArbitraryProductCone (ci : forall i, C) :=
   total2 (fun pp1p2 : total2 (fun p : C => forall i, p --> ci i) =>
             isArbitraryProductCone ci (pr1 pp1p2) (pr2 pp1p2)).

Definition ArbitraryProducts := forall (ci : forall i, C), ArbitraryProductCone ci.
Definition hasArbitraryProducts := ishinh ArbitraryProducts.

Definition ArbitraryProductObject {c : forall i, C} (P : ArbitraryProductCone c) : C := pr1 (pr1 P).
Definition ArbitraryProductPr {c : forall i, C} (P : ArbitraryProductCone c) : forall i, ArbitraryProductObject P --> c i :=
  pr2 (pr1 P).

Definition isArbitraryProductCone_ArbitraryProductCone {c : forall i, C} (P : ArbitraryProductCone c) :
   isArbitraryProductCone c (ArbitraryProductObject P) (ArbitraryProductPr P).
Proof.
  exact (pr2 P).
Defined.

Definition ArbitraryProductArrow {c : forall i, C} (P : ArbitraryProductCone c) {a : C} (f : forall i, a --> c i)
  : a --> ArbitraryProductObject P.
Proof.
  apply (pr1 (pr1 (isArbitraryProductCone_ArbitraryProductCone P _ f))).
Defined.

Lemma ArbitraryProductPrCommutes (c : forall i, C) (P : ArbitraryProductCone c) :
     forall (a : C) (f : forall i, a --> c i) i, ArbitraryProductArrow P f ;; ArbitraryProductPr P i = f i.
Proof.
  intros a f i.
  apply (pr2 (pr1 (isArbitraryProductCone_ArbitraryProductCone P _ f)) i).
Qed.

Lemma ArbitraryProductArrowUnique (c : forall i, C) (P : ArbitraryProductCone c) (x : C)
    (f : forall i, x --> c i) (k : x --> ArbitraryProductObject P)
    (Hk : forall i, k ;; ArbitraryProductPr P i = f i) : k = ArbitraryProductArrow P f.
Proof.
  set (H' := pr2 (isArbitraryProductCone_ArbitraryProductCone P _ f) (k,,Hk)).
  apply (base_paths _ _ H').
Qed.

Definition mk_ArbitraryProductCone (a : forall i, C) :
  ∀ (c : C) (f : forall i, C⟦c,a i⟧), isArbitraryProductCone _ _ f -> ArbitraryProductCone a.
Proof.
  intros c f X.
  simple refine (tpair _ (c,,f) X).
Defined.

Definition mk_isArbitraryProductCone (hsC : has_homsets C) (a : I -> C) (p : C)
  (pa : forall i, C⟦p,a i⟧) : (∀ (c : C) (f : forall i, C⟦c,a i⟧),
                                  ∃! k : C⟦c,p⟧, forall i, k ;; pa i = f i) ->
                              isArbitraryProductCone a p pa.
Proof.
intros H c cc; apply H.
Defined.

Lemma ArbitraryProductArrowEta (c : forall i, C) (P : ArbitraryProductCone c) (x : C)
    (f : x --> ArbitraryProductObject P) :
    f = ArbitraryProductArrow P (fun i => f ;; ArbitraryProductPr P i).
Proof.
  now apply ArbitraryProductArrowUnique.
Qed.

Definition ArbitraryProductOfArrows {c : forall i, C} (Pc : ArbitraryProductCone c) {a : forall i, C}
    (Pa : ArbitraryProductCone a) (f : forall i, a i --> c i) :
      ArbitraryProductObject Pa --> ArbitraryProductObject Pc :=
    ArbitraryProductArrow Pc (fun i => ArbitraryProductPr Pa i ;; f i).

Lemma ArbitraryProductOfArrowsPr {c : forall i, C} (Pc : ArbitraryProductCone c) {a : forall i, C}
    (Pa : ArbitraryProductCone a) (f : forall i, a i --> c i) :
    forall i, ArbitraryProductOfArrows Pc Pa f ;; ArbitraryProductPr Pc i = ArbitraryProductPr Pa i ;; f i.
Proof.
  unfold ArbitraryProductOfArrows; intro i.
  now rewrite (ArbitraryProductPrCommutes _ _ _ _ i).
Qed.

Lemma postcompWithArbitraryProductArrow {c : forall i, C} (Pc : ArbitraryProductCone c) {a : forall i, C}
    (Pa : ArbitraryProductCone a) (f : forall i, a i --> c i)
    {x : C} (k : forall i, x --> a i) :
        ArbitraryProductArrow Pa k ;; ArbitraryProductOfArrows Pc Pa f =
        ArbitraryProductArrow Pc (fun i => k i ;; f i).
Proof.
apply ArbitraryProductArrowUnique; intro i.
now rewrite <- assoc, ArbitraryProductOfArrowsPr, assoc, ArbitraryProductPrCommutes.
Qed.

Lemma precompWithArbitraryProductArrow {c : forall i, C} (Pc : ArbitraryProductCone c)
  {a : C} (f : forall i, a --> c i) {x : C} (k : x --> a)  :
       k ;; ArbitraryProductArrow Pc f = ArbitraryProductArrow Pc (fun i => k ;; f i).
Proof.
apply ArbitraryProductArrowUnique; intro i.
now rewrite <- assoc, ArbitraryProductPrCommutes.
Qed.

End product_def.

Section Products.

Variables (I : UU) (C : precategory) (CC : ArbitraryProducts I C).

Definition ArbitraryProductOfArrows_comp (a b c : forall (i : I), C)
  (f : forall i, a i --> b i) (g : forall i, b i --> c i)
  : ArbitraryProductOfArrows _ _ _ _ f ;; ArbitraryProductOfArrows _ _ _ (CC _) g
    = ArbitraryProductOfArrows _ _ (CC _) (CC _) (fun i => f i ;; g i).
Proof.
apply ArbitraryProductArrowUnique; intro i.
rewrite <- assoc, ArbitraryProductOfArrowsPr.
now rewrite assoc, ArbitraryProductOfArrowsPr, assoc.
Qed.

(* Definition ProductOfArrows_eq (f f' : a --> c) (g g' : b --> d) *)
(*   : f = f' → g = g' → *)
(*       ProductOfArrows _ _ _ f g = ProductOfArrows _ (CC _ _) (CC _ _) f' g'. *)
(* Proof. *)
(*   induction 1. *)
(*   induction 1. *)
(*   apply idpath. *)
(* Qed. *)

End Products.

Section Product_unique.

Variables (I : UU) (C : precategory).
Variable CC : ArbitraryProducts I C.
Variables a : forall (i : I), C.

Lemma ArbitraryProduct_endo_is_identity (P : ArbitraryProductCone _ _ a)
  (k : ArbitraryProductObject _ _ P --> ArbitraryProductObject _ _ P)
  (H1 : forall i, k ;; ArbitraryProductPr _ _ P i = ArbitraryProductPr _ _ P i)
  : identity _ = k.
Proof.
  apply pathsinv0.
  eapply pathscomp0.
  apply ArbitraryProductArrowEta.
  apply pathsinv0.
  apply ArbitraryProductArrowUnique; intro i; apply pathsinv0.
  now rewrite id_left, H1.
Qed.

End Product_unique.

(* The arbitrary product functor: C^I -> C *)
Section arbitrary_product_functor.

Context (I : UU) {C : precategory} (PC : ArbitraryProducts I C).

Definition arbitrary_product_functor_data :
  functor_data (arbitrary_product_precategory I C) C.
Proof.
mkpair.
- intros p.
  apply (ArbitraryProductObject _ _ (PC p)).
- simpl; intros p q f.
  exact (ArbitraryProductOfArrows _ _ _ _ f).
Defined.

Definition arbitrary_product_functor : functor (arbitrary_product_precategory I C) C.
Proof.
apply (tpair _ arbitrary_product_functor_data).
abstract (split;
  [ now intro x; simpl; apply pathsinv0, ArbitraryProduct_endo_is_identity;
        intro i; rewrite ArbitraryProductOfArrowsPr, id_right
  | now intros x y z f g; simpl; rewrite ArbitraryProductOfArrows_comp]).
Defined.

End arbitrary_product_functor.

(* The product of a family of functors *)
Definition arbitrary_product_of_functors (I : UU) {C D : precategory} (HD : ArbitraryProducts I D)
  (F : forall (i : I), functor C D) : functor C D :=
   functor_composite (arbitrary_delta_functor I C)
     (functor_composite (arbitrary_pair_functor _ F) (arbitrary_product_functor _ HD)).
