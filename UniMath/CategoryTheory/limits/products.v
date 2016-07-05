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
Require Import UniMath.CategoryTheory.ProductPrecategory.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Section product_def.

Variable (I : UU) (C : precategory).

Definition isProductCone (c : Π (i : I), C) (p : C)
  (pi : Π i, p --> c i) :=
  Π (a : C) (f : Π i, a --> c i),
    iscontr (total2 (fun (fap : a --> p) => Π i, fap ;; pi i = f i)).

Definition ProductCone (ci : Π i, C) :=
   total2 (fun pp1p2 : total2 (fun p : C => Π i, p --> ci i) =>
             isProductCone ci (pr1 pp1p2) (pr2 pp1p2)).

Definition Products := Π (ci : Π i, C), ProductCone ci.
Definition hasProducts := ishinh Products.

Definition ProductObject {c : Π i, C} (P : ProductCone c) : C := pr1 (pr1 P).
Definition ProductPr {c : Π i, C} (P : ProductCone c) : Π i, ProductObject P --> c i :=
  pr2 (pr1 P).

Definition isProductCone_ProductCone {c : Π i, C} (P : ProductCone c) :
   isProductCone c (ProductObject P) (ProductPr P).
Proof.
  exact (pr2 P).
Defined.

Definition ProductArrow {c : Π i, C} (P : ProductCone c) {a : C} (f : Π i, a --> c i)
  : a --> ProductObject P.
Proof.
  apply (pr1 (pr1 (isProductCone_ProductCone P _ f))).
Defined.

Lemma ProductPrCommutes (c : Π i, C) (P : ProductCone c) :
     Π (a : C) (f : Π i, a --> c i) i, ProductArrow P f ;; ProductPr P i = f i.
Proof.
  intros a f i.
  apply (pr2 (pr1 (isProductCone_ProductCone P _ f)) i).
Qed.

Lemma ProductPr_idtoiso {i1 i2 : I} (a : I -> C) (P : ProductCone a)
      (e : i1 = i2) :
  ProductPr P i1 ;; idtoiso (maponpaths a e) = ProductPr P i2.
Proof.
  induction e.
  apply id_right.
Qed.

Lemma ProductArrowUnique (c : Π i, C) (P : ProductCone c) (x : C)
    (f : Π i, x --> c i) (k : x --> ProductObject P)
    (Hk : Π i, k ;; ProductPr P i = f i) : k = ProductArrow P f.
Proof.
  set (H' := pr2 (isProductCone_ProductCone P _ f) (k,,Hk)).
  apply (base_paths _ _ H').
Qed.

Definition mk_ProductCone (a : Π i, C) :
  Π (c : C) (f : Π i, C⟦c,a i⟧), isProductCone _ _ f -> ProductCone a.
Proof.
  intros c f X.
  simple refine (tpair _ (c,,f) X).
Defined.

Definition mk_isProductCone (hsC : has_homsets C) (a : I -> C) (p : C)
  (pa : Π i, C⟦p,a i⟧) : (Π (c : C) (f : Π i, C⟦c,a i⟧),
                                  ∃! k : C⟦c,p⟧, Π i, k ;; pa i = f i) ->
                              isProductCone a p pa.
Proof.
intros H c cc; apply H.
Defined.

Lemma ProductArrowEta (c : Π i, C) (P : ProductCone c) (x : C)
    (f : x --> ProductObject P) :
    f = ProductArrow P (fun i => f ;; ProductPr P i).
Proof.
  now apply ProductArrowUnique.
Qed.

Definition ProductOfArrows {c : Π i, C} (Pc : ProductCone c) {a : Π i, C}
    (Pa : ProductCone a) (f : Π i, a i --> c i) :
      ProductObject Pa --> ProductObject Pc :=
    ProductArrow Pc (fun i => ProductPr Pa i ;; f i).

Lemma ProductOfArrowsPr {c : Π i, C} (Pc : ProductCone c) {a : Π i, C}
    (Pa : ProductCone a) (f : Π i, a i --> c i) :
    Π i, ProductOfArrows Pc Pa f ;; ProductPr Pc i = ProductPr Pa i ;; f i.
Proof.
  unfold ProductOfArrows; intro i.
  now rewrite (ProductPrCommutes _ _ _ _ i).
Qed.

Lemma postcompWithProductArrow {c : Π i, C} (Pc : ProductCone c) {a : Π i, C}
    (Pa : ProductCone a) (f : Π i, a i --> c i)
    {x : C} (k : Π i, x --> a i) :
        ProductArrow Pa k ;; ProductOfArrows Pc Pa f =
        ProductArrow Pc (fun i => k i ;; f i).
Proof.
apply ProductArrowUnique; intro i.
now rewrite <- assoc, ProductOfArrowsPr, assoc, ProductPrCommutes.
Qed.

Lemma precompWithProductArrow {c : Π i, C} (Pc : ProductCone c)
  {a : C} (f : Π i, a --> c i) {x : C} (k : x --> a)  :
       k ;; ProductArrow Pc f = ProductArrow Pc (fun i => k ;; f i).
Proof.
apply ProductArrowUnique; intro i.
now rewrite <- assoc, ProductPrCommutes.
Qed.

End product_def.

Section Products.

Variables (I : UU) (C : precategory) (CC : Products I C).

Definition ProductOfArrows_comp (a b c : Π (i : I), C)
  (f : Π i, a i --> b i) (g : Π i, b i --> c i)
  : ProductOfArrows _ _ _ _ f ;; ProductOfArrows _ _ _ (CC _) g
    = ProductOfArrows _ _ (CC _) (CC _) (fun i => f i ;; g i).
Proof.
apply ProductArrowUnique; intro i.
rewrite <- assoc, ProductOfArrowsPr.
now rewrite assoc, ProductOfArrowsPr, assoc.
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
Variable CC : Products I C.
Variables a : Π (i : I), C.

Lemma Product_endo_is_identity (P : ProductCone _ _ a)
  (k : ProductObject _ _ P --> ProductObject _ _ P)
  (H1 : Π i, k ;; ProductPr _ _ P i = ProductPr _ _ P i)
  : identity _ = k.
Proof.
  apply pathsinv0.
  eapply pathscomp0.
  apply ProductArrowEta.
  apply pathsinv0.
  apply ProductArrowUnique; intro i; apply pathsinv0.
  now rewrite id_left, H1.
Qed.

End Product_unique.

(* The arbitrary product functor: C^I -> C *)
Section product_functor.

Context (I : UU) {C : precategory} (PC : Products I C).

Definition product_functor_data :
  functor_data (power_precategory I C) C.
Proof.
mkpair.
- intros p.
  apply (ProductObject _ _ (PC p)).
- simpl; intros p q f.
  exact (ProductOfArrows _ _ _ _ f).
Defined.

Definition product_functor : functor (power_precategory I C) C.
Proof.
apply (tpair _ product_functor_data).
abstract (split;
  [ now intro x; simpl; apply pathsinv0, Product_endo_is_identity;
        intro i; rewrite ProductOfArrowsPr, id_right
  | now intros x y z f g; simpl; rewrite ProductOfArrows_comp]).
Defined.

End product_functor.

(* The product of a family of functors *)
Definition product_of_functors_alt
  (I : UU) {C D : precategory} (HD : Products I D)
  (F : Π (i : I), functor C D) : functor C D :=
   functor_composite (delta_functor I C)
     (functor_composite (pair_functor _ F) (product_functor _ HD)).
