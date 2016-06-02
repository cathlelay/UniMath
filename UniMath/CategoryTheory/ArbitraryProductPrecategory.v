
(** **********************************************************

Anders Mörtberg

2016

Definition of the general product category

************************************************************)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Section arbitrary_product_precategory.

Variable I : UU.
Variables C : precategory.

Definition arbitrary_product_precategory_ob_mor : precategory_ob_mor.
Proof.
mkpair.
- apply (forall (i : I), ob C).
- intros f g.
  apply (forall i, f i --> g i).
Defined.

Definition arbitrary_product_precategory_data : precategory_data.
Proof.
  exists arbitrary_product_precategory_ob_mor.
  split.
  - intros f i; simpl in *.
    apply (identity (f i)).
  - intros a b c f g i; simpl in *.
    exact (f i ;; g i).
Defined.

Lemma is_precategory_arbitrary_product_precategory_data :
  is_precategory arbitrary_product_precategory_data.
Proof.
repeat split; intros; apply funextsec; intro i.
- apply id_left.
- apply id_right.
- apply assoc.
Qed.

Definition arbitrary_product_precategory : precategory
  := tpair _ _ is_precategory_arbitrary_product_precategory_data.

Definition has_homsets_arbitrary_product_precategory (hsC : has_homsets C) :
  has_homsets arbitrary_product_precategory.
Proof.
intros a b; simpl.
apply impred_isaset; intro i; apply hsC.
Qed.

End arbitrary_product_precategory.

Section functors.

Definition arbitrary_pair_functor_data (I : UU) {A B : precategory}
  (F : forall (i : I), functor A B) :
  functor_data (arbitrary_product_precategory I A)
               (arbitrary_product_precategory I B).
Proof.
mkpair.
- intros a i; apply (F i (a i)).
- intros a b f i; apply (# (F i) (f i)).
Defined.

Definition arbitrary_pair_functor (I : UU) {A B : precategory}
  (F : forall (i : I), functor A B) :
  functor (arbitrary_product_precategory I A)
          (arbitrary_product_precategory I B).
Proof.
apply (tpair _ (arbitrary_pair_functor_data I F)).
abstract
  (split; [ intro x; apply funextsec; intro i; simpl; apply functor_id
          | intros x y z f g; apply funextsec; intro i; apply functor_comp]).
Defined.

Definition pr_functor_data (I : UU) (C : precategory) (i : I) :
  functor_data (arbitrary_product_precategory I C) C.
Proof.
mkpair.
- intro a; apply (a i).
- intros x y f; simpl; apply (f i).
Defined.

Definition pr_functor (I : UU) (C : precategory) (i : I) :
  functor (arbitrary_product_precategory I C) C.
Proof.
apply (tpair _ (pr_functor_data I C i)).
abstract (split; intros x *; apply idpath).
Defined.

Definition arbitrary_delta_functor_data (I : UU) (C : precategory) :
  functor_data C (arbitrary_product_precategory I C).
Proof.
mkpair.
- intros x i; apply x.
- intros x y f i; simpl; apply f.
Defined.

Definition arbitrary_delta_functor (I : UU) (C : precategory) :
  functor C (arbitrary_product_precategory I C).
Proof.
apply (tpair _ (arbitrary_delta_functor_data I C)).
abstract (split; intros x *; apply idpath).
Defined.

End functors.