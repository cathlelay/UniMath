(** * Uniform Space *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Export UniMath.Bourbaki.Complements.
Require Import UniMath.Dedekind.Complements.
Require Export UniMath.Bourbaki.Filters.

(** ** Definitions *)

Definition subset_prod {X : UU} (A B : X × X -> hProp) :=
  λ x : X × X, ∃ y : X, A (pr1 x,,y) ∧ B (y ,, pr2 x).
Definition subset_square {X : UU} (A : X × X -> hProp) :=
  subset_prod A A.
Definition subset_inv {X : UU} (A : X × X -> hProp) :=
  λ x : X × X, A (pr2 x ,, pr1 x).

(** *** Uniform Structures *)

Definition isUF_diag {X : UU} (F : (X × X -> hProp) -> hProp) :=
  ∀ P, F P -> ∀ x : X, P (x ,, x).
Definition isUF_symm {X : UU} (F : (X × X -> hProp) -> hProp) :=
  ∀ P, F P -> F (subset_inv P).
Definition isUF_square {X : UU} (F : (X × X -> hProp) -> hProp) :=
  ∀ P, F P -> ∃ Q, F Q × ∀ x : X × X, subset_square Q x -> P x.

Definition isUF_prod_inv {X : UU} (F : (X × X -> hProp) -> hProp) :=
  ∀ P, F P -> ∃ Q, F Q × ∀ x : X × X, subset_prod Q (subset_inv Q) x -> P x.

Lemma isUF_prod_inv_imply_symm {X : UU} (F : (X × X -> hProp) -> hProp) :
  (isfilter_imply (X := X × X) F) -> (F (λ _ : X × X, htrue)) -> (∀ A B : X × X → hProp, F A → F B → F (λ x : X × X, A x ∧ B x))
  -> (isUF_diag F) -> isUF_prod_inv F -> isUF_symm F.
Proof.
  intros X F Himpl Htrue Hand Hdiag H.
  intros P FP.
  generalize (H P FP).
  apply hinhuniv.
  intros (Q,(FQ,HQ)).
  apply Himpl with (2 := FQ).
  intros x Qx.
  apply HQ.
  apply hinhpr ; simpl.
  exists (pr2 x) ; split.
  now apply Hdiag.
  now destruct x.
Qed.
Lemma isUF_prod_inv_imply_square {X : UU} (F : (X × X -> hProp) -> hProp) :
  (isfilter_imply (X := X × X) F) -> (F (λ _ : X × X, htrue)) -> (∀ A B : X × X → hProp, F A → F B → F (λ x : X × X, A x ∧ B x))
  -> (isUF_diag F) -> isUF_prod_inv F -> isUF_square F.
Proof.
  intros X F Himpl Htrue Hand Hdiag H.
  intros P FP.
  generalize (H P FP).
  apply hinhfun.
  intros (Q,(FQ,HQ)).
  exists (λ x, Q x ∧ subset_inv Q x).
  split.
  - apply Hand.
    exact FQ.
    now apply isUF_prod_inv_imply_symm.
  - intros x Hx.
    apply HQ.
    revert Hx.
    apply hinhfun.
    intros (y,((Qy1,_),(_,Qy2))).
    now exists y.
Qed.

Lemma isUF_symm_square_imply_prod_inv {X : UU} (F : (X × X -> hProp) -> hProp) :
  (isfilter_imply (X := X × X) F) -> (F (λ _ : X × X, htrue)) -> (∀ A B : X × X → hProp, F A → F B → F (λ x : X × X, A x ∧ B x))
  -> (isUF_diag F) -> isUF_symm F -> isUF_square F -> isUF_prod_inv F.
Proof.
  intros X F Himpl Htrue Hand Hdiag Hsymm Hsqr.
  intros P FP.
  generalize (Hsqr P FP).
  apply hinhfun.
  intros (Q,(FQ,HQ)).
  exists (λ x, Q x ∧ subset_inv Q x).
  split.
  - apply Hand.
    exact FQ.
    now apply Hsymm.
  - intros x Hx.
    apply HQ.
    revert Hx.
    apply hinhfun.
    intros (y,((Qy1,_),(_,Qy2))).
    now exists y.
Qed.

Definition isUniformStructure {X : UU} F :=
  (isfilter_imply (X := X × X) F)
    × (isfilter_finite_intersection F)
    × (isUF_diag F)
    × (isUF_symm F)
    × (isUF_square F).

Definition UniformStructure (X : UU) :=
  Σ (F : (X × X -> hProp) -> hProp), isUniformStructure F.
Definition pr1UniformStructure (X : UU) : UniformStructure X -> ((X × X -> hProp) -> hProp) := pr1.
Coercion pr1UniformStructure : UniformStructure >-> Funclass.

Definition mkUniformStructure {X : UU} (F : (X × X -> hProp) -> hProp)
           (Himpl : isfilter_imply (X := X × X) F) (Htrue : F (λ _ : X × X, htrue))
           (Hand : ∀ A B : X × X → hProp, F A → F B → F (λ x : X × X, A x ∧ B x))
           (Hdiag : isUF_diag F) (Hsymm : isUF_symm F) (Hsquare : isUF_square F) :
  UniformStructure X :=
  F,, Himpl,, isfilter_finite_intersection_carac F Htrue Hand,, Hdiag,, Hsymm,, Hsquare.

Lemma UniformeStructure_isfilter {X : UU}
      (x0 : ∥ X ∥) (F : UniformStructure X) : isfilter F.
Proof.
  intros X x0 F.
  repeat split.
  - apply (pr1 (pr2 F)).
  - apply (pr1 (pr2 (pr2 F))).
  - intro H.
    revert x0.
    apply hinhuniv'.
    exact isapropempty.
    intros x0.
    apply ((pr1 (pr2 (pr2 (pr2 F)))) _ H).
    exact x0.
Qed.

(** *** Uniform Space *)

Definition UniformSpace :=
  Σ (X : UU), UniformStructure X.
Definition pr1UniformSpace : UniformSpace -> UU := pr1.
Coercion pr1UniformSpace : UniformSpace >-> UU.
