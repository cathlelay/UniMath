(** **********************************************************

Contents :

- Definition of the product of two signatures, in particular proof of
     strength laws for the product


Written by Anders Mörtberg, 2016 (adapted from SumOfSignatures.v)


************************************************************)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.CategoryTheory.chains.
Require Import UniMath.CategoryTheory.cocontfunctors.
Require Import UniMath.CategoryTheory.exponentials.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite _ _ _ F G) (at level 35).

Arguments θ_source {_ _} _ .
Arguments θ_target {_ _} _ .
Arguments θ_Strength1 {_ _ _} _ .
Arguments θ_Strength2 {_ _ _} _ .
Arguments θ_Strength1_int {_ _ _} _ .
Arguments θ_Strength2_int {_ _ _} _ .

Section product_of_signatures.

Variable C : precategory.
Variable hsC : has_homsets C.
Variable PC : Products C.

Section construction.

Local Notation "'CCC'" := (Products_functor_precat C C PC hsC : Products [C, C, hsC]).

Variables H1 H2 : functor [C, C, hsC] [C, C, hsC].

Variable θ1 : θ_source H1 ⟶ θ_target H1.
Variable θ2 : θ_source H2 ⟶ θ_target H2.

Variable S11 : θ_Strength1 θ1.
Variable S12 : θ_Strength2 θ1.
Variable S21 : θ_Strength1 θ2.
Variable S22 : θ_Strength2 θ2.

(** * Definition of the data of the product of two signatures *)

Definition H : functor [C, C, hsC] [C, C, hsC] := product_functor _ _ CCC H1 H2.

Local Definition bla1 (X : [C, C, hsC]) (Z : precategory_Ptd C hsC) :
   ∀ c : C,
    (functor_composite_data (pr1 Z)
     (product_functor_data C C PC (H1 X) (H2 X))) c
   --> (product_functor_data C C PC (H1 (functor_composite (pr1 Z) X))
       (H2 (functor_composite (pr1 Z) X))) c.
Proof.
  intro c.
  apply ProductOfArrows.
  - exact (pr1 (θ1 (X ⊗ Z)) c).
  - exact (pr1 (θ2 (X ⊗ Z)) c).
Defined.

Local Lemma bar (X : [C, C, hsC]) (Z : precategory_Ptd C hsC):
   is_nat_trans
     (functor_composite_data (pr1 Z)
        (product_functor_data C C PC (H1 X) (H2 X)))
     (product_functor_data C C PC (H1 (functor_composite (pr1 Z) X))
        (H2 (functor_composite (pr1 Z) X))) (bla1 X Z).
Proof.
  intros x x' f; simpl.
  unfold bla1; simpl.
  unfold product_functor_mor.
  eapply pathscomp0; [ apply ProductOfArrows_comp | ].
  eapply pathscomp0; [ | eapply pathsinv0; apply ProductOfArrows_comp].
  apply ProductOfArrows_eq.
  * apply (nat_trans_ax (θ1 (X ⊗ Z))).
  * apply (nat_trans_ax (θ2 (X ⊗ Z))).
Qed.

Local Definition bla (X : [C, C, hsC]) (Z : precategory_Ptd C hsC) :
   functor_composite_data (pr1 Z)
     (product_functor_data C C PC (H1 X) (H2 X))
   ⟶ product_functor_data C C PC (H1 (functor_composite (pr1 Z) X))
       (H2 (functor_composite (pr1 Z) X)).
Proof.
  exists (bla1 X Z).
  apply bar.
Defined.


Definition θ_ob : ∀ XF, θ_source H XF --> θ_target H XF.
Proof.
  intro XZ.
  destruct XZ as [X Z].
  apply bla.
Defined.


Local Lemma is_nat_trans_θ_ob :
 is_nat_trans (θ_source_functor_data C hsC H) (θ_target_functor_data C hsC H)
     θ_ob.
Proof.
  intros XZ X'Z' αβ.
  assert (Hyp1:= nat_trans_ax θ1 _ _ αβ).
  assert (Hyp2:= nat_trans_ax θ2 _ _ αβ).
  apply nat_trans_eq.
  - exact hsC.
  - intro c; simpl.
    destruct XZ as [X Z].
    destruct X'Z' as [X' Z'].
    destruct αβ as [α β]. simpl in *.
    unfold product_nat_trans_data;
    unfold bla1; simpl.
    unfold product_functor_mor.
    unfold product_nat_trans_pr2_data.
    unfold product_nat_trans_pr1_data.
    eapply pathscomp0; [ | eapply pathsinv0; apply ProductOfArrows_comp].
    eapply pathscomp0. apply cancel_postcomposition. apply ProductOfArrows_comp.
    eapply pathscomp0. apply ProductOfArrows_comp.
    apply ProductOfArrows_eq.
    + apply (nat_trans_eq_pointwise Hyp1 c).
    + apply (nat_trans_eq_pointwise Hyp2 c).
Qed.

Local Definition θ : θ_source H ⟶ θ_target H.
Proof.
  exists θ_ob.
  apply is_nat_trans_θ_ob.
Defined.

(** * Proof of the laws of the product of two signatures *)

Lemma ProductStrength1 : θ_Strength1 θ.
Proof.
  unfold θ_Strength1.
  intro X.
  apply nat_trans_eq.
  - apply hsC.
  - intro x.
    simpl.
    unfold bla1.
    unfold product_nat_trans_data.

    eapply pathscomp0. apply ProductOfArrows_comp.
     apply pathsinv0.
     apply Product_endo_is_identity.
     + rewrite ProductOfArrowsPr1.
       unfold θ_Strength1 in S11.
       assert (Ha := nat_trans_eq_pointwise (S11 X) x).
       eapply pathscomp0; [ | apply id_right].
       apply maponpaths.
       apply Ha.
     + rewrite ProductOfArrowsPr2.
       unfold θ_Strength1 in S21.
       assert (Ha := nat_trans_eq_pointwise (S21 X) x).
       eapply pathscomp0; [ | apply id_right].
       apply maponpaths.
       apply Ha.
Qed.

Lemma ProductStrength2 : θ_Strength2 θ.
Proof.
  intros X Z Z' Y α.
  apply (nat_trans_eq hsC).
    intro x.
    eapply pathscomp0. apply ProductOfArrows_comp.
    apply pathsinv0.
    eapply pathscomp0. apply cancel_postcomposition. simpl. apply ProductOfArrows_comp.
    eapply pathscomp0. apply ProductOfArrows_comp.
    apply pathsinv0.
    apply ProductOfArrows_eq.
       - assert (Ha:=S12 X Z Z' Y α).
         simpl in Ha.
         assert (Ha_x := nat_trans_eq_pointwise Ha x).
         apply Ha_x.
       - assert (Ha:=S22 X Z Z' Y α).
         simpl in Ha.
         assert (Ha_x := nat_trans_eq_pointwise Ha x).
         apply Ha_x.
Qed.

Variable S11' : θ_Strength1_int θ1.
Variable S12' : θ_Strength2_int θ1.
Variable S21' : θ_Strength1_int θ2.
Variable S22' : θ_Strength2_int θ2.

Lemma ProductStrength1' : θ_Strength1_int θ.
Proof.
  clear S11 S12 S21 S22 S12' S22'.
  unfold θ_Strength1_int.
  intro X.
  apply nat_trans_eq.
  - apply hsC.
  - intro x.
    simpl.
    unfold bla1.
    unfold product_nat_trans_data.

    eapply pathscomp0. apply ProductOfArrows_comp.
     apply pathsinv0.
     apply Product_endo_is_identity.
     + rewrite ProductOfArrowsPr1.
       red in S11'.
       assert (Ha := nat_trans_eq_pointwise (S11' X) x).
       simpl in Ha.
       eapply pathscomp0; [ | apply id_right].
       apply maponpaths.
       apply Ha.
     + rewrite ProductOfArrowsPr2.
       red in S21'.
       assert (Ha := nat_trans_eq_pointwise (S21' X) x).
       simpl in Ha.
       eapply pathscomp0; [ | apply id_right].
       apply maponpaths.
       apply Ha.
Qed.


Lemma ProductStrength2' : θ_Strength2_int θ.
Proof.
  clear S11 S12 S21 S22 S11' S21'.
  unfold θ_Strength2_int.
  intros X Z Z'.
  apply nat_trans_eq; try assumption.
    intro x.
    simpl.
    rewrite id_left.
    eapply pathscomp0. apply ProductOfArrows_comp.
    apply pathsinv0.
    eapply pathscomp0. apply ProductOfArrows_comp.
    apply pathsinv0.
    apply ProductOfArrows_eq.
       - assert (Ha:=S12' X Z Z').
         simpl in Ha.
         assert (Ha_x := nat_trans_eq_pointwise Ha x).
         simpl in Ha_x.
         rewrite id_left in Ha_x.
         apply Ha_x.
       - assert (Ha:=S22' X Z Z').
         simpl in Ha.
         assert (Ha_x := nat_trans_eq_pointwise Ha x).
         simpl in Ha_x.
         rewrite id_left in Ha_x.
         apply Ha_x.
Qed.

End construction.


Definition Product_of_Signatures (S1 S2: Signature C hsC): Signature C hsC.
Proof.
  destruct S1 as [H1 [θ1 [S11' S12']]].
  destruct S2 as [H2 [θ2 [S21' S22']]].
  exists (H H1 H2).
  exists (θ H1 H2 θ1 θ2).
  split.
  + apply ProductStrength1'; assumption.
  + apply ProductStrength2'; assumption.
Defined.

Lemma is_omega_cocont_Product_of_Signatures (S1 S2 : Signature C hsC)
  (h1 : is_omega_cocont S1) (h2 : is_omega_cocont S2)
  (hE : has_exponentials (Products_functor_precat C C PC hsC)) :
  is_omega_cocont (Product_of_Signatures S1 S2).
Proof.
destruct S1 as [F1 [F2 [F3 F4]]]; simpl in *.
destruct S2 as [G1 [G2 [G3 G4]]]; simpl in *.
unfold H.
apply is_omega_cocont_product_functor; try assumption.
- apply (Products_functor_precat _ _ PC).
- apply functor_category_has_homsets.
- apply functor_category_has_homsets.
Defined.

End product_of_signatures.
