(** * Uniform Space *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Import UniMath.Algebra.BinaryOperations.
Require Export UniMath.Topology.Prelim.
Require Export UniMath.Topology.Filters.

Unset Automatic Introduction.

(** ** Uniform Spaces *)
(** *** Definitions *)

Definition subset_prod {X : UU} (A B : X → X → hProp) :=
  λ x z : X, ∃ y : X, A x y ∧ B y z.
Definition subset_square {X : UU} (A : X → X → hProp) :=
  subset_prod A A.
Definition subset_inv {X : UU} (A : X → X → hProp) :=
  λ x y : X, A y x.
Definition subset_pow {X : hSet} (A : X → X → hProp) (n : nat) : X → X → hProp.
Proof.
  intros X A n.
  induction n as [ | n _].
  - exact (λ x y : X, hProppair (x = y) (pr2 X _ _)).
  - induction n as [ | n subset_pow].
    + exact A.
    + exact (subset_prod A subset_pow).
Defined.
Lemma subset_pow_S {X : hSet} (A : X → X → hProp) (n : nat) :
  subset_pow A (S n) = subset_prod A (subset_pow A n).
Proof.
  intros X A n.
  induction n as [ | n _].
  - apply funextfun ; intros x.
    apply funextfun ; intros y.
    apply hPropUnivalence.
    + intros Ha ; apply hinhpr.
      exists y.
      easy.
    + apply hinhuniv.
      simpl.
      intros z.
      rewrite <- (pr2 (pr2 z)).
      exact (pr1 (pr2 z)).
  - reflexivity.
Qed.

Lemma isassoc_subset_prod {X : hSet} :
  isassoc (λ A B xy, subset_prod (λ x y : X, A (x,,y)) (λ x y : X, B (x,,y)) (pr1 xy) (pr2 xy)).
Proof.
  intros X.
  intros A B C.
  apply funextfun.
  intros xy.
  apply hPropUnivalence.
  - apply hinhuniv.
    intros z.
    generalize (pr1 (pr2 z)).
    apply hinhfun.
    intros y.
    exists (pr1 y).
    split.
    exact (pr1 (pr2 y)).
    apply hinhpr.
    exists (pr1 z) ; split.
    exact (pr2 (pr2 y)).
    exact (pr2 (pr2 z)).
  - apply hinhuniv.
    intros y.
    generalize (pr2 (pr2 y)).
    apply hinhfun.
    intros z.
    exists (pr1 z).
    split.
    apply hinhpr.
    exists (pr1 y) ; split.
    exact (pr1 (pr2 y)).
    exact (pr1 (pr2 z)).
    exact (pr2 (pr2 z)).
Qed.

Lemma isdiag_square {X : UU} (A : X → X → hProp) :
  (∏ x : X, A x x) -> ∏ x y, A x y -> subset_square A x y.
Proof.
  intros X A Hdiag x y Axy.
  apply hinhpr.
  exists x.
  split.
  now apply Hdiag.
  exact Axy.
Qed.

(** Def 1: Uniform Space *)

Definition isUS_imply {X : UU} (F : (X → X → hProp) -> hProp) :=
  ∏ P Q : X → X → hProp, (∏ x y : X, P x y → Q x y) → F P → F Q.
Definition isUS_finite_intersection {X : UU} (F : (X → X → hProp) → hProp) :=
  ∏ (L : Sequence (X → X → hProp)),
  (∏ n : stn (length L), F (L n))
  → F (λ x y : X, finite_intersection (X := X × X) (functionToSequence (λ (n : stn (length L)) (xy : X × X), L n (pr1 xy) (pr2 xy))) (x,,y)).
Definition isUS_htrue {X : UU} (F : (X → X → hProp) → hProp) :=
  F (λ _ _ : X, htrue).
Definition isUS_and {X : UU} (F : (X → X → hProp) → hProp) :=
∏ A B : X → X → hProp, F A → F B → F (λ x y : X, A x y ∧ B x y).
Definition isUS_diag {X : UU} (F : (X → X → hProp) -> hProp) :=
  ∏ P, F P -> ∏ x : X, P x x.
Definition isUS_symm {X : UU} (F : (X → X → hProp) -> hProp) :=
  ∏ P, F P -> F (subset_inv P).
Definition isUS_squareroot {X : UU} (F : (X → X → hProp) -> hProp) :=
  ∏ P, F P -> ∃ Q, F Q × ∏ x y : X, subset_square Q x y -> P x y.

Definition isUS_prod_inv {X : UU} (F : (X → X → hProp) -> hProp) :=
  ∏ P, F P -> ∃ Q, F Q × ∏ x y : X, subset_prod Q (subset_inv Q) x y -> P x y.

Lemma isUS_filter_imply {X : UU} (F : (X → X → hProp) -> hProp) :
  isUS_imply F
  <-> isfilter_imply (λ A : X × X → hProp, F (λ x y : X, A (x,,y))).
Proof.
  intros X F.
  split.
  - intros Hf A B H.
    apply Hf.
    intros x y.
    apply H.
  - intros Hf A B H.
    apply (Hf (λ xy, A (pr1 xy) (pr2 xy)) (λ xy, B (pr1 xy) (pr2 xy)) (λ _, H _ _)).
Qed.
Lemma isUS_filter_finite_intersection {X : UU} (F : (X → X → hProp) → hProp) :
  isUS_finite_intersection F
  <-> isfilter_finite_intersection (λ A : X × X → hProp, F (λ x y : X, A (x,,y))).
Proof.
  intros X F.
  split.
  - intros Hf L Hl.
    apply (Hf (functionToSequence (λ (n : stn (length L)) (x y : X), L n (x,,y)))).
    intros n ; apply Hl.
  - intros Hf L Hl.
    apply Hf.
    intros n ; apply Hl.
Qed.
Lemma isUS_filter_htrue {X : UU} (F : (X → X → hProp) → hProp) :
  isUS_htrue F <-> isfilter_htrue (λ A : X × X → hProp, F (λ x y : X, A (x,,y))).
Proof.
  intros X F.
  split ;
  intros Hf ; apply Hf.
Qed.
Lemma isUS_filter_and {X : UU} (F : (X → X → hProp) → hProp) :
  isUS_and F <-> isfilter_and (λ A : X × X → hProp, F (λ x y : X, A (x,,y))).
Proof.
  intros X F.
  split.
  - intros Hf A B.
    apply Hf.
  - intros Hf A B.
    apply (Hf (λ xy, A (pr1 xy) (pr2 xy)) (λ xy, B (pr1 xy) (pr2 xy))).
Qed.

Lemma isUS_finite_intersection_carac {X : UU} (F : (X → X → hProp) → hProp) :
  isUS_htrue F → isUS_and F → isUS_finite_intersection F.
Proof.
  intros X F Htrue Hand.
  apply (pr2 (isUS_filter_finite_intersection _)).
  apply isfilter_finite_intersection_carac.
  apply (pr1 (isUS_filter_htrue _)), Htrue.
  apply (pr1 (isUS_filter_and _)), Hand.
Qed.

Lemma isUS_prod_inv_imply_symm {X : UU} (F : (X → X → hProp) -> hProp) :
  (isUS_imply F) -> (isUS_diag F) -> isUS_prod_inv F -> isUS_symm F.
Proof.
  intros X F Himpl Hdiag H.
  intros P FP.
  generalize (H P FP).
  apply hinhuniv.
  intros Q.
  apply Himpl with (2 := pr1 (pr2 Q)).
  intros x y Qx.
  apply (pr2 (pr2 Q)).
  apply hinhpr ; simpl.
  exists y ; split.
  apply Hdiag, (pr1 (pr2 Q)).
  exact Qx.
Qed.
Lemma isUS_prod_inv_imply_squareroot {X : UU} (F : (X → X → hProp) -> hProp) :
  (isUS_imply F) -> (∏ A B : X → X → hProp, F A → F B → F (λ x y : X, A x y ∧ B x y))
  -> (isUS_diag F) -> isUS_prod_inv F -> isUS_squareroot F.
Proof.
  intros X F Himpl Hand Hdiag H.
  intros P FP.
  generalize (H P FP).
  apply hinhfun.
  intros Q.
  exists (λ x y, pr1 Q x y ∧ subset_inv (pr1 Q) x y).
  split.
  - apply Hand.
    exact (pr1 (pr2 Q)).
    apply isUS_prod_inv_imply_symm.
    exact Himpl.
    exact Hdiag.
    exact H.
    exact (pr1 (pr2 Q)).
  - intros x z Hx.
    apply (pr2 (pr2 Q)).
    revert Hx.
    apply hinhfun.
    intros y.
    exists (pr1 y) ; split.
    exact (pr1 (pr1 (pr2 y))).
    exact (pr2 (pr2 (pr2 y))).
Qed.

Lemma isUS_symm_squareroot_imply_prod_inv {X : UU} (F : (X → X -> hProp) -> hProp) :
  (isUS_imply F) -> (∏ A B : X → X → hProp, F A → F B → F (λ x y : X, A x y ∧ B x y))
  -> (isUS_diag F) -> isUS_symm F -> isUS_squareroot F -> isUS_prod_inv F.
Proof.
  intros X F Himpl Hand Hdiag Hsymm Hsqr.
  intros P FP.
  generalize (Hsqr P FP).
  apply hinhfun.
  intros Q.
  exists (λ x y, pr1 Q x y ∧ subset_inv (pr1 Q) x y).
  split.
  - apply Hand.
    exact (pr1 (pr2 Q)).
    apply Hsymm.
    exact (pr1 (pr2 Q)).
  - intros x z Hx.
    apply (pr2 (pr2 Q)).
    revert Hx.
    apply hinhfun.
    intros y.
    exists (pr1 y) ; split.
    exact (pr1 (pr1 (pr2 y))).
    exact (pr2 (pr2 (pr2 y))).
Qed.

Definition isUniformStructure {X : UU} (F : (X → X → hProp) → hProp) :=
  (isUS_imply F)
    × (isUS_finite_intersection F)
    × (isUS_diag F)
    × (isUS_symm F)
    × (isUS_squareroot F).

Definition UniformStructure (X : UU) :=
  ∑ (F : (X → X -> hProp) -> hProp), isUniformStructure F.
Definition pr1UniformStructure (X : UU) : UniformStructure X -> ((X → X -> hProp) -> hProp) := pr1.
Coercion pr1UniformStructure : UniformStructure >-> Funclass.

Definition mkUniformStructure {X : UU} (F : (X → X -> hProp) -> hProp)
           (Himpl : isUS_imply F) (Htrue : isUS_htrue F)
           (Hand : isUS_and F)
           (Hdiag : isUS_diag F) (Hsymm : isUS_symm F) (Hsquareroot : isUS_squareroot F) :
  UniformStructure X :=
  F,, Himpl,, isUS_finite_intersection_carac F Htrue Hand,, Hdiag,, Hsymm,, Hsquareroot.

Lemma UniformStructure_imply {X : UU} (F : UniformStructure X) :
  ∏ A B : X → X → hProp, (∏ x y : X, A x y → B x y) → F A → F B.
Proof.
  intros X F.
  apply (pr1 (pr2 F)).
Qed.
Lemma UniformStructure_finite_intersection {X : UU} (F : UniformStructure X) :
  isUS_finite_intersection F.
Proof.
  intros X F.
  apply (pr1 (pr2 (pr2 F))).
Qed.
Lemma UniformStructure_true {X : UU} (F : UniformStructure X) :
  F (λ _ _, htrue).
Proof.
  intros X F.
  apply (pr2 (isUS_filter_htrue _)).
  apply isfilter_finite_intersection_htrue.
  apply (pr1 (isUS_filter_finite_intersection _)).
  apply UniformStructure_finite_intersection.
Qed.
Lemma UniformStructure_and {X : UU} (F : UniformStructure X) :
   ∏ A B : X → X → hProp, F A → F B → F (λ x y : X, A x y ∧ B x y).
Proof.
  intros X F.
  apply (pr2 (isUS_filter_and _)).
  apply isfilter_finite_intersection_and.
  apply (pr1 (isUS_filter_finite_intersection _)).
  apply UniformStructure_finite_intersection.
Qed.
Lemma UniformStructure_diag {X : UU} (F : UniformStructure X) :
  ∏ P, F P -> ∏ x : X, P x x.
Proof.
  intros X F.
  apply (pr1 (pr2 (pr2 (pr2 F)))).
Qed.
Lemma UniformStructure_symm {X : UU} (F : UniformStructure X) :
  ∏ P, F P -> F (subset_inv P).
Proof.
  intros X F.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 F))))).
Qed.
Lemma UniformStructure_squareroot {X : UU} (F : UniformStructure X) :
  ∏ P, F P -> ∃ Q, F Q × ∏ x y : X, subset_square Q x y -> P x y.
Proof.
  intros X F.
  apply (pr2 (pr2 (pr2 (pr2 (pr2 F))))).
Qed.
Lemma UniformStructure_prod_inv {X : UU} (F : UniformStructure X) :
  ∏ P, F P -> ∃ Q, F Q × ∏ x y : X, subset_prod Q (subset_inv Q) x y -> P x y.
Proof.
  intros X F.
  apply isUS_symm_squareroot_imply_prod_inv.
  intros A B ; apply (UniformStructure_imply F).
  apply UniformStructure_and.
  intros A ; apply (UniformStructure_diag F).
  intros A ; apply (UniformStructure_symm F).
  intros A ; apply (UniformStructure_squareroot F).
Qed.

Lemma UniformeStructure_PreFilter {X : UU}
      (F : UniformStructure X) : PreFilter (X × X).
Proof.
  intros X F.
  exists (λ A : X × X → hProp, F (λ x y : X, A (x,,y))).
  split.
  - apply isUS_filter_imply.
    intros A B.
    apply UniformStructure_imply.
  - apply isUS_filter_finite_intersection.
    apply UniformStructure_finite_intersection.
Defined.

Lemma UniformeStructure_Filter {X : UU}
      (x0 : ∥ X ∥) (F : UniformStructure X) : Filter (X × X).
Proof.
  intros X x0 F.
  exists (λ A : X × X → hProp, F (λ x y : X, A (x,,y))).
  split.
  - apply (pr2 (UniformeStructure_PreFilter F)).
  - abstract (intros A Fa ;
              revert x0 ;
              apply hinhfun ;
              intros x0 ;
              exists (x0,,x0) ;
              apply (UniformStructure_diag F (λ x y, A (x,,y))), Fa).
Defined.

Lemma UniformStructure_square {X : UU} (F : UniformStructure X) :
  ∏ P, F P -> F (subset_square P).
Proof.
  intros X F P Fp.
  apply UniformStructure_imply with (2 := Fp).
  intros x y Pxy.
  apply hinhpr.
  exists x ; split.
  now apply (UniformStructure_diag F).
  exact Pxy.
Qed.

Definition UniformSpace :=
  ∑ (X : UU), UniformStructure X.
Definition pr1UniformSpace : UniformSpace -> UU := pr1.
Coercion pr1UniformSpace : UniformSpace >-> UU.

(** Def 2: Foundamental System of Uniform Structure *)

Definition isUSbase {X : UU} (F : UniformStructure X) (base : (X → X → hProp) → hProp) :=
  (∏ (P : X → X → hProp), base P -> F P)
    × (∏ (P : X → X → hProp), F P → ∃ Q : X → X → hProp, base Q × (∏ x y : X, Q x y → P x y)).


Lemma isUSbase_pow {X : hSet} (F : UniformStructure X) (B : (X → X → hProp) → hProp) :
  isUSbase F B -> isUSbase F (λ P, ∃ (n : nat) Q, (O < n) × B Q × P = subset_pow Q n).
Proof.
  intros X F B Hbase.
  split.
  - intros P.
    apply hinhuniv.
    intros n.
    induction n as [n Q].
    rewrite (pr2 (pr2 (pr2 Q))).
    induction n as [ | n _].
    now generalize (pr1 (pr2 Q)).
    generalize (pr1 Q) (pr1 (pr2 (pr2 Q))) ;
      clear Q ;
      intros Q BQ.
    induction n as [ | n IHn].
    now apply (pr1 Hbase).
    rewrite subset_pow_S.
    generalize (pr2 Hbase _ IHn).
    apply hinhuniv.
    intros Q'.
    generalize (UniformStructure_and F _ _ (pr1 Hbase _ BQ) (pr1 Hbase _ (pr1 (pr2 Q')))).
    apply (UniformStructure_imply F).
    intros x y Hxy.
    apply hinhpr.
    exists x.
    split.
    apply (UniformStructure_diag F).
    now apply (pr1 Hbase).
    apply (pr2 (pr2 Q')).
    exact (pr2 Hxy).
  - intros P Hp.
    generalize (pr2 Hbase P Hp).
    apply hinhfun.
    intros Q.
    exists (pr1 Q) ; split.
    apply hinhpr.
    exists 1%nat, (pr1 Q) ; repeat split.
    exact (pr1 (pr2 Q)).
    exact (pr2 (pr2 Q)).
Qed.

Definition issymmsubset {X : UU} (P : X → X -> hProp) :=
  (∏ x y, P x y <-> subset_inv P x y).
Lemma isaprop_issymmsubset {X : UU} (P : X → X -> hProp) :
  isaprop (issymmsubset P).
Proof.
  intros X P.
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply isapropdirprod ; apply isapropimpl, propproperty.
Qed.

Lemma issymmsubset_and {X : UU} (F : UniformStructure X) (P : X → X -> hProp) :
  F P -> issymmsubset (λ x y, P x y ∧ subset_inv P x y).
Proof.
  intros X F P Fp.
  intros x y ; split ; intros Hp ; split.
  exact (pr2 Hp).
  exact (pr1 Hp).
  exact (pr2 Hp).
  exact (pr1 Hp).
Qed.
Lemma issymmsubset_or {X : UU} (F : UniformStructure X) (P : X → X -> hProp) :
  F P -> issymmsubset (λ x y, P x y ∨ subset_inv P x y).
Proof.
  intros X F P Fp.
  intros x y ; split ; apply hinhfun ; apply sumofmaps ; [intros Hp | intros Hp' | intros Hp | intros Hp'].
  now right.
  now left.
  now right.
  now left.
Qed.

Lemma issymmsubset_USbase {X : UU} (F : UniformStructure X) :
  isUSbase F (λ P, F P ∧ hProppair _ (isaprop_issymmsubset P)).
Proof.
  intros X F.
  split.
  - intros P.
    apply pr1.
  - intros P HP.
    refine (hinhfun _ _).
    2: apply (UniformStructure_prod_inv F).
    intros Q.
    exists (subset_prod (pr1 Q) (subset_inv (pr1 Q))).
    repeat split.
    4: apply (pr2 (pr2 Q)).
    + apply (UniformStructure_imply) with (2 := pr1 (pr2 Q)).
      intros x y Hp.
      apply hinhpr.
      exists y.
      split.
      exact Hp.
      apply (UniformStructure_diag F).
      apply (UniformStructure_symm F).
      exact (pr1 (pr2 Q)).
    + apply hinhfun.
      intros z.
      exists (pr1 z) ; split.
      exact (pr2 (pr2 z)).
      exact (pr1 (pr2 z)).
    + apply hinhfun.
      intros z.
      exists (pr1 z) ; split.
      exact (pr2 (pr2 z)).
      exact (pr1 (pr2 z)).
    + exact HP.
Qed.

Lemma isUSbase_isBaseOfPreFilter {X : UU} (F : UniformStructure X) (base : (X → X -> hProp) -> hProp) :
  isUSbase F base ->
  isBaseOfPreFilter (λ A : X × X → hProp, base (λ x y : X, A (x,,y))).
Proof.
  intros X F base.
  intros Hbase.
  split.
  - intros A B Ha Hb.
    refine (hinhfun _ _).
    2: apply (pr2 Hbase).
    2: apply UniformStructure_and ; apply (pr1 Hbase).
    2: apply Ha.
    2: apply Hb.
    intros C.
    exists (λ xy : X × X, pr1 C (pr1 xy) (pr2 xy)).
    split.
    + apply (pr1 (pr2 C)).
    + intros x Hx.
      apply (pr2 (pr2 C)).
      apply Hx.
  - generalize (pr2 Hbase _ (UniformStructure_true F)).
    apply hinhfun.
    intros A.
    exists (λ xy : X × X, pr1 A (pr1 xy) (pr2 xy)).
    exact (pr1 (pr2 A)).
Qed.
Lemma isUSbase_isBaseOfFilter {X : UU} (x0 : ∥X∥) (F : UniformStructure X) (base : (X → X -> hProp) -> hProp) :
  isUSbase F base -> isBaseOfFilter (λ A : X × X → hProp, base (λ x y, A (x,,y))).
Proof.
  intros X x0 F base.
  intros Hbase.
  repeat split.
  - intros A B Ha Hb.
    refine (hinhfun _ _).
    2: apply (pr2 Hbase).
    2: apply UniformStructure_and ; apply (pr1 Hbase).
    2: apply Ha.
    2: apply Hb.
    intros C.
    exists (λ xy : X × X, pr1 C (pr1 xy) (pr2 xy)).
    split.
    exact (pr1 (pr2 C)).
    intros x.
    apply (pr2 (pr2 C)).
  - generalize (pr2 Hbase _ (UniformStructure_true F)).
    apply hinhfun.
    intros A.
    exists (λ xy, pr1 A (pr1 xy) (pr2 xy)).
    exact (pr1 (pr2 A)).
  - intros A Ha.
    revert x0.
    apply hinhuniv.
    intros x0.
    apply (pr1 Hbase) in Ha.
    apply hinhpr.
    exists (x0,,x0).
    now apply (UniformStructure_diag F _ Ha).
Qed.

Lemma isUSbase_filterbase {X : UU} (F : UniformStructure X) (base : (X → X -> hProp) -> hProp) :
  ∏ Hbase : isUSbase F base,
  ∏ P, (F P <-> filterbase (λ A : X × X → hProp, base (λ x y, A (x,,y))) (λ xy : X × X, P (pr1 xy) (pr2 xy))).
Proof.
  intros X F base Hbase P.
  split.
  - intros HP.
    generalize (pr2 Hbase P HP).
    apply hinhfun.
    intros B.
    exists (λ xy, pr1 B (pr1 xy) (pr2 xy)).
    split.
    exact (pr1 (pr2 B)).
    intros x.
    apply (pr2 (pr2 B)).
  - apply hinhuniv.
    intros A.
    apply UniformStructure_imply with (1 := λ x y, pr2 (pr2 A) (x,,y)).
    apply (pr1 Hbase).
    exact (pr1 (pr2 A)).
Qed.

Lemma isUSbase_PreFilterBase {X : UU} (F : UniformStructure X) (base : (X → X -> hProp) -> hProp) :
  ∏ Hbase : isUSbase F base,
  ∏ P, (F P <-> PreFilterBase ((λ A : X × X → hProp, base (λ x y : X, A (x,, y))) ,, isUSbase_isBaseOfPreFilter F base Hbase) (λ xy, P (pr1 xy) (pr2 xy))).
Proof.
  intros X F base Hbase P.
  now apply isUSbase_filterbase.
Qed.

Lemma isUSbase_FilterBase {X : UU} (x0 : ∥ X ∥) (F : UniformStructure X) (base : (X → X -> hProp) -> hProp) :
  ∏ Hbase : isUSbase F base,
  ∏ P, (F P <-> FilterBase ((λ A : X × X → hProp, base (λ x y : X, A (x,, y))) ,, isUSbase_isBaseOfFilter x0 F base Hbase) (λ xy, P (pr1 xy) (pr2 xy))).
Proof.
  intros X x0 F base Hbase P.
  now apply isUSbase_filterbase.
Qed.

Definition isBaseOfUniformStructure {X : UU} (base : (X → X -> hProp) -> hProp) :=
  (isBaseOfPreFilter (λ A : X × X → hProp, base (λ x y, A (x,,y))))
    × (∏ P, base P -> ∏ x : X, P x x)
    × (∏ P, base P -> ∃ P', base P' × ∏ x y, P' x y -> subset_inv P x y)
    × (∏ P, base P -> ∃ Q, base Q × ∏ x y, subset_square Q x y -> P x y).

Lemma isUSbase_BaseOfUniformStructure {X : UU} (F : UniformStructure X) (base : (X → X -> hProp) -> hProp) :
  isUSbase F base -> isBaseOfUniformStructure base.
Proof.
  intros X F base.
  intros Hbase.
  split.
  now apply (isUSbase_isBaseOfPreFilter F).
  repeat split.
  - intros P Hp.
    apply UniformStructure_diag with F.
    now apply (pr1 Hbase).
  - intros P Hp.
    apply (pr2 Hbase).
    now apply UniformStructure_symm, (pr1 Hbase).
  - intros P Hp.
    generalize (UniformStructure_squareroot F _ (pr1 Hbase _ Hp)).
    apply hinhuniv ; intros Q.
    generalize (pr2 Hbase _ (pr1 (pr2 Q))).
    apply hinhfun.
    intros R.
    exists (pr1 R).
    split.
    exact (pr1 (pr2 R)).
    intros x z Hx.
    apply (pr2 (pr2 Q)).
    revert Hx.
    apply hinhfun.
    intros y.
    exists (pr1 y) ; split ;
    apply (pr2 (pr2 R)).
    exact (pr1 (pr2 y)).
    exact (pr2 (pr2 y)).
Qed.

Lemma isBaseOfUniformStructure_USbase {X : UU} (base : (X → X -> hProp) -> hProp) :
  ∏ Hbase : isBaseOfUniformStructure base,
    isUniformStructure (λ A : X → X → hProp, filterbase (λ A : X × X → hProp, base (λ x y, A (x,,y))) (λ xy, A (pr1 xy) (pr2 xy))).
Proof.
  intros X base Hbase.
  repeat split.
  - intros A B H.
    apply hinhfun.
    intros C.
    exists (pr1 C) ; split.
    exact (pr1 (pr2 C)).
    intros x Hx.
    now apply H, (pr2 (pr2 C)).
  - apply isUS_finite_intersection_carac.
    + generalize (pr2 (pr1 Hbase)).
      apply hinhfun.
      intros A.
      exists (pr1 A), (pr2 A) ; easy.
    + intros A B.
      apply hinhuniv2.
      intros A' B'.
      generalize (pr1 (pr1 Hbase) _ _ (pr1 (pr2 A')) (pr1 (pr2 B'))).
      apply hinhfun.
      intros C.
      exists (pr1 C) ; split.
      exact (pr1 (pr2 C)).
      intros x Cx ; split.
      apply (pr2 (pr2 A')).
      apply (pr1 (pr2 (pr2 C) _ Cx)).
      apply (pr2 (pr2 B')).
      apply (pr2 (pr2 (pr2 C) _ Cx)).
  - intros P Hp x.
    revert Hp.
    apply hinhuniv.
    intros Q.
    apply (pr2 (pr2 Q) (x,,x)).
    apply (pr1 (pr2 Hbase) _ (pr1 (pr2 Q))).
  - intros P.
    apply hinhuniv.
    intros A.
    generalize (pr1 (pr2 (pr2 Hbase)) _ (pr1 (pr2 A))).
    apply hinhfun.
    intros B.
    exists (λ xy, pr1 B (pr1 xy) (pr2 xy)).
    split.
    exact (pr1 (pr2 B)).
    intros x Bx.
    apply (pr2 (pr2 A) (pr2 x,,pr1 x)).
    apply (pr2 (pr2 B)).
    exact Bx.
  - intros P.
    apply hinhuniv.
    intros A.
    generalize (pr2 (pr2 (pr2 Hbase)) _ (pr1 (pr2 A))).
    apply hinhfun.
    intros B.
    exists (pr1 B).
    split.
    apply hinhpr.
    now exists (λ xy, pr1 B (pr1 xy) (pr2 xy)), (pr1 (pr2 B)).
    intros x y Bx.
    now apply (pr2 (pr2 A) (x,,y)), (pr2 (pr2 B)).
Qed.

(** *** Topology in a Uniform Space *)
(** Prop 1 *)

Require Export UniMath.Topology.Topology.

Section UStopology.

Context {X : UU}.
Context (F : UniformStructure X).

Definition USneighborhood : X -> (X -> hProp) -> hProp :=
  (λ (x : X) (A : X → hProp),
    ∃ U : X → X → hProp, F U × (∏ y : X, U x y → A y)).

Lemma USneighborhood_imply :
  ∏ x : X, isfilter_imply (USneighborhood x).
Proof.
  intros x A B H.
  apply hinhfun.
  intros Ua.
  exists (pr1 Ua).
  split.
  apply (pr1 (pr2 Ua)).
  now intros y H0 ; apply H, (pr2 (pr2 Ua)).
Qed.
Lemma USneighborhood_htrue :
  ∏ x : X, isfilter_htrue (USneighborhood x).
Proof.
  intros x.
  apply hinhpr.
  exists (λ _ _, htrue).
  split.
  now apply UniformStructure_true.
  easy.
Qed.
Lemma USneighborhood_and :
  ∏ x : X, isfilter_and (USneighborhood x).
Proof.
  intros x A B.
  apply hinhfun2.
  intros Ua Ub.
  exists (λ x y, pr1 Ua x y ∧ pr1 Ub x y).
  split.
  apply UniformStructure_and.
  exact (pr1 (pr2 Ua)).
  exact (pr1 (pr2 Ub)).
  intros y Hy ; split.
  now apply (pr2 (pr2 Ua)), (pr1 Hy).
  now apply (pr2 (pr2 Ub)), (pr2 Hy).
Qed.
Lemma USneighborhood_point :
  ∏ (x : X) (P : X → hProp), USneighborhood x P → P x.
Proof.
  intros x A.
  apply hinhuniv.
  intros Ua.
  apply (pr2 (pr2 Ua)).
  apply UniformStructure_diag with F.
  exact (pr1 (pr2 Ua)).
Qed.
Lemma USneighborhood_neighborhood :
  ∏ (x : X) (P : X → hProp),
    USneighborhood x P
    → ∃ Q : X → hProp,
        USneighborhood x Q × (∏ y : X, Q y → USneighborhood y P).
Proof.
  intros x A.
  apply hinhuniv.
  intros Ua.
  generalize (UniformStructure_squareroot _ _ (pr1 (pr2 Ua))).
  apply hinhfun.
  intros Ub.
  exists (λ y, pr1 Ub x y).
  split.
  apply hinhpr.
  now exists (pr1 Ub), (pr1 (pr2 Ub)).
  intros y Qy.
  apply hinhpr.
  exists (pr1 Ub).
  split.
  apply (pr1 (pr2 Ub)).
  intros z Hz.
  apply (pr2 (pr2 Ua)), (pr2 (pr2 Ub)).
  apply hinhpr.
  now exists y ; split.
Qed.

Lemma isNeighborhood_USneighborhood :
  isNeighborhood USneighborhood.
Proof.
  repeat split.
  - apply USneighborhood_imply.
  - apply USneighborhood_htrue.
  - apply USneighborhood_and.
  - apply USneighborhood_point.
  - apply USneighborhood_neighborhood.
Qed.

End UStopology.

Definition Topology_UniformSpace {X : UU} (F : UniformStructure X) :
  Topology X.
Proof.
  intros X F.
  simple refine (TopologyFromNeighborhood _ _).
  - apply USneighborhood, F.
  - apply isNeighborhood_USneighborhood.
Defined.

(** ** Convergence in Uniform Spaces *)

Definition USlocally {X : UniformSpace} (x : X) : Filter X.
Proof.
  intros X x.
  exists (USneighborhood (pr2 X) x).
  apply isNeighborhood_isFilter.
  apply (isNeighborhood_USneighborhood (pr2 X)).
Defined.
Lemma USlocally_correct {X : UniformSpace} (x : X) :
  ∏ P : X -> hProp,
    locally (Topology_UniformSpace (pr2 X)) x P <-> USlocally x P.
Proof.
  intros X x P.
  split ; intros H.
  - apply (pr2 (TopologyFromNeighborhood_correct _ _ _ _)) in H.
    apply H.
  - apply (pr1 (TopologyFromNeighborhood_correct _ _ _ _)).
    apply H.
Qed.

Definition USlocally2d {X Y : UniformSpace} (x : X) (y : Y) :
  Filter (X × Y).
Proof.
  intros X Y x y.
  apply FilterDirprod.
  apply (USlocally x).
  apply (USlocally y).
Defined.
Lemma USlocally2d_correct {X Y : UniformSpace} (x : X) (y : Y) :
  ∏ P : X × Y -> hProp,
    locally2d (Topology_UniformSpace (pr2 X)) (Topology_UniformSpace (pr2 Y)) x y P
    <-> USlocally2d x y P.
Proof.
  split ; apply hinhfun ;
  intros A ;
  exists (pr1 A), (pr1 (pr2 A)) ; repeat split.
  - apply (pr1 (USlocally_correct _ _)), (pr1 (pr2 (pr2 A))).
  - apply (pr1 (USlocally_correct _ _)), (pr1 (pr2 (pr2 (pr2 A)))).
  - apply (pr2 (pr2 (pr2 (pr2 A)))).
  - apply (pr2 (USlocally_correct _ _)), (pr1 (pr2 (pr2 A))).
  - apply (pr2 (USlocally_correct _ _)), (pr1 (pr2 (pr2 (pr2 A)))).
  - apply (pr2 (pr2 (pr2 (pr2 A)))).
Qed.

Definition is_filter_USlim {X : UniformSpace} (F : Filter X) (x : X) :=
  filter_le F (USlocally x).
Definition ex_filter_USlim {X : UniformSpace} (F : Filter X) :=
  ∃ x : X, is_filter_USlim F x.
Lemma is_filter_USlim_correct {X : UniformSpace} (F : Filter X) (x : X) :
  is_filter_lim (Topology_UniformSpace (pr2 X)) F x <-> is_filter_USlim F x.
Proof.
  split ; intros H P Hp ; apply H.
  - apply (pr2 (USlocally_correct _ _)), Hp.
  - apply (pr1 (USlocally_correct _ _)), Hp.
Qed.

Definition is_USlim {X : UU} {Y : UniformSpace} (f : X → Y) (F : Filter X) (x : Y) :=
  filterlim f F (USlocally x).
Definition ex_USlim {X : UU} {Y : UniformSpace} (f : X → Y) (F : Filter X) :=
  ∃ x : Y, is_USlim f F x.
Lemma isUS_lim_correct {X : UU} {Y : UniformSpace} (f : X → Y) (F : Filter X) (x : Y) :
  is_lim (Topology_UniformSpace (pr2 Y)) f F x <-> is_USlim f F x.
Proof.
  split ; intros H P Hp ; apply H.
  - apply (pr2 (USlocally_correct _ _)), Hp.
  - apply (pr1 (USlocally_correct _ _)), Hp.
Qed.

Definition UScontinuous_at {X Y : UniformSpace} (f : X → Y) (x : X) :=
  is_USlim f (USlocally x) (f x).
Definition UScontinuous_on {X Y : UniformSpace}
           (dom : X → hProp) (f : ∏ x : X, dom x → Y) :=
  ∏ (x : X) (Hx : dom x),
  ∃ H : ∏ P : X → hProp, (USlocally x) P → ∃ x0 : X, dom x0 ∧ P x0,
    is_USlim (λ y : ∑ x0 : X, dom x0, f (pr1 y) (pr2 y))
             (FilterSubtype (USlocally x) dom H) (f x Hx).
Definition UScontinuous {X Y : UniformSpace} (f : X → Y)  :=
  ∏ x, UScontinuous_at f x.

Definition UScontinuous2d_at {X Y Z : UniformSpace} (f : X → Y → Z) (x : X) (y : Y) :=
  is_USlim (λ z : X × Y, f (pr1 z) (pr2 z)) (USlocally2d x y) (f x y).
Definition UScontinuous2d_on {X Y Z : UniformSpace}
           (dom : X → Y → hProp) (f : ∏ x y, dom x y → Z) :=
  ∏ x y (Hxy : dom x y),
  ∃ H,
    is_USlim (λ y : ∑ z, dom (pr1 z) (pr2 z), f (pr1 (pr1 y)) (pr2 (pr1 y)) (pr2 y))
             (FilterSubtype (USlocally2d x y) (λ z, dom (pr1 z) (pr2 z)) H) (f x y Hxy).
Definition UScontinuous2d {X Y Z : UniformSpace} (f : X → Y → Z)  :=
  ∏ x y, UScontinuous2d_at f x y.

(** ** Uniform continuity *)

Definition UniformlyContinuous {X Y : UniformSpace} (f : X → Y) :=
  ∏ V, pr2 Y V → pr2 X (λ x y : X, V (f x) (f y)).

Lemma UniformlyContinuous_UScontinuous {X Y : UniformSpace} (f : X → Y) :
  UniformlyContinuous f → UScontinuous f.
Proof.
  intros X Y f Cf x P.
  apply hinhfun.
  intros U.
  specialize (Cf _ (pr1 (pr2 U))).
  eexists.
  split.
  apply Cf.
  intros y.
  apply (pr2 (pr2 U)).
Qed.

Definition UniformSpace_dirprod (X Y : UniformSpace) : UniformSpace.
Proof.
  intros X Y.
  exists (X × Y).
  simple refine (mkUniformStructure _ _ _ _ _ _ _).
  - intros U.
    apply (∃ (Ux : X → X → hProp) (Uy : Y → Y → hProp),
             (pr2 X Ux)
               × (pr2 Y Uy)
               × (∏ x x' y y', Ux x x' → Uy y y' → U (x ,, y) (x' ,, y'))).
  - intros A B H.
    apply hinhfun.
    intros U.
    exists (pr1 U), (pr1 (pr2 U)).
    repeat split.
    exact (pr1 (pr2 (pr2 U))).
    exact (pr1 (pr2 (pr2 (pr2 U)))).
    intros x x' y y' Uxx Uyy.
    now apply H, (pr2 (pr2 (pr2 (pr2 U)))).
  - apply hinhpr.
    exists (λ _ _, htrue), (λ _ _, htrue).
    repeat split.
    + apply UniformStructure_true.
    + apply UniformStructure_true.
  - intros A B.
    apply hinhfun2.
    intros A' B'.
    exists (λ x x', pr1 A' x x' ∧ pr1 B' x x'), (λ y y', pr1 (pr2 A') y y' ∧ pr1 (pr2 B') y y').
    repeat split.
    apply UniformStructure_and.
    exact (pr1 (pr2 (pr2 A'))).
    exact (pr1 (pr2 (pr2 B'))).
    apply UniformStructure_and.
    exact (pr1 (pr2 (pr2 (pr2 A')))).
    exact (pr1 (pr2 (pr2 (pr2 B')))).
    apply (pr2 (pr2 (pr2 (pr2 A')))).
    apply (pr1 X0).
    apply (pr1 X1).
    apply (pr2 (pr2 (pr2 (pr2 B')))).
    apply (pr2 X0).
    apply (pr2 X1).
  - intros P Hp xy.
    revert Hp.
    apply hinhuniv.
    intros U.
    apply (pr2 (pr2 (pr2 (pr2 U))) (pr1 xy) (pr1 xy) (pr2 xy) (pr2 xy)).
    now apply (UniformStructure_diag (pr2 X)), (pr1 (pr2 (pr2 U))).
    now apply (UniformStructure_diag (pr2 Y)), (pr1 (pr2 (pr2 (pr2 U)))).
  - intros P.
    apply hinhfun.
    intros U.
    exists (subset_inv (pr1 U)), (subset_inv (pr1 (pr2 U))).
    repeat split.
    now apply UniformStructure_symm, (pr1 (pr2 (pr2 U))).
    now apply UniformStructure_symm, (pr1 (pr2 (pr2 (pr2 U)))).
    intros x x' y y'.
    apply (pr2 (pr2 (pr2 (pr2 U)))).
  - intros P.
    apply hinhuniv.
    intros U.
    generalize (UniformStructure_squareroot _ _ (pr1 (pr2 (pr2 U)))) (UniformStructure_squareroot _ _ (pr1 (pr2 (pr2 (pr2 U))))).
    apply hinhfun2.
    intros Qx Qy.
    exists (λ z z' : (X × Y),
                  pr1 Qx (pr1 z) (pr1 z')
                  ∧ pr1 Qy (pr2 z) (pr2 z')).
    split.
    + apply hinhpr.
      exists (pr1 Qx), (pr1 Qy).
      repeat split ; simpl.
      exact (pr1 (pr2 Qx)).
      exact (pr1 (pr2 Qy)).
      exact X0.
      exact X1.
    + intros x y.
      apply hinhuniv.
      intros z.
      apply (pr2 (pr2 (pr2 (pr2 U))) (pr1 x) (pr1 y) (pr2 x) (pr2 y)).
      apply (pr2 (pr2 Qx)).
      apply hinhpr.
      exists (pr1 (pr1 z)) ; split.
      exact (pr1 (pr1 (pr2 z))).
      exact (pr1 (pr2 (pr2 z))).
      apply (pr2 (pr2 Qy)).
      apply hinhpr.
      exists (pr2 (pr1 z)) ; split.
      exact (pr2 (pr1 (pr2 z))).
      exact (pr2 (pr2 (pr2 z))).
Defined.

Lemma UniformlyContinuous_pr1 {X Y : UniformSpace} :
  UniformlyContinuous (X := UniformSpace_dirprod X Y) (λ x : X × Y, pr1 x).
Proof.
  intros X Y V Hv.
  apply hinhpr.
  exists V, (λ _ _, htrue).
  repeat split ; simpl.
  exact Hv.
  apply UniformStructure_true.
  intros x y _ _ H _.
  exact H.
Qed.
Lemma UniformlyContinuous_pr2 {X Y : UniformSpace} :
  UniformlyContinuous (X := UniformSpace_dirprod X Y) (λ x : X × Y, pr2 x).
Proof.
  intros X Y V Hv.
  apply hinhpr.
  exists (λ _ _, htrue), V.
  repeat split ; simpl.
  apply UniformStructure_true.
  exact Hv.
  intros _ _ x y _ H.
  exact H.
Qed.

(** ** Complete spaces *)
(** *** Def 1 *)

Definition USsmall {X : UU} (F : UniformStructure X) (V : X → X -> hProp) (FV : F V) (A : X -> hProp) :=
  ∏ x y : X, A x -> A y -> V x y.

Lemma USsmall_square {X : UU} (F : UniformStructure X) (V : X → X -> hProp) (Fv : F V) (A B : X -> hProp) :
  USsmall F V Fv A -> USsmall F V Fv B -> (∃ z, A z ∧ B z)
  -> USsmall F (subset_square V) (UniformStructure_square F V Fv) (λ x , A x ∨ B x).
Proof.
  intros X F V Fv A B Ha Hb Hex x y.
  apply hinhuniv2.
  apply (sumofmaps (Z := _ → _)) ; [intros Ax | intros Bx] ;
  apply sumofmaps ; [intros Ay | intros By | intros Ay | intros By].
  - apply isdiag_square.
    now apply (UniformStructure_diag F).
    now apply Ha.
  - revert Hex.
    apply hinhfun.
    intros z.
    exists (pr1 z) ; split.
    apply Ha.
    exact Ax.
    exact (pr1 (pr2 z)).
    apply Hb.
    exact (pr2 (pr2 z)).
    exact By.
  - revert Hex.
    apply hinhfun.
    intros z.
    exists (pr1 z) ; split.
    apply Hb.
    exact Bx.
    exact (pr2 (pr2 z)).
    apply Ha.
    exact (pr1 (pr2 z)).
    exact Ay.
  - apply isdiag_square.
    now apply (UniformStructure_diag F).
    now apply Hb.
Qed.

Definition isCauchy_filter {X : UU} (FX : UniformStructure X) (F : Filter X) :=
  ∏ (V : X → X -> hProp) (Hv : FX V),
  ∃ A : X -> hProp, USsmall FX V Hv A × F A.

Lemma exfilterlim_cauchy {X : UU} (FX : UniformStructure X) (F : Filter X) :
  ex_filter_USlim (X := X,,FX) F
  -> isCauchy_filter FX F.
Proof.
  intros X FX F Hf V Hv.
  revert Hf.
  apply hinhuniv.
  intros x.
  generalize (UniformStructure_prod_inv _ _ Hv).
  apply hinhfun.
  intros Q.
  exists (λ y : X, pr1 Q y (pr1 x)).
  split.
  - intros y z Qy Qz.
    apply (pr2 (pr2 Q)).
    apply hinhpr.
    now exists (pr1 x).
  - apply (pr2 x).
    apply hinhpr.
    exists (subset_inv (pr1 Q)).
    split.
    apply UniformStructure_symm.
    exact (pr1 (pr2 Q)).
    easy.
Qed.

Lemma isCauchy_filter_im {X Y : UniformSpace} (F : Filter X) (f : X → Y) :
  UniformlyContinuous f
  → isCauchy_filter (pr2 X) F
  → isCauchy_filter (pr2 Y) (FilterIm f F).
Proof.
  intros X Y F f Cf H.
  intros V Hv.
  refine (hinhfun _ _).
  2: simple refine (H (λ x y : X, V (f x) (f y)) _).
  - intros A.
    exists (λ y : Y, ∃ x : X, y = f x × pr1 A x).
    split.
    + intros x' y'.
      apply hinhuniv2.
      intros x y.
      rewrite (pr1 (pr2 x)), (pr1 (pr2 y)).
      apply (pr1 (pr2 A)).
      exact (pr2 (pr2 x)).
      exact (pr2 (pr2 y)).
    + generalize (pr2 (pr2 A)).
      apply (filter_imply F).
      intros x Ax.
      apply hinhpr.
      now exists x.
  - now apply Cf.
Qed.