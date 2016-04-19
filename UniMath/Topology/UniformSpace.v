(** * Uniform Space *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Export UniMath.Topology.Complements.
Require Import UniMath.Topology.Complements.
Require Export UniMath.Topology.Filters.

(** ** Definitions *)

Definition subset_prod {X : UU} (A B : X × X -> hProp) :=
  λ x : X × X, ∃ y : X, A (pr1 x,,y) ∧ B (y ,, pr2 x).
Definition subset_square {X : UU} (A : X × X -> hProp) :=
  subset_prod A A.
Definition subset_inv {X : UU} (A : X × X -> hProp) :=
  λ x : X × X, A (pr2 x ,, pr1 x).
Fixpoint subset_pow {X : hSet} (A : X × X -> hProp) (n : nat) :=
  match n with
  | O => λ x : X × X, hProppair (pr1 x = pr2 x) (pr2 X _ _)
  | S n => subset_prod A (subset_pow A n)
  end.

Lemma subset_pow_1 {X : hSet} (A : X × X -> hProp) :
  subset_pow A 1 = A.
Proof.
  intros X A.
  apply funextfun.
  intros (x,y).
  apply uahp.
  - apply hinhuniv.
    simpl.
    intros (z,(Az,->)).
    exact Az.
  - intros H.
    apply hinhpr.
    now exists y.
Qed.

Lemma isassoc_subset_prod {X : UU} :
  isassoc (X := tpair _ _ (Utilities.funspace_isaset isasethProp)) (subset_prod (X := X)).
Proof.
  intros X.
  intros A B C.
  apply funextfun.
  intros x.
  apply uahp.
  - apply hinhuniv.
    intros (z,(H,Hc)).
    revert H.
    apply hinhfun.
    intros (y,(Ha,Hb)).
    exists y.
    split.
    exact Ha.
    apply hinhpr.
    exists z ; split.
    exact Hb.
    exact Hc.
  - apply hinhuniv.
    intros (y,(Ha)).
    apply hinhfun.
    intros (z,(Hb,Hc)).
    exists z.
    split.
    apply hinhpr.
    exists y ; split.
    exact Ha.
    exact Hb.
    exact Hc.
Qed.

(** *** Def 1: Uniform Space *)

(** Uniform Structures *)

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
      (x0 : ∥ X ∥) (F : UniformStructure X) : isFilter F.
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

(** Uniform Space *)

Definition UniformSpace :=
  Σ (X : UU), UniformStructure X.
Definition pr1UniformSpace : UniformSpace -> UU := pr1.
Coercion pr1UniformSpace : UniformSpace >-> UU.

(** *** Def 2: Foundamental System of Uniform Structure *)

Definition isFSUS {X : UU} (F : UniformStructure X) (B : (X × X → hProp) → hProp) :=
  ∀ (P : X × X → hProp),
    F P → ∃ Q : X × X → hProp, B Q × (∀ x : X × X, Q x → P x).

Lemma isFSUS_pow {X : hSet} (F : UniformStructure X) (B : (X × X → hProp) → hProp) :
  isFSUS F B -> isFSUS F (λ P, ∃ (n : nat) Q, B Q × P = subset_pow Q n).
Proof.
  intros X F B is P Hp.
  generalize (is P Hp) ; clear is.
  apply hinhfun.
  intros (Q,(Bq,Hq)).
  exists Q ; split.
  apply hinhpr.
  exists 1%nat, Q.
  now rewrite subset_pow_1.
  exact Hq.
Qed.

Definition is_subset_symm {X : UU} (P : X × X -> hProp) :=
  (∀ x, P x <-> subset_inv P x).
Lemma isaprop_is_subset_symm {X : UU} (P : X × X -> hProp) :
  isaprop (is_subset_symm P).
Proof.
  intros X P.
  apply impred_isaprop ; intros x.
  apply isapropdirprod ; apply isapropimpl, propproperty.
Qed.

Lemma is_subset_symm_and {X : UU} (F : UniformStructure X) (P : X × X -> hProp) :
  F P -> is_subset_symm (λ x, P x ∧ subset_inv P x).
Proof.
  intros X F P Fp.
  now intros (x,y) ; split ; intros (Hp,Hp') ; split.
Qed.
Lemma is_subset_symm_or {X : UU} (F : UniformStructure X) (P : X × X -> hProp) :
  F P -> is_subset_symm (λ x, P x ∨ subset_inv P x).
Proof.
  intros X F P Fp.
  intros (x,y) ; split ; apply hinhfun ; intros [Hp | Hp'].
  now right.
  now left.
  now right.
  now left.
Qed.

Lemma is_subset_symm_FSUS {X : UU} (F : UniformStructure X) :
  isFSUS F (λ P, F P ∧ hProppair _ (isaprop_is_subset_symm P)).
Proof.
  intros X F.
  intros P HP.
  refine (hinhfun _ _).
  2: apply (isUF_symm_square_imply_prod_inv F).
  - intros (Q,(Fq,H)).
    exists (subset_prod Q (subset_inv Q)).
    repeat split.
    4: apply H.
    apply (pr1 (pr2 F)) with (2 := Fq).
    intros (x,y) Hp.
    apply hinhpr.
    exists y.
    split.
    exact Hp.
    apply (pr1 (pr2 (pr2 (pr2 F)))).
    now apply (pr1 (pr2 (pr2 (pr2 (pr2 F))))).
    apply hinhfun.
    intros (y,(Hy,Hy')).
    now exists y.
    apply hinhfun.
    intros (y,(Hy,Hy')).
    now exists y.
  - exact (pr1 (pr2 F)).
  - apply isfilter_finite_intersection_htrue.
    exact (pr1 (pr2 (pr2 F))).
  - apply isfilter_finite_intersection_and.
    exact (pr1 (pr2 (pr2 F))).
  - exact (pr1 (pr2 (pr2 (pr2 F)))).
  - exact (pr1 (pr2 (pr2 (pr2 (pr2 F))))).
  - exact (pr2 (pr2 (pr2 (pr2 (pr2 F))))).
  - exact HP.
Qed.
