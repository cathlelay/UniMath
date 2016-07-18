(** * Uniform Space *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Export UniMath.Topology.Prelim.
Require Export UniMath.Topology.Filters.


(** ** Uniform Spaces *)
(** *** Definitions *)

Definition subset_prod {X : UU} (A B : X × X -> hProp) :=
  λ x : X × X, ∃ y : X, A (pr1 x,,y) ∧ B (y ,, pr2 x).
Definition subset_square {X : UU} (A : X × X -> hProp) :=
  subset_prod A A.
Definition subset_inv {X : UU} (A : X × X -> hProp) :=
  λ x : X × X, A (pr2 x ,, pr1 x).
Definition subset_pow {X : hSet} (A : X × X -> hProp) (n : nat) : X × X → hProp.
Proof.
  intros X A n.
  induction n as [ | n _].
  - exact (λ x : X × X, hProppair (pr1 x = pr2 x) (pr2 X _ _)).
  - induction n as [ | n subset_pow].
    + exact A.
    + exact (subset_prod A subset_pow).
Defined.
Lemma subset_pow_S {X : hSet} (A : X × X -> hProp) (n : nat) :
  subset_pow A (S n) = subset_prod A (subset_pow A n).
Proof.
  intros X A n.
  induction n as [ | n _].
  - apply funextfun ; intros xy.
    apply hPropUnivalence.
    + intros Ha ; apply hinhpr.
      exists (pr2 xy).
      rewrite <- tppr.
      easy.
    + apply hinhuniv.
      simpl.
      intros z.
      rewrite (tppr xy), <- (pr2 (pr2 z)).
      exact (pr1 (pr2 z)).
  - reflexivity.
Qed.

Lemma isassoc_subset_prod {X : UU} :
  isassoc (X := tpair _ _ (Utilities.funspace_isaset isasethProp)) (subset_prod (X := X)).
Proof.
  intros X.
  intros A B C.
  apply funextfun.
  intros x.
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

Lemma isdiag_square {X : UU} (A : X × X -> hProp) :
  (Π x : X, A (x,,x)) -> Π x, A x -> subset_square A x.
Proof.
  intros X A Hdiag xy Axy.
  apply hinhpr.
  exists (pr1 xy).
  split.
  now apply Hdiag.
  rewrite <- tppr.
  exact Axy.
Qed.

(** Def 1: Uniform Space *)

Definition isUS_diag {X : UU} (F : (X × X -> hProp) -> hProp) :=
  Π P, F P -> Π x : X, P (x ,, x).
Definition isUS_symm {X : UU} (F : (X × X -> hProp) -> hProp) :=
  Π P, F P -> F (subset_inv P).
Definition isUS_squareroot {X : UU} (F : (X × X -> hProp) -> hProp) :=
  Π P, F P -> ∃ Q, F Q × Π x : X × X, subset_square Q x -> P x.

Definition isUS_prod_inv {X : UU} (F : (X × X -> hProp) -> hProp) :=
  Π P, F P -> ∃ Q, F Q × Π x : X × X, subset_prod Q (subset_inv Q) x -> P x.

Lemma isUS_prod_inv_imply_symm {X : UU} (F : (X × X -> hProp) -> hProp) :
  (isfilter_imply (X := X × X) F) -> (isUS_diag F) -> isUS_prod_inv F -> isUS_symm F.
Proof.
  intros X F Himpl Hdiag H.
  intros P FP.
  generalize (H P FP).
  apply hinhuniv.
  intros Q.
  apply Himpl with (2 := pr1 (pr2 Q)).
  intros x Qx.
  apply (pr2 (pr2 Q)).
  apply hinhpr ; simpl.
  exists (pr2 x) ; split.
  apply Hdiag, (pr1 (pr2 Q)).
  now induction x as [x y].
Qed.
Lemma isUS_prod_inv_imply_squareroot {X : UU} (F : (X × X -> hProp) -> hProp) :
  (isfilter_imply (X := X × X) F) -> (Π A B : X × X → hProp, F A → F B → F (λ x : X × X, A x ∧ B x))
  -> (isUS_diag F) -> isUS_prod_inv F -> isUS_squareroot F.
Proof.
  intros X F Himpl Hand Hdiag H.
  intros P FP.
  generalize (H P FP).
  apply hinhfun.
  intros Q.
  exists (λ x, pr1 Q x ∧ subset_inv (pr1 Q) x).
  split.
  - apply Hand.
    exact (pr1 (pr2 Q)).
    apply isUS_prod_inv_imply_symm.
    exact Himpl.
    exact Hdiag.
    exact H.
    exact (pr1 (pr2 Q)).
  - intros x Hx.
    apply (pr2 (pr2 Q)).
    revert Hx.
    apply hinhfun.
    intros y.
    exists (pr1 y) ; split.
    exact (pr1 (pr1 (pr2 y))).
    exact (pr2 (pr2 (pr2 y))).
Qed.

Lemma isUS_symm_squareroot_imply_prod_inv {X : UU} (F : (X × X -> hProp) -> hProp) :
  (isfilter_imply (X := X × X) F) -> (Π A B : X × X → hProp, F A → F B → F (λ x : X × X, A x ∧ B x))
  -> (isUS_diag F) -> isUS_symm F -> isUS_squareroot F -> isUS_prod_inv F.
Proof.
  intros X F Himpl Hand Hdiag Hsymm Hsqr.
  intros P FP.
  generalize (Hsqr P FP).
  apply hinhfun.
  intros Q.
  exists (λ x, pr1 Q x ∧ subset_inv (pr1 Q) x).
  split.
  - apply Hand.
    exact (pr1 (pr2 Q)).
    apply Hsymm.
    exact (pr1 (pr2 Q)).
  - intros x Hx.
    apply (pr2 (pr2 Q)).
    revert Hx.
    apply hinhfun.
    intros y.
    exists (pr1 y) ; split.
    exact (pr1 (pr1 (pr2 y))).
    exact (pr2 (pr2 (pr2 y))).
Qed.

Definition isUniformStructure {X : UU} F :=
  (isfilter_imply (X := X × X) F)
    × (isfilter_finite_intersection F)
    × (isUS_diag F)
    × (isUS_symm F)
    × (isUS_squareroot F).

Definition UniformStructure (X : UU) :=
  Σ (F : (X × X -> hProp) -> hProp), isUniformStructure F.
Definition pr1UniformStructure (X : UU) : UniformStructure X -> ((X × X -> hProp) -> hProp) := pr1.
Coercion pr1UniformStructure : UniformStructure >-> Funclass.

Definition mkUniformStructure {X : UU} (F : (X × X -> hProp) -> hProp)
           (Himpl : isfilter_imply (X := X × X) F) (Htrue : isfilter_htrue F)
           (Hand : isfilter_and F)
           (Hdiag : isUS_diag F) (Hsymm : isUS_symm F) (Hsquareroot : isUS_squareroot F) :
  UniformStructure X :=
  F,, Himpl,, isfilter_finite_intersection_carac F Htrue Hand,, Hdiag,, Hsymm,, Hsquareroot.

Lemma UniformStructure_imply {X : UU} (F : UniformStructure X) :
  Π A B : X × X → hProp, (Π x : X × X, A x → B x) → F A → F B.
Proof.
  intros X F.
  apply (pr1 (pr2 F)).
Qed.
Lemma UniformStructure_finite_intersection {X : UU} (F : UniformStructure X) :
  isfilter_finite_intersection F.
Proof.
  intros X F.
  apply (pr1 (pr2 (pr2 F))).
Qed.
Lemma UniformStructure_true {X : UU} (F : UniformStructure X) :
  F (λ _, htrue).
Proof.
  intros X F.
  apply isfilter_finite_intersection_htrue, UniformStructure_finite_intersection.
Qed.
Lemma UniformStructure_and {X : UU} (F : UniformStructure X) :
   Π A B : X × X → hProp, F A → F B → F (λ x : X × X, A x ∧ B x).
Proof.
  intros X F.
  apply isfilter_finite_intersection_and, UniformStructure_finite_intersection.
Qed.
Lemma UniformStructure_diag {X : UU} (F : UniformStructure X) :
  Π P, F P -> Π x : X, P (x ,, x).
Proof.
  intros X F.
  apply (pr1 (pr2 (pr2 (pr2 F)))).
Qed.
Lemma UniformStructure_symm {X : UU} (F : UniformStructure X) :
  Π P, F P -> F (subset_inv P).
Proof.
  intros X F.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 F))))).
Qed.
Lemma UniformStructure_squareroot {X : UU} (F : UniformStructure X) :
  Π P, F P -> ∃ Q, F Q × Π x : X × X, subset_square Q x -> P x.
Proof.
  intros X F.
  apply (pr2 (pr2 (pr2 (pr2 (pr2 F))))).
Qed.
Lemma UniformStructure_prod_inv {X : UU} (F : UniformStructure X) :
  Π P, F P -> ∃ Q, F Q × Π x : X × X, subset_prod Q (subset_inv Q) x -> P x.
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
  exists F.
  split.
  - apply (pr1 (pr2 F)).
  - apply (pr1 (pr2 (pr2 F))).
Defined.

Lemma UniformeStructure_Filter {X : UU}
      (x0 : ∥ X ∥) (F : UniformStructure X) : Filter (X × X).
Proof.
  intros X x0 F.
  exists F.
  split.
  - apply (pr2 (UniformeStructure_PreFilter F)).
  - abstract (intros A Fa ;
              revert x0 ;
              apply hinhfun ;
              intros x0 ;
              exists (x0,,x0) ;
              now apply (UniformStructure_diag F)).
Defined.

Lemma UniformStructure_square {X : UU} (F : UniformStructure X) :
  Π P, F P -> F (subset_square P).
Proof.
  intros X F P Fp.
  apply UniformStructure_imply with (2 := Fp).
  intros xy Pxy.
  apply hinhpr.
  exists (pr1 xy) ; split.
  now apply (UniformStructure_diag F).
  rewrite <- tppr.
  exact Pxy.
Qed.

Definition UniformSpace :=
  Σ (X : UU), UniformStructure X.
Definition pr1UniformSpace : UniformSpace -> UU := pr1.
Coercion pr1UniformSpace : UniformSpace >-> UU.

(** Def 2: Foundamental System of Uniform Structure *)

Definition isUSbase {X : UU} (F : UniformStructure X) (base : (X × X → hProp) → hProp) :=
  (Π (P : X × X → hProp), base P -> F P)
    × (Π (P : X × X → hProp), F P → ∃ Q : X × X → hProp, base Q × (Π x : X × X, Q x → P x)).


Lemma isUSbase_pow {X : hSet} (F : UniformStructure X) (B : (X × X → hProp) → hProp) :
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
    intros xy Hxy.
    apply hinhpr.
    exists (pr1 xy).
    split.
    apply (UniformStructure_diag F).
    now apply (pr1 Hbase).
    apply (pr2 (pr2 Q')).
    rewrite <- tppr.
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

Definition issymmsubset {X : UU} (P : X × X -> hProp) :=
  (Π x, P x <-> subset_inv P x).
Lemma isaprop_issymmsubset {X : UU} (P : X × X -> hProp) :
  isaprop (issymmsubset P).
Proof.
  intros X P.
  apply impred_isaprop ; intros x.
  apply isapropdirprod ; apply isapropimpl, propproperty.
Qed.

Lemma issymmsubset_and {X : UU} (F : UniformStructure X) (P : X × X -> hProp) :
  F P -> issymmsubset (λ x, P x ∧ subset_inv P x).
Proof.
  intros X F P Fp.
  intros xy ; rewrite (tppr xy) ; split ; intros Hp ; split.
  exact (pr2 Hp).
  exact (pr1 Hp).
  exact (pr2 Hp).
  exact (pr1 Hp).
Qed.
Lemma issymmsubset_or {X : UU} (F : UniformStructure X) (P : X × X -> hProp) :
  F P -> issymmsubset (λ x, P x ∨ subset_inv P x).
Proof.
  intros X F P Fp.
  intros xy ; rewrite (tppr xy) ; split ; apply hinhfun ; apply sumofmaps ; [intros Hp | intros Hp' | intros Hp | intros Hp'].
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
      intros xy Hp.
      apply hinhpr.
      exists (pr2 xy).
      split.
      rewrite <- tppr.
      exact Hp.
      apply (UniformStructure_diag F).
      apply (UniformStructure_symm F).
      exact (pr1 (pr2 Q)).
    + apply hinhfun.
      intros y.
      exists (pr1 y) ; split.
      exact (pr2 (pr2 y)).
      exact (pr1 (pr2 y)).
    + apply hinhfun.
      intros y.
      exists (pr1 y) ; split.
      exact (pr2 (pr2 y)).
      exact (pr1 (pr2 y)).
    + exact HP.
Qed.

Lemma isUSbase_isBaseOfPreFilter {X : UU} (F : UniformStructure X) (base : (X × X -> hProp) -> hProp) :
  isUSbase F base -> (isBaseOfPreFilter base).
Proof.
  intros X F base.
  intros Hbase.
  split.
  - intros A B Ha Hb.
    apply (pr2 Hbase).
    now apply UniformStructure_and ; apply (pr1 Hbase).
  - generalize (pr2 Hbase _ (UniformStructure_true F)).
    apply hinhfun.
    intros A.
    exists (pr1 A).
    exact (pr1 (pr2 A)).
Qed.
Lemma isUSbase_isBaseOfFilter {X : UU} (x0 : ∥X∥) (F : UniformStructure X) (base : (X × X -> hProp) -> hProp) :
  isUSbase F base -> (isBaseOfFilter base).
Proof.
  intros X x0 F base.
  intros Hbase.
  repeat split.
  - intros A B Ha Hb.
    apply (pr2 Hbase).
    now apply UniformStructure_and ; apply (pr1 Hbase).
  - generalize (pr2 Hbase _ (UniformStructure_true F)).
    apply hinhfun.
    intros A.
    exists (pr1 A).
    exact (pr1 (pr2 A)).
  - intros A Ha.
    revert x0.
    apply hinhuniv.
    intros x0.
    apply (pr1 Hbase) in Ha.
    apply hinhpr.
    exists (x0,,x0).
    now apply (UniformStructure_diag F).
Qed.

Lemma isUSbase_filterbase {X : UU} (F : UniformStructure X) (base : (X × X -> hProp) -> hProp) :
  Π Hbase : isUSbase F base,
  Π P, (F P <-> filterbase base P).
Proof.
  intros X F base Hbase P.
  split.
  - intros HP.
    apply (pr2 Hbase P HP).
  - apply hinhuniv.
    intros A.
    apply UniformStructure_imply with (1 := pr2 (pr2 A)).
    apply (pr1 Hbase).
    exact (pr1 (pr2 A)).
Qed.

Lemma isUSbase_PreFilterBase {X : UU} (F : UniformStructure X) (base : (X × X -> hProp) -> hProp) :
  Π Hbase : isUSbase F base,
  Π P, (F P <-> PreFilterBase (base ,, isUSbase_isBaseOfPreFilter F base Hbase) P).
Proof.
  intros X F base Hbase P.
  now apply isUSbase_filterbase.
Qed.

Lemma isUSbase_FilterBase {X : UU} (x0 : ∥ X ∥) (F : UniformStructure X) (base : (X × X -> hProp) -> hProp) :
  Π Hbase : isUSbase F base,
  Π P, (F P <-> FilterBase (base ,, isUSbase_isBaseOfFilter x0 F base Hbase) P).
Proof.
  intros X x0 F base Hbase P.
  now apply isUSbase_filterbase.
Qed.

Definition isBaseOfUniformStructure {X : UU} (base : (X × X -> hProp) -> hProp) :=
  (isBaseOfPreFilter base)
    × (Π P, base P -> Π x : X, P (x,,x))
    × (Π P, base P -> ∃ P', base P' × Π x, P' x -> subset_inv P x)
    × (Π P, base P -> ∃ Q, base Q × Π x,  subset_square Q x -> P x).

Lemma isUSbase_BaseOfUniformStructure {X : UU} (F : UniformStructure X) (base : (X × X -> hProp) -> hProp) :
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
    intros x Hx.
    apply (pr2 (pr2 Q)).
    revert Hx.
    apply hinhfun.
    intros y.
    exists (pr1 y) ; split ;
    apply (pr2 (pr2 R)).
    exact (pr1 (pr2 y)).
    exact (pr2 (pr2 y)).
Qed.

Lemma isBaseOfUniformStructure_USbase {X : UU} (base : (X × X -> hProp) -> hProp) :
  Π Hbase : isBaseOfUniformStructure base,
    isUniformStructure (filterbase base).
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
  - apply isfilter_finite_intersection_carac.
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
    apply (pr2 (pr2 Q)).
    apply (pr1 (pr2 Hbase)), (pr1 (pr2 Q)).
  - intros P.
    apply hinhuniv.
    intros A.
    generalize (pr1 (pr2 (pr2 Hbase)) _ (pr1 (pr2 A))).
    apply hinhfun.
    intros B.
    exists (pr1 B).
    split.
    exact (pr1 (pr2 B)).
    intros x Bx.
    now apply (pr2 (pr2 A)), (pr2 (pr2 B)).
  - intros P.
    apply hinhuniv.
    intros A.
    generalize (pr2 (pr2 (pr2 Hbase)) _ (pr1 (pr2 A))).
    apply hinhfun.
    intros B.
    exists (pr1 B).
    split.
    apply hinhpr.
    now exists (pr1 B), (pr1 (pr2 B)).
    intros x Bx.
    now apply (pr2 (pr2 A)), (pr2 (pr2 B)).
Qed.

(** *** Topology in a Uniform Space *)
(** Prop 1 *)

Require Export UniMath.Topology.Topology.

Section UStopology.

Context {X : UU}.
Context (F : UniformStructure X).

Definition USneighborhood : X -> (X -> hProp) -> hProp :=
  (λ (x : X) (A : X → hProp),
    ∃ U : X × X → hProp, F U × (Π y : X, U (x,, y) → A y)).

Lemma USneighborhood_imply :
  Π x : X, isfilter_imply (USneighborhood x).
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
  Π x : X, isfilter_htrue (USneighborhood x).
Proof.
  intros x.
  apply hinhpr.
  exists (λ _, htrue).
  split.
  now apply UniformStructure_true.
  easy.
Qed.
Lemma USneighborhood_and :
  Π x : X, isfilter_and (USneighborhood x).
Proof.
  intros x A B.
  apply hinhfun2.
  intros Ua Ub.
  exists (λ x, pr1 Ua x ∧ pr1 Ub x).
  split.
  apply UniformStructure_and.
  exact (pr1 (pr2 Ua)).
  exact (pr1 (pr2 Ub)).
  intros y Hy ; split.
  now apply (pr2 (pr2 Ua)), (pr1 Hy).
  now apply (pr2 (pr2 Ub)), (pr2 Hy).
Qed.
Lemma USneighborhood_point :
  Π (x : X) (P : X → hProp), USneighborhood x P → P x.
Proof.
  intros x A.
  apply hinhuniv.
  intros Ua.
  apply (pr2 (pr2 Ua)).
  apply UniformStructure_diag with F.
  exact (pr1 (pr2 Ua)).
Qed.
Lemma USneighborhood_neighborhood :
  Π (x : X) (P : X → hProp),
    USneighborhood x P
    → ∃ Q : X → hProp,
        USneighborhood x Q × (Π y : X, Q y → USneighborhood y P).
Proof.
  intros x A.
  apply hinhuniv.
  intros Ua.
  generalize (UniformStructure_squareroot _ _ (pr1 (pr2 Ua))).
  apply hinhfun.
  intros Ub.
  exists (λ y, pr1 Ub (x,,y)).
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
  TopologicalSet.
Proof.
  intros X F.
  simple refine (TopologyFromNeighborhood _ _).
  - apply X.
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
  Π P : X -> hProp,
    locally (T := Topology_UniformSpace (pr2 X)) x P <-> USlocally x P.
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
  Π P : X × Y -> hProp,
    locally2d (T := Topology_UniformSpace (pr2 X)) (S := Topology_UniformSpace (pr2 Y)) x y P
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
  is_filter_lim (T := Topology_UniformSpace (pr2 X)) F x <-> is_filter_USlim F x.
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
  is_lim (T := Topology_UniformSpace (pr2 Y)) f F x <-> is_USlim f F x.
Proof.
  split ; intros H P Hp ; apply H.
  - apply (pr2 (USlocally_correct _ _)), Hp.
  - apply (pr1 (USlocally_correct _ _)), Hp.
Qed.

Definition UScontinuous_at {X Y : UniformSpace} (f : X → Y) (x : X) :=
  is_USlim f (USlocally x) (f x).
Definition UScontinuous_on {X Y : UniformSpace}
           (dom : X → hProp) (f : Π x : X, dom x → Y) :=
  Π (x : X) (Hx : dom x),
  ∃ H : Π P : X → hProp, (USlocally x) P → ∃ x0 : X, dom x0 ∧ P x0,
    is_USlim (λ y : Σ x0 : X, dom x0, f (pr1 y) (pr2 y))
             (FilterSubtype (USlocally x) dom H) (f x Hx).
Definition UScontinuous {X Y : UniformSpace} (f : X → Y)  :=
  Π x, UScontinuous_at f x.

Definition UScontinuous2d_at {X Y Z : UniformSpace} (f : X → Y → Z) (x : X) (y : Y) :=
  is_USlim (λ z : X × Y, f (pr1 z) (pr2 z)) (USlocally2d x y) (f x y).
Definition UScontinuous2d_on {X Y Z : UniformSpace}
           (dom : X → Y → hProp) (f : Π x y, dom x y → Z) :=
  Π x y (Hxy : dom x y),
  ∃ H,
    is_USlim (λ y : Σ z, dom (pr1 z) (pr2 z), f (pr1 (pr1 y)) (pr2 (pr1 y)) (pr2 y))
             (FilterSubtype (USlocally2d x y) (λ z, dom (pr1 z) (pr2 z)) H) (f x y Hxy).
Definition UScontinuous2d {X Y Z : UniformSpace} (f : X → Y → Z)  :=
  Π x y, UScontinuous2d_at f x y.

(** ** Uniform continuity *)

Definition UniformlyContinuous {X Y : UniformSpace} (f : X → Y) :=
  Π V, pr2 Y V → pr2 X (λ xx : X × X, V (f (pr1 xx) ,, f (pr2 xx))).

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
    apply (∃ (Ux : X × X → hProp) (Uy : Y × Y → hProp),
             (pr2 X Ux)
               × (pr2 Y Uy)
               × (Π x y, Ux x → Uy y → U ((pr1 x ,, pr1 y) ,, (pr2 x ,, pr2 y)))).
  - intros A B H.
    apply hinhfun.
    intros U.
    exists (pr1 U), (pr1 (pr2 U)).
    repeat split.
    exact (pr1 (pr2 (pr2 U))).
    exact (pr1 (pr2 (pr2 (pr2 U)))).
    intros x y Uxx Uyy.
    now apply H, (pr2 (pr2 (pr2 (pr2 U)))).
  - apply hinhpr.
    exists (λ _, htrue), (λ _, htrue).
    repeat split.
    + apply UniformStructure_true.
    + apply UniformStructure_true.
  - intros A B.
    apply hinhfun2.
    intros A' B'.
    exists (λ x, pr1 A' x ∧ pr1 B' x), (λ y, pr1 (pr2 A') y ∧ pr1 (pr2 B') y).
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
    rewrite (tppr xy).
    apply (pr2 (pr2 (pr2 (pr2 U))) (pr1 xy,,pr1 xy) (pr2 xy,,pr2 xy)).
    now apply (UniformStructure_diag (pr2 X)), (pr1 (pr2 (pr2 U))).
    now apply (UniformStructure_diag (pr2 Y)), (pr1 (pr2 (pr2 (pr2 U)))).
  - intros P.
    apply hinhfun.
    intros U.
    exists (subset_inv (pr1 U)), (subset_inv (pr1 (pr2 U))).
    repeat split.
    now apply UniformStructure_symm, (pr1 (pr2 (pr2 U))).
    now apply UniformStructure_symm, (pr1 (pr2 (pr2 (pr2 U)))).
    intros x y.
    apply (pr2 (pr2 (pr2 (pr2 U)))).
  - intros P.
    apply hinhuniv.
    intros U.
    generalize (UniformStructure_squareroot _ _ (pr1 (pr2 (pr2 U)))) (UniformStructure_squareroot _ _ (pr1 (pr2 (pr2 (pr2 U))))).
    apply hinhfun2.
    intros Qx Qy.
    exists (λ z : (X × Y) × X × Y,
                  pr1 Qx (pr1 (pr1 z) ,, pr1 (pr2 z))
                  ∧ pr1 Qy (pr2 (pr1 z) ,, pr2 (pr2 z))).
    split.
    + apply hinhpr.
      exists (pr1 Qx), (pr1 Qy).
      repeat split ; simpl.
      exact (pr1 (pr2 Qx)).
      exact (pr1 (pr2 Qy)).
      now rewrite <- tppr.
      now rewrite <- tppr.
    + intros xy.
      apply hinhuniv.
      intros z.
      rewrite (tppr xy), (tppr (pr1 xy)), (tppr (pr2 xy)).
      apply (pr2 (pr2 (pr2 (pr2 U))) (pr1 (pr1 xy),,pr1 (pr2 xy)) (pr2 (pr1 xy),,pr2 (pr2 xy))).
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
  exists V, (λ _, htrue).
  repeat split ; simpl.
  exact Hv.
  apply UniformStructure_true.
  intros xy.
  now rewrite <- tppr.
Qed.
Lemma UniformlyContinuous_pr2 {X Y : UniformSpace} :
  UniformlyContinuous (X := UniformSpace_dirprod X Y) (λ x : X × Y, pr2 x).
Proof.
  intros X Y V Hv.
  apply hinhpr.
  exists (λ _, htrue), V.
  repeat split ; simpl.
  apply UniformStructure_true.
  exact Hv.
  intros _ xy.
  now rewrite <- tppr.
Qed.

(** ** Complete spaces *)
(** *** Def 1 *)

Definition USsmall {X : UU} (F : UniformStructure X) (V : X × X -> hProp) (FV : F V) (A : X -> hProp) :=
  Π x y : X, A x -> A y -> V (x ,, y).

Lemma USsmall_square {X : UU} (F : UniformStructure X) (V : X × X -> hProp) (Fv : F V) (A B : X -> hProp) :
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
  Π (V : X × X -> hProp) (Hv : FX V),
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
  exists (λ y : X, pr1 Q (y,,pr1 x)).
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
  2: simple refine (H (λ x : X × X, V (f (pr1 x),,f (pr2 x))) _).
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