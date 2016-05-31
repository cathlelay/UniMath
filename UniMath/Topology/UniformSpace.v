(** * Uniform Space *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Export UniMath.Topology.Complements.
Require Import UniMath.Topology.Complements.
Require Export UniMath.Topology.Filters.


(** ** Uniform Spaces *)
(** *** Definitions *)

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
Lemma subset_pow_S {X : hSet} (A : X × X -> hProp) (n : nat) :
  subset_pow A (S n) = subset_prod A (subset_pow A n).
Proof.
  intros X A.
  easy.
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

Lemma isdiag_square {X : UU} (A : X × X -> hProp) :
  (∀ x : X, A (x,,x)) -> ∀ x, A x -> subset_square A x.
Proof.
  intros X A Hdiag (x,y) Axy.
  apply hinhpr.
  exists x.
  split.
  now apply Hdiag.
  exact Axy.
Qed.

(** Def 1: Uniform Space *)

Definition isUS_diag {X : UU} (F : (X × X -> hProp) -> hProp) :=
  ∀ P, F P -> ∀ x : X, P (x ,, x).
Definition isUS_symm {X : UU} (F : (X × X -> hProp) -> hProp) :=
  ∀ P, F P -> F (subset_inv P).
Definition isUS_squareroot {X : UU} (F : (X × X -> hProp) -> hProp) :=
  ∀ P, F P -> ∃ Q, F Q × ∀ x : X × X, subset_square Q x -> P x.

Definition isUS_prod_inv {X : UU} (F : (X × X -> hProp) -> hProp) :=
  ∀ P, F P -> ∃ Q, F Q × ∀ x : X × X, subset_prod Q (subset_inv Q) x -> P x.

Lemma isUS_prod_inv_imply_symm {X : UU} (F : (X × X -> hProp) -> hProp) :
  (isfilter_imply (X := X × X) F) -> (isUS_diag F) -> isUS_prod_inv F -> isUS_symm F.
Proof.
  intros X F Himpl Hdiag H.
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
Lemma isUS_prod_inv_imply_squareroot {X : UU} (F : (X × X -> hProp) -> hProp) :
  (isfilter_imply (X := X × X) F) -> (∀ A B : X × X → hProp, F A → F B → F (λ x : X × X, A x ∧ B x))
  -> (isUS_diag F) -> isUS_prod_inv F -> isUS_squareroot F.
Proof.
  intros X F Himpl Hand Hdiag H.
  intros P FP.
  generalize (H P FP).
  apply hinhfun.
  intros (Q,(FQ,HQ)).
  exists (λ x, Q x ∧ subset_inv Q x).
  split.
  - apply Hand.
    exact FQ.
    now apply isUS_prod_inv_imply_symm.
  - intros x Hx.
    apply HQ.
    revert Hx.
    apply hinhfun.
    intros (y,((Qy1,_),(_,Qy2))).
    now exists y.
Qed.

Lemma isUS_symm_squareroot_imply_prod_inv {X : UU} (F : (X × X -> hProp) -> hProp) :
  (isfilter_imply (X := X × X) F) -> (∀ A B : X × X → hProp, F A → F B → F (λ x : X × X, A x ∧ B x))
  -> (isUS_diag F) -> isUS_symm F -> isUS_squareroot F -> isUS_prod_inv F.
Proof.
  intros X F Himpl Hand Hdiag Hsymm Hsqr.
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
  ∀ A B : X × X → hProp, (∀ x : X × X, A x → B x) → F A → F B.
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
   ∀ A B : X × X → hProp, F A → F B → F (λ x : X × X, A x ∧ B x).
Proof.
  intros X F.
  apply isfilter_finite_intersection_and, UniformStructure_finite_intersection.
Qed.
Lemma UniformStructure_diag {X : UU} (F : UniformStructure X) :
  ∀ P, F P -> ∀ x : X, P (x ,, x).
Proof.
  intros X F.
  apply (pr1 (pr2 (pr2 (pr2 F)))).
Qed.
Lemma UniformStructure_symm {X : UU} (F : UniformStructure X) :
  ∀ P, F P -> F (subset_inv P).
Proof.
  intros X F.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 F))))).
Qed.
Lemma UniformStructure_squareroot {X : UU} (F : UniformStructure X) :
  ∀ P, F P -> ∃ Q, F Q × ∀ x : X × X, subset_square Q x -> P x.
Proof.
  intros X F.
  apply (pr2 (pr2 (pr2 (pr2 (pr2 F))))).
Qed.
Lemma UniformStructure_prod_inv {X : UU} (F : UniformStructure X) :
  ∀ P, F P -> ∃ Q, F Q × ∀ x : X × X, subset_prod Q (subset_inv Q) x -> P x.
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
  - abstract (intro H ;
               simple refine (hinhuniv' isapropempty _ x0) ;
               clear x0 ; intros x0 ;
               apply ((pr1 (pr2 (pr2 (pr2 F)))) _ H x0)).
Defined.

Lemma UniformStructure_square {X : UU} (F : UniformStructure X) :
  ∀ P, F P -> F (subset_square P).
Proof.
  intros X F P Fp.
  apply UniformStructure_imply with (2 := Fp).
  intros (x,y) Pxy.
  apply hinhpr.
  exists x ; split.
  now apply (UniformStructure_diag F).
  exact Pxy.
Qed.

Definition UniformSpace :=
  Σ (X : UU), UniformStructure X.
Definition pr1UniformSpace : UniformSpace -> UU := pr1.
Coercion pr1UniformSpace : UniformSpace >-> UU.

(** Def 2: Foundamental System of Uniform Structure *)

Definition isUSbase {X : UU} (F : UniformStructure X) (base : (X × X → hProp) → hProp) :=
  (∀ (P : X × X → hProp), base P -> F P)
    × (∀ (P : X × X → hProp), F P → ∃ Q : X × X → hProp, base Q × (∀ x : X × X, Q x → P x)).


Lemma isUSbase_pow {X : hSet} (F : UniformStructure X) (B : (X × X → hProp) → hProp) :
  isUSbase F B -> isUSbase F (λ P, ∃ (n : nat) Q, (O < n) × B Q × P = subset_pow Q n).
Proof.
  intros X F B (Hincl,Hrep).
  split.
  - intros P.
    apply hinhuniv.
    intros (n,(Q,(Hn,(BQ,->)))).
    destruct n.
    now apply fromempty.
    clear Hn.
    induction n.
    rewrite subset_pow_1.
    now apply Hincl.
    generalize (Hrep _ IHn).
    apply hinhuniv.
    intros (Q',(BQ',HQ')).
    generalize (UniformStructure_and F _ _ (Hincl _ BQ) (Hincl _ BQ')).
    apply (UniformStructure_imply F).
    intros (x,y) (Qx,Q'x).
    rewrite subset_pow_S.
    apply hinhpr.
    exists x.
    split.
    apply (UniformStructure_diag F).
    now apply Hincl.
    now apply HQ'.
  - intros P Hp.
    generalize (Hrep P Hp).
    apply hinhfun.
    intros (Q,(Bq,Hq)).
    exists Q ; split.
    apply hinhpr.
    exists 1%nat, Q.
    now rewrite subset_pow_1.
    exact Hq.
Qed.

Definition issymmsubset {X : UU} (P : X × X -> hProp) :=
  (∀ x, P x <-> subset_inv P x).
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
  now intros (x,y) ; split ; intros (Hp,Hp') ; split.
Qed.
Lemma issymmsubset_or {X : UU} (F : UniformStructure X) (P : X × X -> hProp) :
  F P -> issymmsubset (λ x, P x ∨ subset_inv P x).
Proof.
  intros X F P Fp.
  intros (x,y) ; split ; apply hinhfun ; intros [Hp | Hp'].
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
    intros (Q,(Fq,H)).
    exists (subset_prod Q (subset_inv Q)).
    repeat split.
    4: apply H.
    + apply (UniformStructure_imply) with (2 := Fq).
      intros (x,y) Hp.
      apply hinhpr.
      exists y.
      split.
      exact Hp.
      apply (UniformStructure_diag F).
      now apply (UniformStructure_symm F).
    + apply hinhfun.
      intros (y,(Hy,Hy')).
      exists y ; now split.
    + apply hinhfun.
      intros (y,(Hy,Hy')).
      exists y ; now split.
    + exact HP.
Qed.

Lemma isUSbase_isBaseOfPreFilter {X : UU} (F : UniformStructure X) (base : (X × X -> hProp) -> hProp) :
  isUSbase F base -> (isBaseOfPreFilter base).
Proof.
  intros X F base.
  intros (Hincl,Hrep).
  split.
  - intros A B Ha Hb.
    apply Hrep.
    now apply UniformStructure_and ; apply Hincl.
  - generalize (Hrep _ (UniformStructure_true F)).
    apply hinhfun.
    intros (A,(Ha,_)).
    exists A.
    exact Ha.
Qed.
Lemma isUSbase_isBaseOfFilter {X : UU} (x0 : ∥X∥) (F : UniformStructure X) (base : (X × X -> hProp) -> hProp) :
  isUSbase F base -> (isBaseOfFilter base).
Proof.
  intros X x0 F base.
  intros (Hincl,Hrep).
  repeat split.
  - intros A B Ha Hb.
    apply Hrep.
    now apply UniformStructure_and ; apply Hincl.
  - generalize (Hrep _ (UniformStructure_true F)).
    apply hinhfun.
    intros (A,(Ha,_)).
    exists A.
    exact Ha.
  - intros H.
    revert x0.
    apply hinhuniv'.
    apply isapropempty.
    intros x0.
    apply Hincl in H.
    apply (UniformStructure_diag _ _ H x0).
Qed.

Lemma isUSbase_filterbase {X : UU} (F : UniformStructure X) (base : (X × X -> hProp) -> hProp) :
  ∀ Hbase : isUSbase F base,
  ∀ P, (F P <-> filterbase base P).
Proof.
  intros X F base Hbase P.
  split.
  - intros HP.
    apply (pr2 Hbase P HP).
  - apply hinhuniv.
    intros (A,(Ha,H)).
    apply UniformStructure_imply with (1 := H).
    now apply (pr1 Hbase).
Qed.

Lemma isUSbase_PreFilterBase {X : UU} (F : UniformStructure X) (base : (X × X -> hProp) -> hProp) :
  ∀ Hbase : isUSbase F base,
  ∀ P, (F P <-> PreFilterBase (base ,, isUSbase_isBaseOfPreFilter F base Hbase) P).
Proof.
  intros X F base Hbase P.
  now apply isUSbase_filterbase.
Qed.

Lemma isUSbase_FilterBase {X : UU} (x0 : ∥ X ∥) (F : UniformStructure X) (base : (X × X -> hProp) -> hProp) :
  ∀ Hbase : isUSbase F base,
  ∀ P, (F P <-> FilterBase (base ,, isUSbase_isBaseOfFilter x0 F base Hbase) P).
Proof.
  intros X x0 F base Hbase P.
  now apply isUSbase_filterbase.
Qed.

Definition isBaseOfUniformStructure {X : UU} (base : (X × X -> hProp) -> hProp) :=
  (isBaseOfPreFilter base)
    × (∀ P, base P -> ∀ x : X, P (x,,x))
    × (∀ P, base P -> ∃ P', base P' × ∀ x, P' x -> subset_inv P x)
    × (∀ P, base P -> ∃ Q, base Q × ∀ x,  subset_square Q x -> P x).

Lemma isUSbase_BaseOfUniformStructure {X : UU} (F : UniformStructure X) (base : (X × X -> hProp) -> hProp) :
  isUSbase F base -> isBaseOfUniformStructure base.
Proof.
  intros X F base.
  intros (Himpl,Hrep).
  split.
  now apply (isUSbase_isBaseOfPreFilter F).
  repeat split.
  - intros P Hp.
    apply UniformStructure_diag with F.
    now apply Himpl.
  - intros P Hp.
    apply Hrep.
    now apply UniformStructure_symm, Himpl.
  - intros P Hp.
    generalize (UniformStructure_squareroot F _ (Himpl _ Hp)).
    apply hinhuniv ; intros (Q,(Fq,Hq)).
    generalize (Hrep _ Fq).
    apply hinhfun.
    intros (R,(Hr,H)).
    exists R.
    split.
    exact Hr.
    intros x Hx.
    apply Hq.
    revert Hx.
    apply hinhfun.
    intros (y,(R1,R2)).
    exists y ; split ;
    now apply H.
Qed.

Lemma isBaseOfUniformStructure_USbase {X : UU} (base : (X × X -> hProp) -> hProp) :
  ∀ Hbase : isBaseOfUniformStructure base,
    isUniformStructure (filterbase base).
Proof.
  intros X base ((Hand,Hne),(Hdiag,(Hinv,Hsqr))).
  repeat split.
  - intros A B H.
    apply hinhfun.
    intros (C,(Hc,Hc')).
    exists C ; split.
    exact Hc.
    intros x Hx.
    now apply H, Hc'.
  - apply isfilter_finite_intersection_carac.
    + revert Hne.
      apply hinhfun.
      intros (A,Ha).
      exists A ; easy.
    + intros A B.
      apply hinhuniv2.
      intros (A',(Ha,Ha')) (B',(Hb,Hb')).
      generalize (Hand _ _ Ha Hb).
      apply hinhfun.
      intros (C,(Hc,Hc')).
      exists C ; split.
      exact Hc.
      intros x Cx ; split.
      apply Ha'.
      apply (pr1 (Hc' _ Cx)).
      apply Hb'.
      apply (pr2 (Hc' _ Cx)).
  - intros P Hp x.
    revert Hp.
    apply hinhuniv.
    intros (Q,(Hq,H)).
    apply H.
    now apply Hdiag.
  - intros P.
    apply hinhuniv.
    intros (A,(Ha,Ha')).
    generalize (Hinv _ Ha).
    apply hinhfun.
    intros (B,(Hb,Hb')).
    exists B.
    split.
    exact Hb.
    intros x Bx.
    now apply Ha', Hb'.
  - intros P.
    apply hinhuniv.
    intros (A,(Ha,Ha')).
    generalize (Hsqr _ Ha).
    apply hinhfun.
    intros (B,(Hb,Hb')).
    exists B.
    split.
    apply hinhpr.
    now exists B.
    intros x Bx.
    now apply Ha', Hb'.
Qed.

(** *** Topology in a Uniform Space *)
(** Prop 1 *)

Require Export UniMath.Topology.Topology.

Definition Topology_UniformSpace {X : UU} (F : UniformStructure X) :
  TopologicalSet.
Proof.
  intros X F.
  simple refine (TopologyFromNeighborhood _ _).
  - apply X.
  - intros x A.
    apply (∃ U, F U × ∀ y : X, U (x ,, y) -> A y).
  - repeat split.
    + intros x A B H.
      apply hinhfun.
      intros (Ua,(Fa,Ha)).
      exists Ua.
      split.
      apply Fa.
      now intros y H0 ; apply H, Ha.
    + intros x.
      apply hinhpr.
      exists (λ _, htrue).
      split.
      now apply UniformStructure_true.
      easy.
    + intros x A B.
      apply hinhfun2.
      intros (Ua,(Fa,Ha)) (Ub,(Fb,Hb)).
      exists (λ x, Ua x ∧ Ub x).
      split.
      now apply UniformStructure_and.
      intros y.
      intros (Ay,By) ; split.
      now apply Ha.
      now apply Hb.
    + intros x A.
      apply hinhuniv.
      intros (Ua,(Fa,Ha)).
      apply Ha.
      now apply UniformStructure_diag with F.
    + intros x A.
      apply hinhuniv.
      intros (Ua,(Fa,Ha)).
      generalize (UniformStructure_squareroot _ _ Fa).
      apply hinhfun.
      intros (Ub,(Fb,Hb)).
      exists (λ y, Ub (x,,y)).
      split.
      apply hinhpr.
      now exists Ub.
      intros y Qy.
      apply hinhpr.
      exists Ub.
      split.
      apply Fb.
      intros z Hz.
      apply Ha, Hb.
      apply hinhpr.
      now exists y ; split.
Defined.

(** ** Complete spaces *)
(** *** Def 1 *)

Definition USsmall {X : UU} (F : UniformStructure X) (V : X × X -> hProp) (FV : F V) (A : X -> hProp) :=
  ∀ x y : X, A x -> A y -> V (x ,, y).

Lemma USsmall_square {X : UU} (F : UniformStructure X) (V : X × X -> hProp) (Fv : F V) (A B : X -> hProp) :
  USsmall F V Fv A -> USsmall F V Fv B -> (∃ z, A z ∧ B z)
  -> USsmall F (subset_square V) (UniformStructure_square F V Fv) (λ x , A x ∨ B x).
Proof.
  intros X F V Fv A B Ha Hb Hex x y.
  apply hinhuniv2.
  intros [Ax | Bx] [Ay | By].
  - apply isdiag_square.
    now apply (UniformStructure_diag F).
    now apply Ha.
  - revert Hex.
    apply hinhfun.
    intros (z,(Az,Bz)).
    exists z ; split.
    now apply Ha.
    now apply Hb.
  - revert Hex.
    apply hinhfun.
    intros (z,(Az,Bz)).
    exists z ; split.
    now apply Hb.
    now apply Ha.
  - apply isdiag_square.
    now apply (UniformStructure_diag F).
    now apply Hb.
Qed.

Definition isCauchy_filter {X : UU} (FX : UniformStructure X) (F : Filter X) :=
  ∀ (V : X × X -> hProp) (Hv : FX V),
  ∃ A : X -> hProp, USsmall FX V Hv A × F A.

Lemma exfilterlim_cauchy {X : UU} (FX : UniformStructure X) (F : Filter X) :
  ex_filter_lim (T := Topology_UniformSpace FX) F
  -> isCauchy_filter FX F.
Proof.
  intros X FX F Hf V Hv.
  revert Hf.
  apply hinhuniv.
  intros (x,Hx).
  generalize (UniformStructure_prod_inv _ _ Hv).
  apply hinhfun.
  intros (Q,(Fq,Hq)).
  exists (λ y : Topology_UniformSpace FX, Q (y,,x)).
  split.
  - intros y z Qy Qz.
    apply Hq.
    apply hinhpr.
    now exists x.
  - apply Hx.
    apply TopologyFromNeighborhood_correct.
    apply hinhpr.
    exists (subset_inv Q).
    split.
    now apply UniformStructure_symm.
    easy.
Qed.