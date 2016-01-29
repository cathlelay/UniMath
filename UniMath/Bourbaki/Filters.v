(** * Results about Filters *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Export UniMath.Bourbaki.Topology.

(** ** Filter *)

Section Filter_def.

Context {X : UU}.
Context (F : (X -> hProp) -> hProp).

Definition isfilter_imply : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ A B : X -> hProp, (∀ x : X, A x -> B x) -> F A -> F B).
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply isapropimpl.
  apply isapropimpl.
  apply propproperty.
Defined.

Definition isfilter_finite_intersection : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ (n : nat) (L : (Σ m : nat, m < n) -> X -> hProp), (∀ m : Σ m : nat, m < n, F (L m)) -> F (finite_intersection n L)).
  apply impred_isaprop ; intros n.
  apply impred_isaprop ; intros L.
  apply isapropimpl.
  apply propproperty.
Defined.

Definition isfilter_notempty : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (¬ F (λ _ : X, hfalse)).
  apply isapropneg.
Defined.

Definition isfilter : hProp :=
  isfilter_imply ∧ isfilter_finite_intersection ∧ isfilter_notempty.

Lemma isfilter_finite_intersection_htrue :
  isfilter_finite_intersection -> F (λ _ : X, htrue).
Proof.
  intros Hand.
  rewrite <- (finite_intersection_htrue (λ _ _, htrue)).
  apply (Hand O (λ _ _, htrue)).
  intros (m,Hm).
  apply fromempty.
  revert Hm.
  now apply negnatlthn0.
Qed.
Lemma isfilter_finite_intersection_and :
  isfilter_finite_intersection -> ∀ A B : X -> hProp, F A -> F B -> F (λ x : X, A x ∧ B x).
Proof.
  intros Hand A B Fa Fb.
  rewrite <- (finite_intersection_and (λ _, hfalse)).
  apply Hand.
  intros (m,Hm) ; simpl.
  destruct m.
  exact Fa.
  destruct m.
  exact Fb.
  easy.
Qed.
Lemma isfilter_finite_intersection_carac :
  F (λ _, htrue) -> (∀ A B : X -> hProp, F A -> F B -> F (λ x : X, A x ∧ B x))
  -> isfilter_finite_intersection.
Proof.
  intros Htrue Hand n L Hl.
  induction n.
  - rewrite finite_intersection_htrue.
    exact Htrue.
  - rewrite finite_intersection_S.
    apply Hand.
    now apply Hl.
    apply IHn.
    intros m.
    now apply Hl.
Qed.

End Filter_def.

Lemma emptynofilter :
  ∀ F : (empty -> hProp) -> hProp,
    ¬ isfilter F.
Proof.
  intros F (Himp,(Hand,Hempty)).
  apply Hempty.
  apply isfilter_finite_intersection_htrue in Hand.
  assert ((λ _ : ∅, hfalse) = (λ _ : ∅, htrue)).
  apply funextfun, fromempty.
  rewrite X.
  exact Hand.
Qed.

Definition Filter {X : UU} := Σ F : (X -> hProp) -> hProp, isfilter F.
Definition pr1Filter {X : UU} (F : Filter (X := X)) : (X -> hProp) -> hProp := pr1 F.
Coercion pr1Filter : Filter >-> Funclass.

Definition mkFilter {X : UU} (F : (X -> hProp) -> hProp) (Himp : isfilter_imply F) (Hand : isfilter_finite_intersection F) (Hempty : isfilter_notempty F) : Filter :=
  F,, Himp,, Hand,, Hempty.
Definition mkFilter' {X : UU} (F : (X -> hProp) -> hProp) (Himp : isfilter_imply F) (Htrue : F (λ _ : X, htrue)) (Hand : ∀ A B : X -> hProp, F A -> F B -> F (λ x : X, A x ∧ B x)) (Hempty : isfilter_notempty F) : Filter :=
  mkFilter F Himp (isfilter_finite_intersection_carac F Htrue Hand) Hempty.

Section Filter_pty.

Context {X : UU}.
Context (F : Filter (X := X)).

Lemma filter_imply :
  isfilter_imply F.
Proof.
  exact (pr1 (pr2 F)).
Qed.
Lemma filter_finite_intersection :
  isfilter_finite_intersection F.
Proof.
  exact (pr1 (pr2 (pr2 F))).
Qed.
Lemma filter_htrue :
  F (λ _ : X, htrue).
Proof.
  apply isfilter_finite_intersection_htrue.
  exact filter_finite_intersection.
Qed.
Lemma filter_and :
  ∀ A B : X -> hProp, F A -> F B -> F (λ x : X, A x ∧ B x).
Proof.
  apply isfilter_finite_intersection_and.
  exact filter_finite_intersection.
Qed.
Lemma filter_notempty :
  isfilter_notempty F.
Proof.
  exact (pr2 (pr2 (pr2 F))).
Qed.
Lemma filter_forall :
  ∀ A : X -> hProp, (∀ x : X, A x) -> F A.
Proof.
  intros A Ha.
  generalize filter_htrue.
  apply filter_imply.
  intros x _.
  now apply Ha.
Qed.
Lemma filter_const :
  ∀ A : hProp, F (λ _ : X, A) -> ¬ (¬ A).
Proof.
  intros A Fa Ha.
  apply filter_notempty.
  revert Fa.
  apply filter_imply.
  intros _.
  exact Ha.
Qed.

End Filter_pty.

Definition filter_le {X : UU} (F G : Filter) :=
  ∀ A : X -> hProp, F A -> G A.

Definition filter_bot {X : UU} (x0 : X) : Filter (X := X).
Proof.
  simple refine (mkFilter' _ _ _ _ _).
  - intros A.
    simple refine (hProppair _ _).
    apply (∀ x, A x).
    apply impred_isaprop ; intros x.
    apply propproperty.
  - simpl ; intros A B H Ha x.
    apply H, Ha.
  - simpl ; intros x.
    apply tt.
  - simpl ; intros A B Ha Hb x.
    split.
    apply Ha.
    apply Hb.
  - simpl ; intro H.
    apply H.
    apply x0.
Defined.

Lemma filter_bot_correct {X : UU} :
  ∀ (x0 : X) (F : Filter), filter_le (filter_bot x0) F.
Proof.
  intros x0 F A Ha.
  apply filter_forall, Ha.
Qed.

Definition filter_intersection {X : UU} (FF : Filter (X := X) -> hProp) (Hff : ¬ (∀ F : Filter, ¬ FF F)) : Filter (X := X).
Proof.
  simple refine (mkFilter' _ _ _ _ _).
  - intros A.
    simple refine (hProppair _ _).
    apply (∀ F : Filter, FF F -> F A).
    apply impred_isaprop ; intros F.
    apply isapropimpl.
    apply propproperty.
  - simpl ; intros A B H Ha F Hf.
    refine (filter_imply _ _ _ _ _).
    apply H.
    apply Ha, Hf.
  - simpl ; intros F Hf.
    now apply filter_htrue.
  - simpl ; intros A B Ha Hb F Hf.
    apply filter_and.
    apply Ha, Hf.
    apply Hb, Hf.
  - simpl ; intro Hf.
    apply Hff.
    intros F Hf'.
    apply (filter_notempty F).
    apply Hf, Hf'.
Defined.

Lemma filter_intersection_correct {X : UU} (FF : Filter (X := X) -> hProp) (Hff : ¬ (∀ F : Filter, ¬ FF F)) :
  (∀ F : Filter, FF F -> filter_le (filter_intersection FF Hff) F)
× (∀ F : Filter, (∀ G : Filter, FF G -> filter_le F G) -> filter_le F (filter_intersection FF Hff)).
Proof.
  split.
  - intros F Hf A Ha.
    apply Ha.
    exact Hf.
  - intros F H A Fa G Hg.
    apply H.
    apply Hg.
    apply Fa.
Qed.

Definition generated_filter {X : UU} (L : (X -> hProp) -> hProp) (Hl : ∀ n (L' : (Σ m : nat, m < n) -> X -> hProp), (∀ m, L (L' m)) -> ¬ ∀ x : X, ¬ finite_intersection n L' x) : Filter (X := X).
Proof.
  simple refine (mkFilter' _ _ _ _ _).
  - intros A.
    apply (∃ (n : nat) (L' : (Σ m : nat, m < n) -> X -> hProp), (∀ m : Σ m : nat, m < n, L (L' m)) × (∀ x : X, finite_intersection n L' x -> A x)).
  - intros A B H.
    apply hinhfun ; intro Ha.
    exists (pr1 Ha), (pr1 (pr2 Ha)).
    split.
    apply (pr1 (pr2 (pr2 Ha))).
    intros x Hx.
    apply H.
    apply (pr2 (pr2 (pr2 Ha))), Hx.
  - apply hinhpr.
    exists O, (λ _ _, htrue).
    split.
    intros (m,Hm).
    easy.
    easy.
  - intros A B.
    apply hinhfun2.
    intros Ha Hb.
    exists (pr1 Ha + pr1 Hb).
    simple refine (tpair _ _ _).
    intros m.
    destruct (natlthorgeh (pr1 m) (pr1 Ha)) as [Hm | Hm].
    apply (pr1 (pr2 Ha) (pr1 m ,, Hm)).
    assert (Hm' : (pr1 m - pr1 Ha) < pr1 Hb).
    { apply natlthandplusrinv with (pr1 Ha).
      rewrite minusplusnmm, (natpluscomm (pr1 Hb)).
      exact (pr2 m).
      exact Hm. }
    apply (pr1 (pr2 Hb) ((pr1 m - pr1 Ha) ,, Hm')).
    split.
    + intros m.
      destruct natlthorgeh as [Hm | Hm].
      simpl ; apply (pr1 (pr2 (pr2 Ha))).
      simpl ; apply (pr1 (pr2 (pr2 Hb))).
    + split.
      * apply (pr2 (pr2 (pr2 Ha))).
        intros m.
        assert (Hm : pr1 m < pr1 Ha + pr1 Hb).
        { refine (natlthlehtrans _ _ _ _ _).
          apply (pr2 m).
          apply natlehnplusnm. }
        generalize (X0 (pr1 m ,, Hm)).
        destruct natlthorgeh ; simpl.
        destruct m as [m Hm'] ; simpl.
        assert (h = Hm').
        apply (pr2 (_ < _)).
        now rewrite X1.
        apply fromempty.
        revert h.
        apply natlthtonegnatgeh.
        apply (pr2 m).
      * apply (pr2 (pr2 (pr2 Hb))).
        intros m.
        assert (Hm : pr1 Ha + pr1 m < pr1 Ha + pr1 Hb).
        { apply natlthandplusl.
          apply (pr2 m). }
        generalize (X0 (pr1 Ha + pr1 m ,, Hm)).
        destruct natlthorgeh ; simpl.
        apply fromempty.
        revert h.
        apply natgehtonegnatlth.
        apply natgehplusnmn.
        assert ((pr1 Ha + pr1 m - pr1 Ha,,
      natlthandplusrinv (pr1 Ha + pr1 m - pr1 Ha)
        (pr1 Hb) (pr1 Ha)
        (internal_paths_rew_r nat (pr1 Ha + pr1 m - pr1 Ha + pr1 Ha)
           (pr1 Ha + pr1 m) (λ n : nat, natgtb (pr1 Hb + pr1 Ha) n = true)
           (internal_paths_rew_r nat (pr1 Hb + pr1 Ha)
              (pr1 Ha + pr1 Hb) (λ n : nat, natgtb n (pr1 Ha + pr1 m) = true)
              Hm (natpluscomm (pr1 Hb) (pr1 Ha)))
           (minusplusnmm (pr1 Ha + pr1 m) (pr1 Ha) h))) = m).
        apply subtypeEquality_prop ; simpl.
        now rewrite (natpluscomm _ (pr1 m)), plusminusnmm.
        pattern m at 7.
        now rewrite <- X1.
  - intro H ; revert H.
    apply (hinhuniv (P := hProppair _ isapropempty)).
    intros H.
    simple refine (Hl _ _ _ _).
    apply (pr1 H).
    apply (pr1 (pr2 H)).
    apply (pr1 (pr2 (pr2 H))).
    intros x Hx.
    refine (pr2 (pr2 (pr2 H)) _ _).
    exact Hx.
Defined.

Lemma generated_filter_correct {X : UU} :
   ∀ (L : (X -> hProp) -> hProp)
   (Hl : ∀ (n : nat) (L' : (Σ m : nat, m < n) -> (X -> hProp)),
         (∀ (m : Σ m : nat, m < n), L (L' m)) ->
         ¬ (∀ x : X, ¬ finite_intersection n L' x)),
   (∀ A : X -> hProp, L A -> (generated_filter L Hl) A)
   × (∀ F : Filter,
      (∀ A : X -> hProp, L A -> F A) -> filter_le (generated_filter L Hl) F).
Proof.
  intros L Hl.
  split.
  - intros A La.
    apply hinhpr.
    exists 1.
    simple refine (tpair _ _ _).
    intros _.
    apply A.
    split.
    + easy.
    + intros x Hx.
      apply (Hx (O,,paths_refl _)).
  - intros F Hf A.
    apply hinhuniv.
    intros Ha.
    refine (filter_imply _ _ _ _ _).
    apply (pr2 (pr2 (pr2 Ha))).
    apply filter_finite_intersection.
    intros m.
    apply Hf.
    apply (pr1 (pr2 (pr2 Ha))).
Qed.

Lemma generated_filter_inv {X : UU} :
   ∀ (L : (X -> hProp) -> hProp) (F : Filter),
   (∀ A : X -> hProp, L A -> F A) ->
   ∀ (n : nat) (L' : (Σ m : nat, m < n) -> X -> hProp),
   (∀ (m : Σ m : nat, m < n), L (L' m)) ->
   ¬ (∀ x : X, ¬ finite_intersection n L' x).
Proof.
  intros L F Hf n L' Hl' H.
  apply (filter_notempty F).
  refine (filter_imply _ _ _ _ _).
  apply H.
  apply filter_finite_intersection.
  intros m.
  apply Hf, Hl'.
Qed.

Lemma ex_filter_le {X : UU} :
  ∀ (F : Filter) (A : X -> hProp),
    (Σ G : Filter, filter_le F G × G A)
    <-> (∀ B : X -> hProp, F B -> ¬ (∀ x : X, A x -> B x -> ∅)).
Proof.
  intros F A.
  split.
  - intros G B Fb H.
    simple refine (generated_filter_inv _ _ _ _ _ _ _).
    + exact X.
    + intros C.
      apply (F C ∨ C = A).
    + apply (pr1 G).
    + intros C.
      apply hinhuniv.
      intros [Fc | ->].
      apply (pr1 (pr2 G)), Fc.
      apply (pr2 (pr2 G)).
    + apply 2.
    + intros m x.
      destruct (pr1 m).
      apply (A x).
      destruct n.
      apply (B x).
      apply (B x).
    + intros m.
      apply hinhpr.
      destruct (pr1 m) ; simpl.
      now right.
      destruct n ; now left.
    + intros x.
      rewrite finite_intersection_and.
      intros H0.
      apply (H x).
      apply (pr1 H0).
      apply (pr2 H0).
  - intros H.
    simple refine (tpair _ _ _).
    simple refine (generated_filter _ _).
    + intros B.
      apply (F B ∨ B = A).
    + intros n L Hl Hl'.
      assert (B : ∃ B : X -> hProp, F B × (∀ x, (A x ∧ B x -> A x ∧ finite_intersection n L x))).
      { clear Hl'.
        induction n.
        - apply hinhpr.
          rewrite finite_intersection_htrue.
          exists (λ _, htrue).
          split.
          + apply filter_htrue.
          + easy.
        - rewrite finite_intersection_S.
          refine (hinhuniv _ _).
          2: apply (IHn ((λ m : Σ m : nat, m < n, L (S (pr1 m),, pr2 m)))).
          intros (B,(Fb,Hb)).
          generalize (Hl (0,, idpath (natgtb (S n) 0))).
          apply hinhfun.
          intros [Fl | Fl].
          + refine (tpair _ _ _).
            split.
            * apply filter_and.
              apply Fb.
              apply Fl.
            * intros x (H0,(H1,H2)) ; repeat split.
              apply H0.
              apply H2.
              simple refine (pr2 (Hb x _)).
              split.
              apply H0.
              apply H1.
          + rewrite Fl.
            exists B ; split.
            * exact Fb.
            * intros x (H0,H1) ; repeat split.
              apply H0.
              apply H0.
              simple refine (pr2 (Hb x _)).
              split.
              apply H0.
              apply H1.
          + intros.
            apply Hl. }
      revert B.
      apply (hinhuniv (P := hProppair _ isapropempty)).
      intros (B,(Fb,Hb)).
      apply (H B Fb).
      intros x Ax Bx.
      apply (Hl' x).
      simple refine (pr2 (Hb x _)).
      split.
      apply Ax.
      apply Bx.
    + split.
      intros B Fb.
      apply hinhpr.
      exists 1, (λ _, B).
      split.
      intros _.
      apply hinhpr.
      now left.
      intros x Hx.
      apply (Hx (0 ,, paths_refl _)).
      apply hinhpr.
      exists 1, (λ _, A).
      split.
      intros _.
      apply hinhpr.
      now right.
      intros x Hx.
      apply (Hx (0 ,, paths_refl _)).
Qed.

(** ** Base of a filter *)

Definition mkFilter_base {X : UU} (x0 : X) (base : (X -> hProp) -> hProp) (Hand : ∀ A B : X -> hProp, base A -> base B -> ∃ C : X -> hProp, base C × (∀ x, C x -> A x ∧ B x)) (Hempty : ∃ A : X -> hProp, base A) (Hfalse : ¬ (base (λ _, hfalse))) : Filter (X := X).
Proof.
  simple refine (mkFilter' _ _ _ _ _).
  - intros A.
    apply (∃ B : X -> hProp, base B × ∀ x, B x -> A x).
  - intros A B H.
    apply hinhfun.
    intros A'.
    exists (pr1 A').
    split.
    apply (pr1 (pr2 A')).
    intros x Hx.
    apply H.
    now apply (pr2 (pr2 A')).
  - revert Hempty.
    apply hinhfun.
    intros A.
    exists (pr1 A).
    split.
    apply (pr2 A).
    easy.
  - intros A B.
    apply hinhuniv2.
    intros A' B'.
    refine (hinhfun _ _).
    2: apply Hand.
    2: (apply (pr1 (pr2 A'))).
    2: (apply (pr1 (pr2 B'))).
    intros C'.
    exists (pr1 C').
    split.
    apply (pr1 (pr2 C')).
    intros x Cx ; split.
    apply (pr2 (pr2 A')).
    now refine (pr1 (pr2 (pr2 C') _ _)).
    apply (pr2 (pr2 B')).
    now refine (pr2 (pr2 (pr2 C') _ _)).
  - intros H ; revert H.
    apply (hinhuniv (P := hProppair _ isapropempty)).
    intros A.
    apply Hfalse.
    assert ((λ _ : X, hfalse) = (pr1 A)).
    { apply funextfun ; intro x.
      apply uahp.
      apply fromempty.
      apply (pr2 (pr2 A)). }
    rewrite X0 ; clear X0.
    apply (pr1 (pr2 A)).
Defined.