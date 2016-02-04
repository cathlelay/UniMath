(** * Results about Topology *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Export UniMath.Bourbaki.Complements.
Require Export UniMath.Bourbaki.Filters.


Section OpenSet.

Context {X : UU}.
Context (isOpen : (X -> hProp) -> hProp).

Definition isOpenSet_infinite_union : hProp :=
  hProppair
    (∀ P : (X -> hProp) -> hProp,
       (∀ A : X -> hProp, P A -> isOpen A) -> isOpen (infinite_union P))
    (impred_isaprop _ (λ _, isapropimpl _ _ (propproperty _))).
Definition isOpenSet_finite_intersection : hProp :=
  hProppair
    (∀ (P : Sequence (X -> hProp)), (∀ m, isOpen (P m)) -> isOpen (finite_intersection P))
    (impred_isaprop _ (λ _, isapropimpl _ _ (propproperty _))).

Lemma isOpenSet_hfalse :
  isOpenSet_infinite_union
  -> isOpen (λ _ : X, hfalse).
Proof.
  intros H0.
  rewrite <- infinite_union_hfalse.
  apply H0.
  intro.
  apply fromempty.
Qed.

Lemma isOpenSet_finite_intersection_htrue :
  isOpenSet_finite_intersection
  -> isOpen (λ _, htrue).
Proof.
  intro H0.
  rewrite <- finite_intersection_htrue.
  apply H0.
  intros (m,Hm).
  apply fromempty.
  revert Hm.
  apply negnatlthn0.
Qed.
Lemma isOpenSet_finite_intersection_and :
  isOpenSet_finite_intersection
  -> ∀ A B, isOpen A -> isOpen B -> isOpen (λ x, A x ∧ B x).
Proof.
  intros H0 A B Ha Hb.
  rewrite <- finite_intersection_and.
  apply H0.
  intros (m,Hm) ; simpl.
  destruct m.
  apply Ha.
  apply Hb.
Qed.
Lemma isOpenSet_finite_intersection_carac :
  isOpen (λ _, htrue)
  -> (∀ A B, isOpen A -> isOpen B -> isOpen (λ x, A x ∧ B x))
  -> isOpenSet_finite_intersection.
Proof.
  intros Htrue Hpair L.
  apply (Sequence_rect (P := λ P : Sequence (X -> hProp),
                                   (∀ m : stn (length P), isOpen (P m)) -> isOpen (finite_intersection P))) ; clear L.
  - intros _.
    rewrite finite_intersection_htrue.
    apply Htrue.
  - intros L A IH H.
    rewrite finite_intersection_append.
    apply Hpair.
    generalize (H (lastelement (length L))).
    simpl.
    now rewrite append_fun_compute_2.
    apply IH.
    intros m.
    generalize (H (dni_lastelement m)).
    simpl.
    now rewrite append_fun_compute_1.
Qed.

Definition isOpenSet :=
  isOpenSet_infinite_union ∧ isOpenSet_finite_intersection.

End OpenSet.

Definition isTopologicalSet :=
  λ X : hSet, Σ isOpen : (X -> hProp) -> hProp, isOpenSet isOpen.
Definition TopologicalSet := Σ X : hSet, isTopologicalSet X.

Definition mkTopologicalSet (X : hSet) (isOpen : (X -> hProp) -> hProp)

           (is : isOpenSet_infinite_union isOpen)

(is0 : isOpenSet_finite_intersection isOpen) : TopologicalSet := (X,,isOpen,,is,,is0).
Definition mkTopologicalSet' (X : hSet) (isOpen : (X -> hProp) -> hProp)
(is : isOpenSet_infinite_union isOpen)
(is0 : isOpen (λ _, htrue)) (is1 : ∀ A B, isOpen A -> isOpen B -> isOpen (λ x, A x ∧ B x)) : TopologicalSet.
Proof.
  apply (mkTopologicalSet X isOpen).
  exact is.
  apply isOpenSet_finite_intersection_carac.
  exact is0.
  exact is1.
Defined.

Definition pr1TopologicatSet : TopologicalSet -> hSet := pr1.
Coercion pr1TopologicatSet : TopologicalSet >-> hSet.

Definition isOpen {T : TopologicalSet} : (T -> hProp) -> hProp := pr1 (pr2 T).
Definition Open {T : TopologicalSet} :=
  Σ O : T -> hProp, isOpen O.
Definition pr1Open {T : TopologicalSet} : Open -> (T -> hProp) := pr1.
Coercion pr1Open : Open >-> Funclass.

Section Topology_pty.

Context {T : TopologicalSet}.

Lemma isOpen_infinite_union :
  ∀ P : (T -> hProp) -> hProp,
    (∀ A : T -> hProp, P A -> isOpen A)
    -> isOpen (infinite_union P).
Proof.
  apply (pr1 (pr2 (pr2 T))).
Qed.
Lemma isOpen_finite_intersection :
  ∀ (P : Sequence (T -> hProp)),
    (∀ m , isOpen (P m))
    -> isOpen (finite_intersection P).
Proof.
  apply (pr2 (pr2 (pr2 T))).
Qed.

Lemma isOpen_hfalse :
  isOpen (λ _ : T, hfalse).
Proof.
  rewrite <- infinite_union_hfalse.
  apply isOpen_infinite_union.
  intro.
  apply fromempty.
Qed.
Lemma isOpen_htrue :
  isOpen (λ _ : T, htrue).
Proof.
  rewrite <- finite_intersection_htrue.
  apply isOpen_finite_intersection.
  intros (m,Hm).
  now apply fromempty.
Qed.
Lemma isOpen_and :
  ∀ A B : T -> hProp,
    isOpen A -> isOpen B -> isOpen (λ x : T, A x ∧ B x).
Proof.
  apply isOpenSet_finite_intersection_and.
  intros P Hp.
  apply isOpen_finite_intersection.
  apply Hp.
Qed.
Lemma isOpen_or :
  ∀ A B : T -> hProp,
    isOpen A -> isOpen B -> isOpen (λ x : T, A x ∨ B x).
Proof.
  intros A B Ha Hb.
  rewrite <- infinite_union_or.
  apply isOpen_infinite_union.
  intros C.
  apply hinhuniv.
  intros [-> | ->].
  exact Ha.
  exact Hb.
Qed.

End Topology_pty.

(** ** Topologie induite *)
(* todo : traduire *)

Definition generated_topology {X : hSet} (O : (X -> hProp) -> hProp) : TopologicalSet.
Proof.
  exists X.
  assert (Ho : ∀ P : X -> hProp, isaprop (∀ T : isTopologicalSet X, (∀ Q : X -> hProp, O Q -> (pr1 T) Q) -> (pr1 T P))).
  { intros.
    apply impred_isaprop ; intro T.
    apply isapropimpl.
    now apply pr2. }
  exists (λ P : X -> hProp, hProppair (∀ T : isTopologicalSet X, (∀ Q : X -> hProp, O Q -> (pr1 T) Q) -> (pr1 T P)) (Ho P)).
  split.
  - intros P Hp T Ht.
    apply (pr1 (pr2 T)).
    intros A Pa.
    apply Hp.
    exact Pa.
    exact Ht.
  - intros P Hp T Ht.
    apply (pr2 (pr2 T)).
    intros m.
    apply Hp.
    exact Ht.
Defined.

Lemma generated_topology_smallest {X : hSet} :
  ∀ (O : (X -> hProp) -> hProp) (T : isTopologicalSet X),
    (∀ P : X -> hProp, O P -> pr1 T P)
    -> ∀ P : X -> hProp, isOpen (T := generated_topology O) P -> pr1 T P.
Proof.
  intros O T Ht P Hp.
  apply Hp.
  exact Ht.
Qed.
Lemma generated_topology_included {X : hSet} :
  ∀ (O : (X -> hProp) -> hProp) (P : X -> hProp),
    O P -> isOpen (T := generated_topology O) P.
Proof.
  intros O P Op T Ht.
  apply Ht.
  exact Op.
Qed.

(** ** Neighborhood *)

Section Neighborhood.

Context {T : TopologicalSet}.

Definition neighborhood (x : T) : (T -> hProp) -> hProp :=
  λ P : T -> hProp, ∃ O : Open, O x × (∀ y : T, O y -> P y).

Lemma neighborhood_isOpen (P : T -> hProp) :
  (∀ x, P x -> neighborhood x P) <-> isOpen P.
Proof.
  split.
  - intros Hp.
    assert (H : ∀ A : T -> hProp, isaprop (∀ y : T, A y -> P y)).
    { intros A.
      apply impred_isaprop.
      intro y.
      apply isapropimpl.
      apply propproperty. }
    set (Q := λ A : T -> hProp, isOpen A ∧ (hProppair (∀ y : T, A y -> P y) (H A))).
    assert (P = (infinite_union Q)).
    { apply funextfun.
      intros x.
      apply uahp.
      - intros Px.
        generalize (Hp _ Px).
        apply hinhfun.
        intros (A,(Ax,Ha)).
        exists A ; split.
        split.
        apply (pr2 A).
        exact Ha.
        exact Ax.
      - apply hinhuniv.
        intros (A,((Ha,Hx),Ax)).
        apply Hx.
        exact Ax. }
    rewrite X.
    apply isOpen_infinite_union.
    intros A Ha.
    apply (pr1 Ha).
  - intros Hp x Px.
    apply hinhpr.
    exists (P,,Hp).
    split.
    exact Px.
    intros y Py.
    exact Py.
Qed.

Lemma neighborhood_impl :
  ∀ (x : T) (P Q : T -> hProp),
    (∀ y : T, P y -> Q y) -> neighborhood x P -> neighborhood x Q.
Proof.
  intros x P Q H.
  apply hinhfun.
  intros O.
  exists (pr1 O).
  split.
  - apply (pr1 (pr2 O)).
  - intros y Hy.
    apply H.
    apply (pr2 (pr2 O)).
    exact Hy.
Qed.
Lemma neighborhood_forall :
  ∀ (x : T) (P : T -> hProp),
    (∀ y, P y) -> neighborhood x P.
Proof.
  intros x P H.
  apply hinhpr.
  exists ((λ _ : T, htrue),,isOpen_htrue).
  split.
  easy.
  intros y _.
  now apply H.
Qed.
Lemma neighborhood_and :
  ∀ (x : T) (A B : T -> hProp),
    neighborhood x A -> neighborhood x B -> neighborhood x (λ y, A y ∧ B y).
Proof.
  intros x A B.
  apply hinhfun2.
  intros Oa Ob.
  exists ((λ x, pr1 Oa x ∧ pr1 Ob x) ,, isOpen_and _ _ (pr2 (pr1 Oa)) (pr2 (pr1 Ob))).
  simpl.
  split.
  - split.
    + apply (pr1 (pr2 Oa)).
    + apply (pr1 (pr2 Ob)).
  - intros y Hy.
    split.
    + apply (pr2 (pr2 Oa)).
      apply (pr1 Hy).
    + apply (pr2 (pr2 Ob)).
      apply (pr2 Hy).
Qed.
Lemma neighborhood_point :
  ∀ (x : T) (P : T -> hProp),
    neighborhood x P -> P x.
Proof.
  intros x P.
  apply hinhuniv.
  intros O.
  apply (pr2 (pr2 O)).
  apply (pr1 (pr2 O)).
Qed.

Lemma neighborhood_neighborhood :
  ∀ (x : T) (P : T -> hProp),
    neighborhood x P
    -> ∃ Q : T -> hProp, neighborhood x Q
                        × ∀ y : T, Q y -> neighborhood y P.
Proof.
  intros x P.
  apply hinhfun.
  intros Q.
  exists (pr1 Q).
  split.
  - apply (pr2 (neighborhood_isOpen _)).
    apply (pr2 (pr1 Q)).
    apply (pr1 (pr2 Q)).
  - intros y Qy.
    apply hinhpr.
    exists (pr1 Q).
    split.
    + exact Qy.
    + exact (pr2 (pr2 Q)).
Qed.

End Neighborhood.

(** ** Locally *)

Definition is_base_of_neighborhood {T : TopologicalSet} (x : T) (B : (T -> hProp) -> hProp) :=
  (∀ P : T -> hProp, B P -> neighborhood x P)
    × (∀ P : T -> hProp, neighborhood x P -> ∃ Q : Open, B Q × (∀ t : T, Q t -> P t)).

Definition base_of_neighborhood {T : TopologicalSet} (x : T) :=
  Σ (B : (T -> hProp) -> hProp), is_base_of_neighborhood x B.
Definition pr1base_of_neighborhood {T : TopologicalSet} (x : T) :
  base_of_neighborhood x -> ((T -> hProp) -> hProp) := pr1.
Coercion pr1base_of_neighborhood : base_of_neighborhood >-> Funclass.

Definition neighborhood' {T : TopologicalSet} (x : T) (B : base_of_neighborhood x) : (T -> hProp) -> hProp :=
  λ P : T -> hProp, ∃ O : T -> hProp, B O × (∀ t : T, O t -> P t).

Lemma neighborhood_equiv {T : TopologicalSet} (x : T) (B : base_of_neighborhood x) :
  ∀ P, neighborhood' x B P <-> neighborhood x P.
Proof.
  intros P.
  split.
  - apply hinhuniv.
    intros O.
    generalize ((pr1 (pr2 B)) (pr1 O) (pr1 (pr2 O))).
    apply neighborhood_impl.
    exact (pr2 (pr2 O)).
  - intros Hp.
    generalize (pr2 (pr2 B) P Hp).
    apply hinhfun.
    intros O.
    exists (pr1 O).
    exact (pr2 O).
Qed.

(** ** Limits in a Topological Set *)

Definition locally {T : TopologicalSet} (x : T) (base : base_of_neighborhood x) : Filter (X := T).
Proof.
  simple refine (mkFilter' _ _ _ _ _).
  - apply (neighborhood' x base).
  - intros A B Hab Ha.
    apply (pr2 (neighborhood_equiv _ _ _)) ;
    apply (pr1 (neighborhood_equiv _ _ _)) in Ha.
    revert Ha.
    apply neighborhood_impl, Hab.
  - apply (pr2 (neighborhood_equiv _ _ _)).
    apply (pr2 (neighborhood_isOpen _)).
    apply isOpen_htrue.
    apply tt.
  - intros A B Ha Hb.
    apply (pr2 (neighborhood_equiv _ _ _)) ;
    apply (pr1 (neighborhood_equiv _ _ _)) in Ha ;
    apply (pr1 (neighborhood_equiv _ _ _)) in Hb.
    apply neighborhood_and.
    exact Ha.
    exact Hb.
  - intros Hx.
    apply (pr1 (neighborhood_equiv _ _ _)), neighborhood_point in Hx.
    exact Hx.
Defined.

(** *** Limit of a filter *)

Definition is_filter_lim {T : TopologicalSet} (F : Filter) (x : T) (base : base_of_neighborhood x) :=
  filter_le (locally x base) F.
Definition ex_filter_lim  {T : TopologicalSet} (F : Filter) :=
  ∃ (x : T) (base : base_of_neighborhood x), is_filter_lim F x base.

(** *** Limit of a function *)

Definition is_TSlim {X : UU} {T : TopologicalSet} (f : X -> T) (F : Filter (X := X)) (x : T) (base : base_of_neighborhood x) :=
  filterlim f F (locally x base).
Definition ex_TSlim {X : UU} {T : TopologicalSet} (f : X -> T) (F : Filter (X := X)) :=
  ∃ (x : T) (base : base_of_neighborhood x), is_TSlim f F x base.