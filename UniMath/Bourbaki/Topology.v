(** * Results about Topology *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Export UniMath.Foundations.Basics.Sets.
Require Export UniMath.Foundations.NumberSystems.NaturalNumbers.

(** ** Topological structures *)

Definition infinite_union {X : UU} (P : (X -> hProp) -> hProp) : X -> hProp :=
  λ x : X, ∃ A : X -> hProp, P A × A x.
Definition finite_intersection {X : UU} (n : nat) (P : (Σ m : nat, m < n) -> (X -> hProp)) : X -> hProp :=
  λ (x : X),
  hProppair (∀ m : Σ m : nat, m < n, P m x)
            (impred_isaprop _ (λ _, propproperty _)).

Lemma infinite_union_hfalse {X : UU} :
  infinite_union (λ _ : X -> hProp, hfalse) = (λ _ : X, hfalse).
Proof.
  apply funextfun ; intros x.
  apply uahp.
  - apply hinhuniv.
    intros A.
    apply (pr1 (pr2 A)).
  - apply fromempty.
Qed.

Lemma infinite_union_or {X : UU} :
  ∀ A B : X -> hProp,
    infinite_union (λ C : X -> hProp, C = A ∨ C = B)
    = (λ x : X, A x ∨ B x).
Proof.
  intros A B.
  apply funextfun ; intro x.
  apply uahp.
  - apply hinhuniv.
    intros C.
    generalize (pr1 (pr2 C)).
    apply hinhfun.
    intros [<- | <-].
    + left.
      apply (pr2 (pr2 C)).
    + right.
      apply (pr2 (pr2 C)).
  - apply hinhfun ; intros [Ax | Bx].
    + exists A.
      split.
      apply hinhpr.
      now left.
      exact Ax.
    + exists B.
      split.
      apply hinhpr.
      now right.
      exact Bx.
Qed.

Lemma finite_intersection_htrue {X : UU} :
  ∀ L : (Σ m : nat, m < 0) -> X -> hProp,
  finite_intersection 0 L = (λ _ : X, htrue).
Proof.
  intro A.
  apply funextfun ; intros x.
  apply uahp.
  - intros _.
    apply tt.
  - intros _ (m,Hm).
    apply fromempty.
    revert Hm.
    apply negnatlthn0.
Qed.

Lemma finite_intersection_and {X : UU} :
  ∀ C A B : X -> hProp,
    finite_intersection 2 (λ m x , match (pr1 m) with
                                     | O => A x
                                     | 1 => B x
                                     | _ => C x
                                   end)
    = (λ x : X, A x ∧ B x).
Proof.
  intros C A B.
  apply funextfun ; intro x.
  apply uahp.
  - intros H.
    split.
    simple refine (H (0,,_)).
    reflexivity.
    simple refine (H (1,,_)).
    reflexivity.
  - intros H (m,Hm) ; simpl.
    destruct m.
    apply (pr1 H).
    destruct m.
    apply (pr2 H).
    easy.
Qed.
Lemma finite_intersection_S {X : UU} :
  ∀ (n : nat) (L : (Σ m : nat, m < S n) -> X -> hProp),
    let A := L (0,,paths_refl _) in
    let B := λ m : Σ m, m < n, L (S (pr1 m) ,, (pr2 m)) in
finite_intersection (X := X) (S n) L
= (λ x : X, A x ∧ finite_intersection n B x).
Proof.
  intros n L A B.
  apply funextfun ; intros x.
  apply uahp.
  - intros Hx.
    split.
    apply Hx.
    intros m.
    apply Hx.
  - intros Hx (m,Hm).
    destruct m.
    assert (Hm = idpath (natgtb (S n) 0)).
    { apply (pr2 (0 < S n)). }
    rewrite X0.
    apply (pr1 Hx).
    apply (pr2 Hx (m,,Hm)).
Qed.

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
    (∀ (n : nat) (P : (Σ m : nat, m < n) -> X -> hProp),
       (∀ m : Σ m : nat, m < n, isOpen (P m)) -> isOpen (finite_intersection n P))
    (impred_isaprop _ (λ _, impred_isaprop _ (λ _, isapropimpl _ _ (propproperty _)))).

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
  rewrite <- (finite_intersection_htrue (λ _ _, htrue)).
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
  rewrite <- (finite_intersection_and (λ _, hfalse)).
  apply H0.
  intros (m,Hm) ; simpl.
  destruct m.
  apply Ha.
  destruct m.
  apply Hb.
  easy.
Qed.
Lemma isOpenSet_finite_intersection_carac :
  isOpen (λ _, htrue)
  -> (∀ A B, isOpen A -> isOpen B -> isOpen (λ x, A x ∧ B x))
  -> isOpenSet_finite_intersection.
Proof.
  intros Htrue Hpair n.
  induction n.
  - intros P HP.
    rewrite finite_intersection_htrue.
    apply Htrue.
  - intros P Hp.
    rewrite finite_intersection_S.
    apply Hpair.
    apply Hp.
    apply IHn.
    intros m.
    apply Hp.
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
  ∀ (n : nat) (P : (Σ m : nat, m < n) -> T -> hProp),
    (∀ m : Σ m : nat, m < n, isOpen (P m))
    -> isOpen (finite_intersection n P).
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
  rewrite <- (finite_intersection_htrue (λ _ _, hfalse)).
  apply isOpen_finite_intersection.
  intros _.
  apply isOpen_hfalse.
Qed.
Lemma isOpen_and :
  ∀ A B : T -> hProp,
    isOpen A -> isOpen B -> isOpen (λ x : T, A x ∧ B x).
Proof.
  apply isOpenSet_finite_intersection_and.
  intros n P Hp.
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
  - intros n P Hp T Ht.
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

Definition base_of_neighborhood {T : TopologicalSet} (x : T) (B : (T -> hProp) -> hProp) :=
  (∀ P : T -> hProp, B P -> neighborhood x P)
    × (∀ P : T -> hProp, neighborhood x P -> ∃ Q : Open, B Q × (∀ t : T, Q t -> P t)).

Section Locally.

Context {T : TopologicalSet}.
Context (x : T) (B : (T -> hProp) -> hProp).
Context (base : base_of_neighborhood x B).

Definition locally : (T -> hProp) -> hProp :=
  λ P : T -> hProp, ∃ O : T -> hProp, B O × (∀ t : T, O t -> P t).

Lemma locally_neighborhood :
  ∀ P, locally P <-> neighborhood x P.
Proof.
  intros P.
  split.
  - apply hinhuniv.
    intros O.
    generalize ((pr1 base) (pr1 O) (pr1 (pr2 O))).
    apply neighborhood_impl.
    exact (pr2 (pr2 O)).
  - intros Hp.
    generalize (pr2 base P Hp).
    apply hinhfun.
    intros O.
    exists (pr1 O).
    exact (pr2 O).
Qed.

End Locally.