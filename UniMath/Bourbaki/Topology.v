(** * Results about Topology *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Export UniMath.Foundations.Basics.Sets.
Require Export UniMath.Foundations.NumberSystems.NaturalNumbers.

(** ** Topological structures *)

Section OpenSet.

Context (X : UU).
Context (isOpen : (X -> hProp) -> hProp).

Definition infinite_union (P : (X -> hProp) -> hProp) : X -> hProp :=
  λ x : X, ∃ A : X -> hProp, P A × A x.
Definition finite_intersection (n : nat) (P : (Σ m : nat, m < n) -> (X -> hProp)) : X -> hProp :=
  λ (x : X),
  hProppair (∀ m : Σ m : nat, m < n, P m x)
            (impred_isaprop _ (λ _, propproperty _)).

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
  assert (H : (λ _ : X, hfalse)
              = infinite_union (λ _, hfalse)).
  { apply funextfun.
    intros x.
    apply uahp.
    - apply fromempty.
    - apply hinhuniv.
      intros (_,(H,_)).
      exact H. }
  rewrite H.
  apply H0.
  intro.
  apply fromempty.
Qed.

Lemma isOpenSet_finite_intersection_htrue :
  isOpenSet_finite_intersection
  -> isOpen (λ _, htrue).
Proof.
  assert (H : (λ _ : X, htrue) = (finite_intersection O (λ _ _, hfalse))).
  { apply funextfun.
    intros x.
    apply uahp.
    - intros _ (m).
      apply negnatlthn0.
    - easy. }
  rewrite H.
  intro H0.
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
  assert (H : (λ x : X, A x ∧ B x) = (finite_intersection 2 (λ m x, match (pr1 m) with | O => A x | S O => B x | _ => hfalse end))).
  { apply funextfun.
    intros x.
    apply uahp.
    - intros Hx (m,Hm) ; simpl.
      destruct m.
      exact (pr1 Hx).
      destruct m.
      exact (pr2 Hx).
      simpl in Hm.
      easy.
    - intros Hx.
      split.
      + assert (O < 2) by easy.
        apply (Hx (O,,X0)).
      + assert (1 < 2) by easy.
        apply (Hx (1,,X0)). }
  rewrite H.
  apply H0.
  intros (m,Hm) ; simpl.
  destruct m.
  apply Ha.
  destruct m.
  apply Hb.
  simpl in Hm ; easy.
Qed.
Lemma isOpenSet_finite_intersection_carac :
  isOpen (λ _, htrue)
  -> (∀ A B, isOpen A -> isOpen B -> isOpen (λ x, A x ∧ B x))
  -> isOpenSet_finite_intersection.
Proof.
  intros Htrue Hpair n.
  induction n.
  - intros P HP.
    assert ((finite_intersection 0 P) = (λ _ : X, htrue)).
    { apply funextfun.
      intros x.
      apply uahp.
      - easy.
      - intros _ (m,Hm).
        apply fromempty.
        revert Hm.
        apply negnatlthn0. }
    rewrite X0.
    apply Htrue.
  - intros P Hp.
    assert (H0 : O < S n) by easy.
    set (A := P (O,,H0)).
    set (B := λ m : (Σ m : nat, m < n), P (S (pr1 m) ,, pr2 m)).
    assert ((finite_intersection (S n) P) = (λ x : X, A x ∧ finite_intersection n B x)).
    { apply funextfun.
      intros x.
      apply uahp.
      - intros Hx.
        split.
        apply Hx.
        intros m.
        apply Hx.
      - intros Hx (m,Hm).
        destruct m.
        assert (Hm = H0).
        { apply (pr2 (0 < S n)). }
        rewrite X0.
        apply (pr1 Hx).
        apply (pr2 Hx (m,,Hm)). }
    rewrite X0.
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
  λ X : hSet, Σ isOpen : (X -> hProp) -> hProp, isOpenSet X isOpen.
Definition TopologicalSet := Σ X : hSet, isTopologicalSet X.

Definition mkTopologicalSet (X : hSet) (isOpen : (X -> hProp) -> hProp)
(is : isOpenSet_infinite_union X isOpen)
(is0 : isOpenSet_finite_intersection X isOpen) : TopologicalSet := (X,,isOpen,,is,,is0).
Definition mkTopologicalSet' (X : hSet) (isOpen : (X -> hProp) -> hProp)
(is : isOpenSet_infinite_union X isOpen)
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
Definition Open (T : TopologicalSet) :=
  Σ O : T -> hProp, isOpen O.

Section Topology_pty.

Context {T : TopologicalSet}.

Lemma isOpen_infinite_union :
  ∀ P : (T -> hProp) -> hProp,
    (∀ A : T -> hProp, P A -> isOpen A)
    -> isOpen (infinite_union T P).
Proof.
  apply (pr1 (pr2 (pr2 T))).
Qed.
Lemma isOpen_finite_intersection :
  ∀ (n : nat) (P : (Σ m : nat, m < n) -> T -> hProp),
    (∀ m : Σ m : nat, m < n, isOpen (P m))
    -> isOpen (finite_intersection T n P).
Proof.
  apply (pr2 (pr2 (pr2 T))).
Qed.

Lemma isOpen_hfalse :
  isOpen (λ _ : T, hfalse).
Proof.
  assert (H : (λ _ : T, hfalse)
              = infinite_union T (λ _, hfalse)).
  { apply funextfun.
    intros x.
    apply uahp.
    - apply fromempty.
    - apply hinhuniv.
      intros (_,(H,_)).
      exact H. }
  rewrite H.
  apply isOpen_infinite_union.
  intro.
  apply fromempty.
Qed.
Lemma isOpen_htrue :
  isOpen (λ _ : T, htrue).
Proof.
  assert (H : (λ _ : T, htrue) = (finite_intersection T O (λ _ _, hfalse))).
  { apply funextfun.
    intros x.
    apply uahp.
    - intros _ (m).
      apply negnatlthn0.
    - easy. }
  rewrite H.
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
  set (P := λ C, C = A ∨ C = B).
  assert ((λ x : T, A x ∨ B x) = infinite_union T P).
  { apply funextfun.
    intro x.
    apply uahp.
    - apply hinhfun.
      intros [Hx | Hx].
      + exists A.
        split.
        * apply hinhpr.
          now left.
        * exact Hx.
      + exists B.
        split.
        * apply hinhpr.
          now right.
        * exact Hx.
    - apply hinhuniv.
      intros (C,(Hc,Hx)).
      revert Hc.
      apply hinhfun.
      intros [-> | ->].
      + now left.
      + now right. }
  rewrite X.
  apply isOpen_infinite_union.
  intros C.
  apply hinhuniv.
  intros [-> | ->].
  exact Ha.
  exact Hb.
Qed.

End Topology_pty.