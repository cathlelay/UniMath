(** * Additionals theorems *)

Require Export UniMath.Foundations.Basics.Sets.
Require Export UniMath.Foundations.Combinatorics.FiniteSequences.

(** ** More about Sequence *)

Definition singletonSequence {X} (A : X) : Sequence X := (1 ,, λ _, A).
Definition pairSequence {X} (A B : X) : Sequence X := (2 ,, λ m, match (pr1 m) with | O => A | _ => B end).

(** ** More about sets *)
(** union *)

Definition infinite_union {X : UU} (P : (X -> hProp) -> hProp) : X -> hProp :=
  λ x : X, ∃ A : X -> hProp, P A × A x.

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

(** finite intersection *)

Definition finite_intersection {X : UU} (P : Sequence (X -> hProp)) : X -> hProp.
Proof.
  intros x.
  simple refine (hProppair _ _).
  apply (∀ n, P n x).
  apply (impred_isaprop _ (λ _, propproperty _)).
Defined.

Lemma finite_intersection_htrue {X : UU} :
  finite_intersection nil = (λ _ : X, htrue).
Proof.
  apply funextfun ; intros x.
  apply uahp.
  - intros _.
    apply tt.
  - intros _ (m,Hm).
    apply fromempty.
    revert Hm.
    apply negnatlthn0.
Qed.

Lemma finite_intersection_1 {X : UU} :
  ∀ (A : X -> hProp),
    finite_intersection (singletonSequence A) = A.
Proof.
  intros A.
  apply funextfun ; intros x.
  apply uahp.
  - intros H.
    apply H.
    now exists 0.
  - intros Lx (m,Hm).
    destruct m.
    exact Lx.
    apply fromempty.
    easy.
Qed.

Lemma finite_intersection_and {X : UU} :
  ∀ A B : X -> hProp,
    finite_intersection (pairSequence A B)
    = (λ x : X, A x ∧ B x).
Proof.
  intros A B.
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

Lemma finite_intersection_case {X : UU} :
  ∀ (L : Sequence (X -> hProp)),
    finite_intersection L = match disassembleSequence L with
                            | ii1 _ => λ _, htrue
                            | ii2 (A,,B) => (λ x : X, A x ∧ finite_intersection B x)
                            end.
Proof.
  intros L.
  apply funextfun ; intros x.
  apply uahp.
  - intros Hx.
    destruct L as [n L].
    destruct n ; simpl.
    + apply tt.
    + split.
      apply Hx.
      intros m.
      apply Hx.
  - destruct L as [n L].
    destruct n ; simpl.
    + intros _ (n,Hn).
      now apply fromempty.
    + intros Hx (m,Hm).
      destruct (natlehchoice _ _ (natlthsntoleh _ _ Hm)) as [Hm' | ->].
      generalize (pr2 Hx (m,,Hm')).
      unfold funcomp, dni_lastelement ; simpl.
      assert (H : Hm = natlthtolths m n Hm' ).
      { apply (pr2 (natlth m (S n))). }
      now rewrite H.
      assert (H : (lastelement n) = (n,, Hm)).
      { now apply subtypeEquality_prop. }
      rewrite <- H.
      exact (pr1 Hx).
Qed.
Lemma finite_intersection_append {X : UU} :
  ∀ (A : X -> hProp) (L : Sequence (X -> hProp)),
    finite_intersection (append L A) = (λ x : X, A x ∧ finite_intersection L x).
Proof.
  intros.
  rewrite finite_intersection_case.
  simpl.
  rewrite append_fun_compute_2.
  apply funextfun ; intro x.
  apply maponpaths.
  apply map_on_two_paths.
  destruct L ; simpl.
  apply maponpaths.
  apply funextfun ; intro n.
  apply append_fun_compute_1.
  reflexivity.
Qed.
