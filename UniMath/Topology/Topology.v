(** * Results about Topology *)
(** Author: Catherine LELAY. Jan 2016 - *)
(** Based on Bourbaky *)

Require Import UniMath.MoreFoundations.Tactics.
Require Export UniMath.Topology.Filters.
Require Import UniMath.Algebra.DivisionRig.
Require Import UniMath.Algebra.ConstructiveStructures.

Unset Automatic Introduction.

Section Open.

Context {X : UU}.
Context (O : (X → hProp) → hProp).

Definition isSetOfOpen_union : UU :=
  ∏ P : (X → hProp) → hProp,
    (∏ A : X → hProp, P A → O A) → O (union P).
Lemma isaprop_isSetOfOpen_union :
  isaprop isSetOfOpen_union.
Proof.
  apply (impred_isaprop _ (λ _, isapropimpl _ _ (propproperty _))).
Defined.
Definition isSetOfOpen_finite_intersection : UU :=
  ∏ (P : Sequence (X → hProp)), (∏ m, O (P m)) → O (finite_intersection P).
Lemma isaprop_isSetOfOpen_finite_intersection :
  isaprop isSetOfOpen_finite_intersection.
Proof.
  apply (impred_isaprop _ (λ _, isapropimpl _ _ (propproperty _))).
Defined.

Definition isSetOfOpen_htrue : hProp :=
  O (λ _, htrue).

Definition isSetOfOpen_and : UU :=
  ∏ A B, O A → O B → O (λ x, A x ∧ B x).
Lemma isaprop_isSetOfOpen_and :
  isaprop isSetOfOpen_and.
Proof.
  apply impred_isaprop ; intros A.
  apply impred_isaprop ; intros B.
  apply isapropimpl, isapropimpl.
  now apply propproperty.
Qed.

Lemma isSetOfOpen_hfalse :
  isSetOfOpen_union
  → O (λ _ : X, hfalse).
Proof.
  intros H0.
  rewrite <- union_hfalse.
  apply H0.
  intro.
  apply fromempty.
Qed.

Lemma isSetOfOpen_finite_intersection_htrue :
  isSetOfOpen_finite_intersection
  → isSetOfOpen_htrue.
Proof.
  intro H0.
  unfold isSetOfOpen_htrue.
  rewrite <- finite_intersection_htrue.
  apply H0.
  intros m.
  induction (nopathsfalsetotrue (pr2 m)).
Qed.

Lemma isSetOfOpen_finite_intersection_and :
  isSetOfOpen_finite_intersection
  → isSetOfOpen_and.
Proof.
  intros H0 A B Ha Hb.
  rewrite <- finite_intersection_and.
  apply H0.
  intros m ; simpl.
  induction m as [m Hm].
  now induction m.
Qed.
Lemma isSetOfOpen_finite_intersection_carac :
  isSetOfOpen_htrue
  → isSetOfOpen_and
  → isSetOfOpen_finite_intersection.
Proof.
  intros Htrue Hpair L.
  apply (pr2 (finite_intersection_hProp O)).
  split.
  - exact Htrue.
  - exact Hpair.
Qed.

Definition isSetOfOpen : UU :=
  isSetOfOpen_union × isSetOfOpen_finite_intersection.
Lemma isaprop_isSetOfOpen :
  isaprop isSetOfOpen.
Proof.
  apply isapropdirprod.
  apply isaprop_isSetOfOpen_union.
  apply isaprop_isSetOfOpen_finite_intersection.
Defined.

End Open.

Definition Topology (X : UU) :=
  ∑ O : (X → hProp) → hProp, isSetOfOpen O.
Lemma isaset_Topology (X : UU) :
  isaset (Topology X).
Proof.
  intros X.
  apply isaset_total2.
  - apply impred_isaset ; intros _.
    apply isasethProp.
  - intros O.
    apply isasetaprop, isaprop_isSetOfOpen.
Defined.

Definition TopologicalSet := ∑ X : hSet, Topology X.
Lemma isofhlevel_3_TopologicalSet :
  isofhlevel 3 TopologicalSet.
Proof.
  apply isofhleveltotal2.
  - apply HLevels.hlevel_of_hlevels.
  - intros X.
    apply isofhlevelssnset.
    apply isaset_Topology.
Defined.

Definition pairTopology (X : UU) (O : (X → hProp) → hProp)
           (is : isSetOfOpen_union O)
           (is0 : isSetOfOpen_htrue O)
           (is1 : isSetOfOpen_and O) : Topology X :=
  (O,,is,,(isSetOfOpen_finite_intersection_carac _ is0 is1)).
Definition pairTopologicalSet (X : hSet) (is : Topology X) : TopologicalSet :=
  (X,,is).

Ltac mkTopologicalSet :=
  intros ;
  match goal with
    | |- TopologicalSet => simple refine (pairTopologicalSet _ _) ;
        [ | mkTopologicalSet]
    | |- Topology _ => simple refine (pairTopology _ _ _ _ _)
    | |- _ => idtac "Goal must end by TopologicalSet or Topology _"
  end.

Definition pr1TopologicatSet : TopologicalSet → UU := pr1.
Coercion pr1TopologicatSet : TopologicalSet >-> UU.

Definition isOpen {T : UU} (topo : Topology T) : (T → hProp) → hProp := pr1 topo.
Definition Open {T : UU} (topo : Topology T) :=
  ∑ O : T → hProp, isOpen topo O.
Definition pr1Open {T : UU} (topo : Topology T) :
  (Open topo) → (T → hProp) := pr1.
Coercion pr1Open : Open >-> Funclass.

Section Topology_pty.

Context {T : UU}
        (topo : Topology T).

Lemma isOpen_union :
  ∏ P : (T → hProp) → hProp,
    (∏ A : T → hProp, P A → isOpen topo A)
    → isOpen topo (union P).
Proof.
  apply (pr1 (pr2 topo)).
Qed.
Lemma isOpen_finite_intersection :
  ∏ (P : Sequence (T → hProp)),
    (∏ m , isOpen topo (P m))
    → isOpen topo (finite_intersection P).
Proof.
  apply (pr2 (pr2 topo)).
Qed.

Lemma isOpen_hfalse :
  isOpen topo (λ _ : T, hfalse).
Proof.
  apply isSetOfOpen_hfalse.
  intros P H.
  now apply isOpen_union.
Qed.
Lemma isOpen_htrue :
  isOpen topo (λ _ : T, htrue).
Proof.
  rewrite <- finite_intersection_htrue.
  apply isOpen_finite_intersection.
  intros m.
  induction (nopathsfalsetotrue (pr2 m)).
Qed.
Lemma isOpen_and :
  ∏ A B : T → hProp,
    isOpen topo A → isOpen topo B → isOpen topo (λ x : T, A x ∧ B x).
Proof.
  apply isSetOfOpen_finite_intersection_and.
  intros P Hp.
  apply isOpen_finite_intersection.
  apply Hp.
Qed.
Lemma isOpen_or :
  ∏ A B : T → hProp,
    isOpen topo A → isOpen topo B → isOpen topo (λ x : T, A x ∨ B x).
Proof.
  intros A B Ha Hb.
  rewrite <- union_or.
  apply isOpen_union.
  intros C.
  apply hinhuniv.
  apply sumofmaps ; intros ->.
  exact Ha.
  exact Hb.
Qed.

End Topology_pty.

(** ** Neighborhood *)

Section Neighborhood.

Context {T : UU}
        (topo : Topology T).

Definition neighborhood (x : T) : (T → hProp) → hProp :=
  λ P : T → hProp, ∃ O : Open topo, O x × (∏ y : T, O y → P y).

Lemma neighborhood_isOpen (P : T → hProp) :
  (∏ x, P x → neighborhood x P) <-> isOpen topo P.
Proof.
  split.
  - intros Hp.
    assert (H : ∏ A : T → hProp, isaprop (∏ y : T, A y → P y)).
    { intros A.
      apply impred_isaprop.
      intro y.
      apply isapropimpl.
      apply propproperty. }
    set (Q := λ A : T → hProp, isOpen topo A ∧ (hProppair (∏ y : T, A y → P y) (H A))).
    assert (X : P = (union Q)).
    { apply funextfun.
      intros x.
      apply hPropUnivalence.
      - intros Px.
        generalize (Hp _ Px).
        apply hinhfun.
        intros A.
        exists (pr1 A) ; split.
        split.
        apply (pr2 (pr1 A)).
        exact (pr2 (pr2 A)).
        exact (pr1 (pr2 A)).
      - apply hinhuniv.
        intros A.
        apply (pr2 (pr1 (pr2 A))).
        exact (pr2 (pr2 A)). }
    rewrite X.
    apply isOpen_union.
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

Lemma neighborhood_imply :
  ∏ (x : T) (P Q : T → hProp),
    (∏ y : T, P y → Q y) → neighborhood x P → neighborhood x Q.
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
  ∏ (x : T) (P : T → hProp),
    (∏ y, P y) → neighborhood x P.
Proof.
  intros x P H.
  apply hinhpr.
  exists ((λ _ : T, htrue),,isOpen_htrue topo).
  split.
  exact tt.
  intros y _.
  now apply H.
Qed.
Lemma neighborhood_and :
  ∏ (x : T) (A B : T → hProp),
    neighborhood x A → neighborhood x B → neighborhood x (λ y, A y ∧ B y).
Proof.
  intros x A B.
  apply hinhfun2.
  intros Oa Ob.
  exists ((λ x, pr1 Oa x ∧ pr1 Ob x) ,, isOpen_and _ _ _ (pr2 (pr1 Oa)) (pr2 (pr1 Ob))).
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
  ∏ (x : T) (P : T → hProp),
    neighborhood x P → P x.
Proof.
  intros x P.
  apply hinhuniv.
  intros O.
  apply (pr2 (pr2 O)).
  apply (pr1 (pr2 O)).
Qed.

Lemma neighborhood_neighborhood :
  ∏ (x : T) (P : T → hProp),
    neighborhood x P
    → ∃ Q : T → hProp, neighborhood x Q
                        × ∏ y : T, Q y → neighborhood y P.
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

Definition locally {T : UU} (topo : Topology T) (x : T) :
  Filter T.
Proof.
  intros T topo x.
  simple refine (mkFilter _ _ _ _ _).
  - apply (neighborhood topo x).
  - abstract (intros A B ;
              apply neighborhood_imply).
  - abstract (apply (pr2 (neighborhood_isOpen topo _)) ;
              [ apply isOpen_htrue |
                apply tt]).
  - abstract (intros A B ;
              apply neighborhood_and).
  - abstract (intros A Ha ;
              apply hinhpr ;
              exists x ;
              now apply neighborhood_point in Ha).
Defined.

(** ** Base of Neighborhood *)

Definition is_base_of_neighborhood {T : UU} (topo : Topology T)
           (x : T) (B : (T → hProp) → hProp) :=
  (∏ P : T → hProp, B P → neighborhood topo x P)
    × (∏ P : T → hProp, neighborhood topo x P → ∃ Q : T → hProp, B Q × (∏ t : T, Q t → P t)).

Definition base_of_neighborhood {T : UU} (topo : Topology T)
           (x : T) :=
  ∑ (B : (T → hProp) → hProp), is_base_of_neighborhood topo x B.
Definition pr1base_of_neighborhood {T : UU} (topo : Topology T)
           (x : T) :
  base_of_neighborhood topo x → ((T → hProp) → hProp) := pr1.
Coercion pr1base_of_neighborhood : base_of_neighborhood >-> Funclass.

Section base_default.

Context {T : UU}
        (topo : Topology T)
        (x : T).

Definition base_default : (T → hProp) → hProp :=
  λ P : T → hProp, isOpen topo P ∧ P x.

Lemma base_default_1 :
  ∏ P : T → hProp, base_default P → neighborhood topo x P.
Proof.
  intros P Hp.
  apply hinhpr.
  exists (P,,(pr1 Hp)) ; split.
  exact (pr2 Hp).
  easy.
Qed.
Lemma base_default_2 :
  ∏ P : T → hProp, neighborhood topo x P → ∃ Q : T → hProp, base_default Q × (∏ t : T, Q t → P t).
Proof.
  intros P.
  apply hinhfun.
  intros Q.
  exists (pr1 Q).
  repeat split.
  exact (pr2 (pr1 Q)).
  exact (pr1 (pr2 Q)).
  exact (pr2 (pr2 Q)).
Qed.

End base_default.

Definition base_of_neighborhood_default {T : UU} (topo : Topology T)
           (x : T) : base_of_neighborhood topo x.
Proof.
  intros T topo x.
  exists (base_default topo x).
  split.
  - now apply base_default_1.
  - now apply base_default_2.
Defined.

Definition neighborhood' {T : UU} (topo : Topology T)
           (x : T) (B : base_of_neighborhood topo x) : (T → hProp) → hProp :=
  λ P : T → hProp, ∃ O : T → hProp, B O × (∏ t : T, O t → P t).

Lemma neighborhood_equiv {T : UU} (topo : Topology T)
      (x : T) (B : base_of_neighborhood topo x) :
  ∏ P, neighborhood' topo x B P <-> neighborhood topo x P.
Proof.
  split.
  - apply hinhuniv.
    intros O.
    generalize ((pr1 (pr2 B)) (pr1 O) (pr1 (pr2 O))).
    apply neighborhood_imply.
    exact (pr2 (pr2 O)).
  - intros Hp.
    generalize (pr2 (pr2 B) P Hp).
    apply hinhfun.
    intros O.
    exists (pr1 O).
    exact (pr2 O).
Qed.

(** ** Some topologies *)

(** *** Topology from neighborhood *)

Definition isNeighborhood {X : UU} (B : X → (X → hProp) → hProp) :=
  (∏ x, isfilter_imply (B x))
    × (∏ x, isfilter_htrue (B x))
    × (∏ x, isfilter_and (B x))
    × (∏ x P, B x P → P x)
    × (∏ x P, B x P → ∃ Q, B x Q × ∏ y, Q y → B y P).

Lemma isNeighborhood_neighborhood {T : UU} (topo : Topology T) :
  isNeighborhood (neighborhood topo).
Proof.
  repeat split.
  - intros x A B.
    apply (neighborhood_imply topo x).
  - intros x.
    apply (pr2 (neighborhood_isOpen topo _)).
    exact (isOpen_htrue topo).
    apply tt.
  - intros A B.
    apply neighborhood_and.
  - intros x P.
    apply neighborhood_point.
  - intros x P.
    apply neighborhood_neighborhood.
Qed.

Section TopologyFromNeighborhood.

Context {X : UU}.
Context (N : X → (X → hProp) → hProp).
Context (Himpl : ∏ x, isfilter_imply (N x))
        (Htrue : ∏ x, isfilter_htrue (N x))
        (Hand : ∏ x, isfilter_and (N x))
        (Hpt : ∏ x P, N x P → P x)
        (H : ∏ x P, N x P → ∃ Q, N x Q × ∏ y, Q y → N y P).

Definition topologyfromneighborhood (A : X → hProp) :=
  ∏ x : X, A x → N x A.
Lemma isaprop_topologyfromneighborhood :
  ∏ A, isaprop (topologyfromneighborhood A).
Proof.
  intros A.
  apply impred_isaprop ; intros x ;
  apply isapropimpl, propproperty.
Qed.

Lemma topologyfromneighborhood_open :
  isSetOfOpen_union
   (λ A : X → hProp,
          hProppair (topologyfromneighborhood A)
                    (isaprop_topologyfromneighborhood A)).
Proof.
  intros L Hl x.
  apply hinhuniv.
  intros A.
  apply Himpl with (pr1 A).
  intros y Hy.
  apply hinhpr.
  now exists (pr1 A), (pr1 (pr2 A)).
  apply Hl.
  exact (pr1 (pr2 A)).
  exact (pr2 (pr2 A)).
Qed.

End TopologyFromNeighborhood.

Definition TopologyFromNeighborhood {X : UU} (N : X → (X → hProp) → hProp) (H : isNeighborhood N) : Topology X.
Proof.
  intros X N H.
  mkTopologicalSet.
  - intros A.
    simple refine (hProppair _ _).
    apply (topologyfromneighborhood N A).
    apply isaprop_topologyfromneighborhood.
  - apply topologyfromneighborhood_open.
    apply (pr1 H).
  - intros x _.
    apply (pr1 (pr2 H)).
  - intros A B Ha Hb x Hx.
    apply (pr1 (pr2 (pr2 H))).
    now apply Ha, (pr1 Hx).
    now apply Hb, (pr2 Hx).
Defined.
Definition TopologicalSetFromNeighborhood {X : hSet} (N : X → (X → hProp) → hProp) (H : isNeighborhood N) : TopologicalSet.
Proof.
  intros X N H.
  refine (pairTopologicalSet _ _).
  apply (TopologyFromNeighborhood N).
  exact H.
Defined.

Lemma TopologyFromNeighborhood_correct {X : UU} (N : X → (X → hProp) → hProp) (H : isNeighborhood N) :
  ∏ (x : X) (P : X → hProp),
    N x P <-> neighborhood (TopologyFromNeighborhood N H) x P.
Proof.
  split.
  - intros Hx.
    apply hinhpr.
    simple refine (tpair _ _ _).
    simple refine (tpair _ _ _).
    + intros y.
      apply (N y P).
    + simpl ; intros y Hy.
      generalize (pr2 (pr2 (pr2 (pr2 H))) _ _ Hy).
      apply hinhuniv.
      intros Q.
      apply (pr1 H) with (2 := pr1 (pr2 Q)).
      exact (pr2 (pr2 Q)).
    + split ; simpl.
      exact Hx.
      intros y.
      now apply (pr1 (pr2 (pr2 (pr2 H)))).
  - apply hinhuniv.
    intros O.
    apply (pr1 H) with (pr1 (pr1 O)).
    apply (pr2 (pr2 O)).
    simple refine (pr2 (pr1 O) _ _).
    exact (pr1 (pr2 O)).
Qed.

Lemma isNeighborhood_isPreFilter {X : UU} N :
  isNeighborhood N -> ∏ x : X, isPreFilter (N x).
Proof.
  intros X N Hn x.
  split.
  - apply (pr1 Hn).
  - apply isfilter_finite_intersection_carac.
    + apply (pr1 (pr2 Hn)).
    + apply (pr1 (pr2 (pr2 Hn))).
Qed.
Lemma isNeighborhood_isFilter {X : UU} N :
  isNeighborhood N -> ∏ x : X, isFilter (N x).
Proof.
  intros X N Hn x.
  split.
  - apply isNeighborhood_isPreFilter, Hn.
  - intros A Fa.
    apply hinhpr.
    exists x.
    apply ((pr1 (pr2 (pr2 (pr2 Hn)))) _ _ Fa).
Qed.

(** *** Generated Topology *)

Section topologygenerated.

Context {X : UU} (O : (X → hProp) → hProp).

Definition topologygenerated :=
  λ (x : X) (A : X → hProp),
  (∃ L : Sequence (X → hProp), (∏ n, O (L n)) × (finite_intersection L x) × (∏ y, finite_intersection L y → A y)).

Lemma topologygenerated_imply :
  ∏ x : X, isfilter_imply (topologygenerated x).
Proof.
  intros x A B H.
  apply hinhfun.
  intros L.
  exists (pr1 L).
  repeat split.
  exact (pr1 (pr2 L)).
  exact (pr1 (pr2 (pr2 L))).
  intros y Hy.
  apply H, (pr2 (pr2 (pr2 L))), Hy.
Qed.

Lemma topologygenerated_htrue :
  ∏ x : X, isfilter_htrue (topologygenerated x).
Proof.
  intros x.
  apply hinhpr.
  exists nil.
  repeat split; intros n; induction (nopathsfalsetotrue (pr2 n)).
Qed.

Lemma topologygenerated_and :
  ∏ x : X, isfilter_and (topologygenerated x).
Proof.
  intros x A B.
  apply hinhfun2.
  intros La Lb.
  exists (concatenate (pr1 La) (pr1 Lb)).
  repeat split.
  - simpl ; intro.
    apply (coprod_rect (λ x, O (coprod_rect _ _ _ x))) ; intros m.
    + rewrite coprod_rect_compute_1.
      exact (pr1 (pr2 La) _).
    + rewrite coprod_rect_compute_2.
      exact (pr1 (pr2 Lb) _).
  - simpl ; intro.
    apply (coprod_rect (λ y, (coprod_rect (λ _ : stn (length (pr1 La)) ⨿ stn (length (pr1 Lb)), X → hProp) (λ j : stn (length (pr1 La)), (pr1 La) j)
       (λ k : stn (length (pr1 Lb)), (pr1 Lb) k) y) x)) ; intros m.
    + rewrite coprod_rect_compute_1.
      exact (pr1 (pr2 (pr2 La)) _).
    + rewrite coprod_rect_compute_2.
      exact (pr1 (pr2 (pr2 Lb)) _).
  - apply (pr2 (pr2 (pr2 La))).
    intros n.
    simpl in X0.
    unfold concatenate' in X0.
    specialize (X0 (weqfromcoprodofstn_map (length (pr1 La)) (length (pr1 Lb)) (ii1 n))).
    now rewrite (weqfromcoprodofstn_eq1 _ _) , coprod_rect_compute_1 in X0.
  - apply (pr2 (pr2 (pr2 Lb))).
    intros n.
    simpl in X0.
    unfold concatenate' in X0.
    specialize (X0 (weqfromcoprodofstn_map (length (pr1 La)) (length (pr1 Lb)) (ii2 n))).
    now rewrite (weqfromcoprodofstn_eq1 _ _), coprod_rect_compute_2 in X0.
Qed.

Lemma topologygenerated_point :
  ∏ (x : X) (P : X → hProp), topologygenerated x P → P x.
Proof.
  intros x P.
  apply hinhuniv.
  intros L.
  apply (pr2 (pr2 (pr2 L))).
  exact (pr1 (pr2 (pr2 L))).
Qed.

Lemma topologygenerated_neighborhood :
∏ (x : X) (P : X → hProp),
 topologygenerated x P
 → ∃ Q : X → hProp,
    topologygenerated x Q × (∏ y : X, Q y → topologygenerated y P).
Proof.
  intros x P.
  apply hinhfun.
  intros L.
  exists (finite_intersection (pr1 L)).
  split.
  - apply hinhpr.
    exists (pr1 L).
    repeat split.
    exact (pr1 (pr2 L)).
    exact (pr1 (pr2 (pr2 L))).
    easy.
  - intros y Hy.
    apply hinhpr.
    exists (pr1 L).
    repeat split.
    exact (pr1 (pr2 L)).
    exact Hy.
    exact (pr2 (pr2 (pr2 L))).
Qed.

End topologygenerated.

Definition TopologyGenerated {X : UU} (O : (X → hProp) → hProp) : Topology X.
Proof.
  intros X O.
  simple refine (TopologyFromNeighborhood _ _).
  - apply topologygenerated, O.
  - repeat split.
    + apply topologygenerated_imply.
    + apply topologygenerated_htrue.
    + apply topologygenerated_and.
    + apply topologygenerated_point.
    + apply topologygenerated_neighborhood.
Defined.
Definition TopologicalSetGenerated {X : hSet} (O : (X → hProp) → hProp) : TopologicalSet.
Proof.
  intros X O.
  simple refine (pairTopologicalSet _ _).
  - exact X.
  - apply TopologyGenerated, O.
Defined.

Lemma TopologyGenerated_included {X : UU} :
  ∏ (O : (X → hProp) → hProp) (P : X → hProp),
    O P → isOpen (TopologyGenerated O) P.
Proof.
  intros X O P Op.
  apply neighborhood_isOpen.
  intros x Hx.
  apply TopologyFromNeighborhood_correct.
  apply hinhpr.
  exists (singletonSequence P).
  repeat split.
  - induction n as [n Hn].
    exact Op.
  - intros n ;
    induction n as [n Hn].
    exact Hx.
  - intros y Hy.
    now apply (Hy (0%nat,,paths_refl _)).
Qed.
Lemma TopologyGenerated_smallest {X : UU} :
  ∏ (O : (X → hProp) → hProp) (T : Topology X),
    (∏ P : X → hProp, O P → pr1 T P)
    → ∏ P : X → hProp, isOpen (TopologyGenerated O) P → pr1 T P.
Proof.
  intros X O T Ht P Hp.
  apply (neighborhood_isOpen T).
  intros x Px.
  generalize (Hp x Px) ; clear Hp.
  apply hinhfun.
  intros L.
  simple refine (tpair _ _ _).
  simple refine (tpair _ _ _).
  apply (finite_intersection (pr1 L)).
  apply (isOpen_finite_intersection T).
  intros m.
  apply Ht.
  apply (pr1 (pr2 L)).
  split.
  exact (pr1 (pr2 (pr2 L))).
  exact (pr2 (pr2 (pr2 L))).
Qed.

(** *** Product of topologies *)

Section topologydirprod.

Context {U V : UU}
        (topoU : Topology U)
        (topoV : Topology V).

Definition topologydirprod :=
  λ (z : U × V) (A : U × V → hProp),
  (∃ (Ax : U → hProp) (Ay : V → hProp),
      (Ax (pr1 z) × isOpen topoU Ax)
        × (Ay (pr2 z) × isOpen topoV Ay)
        × (∏ x y, Ax x → Ay y → A (x,,y))).

Lemma topologydirprod_imply :
  ∏ x : U × V, isfilter_imply (topologydirprod x).
Proof.
  intros x A B H.
  apply hinhfun.
  intros AB.
  exists (pr1 AB), (pr1 (pr2 AB)) ; split ; [ | split].
  exact (pr1 (pr2 (pr2 AB))).
  exact (pr1 (pr2 (pr2 (pr2 AB)))).
  intros x' y' Hx' Hy'.
  now apply H, (pr2 (pr2 (pr2 (pr2 AB)))).
Qed.

Lemma topologydirprod_htrue :
  ∏ x : U × V, isfilter_htrue (topologydirprod x).
Proof.
  intros z.
  apply hinhpr.
  exists (λ _, htrue), (λ _, htrue).
  repeat split.
  apply isOpen_htrue.
  apply isOpen_htrue.
Qed.

Lemma topologydirprod_and :
  ∏ x : U × V, isfilter_and (topologydirprod x).
Proof.
  intros z A B.
  apply hinhfun2.
  intros A' B'.
  exists (λ x, pr1 A' x ∧ pr1 B' x), (λ y, pr1 (pr2 A') y ∧ pr1 (pr2 B') y).
  repeat split.
  apply (pr1 (pr1 (pr2 (pr2 A')))).
  apply (pr1 (pr1 (pr2 (pr2 B')))).
  apply isOpen_and.
  apply (pr2 (pr1 (pr2 (pr2 A')))).
  apply (pr2 (pr1 (pr2 (pr2 B')))).
  apply (pr1 (pr1 (pr2 (pr2 (pr2 A'))))).
  apply (pr1 (pr1 (pr2 (pr2 (pr2 B'))))).
  apply isOpen_and.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 A'))))).
  apply (pr2 (pr1 (pr2 (pr2 (pr2 B'))))).
  apply (pr2 (pr2 (pr2 (pr2 A')))).
  apply (pr1 X).
  apply (pr1 X0).
  apply (pr2 (pr2 (pr2 (pr2 B')))).
  apply (pr2 X).
  apply (pr2 X0).
Qed.

Lemma topologydirprod_point :
  ∏ (x : U × V) (P : U × V → hProp), topologydirprod x P → P x.
Proof.
  intros xy A.
  apply hinhuniv.
  intros A'.
  apply (pr2 (pr2 (pr2 (pr2 A')))).
  exact (pr1 (pr1 (pr2 (pr2 A')))).
  exact (pr1 (pr1 (pr2 (pr2 (pr2 A'))))).
Qed.

Lemma topologydirprod_neighborhood :
  ∏ (x : U × V) (P : U × V → hProp),
    topologydirprod x P
    → ∃ Q : U × V → hProp,
      topologydirprod x Q
                      × (∏ y : U × V, Q y → topologydirprod y P).
Proof.
  intros xy P.
  apply hinhfun.
  intros A'.
  exists (λ z, pr1 A' (pr1 z) ∧ pr1 (pr2 A') (pr2 z)).
  split.
  - apply hinhpr.
    exists (pr1 A'), (pr1 (pr2 A')).
    split.
    exact (pr1 (pr2 (pr2 A'))).
    split.
    exact (pr1 (pr2 (pr2 (pr2 A')))).
    intros x' y' Ax' Ay'.
    now split.
  - intros z Az.
    apply hinhpr.
    exists (pr1 A'), (pr1 (pr2 A')).
    repeat split.
    exact (pr1 Az).
    exact (pr2 (pr1 (pr2 (pr2 A')))).
    exact (pr2 Az).
    exact (pr2 (pr1 (pr2 (pr2 (pr2 A'))))).
    exact (pr2 (pr2 (pr2 (pr2 A')))).
Qed.

End topologydirprod.

Definition TopologyDirprod {U V : UU}
           (topoU : Topology U) (topoV : Topology V) : Topology (U × V).
Proof.
  intros U V topoU topoV.
  simple refine (TopologyFromNeighborhood _ _).
  - apply topologydirprod.
    + apply topoU.
    + apply topoV.
  - repeat split.
    + apply topologydirprod_imply.
    + apply topologydirprod_htrue.
    + apply topologydirprod_and.
    + apply topologydirprod_point.
    + apply topologydirprod_neighborhood.
Defined.
Definition TopologicalSetDirprod {U V : TopologicalSet} : TopologicalSet.
Proof.
  intros U V.
  simple refine (pairTopologicalSet _ _).
  - simple refine (hSetpair _ _).
    exact (U × V).
    apply isasetdirprod ; apply setproperty.
  - apply TopologyDirprod.
    apply (pr2 U).
    apply (pr2 V).
Defined.

Definition locally2d {U V : UU} (topoU : Topology U) (topoV : Topology V)
           (x : U) (y : V) : Filter (U × V) :=
  FilterDirprod (locally topoU x) (locally topoV y).

Lemma locally2d_correct {U V : UU} (topoU : Topology U) (topoV : Topology V) (x : U) (y : V) :
  ∏ P : U × V → hProp, locally2d topoU topoV x y P <-> locally (TopologyDirprod topoU topoV) (x,,y) P.
Proof.
  intros P.
  split ; apply hinhuniv.
  - intros A.
    apply TopologyFromNeighborhood_correct.
    generalize (pr1 (pr2 (pr2 A))) (pr1 (pr2 (pr2 (pr2 A)))).
    apply hinhfun2.
    intros Ox Oy.
    exists (pr1 Ox), (pr1 Oy).
    repeat split.
    + exact (pr1 (pr2 Ox)).
    + exact (pr2 (pr1 Ox)).
    + exact (pr1 (pr2 Oy)).
    + exact (pr2 (pr1 Oy)).
    + intros x' y' Hx' Hy'.
      apply (pr2 (pr2 (pr2 (pr2 A)))).
      now apply (pr2 (pr2 Ox)).
      now apply (pr2 (pr2 Oy)).
  - intros O.
    generalize (pr2 (pr1 O) _ (pr1 (pr2 O))).
    apply hinhfun.
    intros A.
    exists (pr1 A), (pr1 (pr2 A)).
    repeat split.
    apply (pr2 (neighborhood_isOpen topoU _)).
    exact (pr2 (pr1 (pr2 (pr2 A)))).
    exact (pr1 (pr1 (pr2 (pr2 A)))).
    apply (pr2 (neighborhood_isOpen topoV _)).
    exact (pr2 (pr1 (pr2 (pr2 (pr2 A))))).
    exact (pr1 (pr1 (pr2 (pr2 (pr2 A))))).
    intros x' y' Ax' Ay'.
    apply (pr2 (pr2 O)).
    now apply (pr2 (pr2 (pr2 (pr2 A)))).
Qed.

(** *** Topology on a subtype *)

Section topologysubtype.

Context {T : UU}
        (topo : Topology T)
        (dom : T → hProp).

Definition topologysubtype :=
  λ (x : ∑ x : T, dom x) (A : (∑ x0 : T, dom x0) → hProp),
  ∃ B : T → hProp,
    (B (pr1 x) × isOpen topo B) × (∏ y : ∑ x0 : T, dom x0, B (pr1 y) → A y).

Lemma topologysubtype_imply :
  ∏ x : ∑ x : T, dom x, isfilter_imply (topologysubtype x).
Proof.
  intros x A B H.
  apply hinhfun.
  intros A'.
  exists (pr1 A').
  split.
  exact (pr1 (pr2 A')).
  intros y Hy.
  now apply H, (pr2 (pr2 A')).
Qed.

Lemma topologysubtype_htrue :
  ∏ x : ∑ x : T, dom x, isfilter_htrue (topologysubtype x).
Proof.
  intros x.
  apply hinhpr.
  exists (λ _, htrue).
  repeat split.
  now apply isOpen_htrue.
Qed.

Lemma topologysubtype_and :
  ∏ x : ∑ x : T, dom x, isfilter_and (topologysubtype x).
Proof.
  intros x A B.
  apply hinhfun2.
  intros A' B'.
  exists (λ x, pr1 A' x ∧ pr1 B' x).
  repeat split.
  exact (pr1 (pr1 (pr2 A'))).
  exact (pr1 (pr1 (pr2 B'))).
  apply isOpen_and.
  exact (pr2 (pr1 (pr2 A'))).
  exact (pr2 (pr1 (pr2 B'))).
  apply (pr2 (pr2 A')), (pr1 X).
  apply (pr2 (pr2 B')), (pr2 X).
Qed.

Lemma topologysubtype_point :
  ∏ (x : ∑ x : T, dom x) (P : (∑ x0 : T, dom x0) → hProp),
    topologysubtype x P → P x.
Proof.
  intros x A.
  apply hinhuniv.
  intros B.
  apply (pr2 (pr2 B)), (pr1 (pr1 (pr2 B))).
Qed.

Lemma topologysubtype_neighborhood :
  ∏ (x : ∑ x : T, dom x) (P : (∑ x0 : T, dom x0) → hProp),
    topologysubtype x P
    → ∃ Q : (∑ x0 : T, dom x0) → hProp,
      topologysubtype x Q
       × (∏ y : ∑ x0 : T, dom x0, Q y → topologysubtype y P).
Proof.
  intros x A.
  apply hinhfun.
  intros B.
  exists (λ y : ∑ x : T, dom x, pr1 B (pr1 y)).
  split.
  - apply hinhpr.
    exists (pr1 B).
    split.
    exact (pr1 (pr2 B)).
    easy.
  - intros y By.
    apply hinhpr.
    exists (pr1 B).
    repeat split.
    exact By.
    exact (pr2 (pr1 (pr2 B))).
    exact (pr2 (pr2 B)).
Qed.

End topologysubtype.

Definition TopologySubtype {T : UU} (topo : Topology T) (dom : T → hProp) : Topology (∑ x : T, dom x).
Proof.
  intros T topo dom.
  simple refine (TopologyFromNeighborhood _ _).
  - apply topologysubtype, topo.
  - repeat split.
    + apply topologysubtype_imply.
    + apply topologysubtype_htrue.
    + apply topologysubtype_and.
    + apply topologysubtype_point.
    + apply topologysubtype_neighborhood.
Defined.
Definition TopologicalSetSubtype {T : TopologicalSet} (dom : T → hProp) : TopologicalSet.
Proof.
  intros T dom.
  simple refine (pairTopologicalSet _ _).
  - apply (hSetpair (∑ x : T, dom x)).
    apply isaset_total2.
    apply setproperty.
    intros x.
    apply isasetaprop.
    apply propproperty.
  - apply TopologySubtype.
    apply (pr2 T).
Defined.

(** ** Limits in a Topological Set *)

Section locally_base.

Context {T : UU}
        (topo : Topology T)
        (x : T)
        (base : base_of_neighborhood topo x).

Lemma locally_base_imply :
  isfilter_imply (neighborhood' topo x base).
Proof.
  intros A B H Ha.
  apply (pr2 (neighborhood_equiv _ _ _ _)).
  eapply neighborhood_imply.
  exact H.
  eapply neighborhood_equiv.
  exact Ha.
Qed.
Lemma locally_base_htrue :
  isfilter_htrue (neighborhood' topo x base).
Proof.
  apply (pr2 (neighborhood_equiv _ _ _ _)).
  apply (pr2 (neighborhood_isOpen topo _)).
  apply isOpen_htrue.
  apply tt.
Qed.
Lemma locally_base_and :
  isfilter_and (neighborhood' topo x base).
Proof.
  intros A B Ha Hb.
  apply (pr2 (neighborhood_equiv _ _ _ _)).
  eapply neighborhood_and.
  eapply neighborhood_equiv, Ha.
  eapply neighborhood_equiv, Hb.
Qed.

End locally_base.

Definition locally_base {T : UU} (topo : Topology T)
           (x : T) (base : base_of_neighborhood topo x) : Filter T.
Proof.
  intros T topo x base.
  simple refine (mkFilter _ _ _ _ _).
  - apply (neighborhood' topo x base).
  - apply locally_base_imply.
  - apply locally_base_htrue.
  - apply locally_base_and.
  - intros A Ha.
    apply neighborhood_equiv in Ha.
    apply neighborhood_point in Ha.
    apply hinhpr.
    now exists x.
Defined.

(** *** Limit of a filter *)

Definition is_filter_lim {T : UU} (topo : Topology T)
           (F : Filter T) (x : T) :=
  filterlim (λ x : T, x) F (locally topo x).
Definition ex_filter_lim  {T : UU} (topo : Topology T) (F : Filter T) :=
  ∃ (x : T), is_filter_lim topo F x.

Definition is_filter_lim_base {T : UU} (topo : Topology T)
           (F : Filter T) (x : T) base :=
  filterlim (λ x : T, x) F (locally_base topo x base).
Definition ex_filter_lim_base  {T : UU} (topo : Topology T) (F : Filter T) :=
  ∃ (x : T) base, is_filter_lim_base topo F x base.

Lemma is_filter_lim_base_correct {T : UU} (topo : Topology T)
      (F : Filter T) (x : T) base :
  is_filter_lim_base topo F x base <-> is_filter_lim topo F x.
Proof.
  split.
  - intros Hx P HP.
    apply (pr2 (neighborhood_equiv _ _ base _)) in HP.
    apply Hx.
    exact HP.
  - intros Hx P HP.
    apply neighborhood_equiv in HP.
    apply Hx.
    exact HP.
Qed.
Lemma ex_filter_lim_base_correct {T : UU} (topo : Topology T) (F : Filter T) :
  ex_filter_lim_base topo F <-> ex_filter_lim topo F.
Proof.
  split.
  - apply hinhfun.
    intros x.
    exists (pr1 x).
    eapply is_filter_lim_base_correct.
    exact (pr2 (pr2 x)).
  - apply hinhfun.
    intros x.
    exists (pr1 x), (base_of_neighborhood_default _ (pr1 x)).
    apply (pr2 (is_filter_lim_base_correct _ _ _ _)).
    exact (pr2 x).
Qed.

(** *** Limit of a function *)

Definition is_lim {X T : UU} (topo : Topology T) (f : X → T) (F : Filter X) (x : T) :=
  filterlim f F (locally topo x).
Definition ex_lim {X T : UU} (topo : Topology T) (f : X → T) (F : Filter X) :=
  ∃ (x : T), is_lim topo f F x.

Definition is_lim_base {X T : UU} (topo : Topology T) (f : X → T) (F : Filter X) (x : T) base :=
  filterlim f F (locally_base topo x base).
Definition ex_lim_base {X T : UU} (topo : Topology T) (f : X → T) (F : Filter X) :=
  ∃ (x : T) base, is_lim_base topo f F x base.

Lemma is_lim_base_correct {X T : UU} (topo : Topology T) (f : X → T) (F : Filter X) (x : T) base :
  is_lim_base topo f F x base <-> is_lim topo f F x.
Proof.
  split.
  - intros Hx P HP.
    apply Hx, (pr2 (neighborhood_equiv _ _ _ _)).
    exact HP.
  - intros Hx P HP.
    eapply Hx, neighborhood_equiv.
    exact HP.
Qed.
Lemma ex_lim_base_correct {X T : UU} (topo : Topology T) (f : X → T) (F : Filter X) :
  ex_lim_base topo f F <-> ex_lim topo f F.
Proof.
  split.
  - apply hinhfun.
    intros x.
    exists (pr1 x).
    eapply is_lim_base_correct.
    exact (pr2 (pr2 x)).
  - apply hinhfun.
    intros x.
    exists (pr1 x), (base_of_neighborhood_default _ (pr1 x)).
    apply (pr2 (is_lim_base_correct _ _ _ _ _)).
    exact (pr2 x).
Qed.

(** *** Continuity *)

Definition continuous_at {U V : UU} (topoU : Topology U) (topoV : Topology V)
           (f : U → V) (x : U) :=
  is_lim topoV f (locally topoU x) (f x).

Definition continuous_on {U V : UU} (topoU : Topology U) (topoV : Topology V)
            (dom : U → hProp) (f : ∏ (x : U), dom x → V) :=
  ∏ (x : U) (Hx : dom x),
    ∃ H,
      is_lim topoV (λ y : (∑ x : U, dom x), f (pr1 y) (pr2 y)) (FilterSubtype (locally topoU x) dom H) (f x Hx).
Definition continuous {U V : UU} (topoU : Topology U) (topoV : Topology V)
            (f : U → V) :=
  ∏ x : U, continuous_at topoU topoV f x.

Definition continuous_base_at {U V : UU} (topoU : Topology U) (topoV : Topology V)
            (f : U → V) (x : U) base_x base_fx :=
  is_lim_base topoV f (locally_base topoU x base_x) (f x) base_fx.

(** *** Continuity for 2 variable functions *)

Definition continuous2d_at {U V W : UU}
           (topoU : Topology U) (topoV : Topology V) (topoW : Topology W)
           (f : U → V → W) (x : U) (y : V) :=
  is_lim topoW (λ z : U × V, f (pr1 z) (pr2 z)) (FilterDirprod (locally topoU x) (locally topoV y)) (f x y).
Definition continuous2d {U V W : UU}
           (topoU : Topology U) (topoV : Topology V) (topoW : Topology W)
           (f : U → V → W) :=
  ∏ (x : U) (y : V), continuous2d_at topoU topoV topoW f x y.

Definition continuous2d_base_at {U V W : UU}
           (topoU : Topology U) (topoV : Topology V) (topoW : Topology W)
           (f : U → V → W)
           (x : U) (y : V) base_x base_y base_fxy :=
  is_lim_base topoW (λ z : U × V, f (pr1 z) (pr2 z))
              (FilterDirprod (locally_base topoU x base_x) (locally_base topoV y base_y))
              (f x y) base_fxy.

(** *** Continuity of basic functions *)

Lemma is_lim_comp {X U V : UU} (topoU : Topology U) (topoV : Topology V)
            (f : X → U) (g : U → V) (F : Filter X) (l : U) :
  is_lim topoU f F l → continuous_at topoU topoV g l →
  is_lim topoV (funcomp f g) F (g l).
Proof.
  intros X U V topoU topoV f g F l.
  apply filterlim_comp.
Qed.
Lemma continuous_comp {X Y Z : UU}
      (topoX : Topology X) (topoY : Topology Y) (topoZ : Topology Z)
      (f : X → Y) (g : Y → Z) :
  continuous topoX topoY f → continuous topoY topoZ g →
  continuous topoX topoZ (funcomp f g).
Proof.
  intros X Y Z topoX topoY topoZ f g Hf Hg x.
  refine (is_lim_comp _ _ _ _ _ _ _ _).
  apply Hf.
  apply Hg.
Qed.

Lemma continuous2d_comp {X : UU} {U V W : UU}
           (topoU : Topology U) (topoV : Topology V) (topoW : Topology W)
           (f : X → U) (g : X → V) (h : U → V → W) (F : Filter X) (lf : U) (lg : V) :
  is_lim topoU f F lf → is_lim topoV g F lg → continuous2d_at topoU topoV topoW h lf lg →
  is_lim topoW (λ x, h (f x) (g x)) F (h lf lg).
Proof.
  intros X U V W topoU topoV topoW f g h F lf lg Hf Hg.
  apply (filterlim_comp (λ x, (f x ,, g x))).
  intros P.
  apply hinhuniv.
  intros Hp.
  generalize (filter_and F _ _ (Hf _ (pr1 (pr2 (pr2 Hp)))) (Hg _ (pr1 (pr2 (pr2 (pr2 Hp)))))).
  apply (filter_imply F).
  intros x Hx.
  apply (pr2 (pr2 (pr2 (pr2 Hp)))).
  exact (pr1 Hx).
  exact (pr2 Hx).
Qed.

Lemma continuous_tpair {U V : UU} (topoU : Topology U) (topoV : Topology V) :
  continuous2d topoU topoV (TopologyDirprod topoU topoV) (λ (x : U) (y : V), (x,,y)).
Proof.
  intros U V topoU topoV x y P.
  apply hinhuniv.
  intros O.
  simple refine (filter_imply _ _ _ _ _).
  - exact (pr1 O).
  - exact (pr2 (pr2 O)).
  - generalize (pr2 (pr1 O) _ (pr1 (pr2 O))).
    apply hinhfun.
    intros Ho.
    exists (pr1 Ho), (pr1 (pr2 Ho)).
    repeat split.
    + apply (pr2 (neighborhood_isOpen topoU _)).
      exact (pr2 (pr1 (pr2 (pr2 Ho)))).
      exact (pr1 (pr1 (pr2 (pr2 Ho)))).
    + apply (pr2 (neighborhood_isOpen topoV _)).
      exact (pr2 (pr1 (pr2 (pr2 (pr2 Ho))))).
      exact (pr1 (pr1 (pr2 (pr2 (pr2 Ho))))).
    + exact (pr2 (pr2 (pr2 (pr2 Ho)))).
Qed.
Lemma continuous_pr1 {U V : UU} (topoU : Topology U) (topoV : Topology V)
            :
  continuous (TopologyDirprod topoU topoV) topoU (λ (xy : U × V), pr1 xy).
Proof.
  intros U V topoU topoV xy P.
  apply hinhuniv.
  intros O.
  simple refine (filter_imply _ _ _ _ _).
  - exact (pr1 (pr1 O)).
  - exact (pr2 (pr2 O)).
  - apply hinhpr.
    use tpair.
    use tpair.
    + apply (λ xy : U × V, pr1 O (pr1 xy)).
    + intros xy' Oxy.
      apply hinhpr.
      exists (pr1 O), (λ _, htrue).
      repeat split.
      exact Oxy.
      exact (pr2 (pr1 O)).
      exact (isOpen_htrue _).
      easy.
    + repeat split.
      * exact (pr1 (pr2 O)).
      * easy.
Qed.
Lemma continuous_pr2 {U V : UU} (topoU : Topology U) (topoV : Topology V) :
  continuous (TopologyDirprod topoU topoV) topoV (λ (xy : U × V), pr2 xy).
Proof.
  intros U V topoU topoV xy P.
  apply hinhuniv.
  intros O.
  simple refine (filter_imply _ _ _ _ _).
  - exact (pr1 (pr1 O)).
  - exact (pr2 (pr2 O)).
  - apply hinhpr.
    use tpair.
    use tpair.
    + apply (λ xy : U × V, pr1 O (pr2 xy)).
    + intros xy' Oxy.
      apply hinhpr.
      exists (λ _, htrue), (pr1 O).
      repeat split.
      exact (isOpen_htrue _).
      exact Oxy.
      exact (pr2 (pr1 O)).
      easy.
    + repeat split.
      * exact (pr1 (pr2 O)).
      * easy.
Qed.

(** ** Topology in algebraic structures *)

Definition isTopological_monoid (X : monoid) (topo : Topology X) :=
  continuous2d topo topo topo BinaryOperations.op.
Definition Topological_monoid :=
  ∑ (X : monoid) (topo : Topology X), isTopological_monoid X topo.

Definition isTopological_gr (X : gr) (topo : Topology X) :=
  isTopological_monoid X topo
  × continuous topo topo (grinv X).
Definition Topological_gr :=
  ∑ (X : gr) topo, isTopological_gr X topo.

Definition isTopological_rig (X : rig) (topo : Topology X) :=
  isTopological_monoid (rigaddabmonoid X) topo
  × isTopological_monoid (rigmultmonoid X) topo.
Definition Topological_rig :=
  ∑ (X : rig) topo, isTopological_rig X topo.

Definition isTopological_rng (X : rng) (topo : Topology X) :=
  isTopological_gr (rngaddabgr X) topo
  × isTopological_monoid (rigmultmonoid X) topo.
Definition Topological_rng :=
  ∑ (X : rng) topo, isTopological_rng X topo.

Definition isTopological_DivRig (X : DivRig) (topo : Topology X) :=
  isTopological_rig (pr1 X) topo
  × continuous_on topo topo
                  (λ x : X, hProppair (x != 0%dr) (isapropneg _)) (λ x Hx, invDivRig (x,,Hx)).
Definition Topological_DivRig :=
  ∑ (X : DivRig) topo, isTopological_DivRig X topo.

Definition isTopological_fld (X : fld) (topo : Topology X) :=
  isTopological_rng (pr1 X) topo
  × continuous_on topo topo
                  (λ x : X, hProppair (x != 0%rng) (isapropneg _))
                  fldmultinv.
Definition Topological_fld :=
  ∑ (X : fld) is, isTopological_fld X is.

Definition isTopological_ConstructiveDivisionRig (X : ConstructiveDivisionRig) (topo : Topology X) :=
  isTopological_rig (pr1 X) topo
  × continuous_on topo topo (λ x : X, (x ≠ 0)%CDR) CDRinv.
Definition Topological_ConstructiveDivisionRig :=
  ∑ (X : ConstructiveDivisionRig) topo, isTopological_ConstructiveDivisionRig X topo.

Definition isTopological_ConstructiveField (X : ConstructiveField) (topo : Topology X) :=
  isTopological_rng (pr1 X) topo
  × continuous_on topo topo (λ x : X, (x ≠ 0)%CF) CFinv.
Definition Topological_ConstructiveField :=
  ∑ (X : ConstructiveField) is, isTopological_ConstructiveField X is.
