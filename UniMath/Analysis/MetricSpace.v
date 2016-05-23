(** * Results about Metric Spaces *)
(** Author: Catherine LELAY. Jan 2016 - *)

Require Export UniMath.Topology.Filters.
Require Import UniMath.Topology.Topology.
Require Import UniMath.Topology.UniformSpace.
Require Import UniMath.RealNumbers.Sets.
Require Import UniMath.Foundations.Algebra.Apartness.

(** ** Lattice *)

Definition islatticeop {X : hSet} (min max : binop X) :=
  (isassoc min)
    × (iscomm min)
    × (isassoc max)
    × (iscomm max)
    × (∀ x y : X, min x (max x y) = x)
    × (∀ x y : X, max x (min x y) = x).
Definition islattice (X : hSet) := Σ min max : binop X, islatticeop min max.
Definition lattice := Σ X : hSet, islattice X.
Definition pr1lattice : lattice -> setwith2binop :=
  λ L : lattice, pr1 L,, pr1 (pr2 L),, pr1 (pr2 (pr2 L)).
Coercion pr1lattice : lattice >-> setwith2binop.

Section lattice_pty.

Context {L : lattice}.

Definition Lmin : binop L := BinaryOperations.op1.
Definition Lmax : binop L := BinaryOperations.op2.
Definition Lle : hrel L :=
  λ (x y : L), hProppair (Lmin x y = x) (pr2 (pr1 L) (Lmin x y) x).

Local Lemma pr2lattice :
  (isassoc Lmin)
    × (iscomm Lmin)
    × (isassoc Lmax)
    × (iscomm Lmax)
    × (∀ x y : L, Lmin x (Lmax x y) = x)
    × (∀ x y : L, Lmax x (Lmin x y) = x).
Proof.
  apply (pr2 (pr2 (pr2 L))).
Qed.

Lemma isassoc_Lmin :
  isassoc Lmin.
Proof.
  exact (pr1 pr2lattice).
Qed.
Lemma iscomm_Lmin :
  iscomm Lmin.
Proof.
  exact (pr1 (pr2 pr2lattice)).
Qed.
Lemma isassoc_Lmax :
  isassoc Lmax.
Proof.
  exact (pr1 (pr2 (pr2 pr2lattice))).
Qed.
Lemma iscomm_Lmax :
  iscomm Lmax.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 pr2lattice)))).
Qed.
Lemma Lmin_absorb :
  ∀ x y : L, Lmin x (Lmax x y) = x.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 pr2lattice))))).
Qed.
Lemma Lmax_absorb :
  ∀ x y : L, Lmax x (Lmin x y) = x.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 pr2lattice))))).
Qed.

Lemma Lmin_id :
  ∀ x : L, Lmin x x = x.
Proof.
  intros x.
  pattern x at 2 ; rewrite <- (Lmax_absorb x x).
  apply Lmin_absorb.
Qed.
Lemma Lmax_id :
  ∀ x : L, Lmax x x = x.
Proof.
  intros x.
  pattern x at 2 ; rewrite <- (Lmin_absorb x x).
  apply Lmax_absorb.
Qed.

Lemma isrefl_Lle :
  isrefl Lle.
Proof.
  intros x.
  apply Lmin_id.
Qed.
Lemma isantisymm_Lle :
  isantisymm Lle.
Proof.
  intros x y Hxy Hyx.
  rewrite <- Hxy.
  pattern y at 2 ; rewrite <- Hyx.
  apply iscomm_Lmin.
Qed.
Lemma istrans_Lle :
  istrans Lle.
Proof.
  intros x y z <- <-.
  simpl.
  rewrite !isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.

Lemma Lmin_le_l :
  ∀ x y : L, Lle (Lmin x y) x.
Proof.
  intros x y.
  simpl.
  rewrite iscomm_Lmin, <- isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma Lmin_le_r :
  ∀ x y : L, Lle (Lmin x y) y.
Proof.
  intros x y.
  rewrite iscomm_Lmin.
  apply Lmin_le_l.
Qed.
Lemma Lmax_le_l :
  ∀ x y : L, Lle x (Lmax x y).
Proof.
  intros x y.
  simpl.
  apply Lmin_absorb.
Qed.
Lemma Lmax_le_r :
  ∀ x y : L, Lle y (Lmax x y).
Proof.
  intros x y.
  rewrite iscomm_Lmax.
  apply Lmax_le_l.
Qed.

Lemma Lmin_eq_l :
  ∀ x y : L, Lle x y -> Lmin x y = x.
Proof.
  intros x y H.
  apply H.
Qed.
Lemma Lmin_eq_r :
  ∀ x y : L, Lle y x -> Lmin x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmin.
  apply H.
Qed.

Lemma Lmax_eq_l :
  ∀ x y : L, Lle y x -> Lmax x y = x.
Proof.
  intros x y <-.
  rewrite iscomm_Lmin.
  apply Lmax_absorb.
Qed.
Lemma Lmax_eq_r :
  ∀ x y : L, Lle x y -> Lmax x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmax.
  now apply Lmax_eq_l.
Qed.

End lattice_pty.

Definition islatticelt (L : lattice) (lt : StrongOrder L) :=
  (∀ x y : L, (¬ (lt x y)) <-> Lle y x)
    × (∀ x y z : L, lt z x -> lt z y -> lt z (Lmin x y))
    × (∀ x y z : L, lt x z -> lt y z -> lt (Lmax x y) z).

Lemma notlt_Lle (L : lattice) (lt : StrongOrder L) (Hlt : islatticelt L lt) :
  ∀ x y : L, (¬ (lt x y)) <-> Lle y x.
Proof.
  intros L lt Hlt.
  apply (pr1 Hlt).
Qed.
Lemma lt_Lle (L : lattice) (lt : StrongOrder L) (Hlt : islatticelt L lt) :
  ∀ x y : L, lt x y -> Lle x y.
Proof.
  intros L lt Hlt.
  intros x y H.
  apply (notlt_Lle L lt).
  exact Hlt.
  intro H0.
  eapply isirrefl_StrongOrder.
  eapply istrans_StrongOrder.
  exact H.
  exact H0.
Qed.

Lemma Lmin_lt (L : lattice) (lt : StrongOrder L) (Hlt : islatticelt L lt) :
  ∀ x y z : L, lt z x -> lt z y -> lt z (Lmin x y).
Proof.
  intros L lt Hlt.
  apply (pr1 (pr2 Hlt)).
Qed.
Lemma Lmax_lt (L : lattice) (lt : StrongOrder L) (Hlt : islatticelt L lt) :
  ∀ x y z : L, lt x z -> lt y z -> lt (Lmax x y) z.
Proof.
  intros L lt Hlt.
  apply (pr2 (pr2 Hlt)).
Qed.

Definition apfromlt {X : hSet} (lt : StrongOrder X) : aprel X.
Proof.
  intros X lt.
  mkpair.
  - intros x y.
    simple refine (hProppair _ _).
    apply (coprod (lt x y) (lt y x)).
    apply isapropcoprod.
    apply propproperty.
    apply propproperty.
    intros Hxy Hyx.
    apply (isirrefl_StrongOrder lt x).
    now apply (istrans_StrongOrder lt _ y).
  - repeat split.
    + intros x [ | ] ;
      apply isirrefl_StrongOrder.
    + intros x y [Hxy | Hyx].
      now right.
      now left.
    + intros x y z [H | H] ;
      generalize (iscotrans_StrongOrder lt _ y _ H) ;
      apply hinhfun ; intros [H' | H'].
      now left ; left.
      now right ; left.
      now right ; right.
      now left ; right.
Defined.
Definition tightapfromlt {X : hSet} (lt : StrongOrder X) (le : hrel X)
           (Hnltle : ∀ x y, (¬ lt x y) <-> le y x) (Hle : isantisymm le) : tightap X.
Proof.
  intros X lt le Hnltle Hle.
  refine (tpair _ _ _).
  split.
  apply (pr2 (apfromlt lt)).
  intros x y Hlt.
  apply Hle ; apply (pr1 (Hnltle _ _)) ; intro H ; apply Hlt.
  now right.
  now left.
Defined.

(** ** Nonnegative Monoid *)

Open Scope addmonoid_scope.

Definition is_minus {X : monoid} (is : islattice X) (minus : binop X) :=
  (∀ x y : X, minus x y + y = Lmax (L := _,,is) x y).

Lemma minus_pos_lt {X : monoid} {is : islattice X}
      (lt : StrongOrder X) (is_lt : islatticelt (_,,is) lt) (is_lt' : isbinophrel lt)
      (minus : binop X) (is0 : is_minus is minus):
  ∀ x y : X, lt 0 (minus x y) -> lt y x.
Proof.
  intros.
  apply (pr2 is_lt' _ _ y) in X0.
  rewrite lunax, is0 in X0.
  rewrite <- (Lmax_eq_l (L := _,,is) x y).
  exact X0.
  apply (notlt_Lle _ _ is_lt).
  intros H ; revert X0.
  apply (pr2 (notlt_Lle _ _ is_lt _ _)).
  rewrite Lmax_eq_r.
  apply isrefl_Lle.
  now apply lt_Lle with (2 := H).
Qed.
Lemma minus_lt_pos {X : monoid} {is : islattice X}
      (lt : StrongOrder X) (is_lt : islatticelt (_,,is) lt) (is_lt' : isinvbinophrel lt)
      (minus : binop X) (is0 : is_minus is minus):
  ∀ x y : X, lt y x -> lt 0 (minus x y).
Proof.
  intros.
  apply (pr2 is_lt' _ _ y).
  rewrite lunax, is0.
  rewrite (Lmax_eq_l (L := _,,is) x y).
  exact X0.
  now apply lt_Lle with (2 := X0).
Qed.

Definition ex_minus {X : monoid} (is : islattice X) := Σ minus : binop X, is_minus is minus.

Definition isNonnegativeMonoid {X : monoid} (is : islattice X) (lt : StrongOrder X) :=
  (ex_minus is)
    × (islatticelt (_,,is) lt)
    × isbinophrel lt
    × isinvbinophrel lt
    × (∀ x : X, Lle (L := _,,is) 0 x)
    × (∃ x0, lt 0 x0)
    × (∀ x : X, Σ y : X, (Lle (L := _,,is) (y + y) x) × (lt 0 x -> lt 0 y)).

Definition NonnegativeMonoid :=
  Σ (X : monoid) (is : islattice X) (lt : StrongOrder X) (le : hrel X), isNonnegativeMonoid is lt.

Definition pr1NonnegativeMonoid : NonnegativeMonoid -> monoid := pr1.
Coercion pr1NonnegativeMonoid : NonnegativeMonoid >-> monoid.

Definition NnMlt (X : NonnegativeMonoid) : StrongOrder X :=
  pr1 (pr2 (pr2 X)).
Definition NnMle (X : NonnegativeMonoid) : PartialOrder X.
Proof.
  intros X.
  mkpair.
  apply (Lle (L := _,, pr1 (pr2 X))).
  repeat split.
  - now apply (istrans_Lle (L := _ ,, pr1 (pr2 X))).
  - now apply (isrefl_Lle (L := _ ,, pr1 (pr2 X))).
  - now apply (isantisymm_Lle (L := _ ,, pr1 (pr2 X))).
Defined.
Definition NnMap (X : NonnegativeMonoid) : tightap X.
Proof.
  intros X.
  simple refine (tightapfromlt _ _ _ _).
  - apply NnMlt.
  - apply (pr1 (NnMle _)).
  - apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
  - now apply (isantisymm_Lle (L := _ ,, pr1 (pr2 X))).
Defined.
Definition NnMmin {X : NonnegativeMonoid} : binop X :=
  Lmin (L := _,,(pr1 (pr2 X))).
Definition NnMmax {X : NonnegativeMonoid} : binop X :=
  Lmax (L := _,,(pr1 (pr2 X))).
Definition NnMminus {X : NonnegativeMonoid} : binop X :=
  (pr1 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))).
Definition NnMhalf {X : NonnegativeMonoid} : unop X :=
  λ x : X, (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))))) x)).

Local Notation "0" := (0%addmonoid).
Local Notation "x + y" := ((x + y)%addmonoid).
Local Notation "x - y" := (NnMminus _ x y).
Local Notation "x ≠ y" := (NnMap _ x y).
Local Notation "x < y" :=  (NnMlt _ x y).
Local Notation "x <= y" :=  (NnMle _ x y).

Lemma istight_NnMap {X : NonnegativeMonoid} : istight (NnMap X).
Proof.
  intros X.
  exact (pr2 (pr2 (NnMap X))).
Qed.
Lemma isirrefl_NnMap {X : NonnegativeMonoid} : isirrefl (NnMap X).
Proof.
  intros X.
  exact (pr1 (pr1 (pr2 (NnMap X)))).
Qed.
Lemma istotal_NnMlt {X : NonnegativeMonoid} :
  ∀ x y : X, x ≠ y <-> (x < y) ⨿ (y < x).
Proof.
  intros X.
  easy.
Qed.

Lemma notNnMlt_le {X : NonnegativeMonoid} :
  ∀ x y : X, (¬ (x < y)) <-> (y <= x).
Proof.
  intros X.
  now apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
Qed.
Lemma isirrefl_NnMlt {X : NonnegativeMonoid} :
  ∀ x : X, ¬ (x < x).
Proof.
  intros X.
  apply isirrefl_StrongOrder.
Qed.
Lemma istrans_NnMlt {X : NonnegativeMonoid} :
  ∀ x y z : X, x < y -> y < z -> x < z.
Proof.
  intros X.
  apply istrans_StrongOrder.
Qed.
Lemma iscotrans_NnMlt {X : NonnegativeMonoid} :
  ∀ x y z : X, x < z -> x < y ∨ y < z.
Proof.
  intros X.
  apply iscotrans_StrongOrder.
Qed.

Lemma NnMlt_le {X : NonnegativeMonoid} :
  ∀ x y : X, x < y -> x <= y.
Proof.
  intros X x y Hlt.
  apply (pr1 (notNnMlt_le _ _)).
  intros Hgt.
  simple refine (isirrefl_NnMlt _ _).
  apply X.
  apply x.
  simple refine (istrans_NnMlt _ _ _ _ _).
  apply y.
  exact Hlt.
  exact Hgt.
Qed.

Lemma istrans_NnMlt_le {X : NonnegativeMonoid} :
  ∀ x y z : X, x < y -> y <= z -> x < z.
Proof.
  intros X.
  intros x y z Hxy Hyz.
  generalize (iscotrans_NnMlt x z y Hxy).
  apply hinhuniv.
  intros [H | H].
  exact H.
  now apply (pr2 (notNnMlt_le _ _)) in Hyz.
Qed.

Lemma istrans_NnMle_lt {X : NonnegativeMonoid} :
  ∀ x y z : X, x <= y -> y < z -> x < z.
Proof.
  intros X.
  intros x y z Hxy Hyz.
  generalize (iscotrans_NnMlt y x z Hyz).
  apply hinhuniv.
  intros [H | H].
  now apply (pr2 (notNnMlt_le _ _)) in Hxy.
  exact H.
Qed.

Lemma isnonnegative_NnM {X : NonnegativeMonoid} :
  ∀ x : X, 0 <= x.
Proof.
  intros X.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))))).
Qed.
Lemma isnonnegative_NnM' {X : NonnegativeMonoid} :
  ∀ x : X, ¬ (x < 0).
Proof.
  intros X x.
  apply (pr2 (notNnMlt_le _ _)).
  now apply isnonnegative_NnM.
Qed.

Lemma NnMplus_lt_l {X : NonnegativeMonoid} :
  ∀ k x y : X, x < y -> k + x < k + y.
Proof.
  intros X k x y.
  apply (pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))).
Qed.
Lemma NnMplus_lt_r {X : NonnegativeMonoid} :
  ∀ k x y : X, x < y -> x + k < y + k.
Proof.
  intros X k x y.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))).
Qed.

Lemma NnMap_lt_0 {X : NonnegativeMonoid} :
  ∀ x : X, x ≠ 0 -> 0 < x.
Proof.
  intros X x Hx.
  apply istotal_NnMlt in Hx.
  destruct Hx as [Hx | Hx].
  apply fromempty.
  revert Hx.
  now apply isnonnegative_NnM'.
  exact Hx.
Qed.
Lemma NnMlt_ap {X : NonnegativeMonoid} :
  ∀ x y : X, x < y -> x ≠ y.
Proof.
  intros X x y H.
  apply (pr2 (istotal_NnMlt _ _)).
  now left.
Qed.

Lemma NnM_nottrivial (X : NonnegativeMonoid) :
  ∃ x0 : X, 0 < x0.
Proof.
  intros X.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))))).
Qed.

Lemma NnMmin_le_l {X : NonnegativeMonoid} :
  ∀ x y : X, NnMmin x y <= x.
Proof.
  intros X.
  apply (Lmin_le_l (L := _,,(pr1 (pr2 X)))).
Qed.
Lemma NnMmin_le_r {X : NonnegativeMonoid} :
  ∀ x y : X, NnMmin x y <= y.
Proof.
  intros X.
  apply (Lmin_le_r (L := _,,(pr1 (pr2 X)))).
Qed.
Lemma NnMmin_gt {X : NonnegativeMonoid} :
  ∀ x y z : X, z < x -> z < y -> z < NnMmin x y.
Proof.
  intros X.
  apply (Lmin_lt (_,,(pr1 (pr2 X)))).
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
Qed.

Lemma iscomm_NnMmin {X : NonnegativeMonoid} :
  iscomm (NnMmin (X := X)).
Proof.
  intros X.
  apply (iscomm_Lmin (L := _,,(pr1 (pr2 X)))).
Qed.
Lemma isassoc_NnMmin {X : NonnegativeMonoid} :
  isassoc (NnMmin (X := X)).
Proof.
  intros X.
  apply (isassoc_Lmin (L := _,,(pr1 (pr2 X)))).
Qed.

Lemma iscomm_NnMmax {X : NonnegativeMonoid} :
  iscomm (NnMmax (X := X)).
Proof.
  intros X.
  apply (iscomm_Lmax (L := _,,(pr1 (pr2 X)))).
Qed.
Lemma isassoc_NnMmax {X : NonnegativeMonoid} :
  isassoc (NnMmax (X := X)).
Proof.
  intros X.
  apply (isassoc_Lmax (L := _,,(pr1 (pr2 X)))).
Qed.

Lemma NnMmin_eq_l {X : NonnegativeMonoid} :
  ∀ (x y : X), x <= y → NnMmin x y = x.
Proof.
  intros X.
  apply (Lmin_eq_l (L := _,,(pr1 (pr2 X)))).
Qed.
Lemma NnMmin_eq_r {X : NonnegativeMonoid} :
  ∀ (x y : X), y <= x → NnMmin x y = y.
Proof.
  intros X.
  apply (Lmin_eq_r (L := _,,(pr1 (pr2 X)))).
Qed.
Lemma NnMmax_eq_l {X : NonnegativeMonoid} :
  ∀ (x y : X), y <= x → NnMmax x y = x.
Proof.
  intros X.
  apply (Lmax_eq_l (L := _,,(pr1 (pr2 X)))).
Qed.
Lemma NnMmax_eq_r {X : NonnegativeMonoid} :
  ∀ (x y : X), x <= y → NnMmax x y = y.
Proof.
  intros X.
  apply (Lmax_eq_r (L := _,,(pr1 (pr2 X)))).
Qed.

Lemma NnMminus_lt_pos {X : NonnegativeMonoid} :
  ∀ x y : X, y < x -> 0 < NnMminus x y.
Proof.
  intros X.
  eapply minus_lt_pos.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))).
  exact (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))).
Qed.

Lemma NnMminus_plus {X : NonnegativeMonoid} :
  ∀ x y : X, (NnMminus x y) + y = NnMmax x y.
Proof.
  intros X x y.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))).
Qed.

Lemma NnMhalf_carac {X : NonnegativeMonoid} :
  ∀ x : X, NnMhalf x + NnMhalf x <= x.
Proof.
  intros X x.
  exact (pr1 (pr2 ((pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))))) x))).
Qed.
Lemma NnMhalf_pos {X : NonnegativeMonoid} :
  ∀ x : X, 0 < x -> 0 < NnMhalf x.
Proof.
  intros X x.
  exact (pr2 (pr2 ((pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))))) x))).
Qed.

(** ** Definition of metric spaces *)

Section MetricSet.

Context {NR : NonnegativeMonoid}.
Context {X : tightapSet}.
Context (dist : X -> X -> NR).

Definition issymm_isdist : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ x y : X, dist x y = dist y x).
  apply impred_isaprop ; intro x.
  apply impred_isaprop ; intro y.
  apply (pr2 (pr1 (pr1 (pr1 NR)))).
Defined.

Definition issepp_isdist : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ x y : X, (x ≠ y)%tap <-> (0%addmonoid < (dist x y))).
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply isapropdirprod.
  apply isapropimpl.
  apply propproperty.
  apply isapropimpl.
  apply propproperty.
Defined.

Definition istriangle_isdist : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ x y z : X,  (dist x z) <= (dist x y + dist y z)%addmonoid).
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply impred_isaprop ; intros z.
  apply propproperty.
Defined.

End MetricSet.

Definition isdist {NR : NonnegativeMonoid} {X : tightapSet} (dist : X -> X -> NR) : hProp :=
  issymm_isdist dist ∧ issepp_isdist dist ∧ istriangle_isdist dist.

Definition MetricSet (NR : NonnegativeMonoid) :=
  Σ (X : tightapSet) (dist : X -> X -> NR), isdist dist.

Definition pr1MetricSet {NR : NonnegativeMonoid} : MetricSet NR -> tightapSet := pr1.
Coercion pr1MetricSet : MetricSet >-> tightapSet.

Definition dist {NR : NonnegativeMonoid} {X : MetricSet NR} : (X -> X -> NR) := pr1 (pr2 X).

Lemma issymm_dist {NR : NonnegativeMonoid} {X : MetricSet NR} :
  ∀ x y : X, dist x y = dist y x.
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 X))).
Qed.
Lemma issepp_dist {NR : NonnegativeMonoid} {X : MetricSet NR} :
  ∀ x y : X, (x ≠ y)%tap <-> (0 < (dist x y)).
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 (pr2 X)))).
Qed.
Lemma istriangle_dist {NR : NonnegativeMonoid} {X : MetricSet NR} :
  ∀ x y z : X, (dist x z) <= (dist x y + dist y z).
Proof.
  intros.
  now apply (pr2 (pr2 (pr2 (pr2 X)))).
Qed.

Lemma dist_0 {NR : NonnegativeMonoid} {X : MetricSet NR} :
  ∀ x : X, dist x x = 0.
Proof.
  intros.
  apply istight_NnMap.
  intro H.
  apply NnMap_lt_0, (pr2 (issepp_dist _ _)) in H.
  revert H.
  apply isirrefltightapSet.
Qed.

(** ** Topology on metric spaces *)

Section Balls.

Context {NR : NonnegativeMonoid}.
Context {M : MetricSet NR}.

Definition ball (x : M) (eps : NR) (y : M) : hProp :=
  (dist x y < eps).

Lemma ball_center :
  ∀ (x : M) (eps : NR), 0 < eps -> ball x eps x.
Proof.
  intros x eps He.
  unfold ball.
  now rewrite dist_0.
Qed.
Lemma ball_le :
  ∀ x e e' y, e <= e' -> ball x e y -> ball x e' y.
Proof.
  intros x e e' y H H'.
  refine (istrans_NnMlt_le _ _ _ _ _).
  apply H'.
  apply H.
Qed.
Lemma ball_recenter :
  ∀ (x y : M) (eps : NR), ball y eps x -> Σ eps' : NR, 0 < eps' × ∀ z : M, ball x eps' z -> ball y eps z.
Proof.
  intros x y eps Hy.
  exists (NnMminus eps (dist y x)).
  split.
  apply NnMminus_lt_pos, Hy.
  intros z Hz.
  unfold ball.
  eapply istrans_NnMle_lt, istrans_NnMlt_le.
  rewrite issymm_dist.
  eapply istriangle_dist.
  apply NnMplus_lt_r.
  rewrite issymm_dist.
  apply Hz.
  rewrite issymm_dist.
  rewrite NnMminus_plus.
  rewrite NnMmax_eq_l.
  apply isrefl_Lle.
  rewrite issymm_dist.
  apply NnMlt_le, Hy.
Qed.

Lemma ball_symm :
  ∀ (x y : M) (eps : NR), ball x eps y -> ball y eps x.
Proof.
  intros x y eps.
  unfold ball.
  now rewrite issymm_dist.
Qed.

Definition metricUniformStructure : UniformStructure M.
Proof.
  simple refine (mkUniformStructure _ _ _ _ _ _ _).
  - intros A.
    apply (∃ e : NR, 0 < e × ∀ x y : M, ball x e y -> A (x,,y)).
  - intros A B H.
    apply hinhfun.
    intros (e,(He,Ha)).
    exists e ; split.
    exact He.
    intros x y Hxy.
    now apply H, Ha.
  - generalize (NnM_nottrivial NR).
    apply hinhfun.
    intros (e,He).
    now exists e.
  - intros A B.
    apply hinhfun2.
    intros (ea,(Hea,Ha)) (eb,(Heb,Hb)).
    exists (NnMmin ea eb).
    split.
    now apply NnMmin_gt.
    intros x y He.
    split.
    apply Ha.
    eapply istrans_NnMlt_le, NnMmin_le_l.
    exact He.
    apply Hb.
    eapply istrans_NnMlt_le, NnMmin_le_r.
    exact He.
  - intros A Ha x.
    revert Ha.
    apply hinhuniv.
    intros (e,(He,Ha)).
    apply Ha.
    now apply ball_center.
  - intros A.
    apply hinhfun.
    intros (e,(He,Ha)).
    exists e ; split.
    exact He.
    intros x y H.
    apply Ha.
    now apply ball_symm.
  - intros A.
    apply hinhfun.
    intros (e,(He,Ha)).
    mkpair.
    intros x.
    apply (ball (pr1 x) (NnMhalf e) (pr2 x)).
    split.
    apply hinhpr.
    exists (NnMhalf e).
    split.
    apply NnMhalf_pos, He.
    easy.
    intros (x,y).
    apply hinhuniv.
    intros (z,(Hxz,Hzy)).
    apply Ha.
    eapply istrans_NnMle_lt, istrans_NnMlt_le.
    eapply istriangle_dist.
    eapply istrans_NnMlt.
    apply NnMplus_lt_l.
    apply Hzy.
    apply NnMplus_lt_r.
    apply Hxz.
    apply NnMhalf_carac.
Defined.

Definition metric_topology : TopologicalSet.
Proof.
  refine (Topology_UniformSpace _).
  apply metricUniformStructure.
Defined.

Lemma isOpen_ball :
  ∀ (x : M) (eps : Σ e : NR, 0 < e),
    isOpen (T := metric_topology) (ball x (pr1 eps)).
Proof.
  intros x (e,He).
  apply neighborhood_isOpen.
  intros y Hy.
  apply TopologyFromNeighborhood_correct.
  apply hinhpr.
  apply ball_recenter in Hy.
  exists (λ z : M × M, ball (pr1 z) (pr1 Hy) (pr2 z)).
  split.
  apply hinhpr.
  exists (pr1 Hy).
  split.
  apply (pr1 (pr2 Hy)).
  easy.
  apply (pr2 (pr2 Hy)).
Qed.

End Balls.

(** ** Limits in a Metric Space *)

Definition locally {NR : NonnegativeMonoid} {M : MetricSet NR} (x : M) : Filter M :=
  locally (T := metric_topology) x.

Lemma locally_ball {NR : NonnegativeMonoid} {M : MetricSet NR} (x : M) :
  ∀ e : NR, 0 < e -> locally x (ball x e).
Proof.
  intros NR M x e He.
  apply (pr2 (neighborhood_isOpen _)).
  simple refine (isOpen_ball _ (_,,_)).
  exact He.
  now apply ball_center.
Qed.

(** *** Limit of a filter *)

Definition is_filter_lim {NR : NonnegativeMonoid} {M : MetricSet NR} (F : Filter M) (x : M) :=
  is_filter_lim (T := metric_topology) F x.
Definition ex_filter_lim {NR : NonnegativeMonoid} {M : MetricSet NR} (F : Filter M) :=
  ∃ (x : M), is_filter_lim F x.

(** *** Limit of a function *)

Definition is_lim {X : UU} {NR : NonnegativeMonoid} {M : MetricSet NR} (f : X -> M) (F : Filter X) (x : M) :=
  is_lim (T := metric_topology) f F x.
Definition ex_lim {X : UU} {NR : NonnegativeMonoid} {M : MetricSet NR} (f : X -> M) (F : Filter X) :=
  ∃ (x : M), is_lim f F x.

Lemma is_lim_aux {X : UU} {NR : NonnegativeMonoid} {M : MetricSet NR} (f : X -> M) (F : Filter X) (x : M) :
  is_lim f F x <->
  (∀ eps : (Σ e : NR, 0 < e), F (λ y, ball x (pr1 eps) (f y))).
Proof.
  intros X NR M f F x.
  split.
  - intros H e.
    eapply filter_imply.
    2: apply H.
    intros y Hy.
    apply Hy.
    apply locally_ball.
    now apply (pr2 e).
  - intros H P.
    apply hinhuniv.
    intros ((O,Hopen),(Ho,Ho')).
    simpl in Ho, Ho'.
    generalize (Hopen x Ho) ; clear Hopen.
    apply hinhuniv.
    intros (U,(Hu,Hu')).
    revert Hu.
    apply hinhuniv.
    intros (e,(He,He')).
    generalize (H (e,,He)).
    apply (filter_imply F).
    intros y Hy.
    apply Ho', Hu', He'.
    apply Hy.
Qed.

(** *** Continuity *)

Definition continuous_at {NR : NonnegativeMonoid} {U V : MetricSet NR} (f : U -> V) (x : U) :=
  continuous_at (U := metric_topology) (V := metric_topology) f x.

Definition continuous_on {NR : NonnegativeMonoid} {U V : MetricSet NR} (dom : U -> hProp) (f : U -> V) :=
  ∀ (x : U) (Hx : dom x) H,
    is_lim f (FilterDom (locally x) dom H) (f x).
Definition continuous_subtypes {NR : NonnegativeMonoid} {U V : MetricSet NR} (dom : U -> hProp) (f : (Σ x : U, dom x) -> V) :=
  ∀ (x : Σ x : U, dom x) H,
    is_lim f (FilterSubtype (locally (pr1 x)) dom H) (f x).
Definition continuous {NR : NonnegativeMonoid} {U V : MetricSet NR} (f : U -> V) :=
  ∀ x : U, continuous_at f x.

(** *** Continuity for 2 variable functions *)

Definition continuous2d_at {NR : NonnegativeMonoid} {U V W : MetricSet NR} (f : U -> V -> W) (x : U) (y : V) :=
  continuous2d_at (U := metric_topology) (V := metric_topology) (W := metric_topology) f x y.

Definition continuous2d {NR : NonnegativeMonoid} {U V W : MetricSet NR} (f : U -> V -> W) :=
  ∀ (x : U) (y : V), continuous2d_at f x y.
