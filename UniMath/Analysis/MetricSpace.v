(** * Results about Metric Spaces *)
(** Author: Catherine LELAY. Jan 2016 - *)

Require Import UniMath.Topology.Prelim.
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
    × (Π x y : X, min x (max x y) = x)
    × (Π x y : X, max x (min x y) = x).
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
    × (Π x y : L, Lmin x (Lmax x y) = x)
    × (Π x y : L, Lmax x (Lmin x y) = x).
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
  Π x y : L, Lmin x (Lmax x y) = x.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 pr2lattice))))).
Qed.
Lemma Lmax_absorb :
  Π x y : L, Lmax x (Lmin x y) = x.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 pr2lattice))))).
Qed.

Lemma Lmin_id :
  Π x : L, Lmin x x = x.
Proof.
  intros x.
  pattern x at 2 ; rewrite <- (Lmax_absorb x x).
  apply Lmin_absorb.
Qed.
Lemma Lmax_id :
  Π x : L, Lmax x x = x.
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
  Π x y : L, Lle (Lmin x y) x.
Proof.
  intros x y.
  simpl.
  rewrite iscomm_Lmin, <- isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma Lmin_le_r :
  Π x y : L, Lle (Lmin x y) y.
Proof.
  intros x y.
  rewrite iscomm_Lmin.
  apply Lmin_le_l.
Qed.
Lemma Lmax_le_l :
  Π x y : L, Lle x (Lmax x y).
Proof.
  intros x y.
  simpl.
  apply Lmin_absorb.
Qed.
Lemma Lmax_le_r :
  Π x y : L, Lle y (Lmax x y).
Proof.
  intros x y.
  rewrite iscomm_Lmax.
  apply Lmax_le_l.
Qed.

Lemma Lmin_eq_l :
  Π x y : L, Lle x y -> Lmin x y = x.
Proof.
  intros x y H.
  apply H.
Qed.
Lemma Lmin_eq_r :
  Π x y : L, Lle y x -> Lmin x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmin.
  apply H.
Qed.

Lemma Lmax_eq_l :
  Π x y : L, Lle y x -> Lmax x y = x.
Proof.
  intros x y <-.
  rewrite iscomm_Lmin.
  apply Lmax_absorb.
Qed.
Lemma Lmax_eq_r :
  Π x y : L, Lle x y -> Lmax x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmax.
  now apply Lmax_eq_l.
Qed.

End lattice_pty.

Definition islatticelt (L : lattice) (lt : StrongOrder L) :=
  (Π x y : L, (¬ (lt x y)) <-> Lle y x)
    × (Π x y z : L, lt z x -> lt z y -> lt z (Lmin x y))
    × (Π x y z : L, lt x z -> lt y z -> lt (Lmax x y) z).

Lemma notlt_Lle (L : lattice) (lt : StrongOrder L) (Hlt : islatticelt L lt) :
  Π x y : L, (¬ (lt x y)) <-> Lle y x.
Proof.
  intros L lt Hlt.
  apply (pr1 Hlt).
Qed.
Lemma lt_Lle (L : lattice) (lt : StrongOrder L) (Hlt : islatticelt L lt) :
  Π x y : L, lt x y -> Lle x y.
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
  Π x y z : L, lt z x -> lt z y -> lt z (Lmin x y).
Proof.
  intros L lt Hlt.
  apply (pr1 (pr2 Hlt)).
Qed.
Lemma Lmax_lt (L : lattice) (lt : StrongOrder L) (Hlt : islatticelt L lt) :
  Π x y z : L, lt x z -> lt y z -> lt (Lmax x y) z.
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
    + intros x H ; revert H ; apply sumofmaps ;
      apply isirrefl_StrongOrder.
    + intros x y ; apply sumofmaps ; [intros Hxy | intros Hyx].
      now right.
      now left.
    + intros x y z ; apply sumofmaps ; intros H ;
      generalize (iscotrans_StrongOrder lt _ y _ H) ;
      apply hinhfun ; apply sumofmaps ;
      intros H'.
      now left ; left.
      now right ; left.
      now right ; right.
      now left ; right.
Defined.
Definition tightapfromlt {X : hSet} (lt : StrongOrder X) (le : hrel X)
           (Hnltle : Π x y, (¬ lt x y) <-> le y x) (Hle : isantisymm le) : tightap X.
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
  (Π x y : X, minus x y + y = Lmax (L := _,,is) x y).

Lemma minus_pos_lt {X : monoid} {is : islattice X}
      (lt : StrongOrder X) (is_lt : islatticelt (_,,is) lt) (is_lt' : isbinophrel lt)
      (minus : binop X) (is0 : is_minus is minus):
  Π x y : X, lt 0 (minus x y) -> lt y x.
Proof.
  intros X is lt is_lt is_lt' minus is0 x y H0.
  apply (pr2 is_lt' _ _ y) in H0.
  rewrite lunax, is0 in H0.
  rewrite <- (Lmax_eq_l (L := _,,is) x y).
  exact H0.
  apply (notlt_Lle _ _ is_lt).
  intros H ; revert H0.
  apply (pr2 (notlt_Lle _ _ is_lt _ _)).
  rewrite Lmax_eq_r.
  apply isrefl_Lle.
  now apply lt_Lle with (2 := H).
Qed.
Lemma minus_lt_pos {X : monoid} {is : islattice X}
      (lt : StrongOrder X) (is_lt : islatticelt (_,,is) lt) (is_lt' : isinvbinophrel lt)
      (minus : binop X) (is0 : is_minus is minus):
  Π x y : X, lt y x -> lt 0 (minus x y).
Proof.
  intros X is lt is_lt is_lt' minus is0 x y H0.
  apply (pr2 is_lt' _ _ y).
  rewrite lunax, is0.
  rewrite (Lmax_eq_l (L := _,,is) x y).
  exact H0.
  now apply lt_Lle with (2 := H0).
Qed.

Definition ex_minus {X : monoid} (is : islattice X) := Σ minus : binop X, is_minus is minus.

Definition isNonnegativeMonoid {X : monoid} (is : islattice X) (lt : StrongOrder X) :=
  (ex_minus is)
    × (islatticelt (_,,is) lt)
    × isbinophrel lt
    × isinvbinophrel lt
    × (Π x : X, Lle (L := _,,is) 0 x)
    × (∃ x0, lt 0 x0)
    × (Π x : X, Σ y : X, (Lle (L := _,,is) (y + y) x) × (lt 0 x -> lt 0 y)).

Definition NonnegativeMonoid :=
  Σ (X : monoid) (is : islattice X) (lt : StrongOrder X), isNonnegativeMonoid is lt.

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
  - apply (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
  - now apply (isantisymm_Lle (L := _ ,, pr1 (pr2 X))).
Defined.
Definition NnMmin {X : NonnegativeMonoid} : binop X :=
  Lmin (L := _,,(pr1 (pr2 X))).
Definition NnMmax {X : NonnegativeMonoid} : binop X :=
  Lmax (L := _,,(pr1 (pr2 X))).
Definition NnMminus {X : NonnegativeMonoid} : binop X :=
  (pr1 (pr1 (pr2 (pr2 (pr2 X))))).
Definition NnMhalf {X : NonnegativeMonoid} : unop X :=
  λ x : X, (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))) x)).

Local Notation "0" := (0%addmonoid).
Local Notation "x + y" := ((x + y)%addmonoid).
Local Notation "x - y" := (NnMminus x y).
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
  Π x y : X, x ≠ y <-> (x < y) ⨿ (y < x).
Proof.
  intros X.
  easy.
Qed.

Lemma notNnMlt_le {X : NonnegativeMonoid} :
  Π x y : X, (¬ (x < y)) <-> (y <= x).
Proof.
  intros X.
  now apply (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
Qed.
Lemma isirrefl_NnMlt {X : NonnegativeMonoid} :
  Π x : X, ¬ (x < x).
Proof.
  intros X.
  apply isirrefl_StrongOrder.
Qed.
Lemma istrans_NnMlt {X : NonnegativeMonoid} :
  Π x y z : X, x < y -> y < z -> x < z.
Proof.
  intros X.
  apply istrans_StrongOrder.
Qed.
Lemma iscotrans_NnMlt {X : NonnegativeMonoid} :
  Π x y z : X, x < z -> x < y ∨ y < z.
Proof.
  intros X.
  apply iscotrans_StrongOrder.
Qed.

Lemma NnMlt_le {X : NonnegativeMonoid} :
  Π x y : X, x < y -> x <= y.
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
  Π x y z : X, x < y -> y <= z -> x < z.
Proof.
  intros X.
  intros x y z Hxy Hyz.
  generalize (iscotrans_NnMlt x z y Hxy).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  exact H.
  now apply (pr2 (notNnMlt_le _ _)) in Hyz.
Qed.

Lemma istrans_NnMle_lt {X : NonnegativeMonoid} :
  Π x y z : X, x <= y -> y < z -> x < z.
Proof.
  intros X.
  intros x y z Hxy Hyz.
  generalize (iscotrans_NnMlt y x z Hyz).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  now apply (pr2 (notNnMlt_le _ _)) in Hxy.
  exact H.
Qed.

Lemma isnonnegative_NnM {X : NonnegativeMonoid} :
  Π x : X, 0 <= x.
Proof.
  intros X.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))).
Qed.
Lemma isnonnegative_NnM' {X : NonnegativeMonoid} :
  Π x : X, ¬ (x < 0).
Proof.
  intros X x.
  apply (pr2 (notNnMlt_le _ _)).
  now apply isnonnegative_NnM.
Qed.

Lemma NnMplus_lt_l {X : NonnegativeMonoid} :
  Π k x y : X, x < y -> k + x < k + y.
Proof.
  intros X k x y.
  apply (pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.
Lemma NnMplus_lt_r {X : NonnegativeMonoid} :
  Π k x y : X, x < y -> x + k < y + k.
Proof.
  intros X k x y.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.

Lemma NnMap_lt_0 {X : NonnegativeMonoid} :
  Π x : X, x ≠ 0 -> 0 < x.
Proof.
  intros X x Hx.
  apply istotal_NnMlt in Hx.
  induction Hx as [Hx | Hx].
  apply fromempty.
  revert Hx.
  now apply isnonnegative_NnM'.
  exact Hx.
Qed.
Lemma NnMlt_ap {X : NonnegativeMonoid} :
  Π x y : X, x < y -> x ≠ y.
Proof.
  intros X x y H.
  apply (pr2 (istotal_NnMlt _ _)).
  now left.
Qed.

Lemma NnM_nottrivial (X : NonnegativeMonoid) :
  ∃ x0 : X, 0 < x0.
Proof.
  intros X.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))))).
Qed.

Lemma NnMmin_le_l {X : NonnegativeMonoid} :
  Π x y : X, NnMmin x y <= x.
Proof.
  intros X.
  apply (Lmin_le_l (L := _,,(pr1 (pr2 X)))).
Qed.
Lemma NnMmin_le_r {X : NonnegativeMonoid} :
  Π x y : X, NnMmin x y <= y.
Proof.
  intros X.
  apply (Lmin_le_r (L := _,,(pr1 (pr2 X)))).
Qed.
Lemma NnMmin_gt {X : NonnegativeMonoid} :
  Π x y z : X, z < x -> z < y -> z < NnMmin x y.
Proof.
  intros X.
  apply (Lmin_lt (_,,(pr1 (pr2 X)))).
  apply (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
Qed.

Lemma NnMmax_le_l {X : NonnegativeMonoid} :
  Π x y : X, x <= NnMmax x y.
Proof.
  intros X.
  apply (Lmax_le_l (L := _,,(pr1 (pr2 X)))).
Qed.
Lemma NnMmax_le_r {X : NonnegativeMonoid} :
  Π x y : X, y <= NnMmax x y.
Proof.
  intros X.
  apply (Lmax_le_r (L := _,,(pr1 (pr2 X)))).
Qed.
Lemma NnMmax_gt {X : NonnegativeMonoid} :
  Π x y z : X, x < z -> y < z -> NnMmax x y < z.
Proof.
  intros X.
  apply (Lmax_lt (_,,(pr1 (pr2 X)))).
  apply (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
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
  Π (x y : X), x <= y → NnMmin x y = x.
Proof.
  intros X.
  apply (Lmin_eq_l (L := _,,(pr1 (pr2 X)))).
Qed.
Lemma NnMmin_eq_r {X : NonnegativeMonoid} :
  Π (x y : X), y <= x → NnMmin x y = y.
Proof.
  intros X.
  apply (Lmin_eq_r (L := _,,(pr1 (pr2 X)))).
Qed.
Lemma NnMmax_eq_l {X : NonnegativeMonoid} :
  Π (x y : X), y <= x → NnMmax x y = x.
Proof.
  intros X.
  apply (Lmax_eq_l (L := _,,(pr1 (pr2 X)))).
Qed.
Lemma NnMmax_eq_r {X : NonnegativeMonoid} :
  Π (x y : X), x <= y → NnMmax x y = y.
Proof.
  intros X.
  apply (Lmax_eq_r (L := _,,(pr1 (pr2 X)))).
Qed.

Lemma NnMminus_lt_pos {X : NonnegativeMonoid} :
  Π x y : X, y < x -> 0 < NnMminus x y.
Proof.
  intros X.
  eapply minus_lt_pos.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
  exact (pr2 (pr1 (pr2 (pr2 (pr2 X))))).
Qed.

Lemma NnMminus_plus {X : NonnegativeMonoid} :
  Π x y : X, (NnMminus x y) + y = NnMmax x y.
Proof.
  intros X x y.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 X))))).
Qed.

Lemma NnMhalf_carac {X : NonnegativeMonoid} :
  Π x : X, NnMhalf x + NnMhalf x <= x.
Proof.
  intros X x.
  exact (pr1 (pr2 ((pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))))) x))).
Qed.
Lemma NnMhalf_pos {X : NonnegativeMonoid} :
  Π x : X, 0 < x -> 0 < NnMhalf x.
Proof.
  intros X x.
  exact (pr2 (pr2 ((pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))))) x))).
Qed.

(** ** Definition of metric spaces *)

Section MetricSet.

Context {NR : NonnegativeMonoid}.
Context {X : tightapSet}.
Context (dist : X -> X -> NR).

Definition issymm_isdist : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (Π x y : X, dist x y = dist y x).
  apply impred_isaprop ; intro x.
  apply impred_isaprop ; intro y.
  apply (pr2 (pr1 (pr1 (pr1 NR)))).
Defined.

Definition issepp_isdist : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (Π x y : X, (x ≠ y)%tap <-> (0%addmonoid < (dist x y))).
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
  apply (Π x y z : X,  (dist x z) <= (dist x y + dist y z)%addmonoid).
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
  Π x y : X, dist x y = dist y x.
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 X))).
Qed.
Lemma issepp_dist {NR : NonnegativeMonoid} {X : MetricSet NR} :
  Π x y : X, (x ≠ y)%tap <-> (0 < (dist x y)).
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 (pr2 X)))).
Qed.
Lemma istriangle_dist {NR : NonnegativeMonoid} {X : MetricSet NR} :
  Π x y z : X, (dist x z) <= (dist x y + dist y z).
Proof.
  intros.
  now apply (pr2 (pr2 (pr2 (pr2 X)))).
Qed.

Lemma dist_0 {NR : NonnegativeMonoid} {X : MetricSet NR} :
  Π x : X, dist x x = 0.
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
  Π (x : M) (eps : NR), 0 < eps -> ball x eps x.
Proof.
  intros x eps He.
  unfold ball.
  now rewrite dist_0.
Qed.
Lemma ball_le :
  Π x e e' y, e <= e' -> ball x e y -> ball x e' y.
Proof.
  intros x e e' y H H'.
  refine (istrans_NnMlt_le _ _ _ _ _).
  apply H'.
  apply H.
Qed.
Lemma ball_recenter :
  Π (x y : M) (eps : NR), ball y eps x -> Σ eps' : NR, 0 < eps' × Π z : M, ball x eps' z -> ball y eps z.
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
  Π (x y : M) (eps : NR), ball x eps y -> ball y eps x.
Proof.
  intros x y eps.
  unfold ball.
  now rewrite issymm_dist.
Qed.

Definition metricUniformStructure : UniformStructure M.
Proof.
  simple refine (mkUniformStructure _ _ _ _ _ _ _).
  - intros A.
    apply (∃ e : NR, 0 < e × Π x y : M, ball x e y -> A (x,,y)).
  - intros A B H.
    apply hinhfun.
    intros e.
    exists (pr1 e) ; split.
    exact (pr1 (pr2 e)).
    intros x y Hxy.
    now apply H, (pr2 (pr2 e)).
  - generalize (NnM_nottrivial NR).
    apply hinhfun.
    intros e.
    now exists (pr1 e), (pr2 e).
  - intros A B.
    apply hinhfun2.
    intros ea eb.
    exists (NnMmin (pr1 ea) (pr1 eb)).
    split.
    apply NnMmin_gt.
    exact (pr1 (pr2 ea)).
    exact (pr1 (pr2 eb)).
    intros x y He.
    split.
    apply (pr2 (pr2 ea)).
    eapply istrans_NnMlt_le, NnMmin_le_l.
    exact He.
    apply (pr2 (pr2 eb)).
    eapply istrans_NnMlt_le, NnMmin_le_r.
    exact He.
  - intros A Ha x.
    revert Ha.
    apply hinhuniv.
    intros e.
    apply (pr2 (pr2 e)).
    apply ball_center.
    exact (pr1 (pr2 e)).
  - intros A.
    apply hinhfun.
    intros e.
    exists (pr1 e) ; split.
    exact (pr1 (pr2 e)).
    intros x y H.
    apply (pr2 (pr2 e)).
    now apply ball_symm.
  - intros A.
    apply hinhfun.
    intros e.
    mkpair.
    intros x.
    apply (ball (pr1 x) (NnMhalf (pr1 e)) (pr2 x)).
    split.
    apply hinhpr.
    exists (NnMhalf (pr1 e)).
    split.
    apply NnMhalf_pos, (pr1 (pr2 e)).
    easy.
    intros xy.
    apply hinhuniv.
    intros z.
    rewrite (tppr xy) ; apply (pr2 (pr2 e)).
    eapply istrans_NnMle_lt, istrans_NnMlt_le.
    eapply istriangle_dist.
    eapply istrans_NnMlt.
    apply NnMplus_lt_l.
    apply (pr2 (pr2 z)).
    apply NnMplus_lt_r.
    apply (pr1 (pr2 z)).
    apply NnMhalf_carac.
Defined.

End Balls.

(** ** Limits in a Metric Space *)

Section MSlocally.

Context {NR : NonnegativeMonoid} {M : MetricSet NR}.

Definition MSneighborhood (x : M) (A : M -> hProp) :=
  ∃ e : NR, 0 < e × Π y, ball x e y -> A y.

Lemma MSneighborhood_equiv :
  Π x A, USneighborhood metricUniformStructure x A <-> MSneighborhood x A.
Proof.
  split.
  - apply hinhuniv ; intros U.
    generalize (pr1 (pr2 U)).
    apply hinhfun.
    intros e.
    exists (pr1 e) ; split.
    exact (pr1 (pr2 e)).
    intros y Hy.
    apply (pr2 (pr2 U)), (pr2 (pr2 e)), Hy.
  - apply hinhfun.
    intros e.
    exists (λ z, ball (pr1 z) (pr1 e) (pr2 z)).
    split.
    apply hinhpr.
    now exists (pr1 e), (pr1 (pr2 e)).
    apply (pr2 (pr2 e)).
Qed.

Lemma MSneighborhood_imply :
  Π x : M, isfilter_imply (MSneighborhood x).
Proof.
  intros x A B H Ha.
  apply MSneighborhood_equiv.
  apply USneighborhood_imply with (1 := H).
  apply_pr2 MSneighborhood_equiv.
  exact Ha.
Qed.

Lemma MSneighborhood_htrue :
  Π x : M, isfilter_htrue (MSneighborhood x).
Proof.
  intros x.
  apply MSneighborhood_equiv.
  apply USneighborhood_htrue.
Qed.
Lemma MSneighborhood_and :
  Π x : M, isfilter_and (MSneighborhood x).
Proof.
  intros x A B Ha Hb.
  apply MSneighborhood_equiv.
  apply USneighborhood_and.
  apply_pr2 MSneighborhood_equiv.
  exact Ha.
  apply_pr2 MSneighborhood_equiv.
  exact Hb.
Qed.
Lemma MSneighborhood_point :
  Π (x : M) (P : M → hProp), MSneighborhood x P → P x.
Proof.
  intros x P Hp.
  simple refine (USneighborhood_point _ _ _ _).
  apply metricUniformStructure.
  apply_pr2 MSneighborhood_equiv.
  exact Hp.
Qed.
Lemma MSneighborhood_neighborhood :
  Π (x : M) (P : M → hProp),
    MSneighborhood x P
    → ∃ Q : M → hProp, MSneighborhood x Q × (Π y : M, Q y → MSneighborhood y P).
Proof.
  intros x P Hp.
  apply_pr2_in MSneighborhood_equiv Hp.
  generalize (USneighborhood_neighborhood _ _ _ Hp).
  apply hinhfun.
  intros Q.
  exists (pr1 Q).
  split.
  apply MSneighborhood_equiv.
  exact (pr1 (pr2 Q)).
  intros y Hy.
  apply MSneighborhood_equiv.
  apply (pr2 (pr2 Q)), Hy.
Qed.

Lemma isNeighborhood_MSneighborhood :
  isNeighborhood MSneighborhood.
Proof.
  repeat split.
  - exact MSneighborhood_imply.
  - exact MSneighborhood_htrue.
  - exact MSneighborhood_and.
  - exact MSneighborhood_point.
  - exact MSneighborhood_neighborhood.
Qed.

End MSlocally.

Definition MSlocally {NR : NonnegativeMonoid} {M : MetricSet NR} (x : M) : Filter M.
Proof.
  intros NR M x.
  exists (MSneighborhood x).
  revert x.
  apply isNeighborhood_isFilter.
  apply isNeighborhood_MSneighborhood.
Defined.

Lemma MSlocally_ball {NR : NonnegativeMonoid} {M : MetricSet NR} (x : M) :
  Π e : NR, 0 < e -> MSlocally x (ball x e).
Proof.
  intros NR M x e He.
  apply hinhpr.
  now exists e.
Qed.

Definition MSlocally2d {NR : NonnegativeMonoid} {X Y : MetricSet NR} (x : X) (y : Y) :=
  FilterDirprod (MSlocally x) (MSlocally y).

(** *** Limit of a filter *)

Definition is_filter_MSlim {NR : NonnegativeMonoid} {M : MetricSet NR} (F : Filter M) (x : M) :=
  filter_le F (MSlocally x).
Definition ex_filter_MSlim {NR : NonnegativeMonoid} {M : MetricSet NR} (F : Filter M) :=
  ∃ (x : M), is_filter_MSlim F x.

(** *** Limit of a function *)

Definition is_MSlim {X : UU} {NR : NonnegativeMonoid} {M : MetricSet NR} (f : X -> M) (F : Filter X) (x : M) :=
  filterlim f F (MSlocally x).
Definition ex_MSlim {X : UU} {NR : NonnegativeMonoid} {M : MetricSet NR} (f : X -> M) (F : Filter X) :=
  ∃ (x : M), is_MSlim f F x.

Lemma is_MSlim_correct :
  Π {X : UU} {NR : NonnegativeMonoid} {M : MetricSet NR} (f : X -> M) (F : Filter X) (x : M),
    is_USlim (Y := _ ,, metricUniformStructure (M := M)) f F x <-> is_MSlim f F x.
Proof.
  split ; intros H P Hp.
  - apply H ; revert Hp.
    refine (pr2 (MSneighborhood_equiv _ _)).
  - apply H ; revert Hp.
    refine (pr1 (MSneighborhood_equiv _ _)).
Qed.

Lemma is_MSlim_aux {X : UU} {NR : NonnegativeMonoid} {M : MetricSet NR} (f : X -> M) (F : Filter X) (x : M) :
  is_MSlim f F x <->
  (Π eps : NR, 0 < eps -> F (λ y, ball x eps (f y))).
Proof.
  intros X NR M f F x.
  split.
  - intros H e He.
    apply H.
    apply MSlocally_ball, He.
  - intros H P.
    apply hinhuniv.
    intros e.
    eapply (filter_imply F).
    intros y Hy.
    apply (pr2 (pr2 e)).
    apply Hy.
    apply H, (pr1 (pr2 e)).
Qed.

(** *** Continuity *)

Definition MScontinuous_at {NR : NonnegativeMonoid} {U V : MetricSet NR} (f : U -> V) (x : U) :=
  is_MSlim f (MSlocally x) (f x).
Definition MScontinuous_on {NR : NonnegativeMonoid} {U V : MetricSet NR} (dom : U -> hProp) (f : Π (x : U), dom x -> V) :=
  Π (x : U) (Hx : dom x),
  ∃ H,
  is_MSlim (λ y, f (pr1 y) (pr2 y))
  (FilterSubtype (MSlocally x) dom H) (f x Hx).
Definition MScontinuous {NR : NonnegativeMonoid} {U V : MetricSet NR} (f : U -> V) :=
  Π x : U, MScontinuous_at f x.

(** *** Continuity for 2 variable functions *)

Definition MScontinuous2d_at {NR : NonnegativeMonoid} {U V W : MetricSet NR} (f : U -> V -> W) (x : U) (y : V) :=
  is_MSlim (λ z : U × V, f (pr1 z) (pr2 z)) (MSlocally2d x y) (f x y).
Definition MScontinuous2d_on {NR : NonnegativeMonoid} {U V W : MetricSet NR} (dom : U → V -> hProp) (f : Π x y, dom x y -> V) :=
  Π x y (Hxy : dom x y),
  ∃ H,
    is_MSlim
      (λ y0,
       f (pr1 (pr1 y0)) (pr2 (pr1 y0)) (pr2 y0))
      (FilterSubtype (MSlocally2d x y) (λ z, dom (pr1 z) (pr2 z)) H)
      (f x y Hxy).
Definition MScontinuous2d {NR : NonnegativeMonoid} {U V W : MetricSet NR} (f : U -> V -> W) :=
  Π x y, MScontinuous2d_at f x y.

(** * NonnegativeMonoid is a MetricSet *)

Definition NnMtoMS (NR : NonnegativeMonoid)
           (is : Π x y z : NR, z < NnMmax x y -> coprod (z < x) (z < y))
           (is0 : isrdistr (@NnMmax NR) (λ x y : NR, x + y))
: MetricSet NR.
Proof.
  intros NR.
  intros Hmax Hdistr.
  mkpair.
  eexists ; exact (NnMap NR).
  mkpair.
  apply (λ x y : NR, NnMmax (x - y) (y - x)).
  repeat split.
  - intros x y.
    apply iscomm_NnMmax.
  - apply sumofmaps ; intros H.
    eapply istrans_NnMlt_le, NnMmax_le_r.
    now apply NnMminus_lt_pos.
    eapply istrans_NnMlt_le, NnMmax_le_l.
    now apply NnMminus_lt_pos.
  - intros H.
    generalize (Hmax _ _ _ H).
    clear H ; apply sumofmaps ; intros H.
    right.
    apply (NnMplus_lt_r y) in H.
    rewrite NnMminus_plus, lunax in H.
    generalize (Hmax _ _ _ H).
    clear H ; apply sumofmaps ; intros H.
    exact H.
    apply fromempty ; revert H.
    apply isirrefl_NnMlt.
    left.
    apply (NnMplus_lt_r x) in H.
    rewrite NnMminus_plus, lunax in H.
    generalize (Hmax _ _ _ H).
    clear H ; apply sumofmaps ; intros H.
    exact H.
    apply fromempty ; revert H.
    apply isirrefl_NnMlt.
  - intros x y z.
    change (NnMmax (x - z) (z - x) <=
            NnMmax (x - y) (y - x) + NnMmax (y - z) (z - y)).
    apply notNnMlt_le ; intros H.
    generalize (Hmax _ _ _ H).
    clear H ; apply sumofmaps ; intros H.
    apply (NnMplus_lt_r z) in H.
    rewrite assocax, !Hdistr, !NnMminus_plus in H.
    generalize (Hmax _ _ _ H).
    clear H ; apply sumofmaps ;
    apply_pr2 (notNnMlt_le (X := NR)).
    admit.
    admit.
    admit.
Admitted.
