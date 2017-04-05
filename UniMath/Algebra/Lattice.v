(** * Lattice *)
(** Catherine Lelay. Nov. 2016 - *)
(**
Definition of a lattice: (Burris, S., & Sankappanavar, H. P. (2006).
A Course in Universal Algebra-With 36 Illustrations. Chapter I)
A lattice is a set with two binary operators min and max such that:
- min and max are associative
- min and max are commutative
- ∏ x y : X, min x (max x y) = x
- ∏ x y : X, max x (min x y) = x

In a lattice, we can define a partial order:
- le := λ (x y : X), min is x y = x

Lattice with a strict order:
A lattice with a strict order gt is lattice such that:
- ∏ (x y : X), (¬ gt x y) <-> le x y
- ∏ x y z : X, gt x z → gt y z → gt (min x y) z
- ∏ x y z : X, gt z x → gt z y → gt z (max is x y)

Lattice with a total and decidable order:
- le is total and decidable
- it is a lattice with a strong order *)

(**
Lattice in an abelian monoid:
- compatibility and cancelation of addition for le

Truncated minus is a lattice:
- a function minus such that: ∏ (x y : X), (minus x y) + y = max x y *)

(**
Define new lattices using:
- weq
- abmonoidfrac
*)

Require Export UniMath.Algebra.Domains_and_Fields.

Require Import UniMath.MoreFoundations.Tactics.

Unset Automatic Introduction.

Set Default Timeout 5.

(** ** Strong Order *)
(* todo : move it into UniMath.Foundations.Sets *)

Definition isStrongOrder {X : UU} (R : hrel X) : UU :=
  istrans R × iscotrans R × isirrefl R.
Definition mkStrongOrder {X : UU} (R : hrel X)
           (Htrans : istrans R) (Hcotrans : iscotrans R) (Hirrefl : isirrefl R) :
  isStrongOrder R := Htrans,,Hcotrans,,Hirrefl.
Definition StrongOrder (X : UU) := ∑ R : hrel X, isStrongOrder R.
Definition pairStrongOrder {X : UU} (R : hrel X) (is : isStrongOrder R) : StrongOrder X :=
  R,,is.
Definition pr1StrongOrder {X : UU} : StrongOrder X → hrel X := pr1.
Coercion  pr1StrongOrder : StrongOrder >-> hrel.

Section so_pty.

Context {X : UU}.
Context (R : StrongOrder X).

Definition istrans_StrongOrder : istrans R :=
  pr1 (pr2 R).
Definition iscotrans_StrongOrder : iscotrans R :=
  pr1 (pr2 (pr2 R)).
Definition isirrefl_StrongOrder : isirrefl R :=
  pr2 (pr2 (pr2 R)).
Definition isasymm_StrongOrder : isasymm R :=
  istransandirrefltoasymm
    istrans_StrongOrder
    isirrefl_StrongOrder.

End so_pty.

Lemma isStrongOrder_bck {X Y : UU} (f : Y → X) (gt : hrel X) :
  isStrongOrder gt → isStrongOrder (fun_hrel_comp f gt).
Proof.
  intros X Y H gt is.
  apply mkStrongOrder.
  - intros x y z.
    apply (istrans_StrongOrder (_,,is)).
  - intros x y z.
    apply (iscotrans_StrongOrder (_,,is)).
  - intros x.
    apply (isirrefl_StrongOrder (_,,is)).
Qed.
Definition StrongOrder_bck {X Y : UU} (f : Y → X) (gt : StrongOrder X) : StrongOrder Y :=
  (fun_hrel_comp f gt) ,, isStrongOrder_bck f _ (pr2 gt).

Lemma isStrongOrder_setquot {X : UU} {R : eqrel X} {L : hrel X} (is : iscomprelrel R L) :
  isStrongOrder L → isStrongOrder (quotrel is).
Proof.
  intros X R L is H.
  apply mkStrongOrder.
  - apply istransquotrel, (istrans_StrongOrder (_,,H)).
  - apply iscotransquotrel, (iscotrans_StrongOrder (_,,H)).
  - apply isirreflquotrel, (isirrefl_StrongOrder (_,,H)).
Qed.
Definition StrongOrder_setquot {X : UU} {R : eqrel X} {L : StrongOrder X} (is : iscomprelrel R L) : StrongOrder (setquot R) :=
  quotrel is,, isStrongOrder_setquot is (pr2 L).

Lemma isStrongOrder_abmonoidfrac {X : abmonoid} (Y : @submonoid X) (gt : hrel X)
      (Hgt : ispartbinophrel Y gt) :
  isStrongOrder gt → isStrongOrder (abmonoidfracrel X Y Hgt).
Proof.
  intros X Y gt Hgt H.
  apply mkStrongOrder.
  - apply istransabmonoidfracrel, (istrans_StrongOrder (_,,H)).
  - apply iscotransabmonoidfracrel, (iscotrans_StrongOrder (_,,H)).
  - apply isirreflabmonoidfracrel, (isirrefl_StrongOrder (_,,H)).
Qed.
Definition StrongOrder_abmonoidfrac {X : abmonoid} (Y : @submonoid X) (gt : StrongOrder X)
           (Hgt : ispartbinophrel Y gt) : StrongOrder (abmonoidfrac X Y) :=
  abmonoidfracrel X Y Hgt,, isStrongOrder_abmonoidfrac Y gt Hgt (pr2 gt).

Lemma isStrongOrder_abgrdiff {X : abmonoid} (gt : hrel X)
      (Hgt : isbinophrel gt) :
  isStrongOrder gt → isStrongOrder (abgrdiffrel X Hgt).
Proof.
  intros X gt Hgt H.
  apply mkStrongOrder.
  - apply istransabgrdiffrel, (istrans_StrongOrder (_,,H)).
  - apply iscotransabgrdiffrel, (iscotrans_StrongOrder (_,,H)).
  - apply isirreflabgrdiffrel, (isirrefl_StrongOrder (_,,H)).
Qed.
Definition StrongOrder_abgrdiff {X : abmonoid} (gt : StrongOrder X)
           (Hgt : isbinophrel gt) : StrongOrder (abgrdiff X) :=
  abgrdiffrel X Hgt,, isStrongOrder_abgrdiff gt Hgt (pr2 gt).

Lemma StrongOrder_correct_commrngfrac (X : commrng) (Y : @subabmonoid (rngmultabmonoid X))
      (gt : StrongOrder X)
      Hgt Hle Hmult Hpos :
  commrngfracgt X Y (R := gt) Hle Hmult Hpos = StrongOrder_abmonoidfrac Y gt Hgt.
Proof.
  intros X Y gt Hgt Hle Hmult Hpos.
  apply funextfun ; intros x.
  apply funextfun ; intros y.
  apply (maponpaths (λ H, abmonoidfracrel (rngmultabmonoid X) Y H x y)).
  assert (H : isaprop (ispartbinophrel Y gt)).
  { apply isapropdirprod ;
    apply impred_isaprop ; intros a ;
    apply impred_isaprop ; intros b ;
    apply impred_isaprop ; intros c ;
    apply isapropimpl, isapropimpl, (pr2 (gt _ _)). }
  apply H.
Qed.

(** ** Definition *)

Definition islatticeop {X : hSet} (min max : binop X) :=
  ((isassoc min) × (iscomm min))
    × ((isassoc max) × (iscomm max))
    × (isabsorb min max)
    × (isabsorb max min).
Definition lattice (X : hSet) :=
  ∑ min max : binop X, islatticeop min max.

Definition mklattice {X : hSet} {min max : binop X} : islatticeop min max → lattice X :=
  λ (is : islatticeop min max), min,, max ,, is.

Definition Lmin {X : hSet} (is : lattice X) : binop X := pr1 is.
Definition Lmax {X : hSet} (is : lattice X) : binop X := pr1 (pr2 is).

Section lattice_pty.

Context {X : hSet}
        (is : lattice X).

Definition isassoc_Lmin : isassoc (Lmin is) :=
  pr1 (pr1 (pr2 (pr2 is))).
Definition iscomm_Lmin : iscomm (Lmin is) :=
  pr2 (pr1 (pr2 (pr2 is))).
Definition isassoc_Lmax : isassoc (Lmax is) :=
  pr1 (pr1 (pr2 (pr2 (pr2 is)))).
Definition iscomm_Lmax : iscomm (Lmax is) :=
  pr2 (pr1 (pr2 (pr2 (pr2 is)))).
Definition Lmin_absorb : isabsorb (Lmin is) (Lmax is) :=
  pr1 (pr2 (pr2 (pr2 (pr2 is)))).
Definition Lmax_absorb : isabsorb (Lmax is) (Lmin is) :=
  pr2 (pr2 (pr2 (pr2 (pr2 is)))).

Lemma Lmin_id :
  ∏ x : X, Lmin is x x = x.
Proof.
  intros x.
  apply (pathscomp0 (b := Lmin is x (Lmax is x (Lmin is x x)))).
  - apply maponpaths, pathsinv0, Lmax_absorb.
  - apply Lmin_absorb.
Qed.
Lemma Lmax_id :
  ∏ x : X, Lmax is x x = x.
Proof.
  intros x.
  apply (pathscomp0 (b := Lmax is x (Lmin is x (Lmax is x x)))).
  - apply maponpaths, pathsinv0, Lmin_absorb.
  - apply Lmax_absorb.
Qed.

End lattice_pty.

(** ** Partial order in a lattice *)

(** [Lle] *)

Definition Lle {X : hSet} (is : lattice X) : hrel X :=
  λ (x y : X), hProppair (Lmin is x y = x) (setproperty X (Lmin is x y) x).

Section lattice_le.

Context {X : hSet}
        (is : lattice X).

Definition isrefl_Lle : isrefl (Lle is) :=
  Lmin_id is.
Lemma isantisymm_Lle :
  isantisymm (Lle is).
Proof.
  intros x y Hxy Hyx.
  apply pathscomp0 with (1 := pathsinv0 Hxy).
  apply pathscomp0 with (2 := Hyx).
  apply iscomm_Lmin.
Qed.
Lemma istrans_Lle :
  istrans (Lle is).
Proof.
  intros x y z <- <-.
  simpl.
  rewrite !isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma isPartialOrder_Lle :
  isPartialOrder (Lle is).
Proof.
  split ; [ split | ].
  - exact istrans_Lle.
  - exact isrefl_Lle.
  - exact isantisymm_Lle.
Qed.

Lemma Lmin_le_l :
  ∏ x y : X, Lle is (Lmin is x y) x.
Proof.
  intros x y.
  simpl.
  rewrite iscomm_Lmin, <- isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma Lmin_le_r :
  ∏ x y : X, Lle is (Lmin is x y) y.
Proof.
  intros x y.
  rewrite iscomm_Lmin.
  apply Lmin_le_l.
Qed.
Lemma Lmin_le_case :
  ∏ x y z : X, Lle is z x → Lle is z y → Lle is z (Lmin is x y).
Proof.
  intros x y z <- <-.
  simpl.
  rewrite (iscomm_Lmin _ x), <- isassoc_Lmin.
  rewrite (isassoc_Lmin _ _ _ y), Lmin_id.
  rewrite isassoc_Lmin, (iscomm_Lmin _ y).
  rewrite isassoc_Lmin, <- (isassoc_Lmin _ x), Lmin_id.
  apply pathsinv0, isassoc_Lmin.
Qed.

Lemma Lmax_le_l :
  ∏ x y : X, Lle is x (Lmax is x y).
Proof.
  intros x y.
  simpl.
  apply Lmin_absorb.
Qed.
Lemma Lmax_le_r :
  ∏ x y : X, Lle is y (Lmax is x y).
Proof.
  intros x y.
  rewrite iscomm_Lmax.
  apply Lmax_le_l.
Qed.
Lemma Lmax_le_case :
  isrdistr (Lmax is) (Lmin is)
  → ∏ x y z : X, Lle is x z → Lle is y z → Lle is (Lmax is x y) z.
Proof.
  intros H x y z <- <-.
  rewrite <- H.
  apply Lmin_le_r.
Qed.

Lemma Lmin_le_eq_l :
  ∏ x y : X, Lle is x y → Lmin is x y = x.
Proof.
  intros x y H.
  apply H.
Qed.
Lemma Lmin_le_eq_r :
  ∏ x y : X, Lle is y x → Lmin is x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmin.
  apply H.
Qed.

Lemma Lmax_le_eq_l :
  ∏ x y : X, Lle is y x → Lmax is x y = x.
Proof.
  intros x y <-.
  rewrite iscomm_Lmin.
  apply Lmax_absorb.
Qed.
Lemma Lmax_le_eq_r :
  ∏ x y : X, Lle is x y → Lmax is x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmax.
  now apply Lmax_le_eq_l.
Qed.

End lattice_le.

(** [Lge] *)

Definition Lge {X : hSet} (is : lattice X) : hrel X :=
  λ x y : X, Lle is y x.

Section Lge_pty.

Context {X : hSet}
        (is : lattice X).

Definition isrefl_Lge : isrefl (Lge is) :=
  isrefl_Lle is.
Lemma isantisymm_Lge :
  isantisymm (Lge is).
Proof.
  intros x y Hle Hge.
  apply (isantisymm_Lle is).
  exact Hge.
  exact Hle.
Qed.
Lemma istrans_Lge :
  istrans (Lge is).
Proof.
  intros x y z Hxy Hyz.
  apply (istrans_Lle is) with y.
  exact Hyz.
  exact Hxy.
Qed.
Lemma isPartialOrder_Lge :
  isPartialOrder (Lge is).
Proof.
  split ; [ split | ].
  - exact istrans_Lge.
  - exact isrefl_Lge.
  - exact isantisymm_Lge.
Qed.

Definition Lmin_ge_l :
  ∏ (x y : X), Lge is x (Lmin is x y) :=
  Lmin_le_l is.
Definition Lmin_ge_r :
  ∏ (x y : X), Lge is y (Lmin is x y) :=
  Lmin_le_r is.
Definition Lmin_ge_case :
  ∏ (x y z : X),
  Lge is x z → Lge is y z → Lge is (Lmin is x y) z :=
  Lmin_le_case is.

Definition Lmax_ge_l :
  ∏ (x y : X), Lge is (Lmax is x y) x :=
  Lmax_le_l is.
Definition Lmax_ge_r :
  ∏ (x y : X), Lge is (Lmax is x y) y :=
  Lmax_le_r is.
Definition Lmax_ge_case :
  isrdistr (Lmax is) (Lmin is)
  → ∏ x y z : X, Lge is z x → Lge is z y → Lge is z (Lmax is x y) :=
  Lmax_le_case is.

Definition Lmin_ge_eq_l :
  ∏ (x y : X), Lge is y x → Lmin is x y = x :=
  Lmin_le_eq_l is.
Definition Lmin_ge_eq_r :
  ∏ (x y : X), Lge is x y → Lmin is x y = y :=
  Lmin_le_eq_r is.

Definition Lmax_ge_eq_l :
  ∏ (x y : X), Lge is x y → Lmax is x y = x :=
  Lmax_le_eq_l is.
Definition Lmax_ge_eq_r :
  ∏ (x y : X), Lge is y x → Lmax is x y = y :=
  Lmax_le_eq_r is.

End Lge_pty.

(** ** Lattice with a strong order *)

Definition islatticewithgtrel {X : hSet} (is : lattice X) (gt : StrongOrder X) :=
  (∏ x y : X, (¬ (gt x y)) <-> Lle is x y)
    × (∏ x y z : X, gt x z → gt y z → gt (Lmin is x y) z)
    × (∏ x y z : X, gt z x → gt z y → gt z (Lmax is x y)).

Definition latticewithgt (X : hSet) :=
  ∑ (is : lattice X) (gt : StrongOrder X), islatticewithgtrel is gt.

Definition lattice_latticewithgt {X : hSet} : latticewithgt X → lattice X :=
  pr1.
Coercion lattice_latticewithgt : latticewithgt >-> lattice.

(** [Lgt] *)

Definition Lgt {X : hSet} (is : latticewithgt X) : StrongOrder X :=
  pr1 (pr2 is).

Section latticewithgt_pty.

Context {X : hSet}
        (is : latticewithgt X).

Definition notLgt_Lle :
  ∏ x y : X, (¬ Lgt is x y) → Lle is x y :=
  λ x y : X, pr1 (pr1 (pr2 (pr2 is)) x y).
Definition Lle_notLgt :
  ∏ x y : X, Lle is x y → ¬ Lgt is x y :=
  λ x y : X, pr2 (pr1 (pr2 (pr2 is)) x y).

Definition isirrefl_Lgt : isirrefl (Lgt is) :=
  isirrefl_StrongOrder (Lgt is).
Definition istrans_Lgt : istrans (Lgt is) :=
  istrans_StrongOrder (Lgt is).
Definition iscotrans_Lgt : iscotrans (Lgt is) :=
  iscotrans_StrongOrder (Lgt is).
Definition isasymm_Lgt : isasymm (Lgt is) :=
  isasymm_StrongOrder (Lgt is).

Lemma Lgt_Lge :
  ∏ x y : X, Lgt is x y → Lge is x y.
Proof.
  intros x y H.
  apply notLgt_Lle.
  intro H0.
  eapply isasymm_Lgt.
  exact H.
  exact H0.
Qed.

Lemma istrans_Lgt_Lge :
  ∏ x y z : X, Lgt is x y → Lge is y z → Lgt is x z.
Proof.
  intros x y z Hgt Hge.
  generalize (iscotrans_Lgt _ z _ Hgt).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  - exact H.
  - apply fromempty.
    refine (Lle_notLgt _ _ _ _).
    exact Hge.
    exact H.
Qed.
Lemma istrans_Lge_Lgt :
  ∏ x y z : X, Lge is x y → Lgt is y z → Lgt is x z.
Proof.
  intros x y z Hge Hgt.
  generalize (iscotrans_Lgt _ x _ Hgt).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  - apply fromempty.
    refine (Lle_notLgt _ _ _ _).
    exact Hge.
    exact H.
  - exact H.
Qed.

Definition Lmin_Lgt :
  ∏ x y z : X, Lgt is x z → Lgt is y z → Lgt is (Lmin is x y) z :=
  pr1 (pr2 (pr2 (pr2 is))).

Definition Lmax_Lgt :
  ∏ x y z : X, Lgt is z x → Lgt is z y → Lgt is z (Lmax is x y) :=
  pr2 (pr2 (pr2 (pr2 is))).

End latticewithgt_pty.


(** ** Lattice with a total order *)

Definition latticedec (X : hSet) :=
  ∑ is : lattice X, istotal (Lle is) × (isdecrel (Lle is)).
Definition lattice_latticedec {X : hSet} (is : latticedec X) : lattice X :=
  pr1 is.
Coercion lattice_latticedec : latticedec >-> lattice.
Definition istotal_latticedec {X : hSet} (is : latticedec X) : istotal (Lle is) :=
  pr1 (pr2 is).
Definition isdecrel_latticedec {X : hSet} (is : latticedec X) : isdecrel (Lle is) :=
  pr2 (pr2 is).

Section latticedec_pty.

Context {X : hSet}
        (is : latticedec X).

Lemma Lmin_case_strong :
  ∏ (P : X → UU) (x y : X),
  (Lle is x y → P x) → (Lle is y x → P y) → P (Lmin is x y).
Proof.
  intros P x y Hx Hy.
  generalize (isdecrel_latticedec is x y).
  apply sumofmaps ; intros H.
  - rewrite Lmin_le_eq_l.
    apply Hx, H.
    exact H.
  - enough (H0 : Lle is y x).
    + rewrite Lmin_le_eq_r.
      apply Hy, H0.
      exact H0.
    + generalize (istotal_latticedec is x y).
      apply hinhuniv, sumofmaps ; intros H0.
      apply fromempty, H, H0.
      exact H0.
Qed.
Lemma Lmin_case :
  ∏ (P : X → UU) (x y : X),
  P x → P y → P (Lmin is x y).
Proof.
  intros P x y Hx Hy.
  apply Lmin_case_strong ; intros _.
  - exact Hx.
  - exact Hy.
Qed.

Lemma Lmax_case_strong :
  ∏ (P : X → UU) (x y : X),
  (Lle is y x → P x) → (Lle is x y → P y) → P (Lmax is x y).
Proof.
  intros P x y Hx Hy.
  generalize (isdecrel_latticedec is x y).
  apply sumofmaps ; intros H.
  - rewrite Lmax_le_eq_r.
    apply Hy, H.
    exact H.
  - enough (H0 : Lle is y x).
    + rewrite Lmax_le_eq_l.
      apply Hx, H0.
      exact H0.
    + generalize (istotal_latticedec is x y).
      apply hinhuniv, sumofmaps ; intros H0.
      apply fromempty, H, H0.
      exact H0.
Qed.
Lemma Lmax_case :
  ∏ (P : X → UU) (x y : X),
  P x → P y → P (Lmax is x y).
Proof.
  intros P x y Hx Hy.
  apply Lmax_case_strong ; intros _.
  - exact Hx.
  - exact Hy.
Qed.

End latticedec_pty.

(** It is a lattice with a strong order *)

Section latticedec_gt.

Context {X : hSet}
        (is : latticedec X).

Definition latticedec_gt_rel : hrel X :=
  λ x y, hneg (Lle is x y).

Lemma latticedec_gt_ge :
  ∏ x y : X, latticedec_gt_rel x y → Lge is x y.
Proof.
  intros x y Hxy.
  generalize (istotal_latticedec is x y).
  apply hinhuniv, sumofmaps ; intros H.
  - apply fromempty.
    exact (Hxy H).
  - exact H.
Qed.

Lemma istrans_latticedec_gt_rel :
  istrans latticedec_gt_rel.
Proof.
  intros x y z Hxy Hyz Hxz.
  simple refine (Hxy _).
  apply istrans_Lle with z.
  apply Hxz.
  apply latticedec_gt_ge.
  exact Hyz.
Qed.
Lemma iscotrans_latticedec_gt_rel :
  iscotrans latticedec_gt_rel.
Proof.
  intros x y z Hxz.
  induction (isdecrel_latticedec is x y) as [Hxy | Hyx].
  - apply hinhpr, ii2.
    intros Hyz.
    simple refine (Hxz _).
    apply istrans_Lle with y.
    exact Hxy.
    exact Hyz.
  - apply hinhpr, ii1.
    exact Hyx.
Qed.

Definition latticedec_gt_so : StrongOrder X.
Proof.
  simple refine (pairStrongOrder _ _).
  - apply latticedec_gt_rel.
  - apply mkStrongOrder.
    + apply istrans_latticedec_gt_rel.
    + apply iscotrans_latticedec_gt_rel.
    + intros x Hx.
      simple refine (Hx _).
      apply isrefl_Lle.
Defined.

Lemma latticedec_notgtle :
  ∏ (x y : X), ¬ latticedec_gt_so x y → Lle is x y.
Proof.
  intros x y H.
  induction (isdecrel_latticedec is x y) as [H0 | H0].
  + exact H0.
  + apply fromempty, H.
    exact H0.
Qed.

Lemma latticedec_lenotgt :
  ∏ (x y : X), Lle is x y → ¬ latticedec_gt_so x y.
Proof.
  intros x y H H0.
  simple refine (H0 _).
  exact H.
Qed.

Lemma latticedec_gtmin :
  ∏ (x y z : X),
  latticedec_gt_so x z
  → latticedec_gt_so y z → latticedec_gt_so (Lmin is x y) z.
Proof.
  intros x y z Hxz Hyz.
  apply (Lmin_case is (λ t : X, latticedec_gt_so t z)).
  - exact Hxz.
  - exact Hyz.
Qed.

Lemma latticedec_gtmax :
  ∏ (x y z : X),
  latticedec_gt_so z x
  → latticedec_gt_so z y → latticedec_gt_so z (Lmax is x y).
Proof.
  intros x y z Hxz Hyz.
  apply (Lmax_case is (latticedec_gt_so z)).
  - exact Hxz.
  - exact Hyz.
Qed.

Definition latticedec_gt : latticewithgt X.
Proof.
  exists (lattice_latticedec is).
  exists latticedec_gt_so.
  split ; split.
  - apply latticedec_notgtle.
  - apply latticedec_lenotgt.
  - apply latticedec_gtmin.
  - apply latticedec_gtmax.
Defined.

End latticedec_gt.

(** ** Lattice in an abmonoid *)

Local Open Scope addmonoid.

Section lattice_abmonoid.

Context {X : abmonoid}
        (is : lattice X)
        (is0 : isinvbinophrel (λ x y, hProppair (x = y) (setproperty X _ _)))
        (is2 : isrdistr (Lmin is) op).

Lemma op_le_r :
  ∏ k x y : X, Lle is x y → Lle is (x + k) (y + k).
Proof.
  intros k x y H.
  unfold Lle ; simpl.
  now rewrite <- is2, H.
Qed.
Lemma op_le_r' :
  ∏ k x y : X, Lle is (x + k) (y + k) → Lle is x y.
Proof.
  intros k x y H.
  apply (pr2 is0 _ _ k).
  now rewrite is2, H.
Qed.

End lattice_abmonoid.

(** ** Truncated minus *)

Definition istruncminus {X : abmonoid} (is : lattice X) (minus : binop X) :=
  ∏ x y : X, minus x y + y = Lmax is x y.
Lemma isaprop_istruncminus {X : abmonoid} (is : lattice X) (minus : binop X) :
  isaprop (istruncminus is minus).
Proof.
  intros X is minus.
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply setproperty.
Qed.

Definition extruncminus {X : abmonoid} (is : lattice X) :=
  ∑ minus : binop X, istruncminus is minus.
Lemma isaprop_extruncminus {X : abmonoid} (is : lattice X)
      (Hop : isinvbinophrel (λ x y, hProppair (x = y) (setproperty X _ _))) :
  isaprop (extruncminus is).
Proof.
  intros X is Hop.
  intros minus1 minus2 ; simpl.
  rewrite (subtypeEquality' (s := minus1) (s' := minus2)).
  - apply iscontrloopsifisaset.
    apply isaset_total2.
    apply impred_isaset ; intros _.
    apply impred_isaset ; intros _.
    apply setproperty.
    intros minus.
    apply isasetaprop.
    apply isaprop_istruncminus.
  - apply weqfunextsec ; intros x.
    apply weqfunextsec ; intros y.
    apply (pr2 Hop _ _ y).
    rewrite (pr2 minus1).
    apply pathsinv0, (pr2 minus2).
  - apply isaprop_istruncminus.
Qed.

Definition truncminus {X : abmonoid} {is : lattice X} (ex : extruncminus is) : binop X :=
  pr1 ex.

Lemma istruncminus_ex {X : abmonoid} {is : lattice X} (ex : extruncminus is) :
  ∏ x y : X, truncminus ex x y + y = Lmax is x y.
Proof.
  intros X is ex.
  apply (pr2 ex).
Qed.

Section truncminus_pty.

Context {X : abmonoid}
        {is : lattice X}
        (ex : extruncminus is)
        (is1 : isinvbinophrel (λ x y, hProppair (x = y) (setproperty X _ _)))
        (is2 : isrdistr (Lmax is) op)
        (is3 : isrdistr (Lmin is) op)
        (is4 : isrdistr (Lmin is) (Lmax is))
        (is5 : isrdistr (Lmax is) (Lmin is)).

Lemma truncminus_0_r :
  ∏ x : X, truncminus ex x 0 = Lmax is x 0.
Proof.
  intros x.
  rewrite <- (runax _ (truncminus _ _ _)).
  apply (istruncminus_ex).
Qed.

Lemma truncminus_eq_0 :
  ∏ x y : X, Lle is x y → truncminus ex x y = 0.
Proof.
  intros x y H.
  apply (pr2 is1 _ _ y).
  simpl.
  refine (pathscomp0 _ _).
  apply istruncminus_ex.
  refine (pathscomp0 _ _).
  apply Lmax_le_eq_r, H.
  apply pathsinv0, (lunax X).
Qed.

Lemma truncminus_0_l_ge0 :
  ∏ x : X, Lle is 0 x → truncminus ex 0 x = 0.
Proof.
  intros x Hx.
  apply truncminus_eq_0, Hx.
Qed.
Lemma truncminus_0_l_le0 :
  ∏ x : X, Lle is x 0 → truncminus ex 0 x + x = 0.
Proof.
  intros x Hx.
  rewrite istruncminus_ex.
  apply Lmax_le_eq_l, Hx.
Qed.

Lemma truncminus_ge_0 :
  ∏ x y : X, Lle is 0 (truncminus ex x y).
Proof.
  intros x y.
  apply (op_le_r' _ is1 is3 y).
  rewrite istruncminus_ex, lunax.
  apply Lmax_ge_r.
Qed.

Lemma truncminus_le :
  ∏ x y : X,
          Lle is 0 x → Lle is 0 y
          → Lle is (truncminus ex x y) x.
Proof.
  intros x y Hx Hy.
  apply (op_le_r' _ is1 is3 y).
  rewrite istruncminus_ex.
  apply Lmax_le_case.
  - apply is5.
  - apply istrans_Lle with (0 + x).
    + rewrite (lunax _ x).
      apply isrefl_Lle.
    + rewrite (commax _ x).
      now apply op_le_r.
  - apply istrans_Lle with (0 + y).
    + rewrite (lunax _ y).
      apply isrefl_Lle.
    + now apply op_le_r.
Qed.

Lemma truncminus_truncminus :
  ∏ x y, Lle is 0 x → Lle is x y → truncminus ex y (truncminus ex y x) = x.
Proof.
  intros x y Hx Hxy.
  apply (pr2 is1 _ _ (truncminus ex y x)).
  simpl.
  rewrite (commax _ x), istruncminus_ex.
  refine (pathscomp0 _ _).
  apply istruncminus_ex.
  rewrite !Lmax_le_eq_l.
  - reflexivity.
  - exact Hxy.
  - apply truncminus_le.
    apply istrans_Lle with x.
    exact Hx.
    exact Hxy.
    exact Hx.
Qed.

Lemma truncminus_le_r :
  ∏ k x y : X, Lle is x y → Lle is (truncminus ex x k) (truncminus ex y k).
Proof.
  intros k x y <-.
  apply (pr2 is1 _ _ k).
  simpl.
  rewrite is3, 2!istruncminus_ex.
  rewrite is4, isassoc_Lmin, Lmin_id.
  rewrite <- is4.
  apply pathsinv0, istruncminus_ex.
Qed.
Lemma truncminus_le_l :
  ∏ k x y : X, Lle is y x → Lle is (truncminus ex k x) (truncminus ex k y).
Proof.
  intros k x y H.
  apply (pr2 is1 _ _ y).
  change ((Lmin is (truncminus ex k x) (truncminus ex k y) * y)%multmonoid =
     (truncminus ex k x * y)%multmonoid).
  rewrite is3, istruncminus_ex.
  apply (pr2 is1 _ _ x).
  change ((Lmin is (truncminus ex k x * y) (Lmax is k y) * x)%multmonoid =
     (truncminus ex k x * y * x)%multmonoid).
  rewrite is3, assocax, (commax _ y), <- assocax, istruncminus_ex.
  rewrite !is2, (commax _ y), <- is4, !(commax _ k), <- is3, H.
  reflexivity.
Qed.

Lemma truncminus_Lmax_l :
  ∏ (k x y : X),
  truncminus ex (Lmax is x y) k = Lmax is (truncminus ex x k) (truncminus ex y k).
Proof.
  intros k x y.
  apply (pr2 is1 _ _ k).
  change ((truncminus ex (Lmax is x y) k * k)%multmonoid =
     (Lmax is (truncminus ex x k) (truncminus ex y k) * k)%multmonoid).
  rewrite is2, !istruncminus_ex.
  rewrite !isassoc_Lmax, (iscomm_Lmax _ k), isassoc_Lmax, Lmax_id.
  reflexivity.
Qed.
Lemma truncminus_Lmax_r :
  ∏ (k x y : X),
  Lle is (Lmin is (y + y) (x + x)) (x + y) →
  truncminus ex k (Lmax is x y) = Lmin is (truncminus ex k x) (truncminus ex k y).
Proof.
  intros k x y H.
  apply (pr2 is1 _ _ (Lmax is x y)).
  change ((truncminus ex k (Lmax is x y) * Lmax is x y)%multmonoid =
     (Lmin is (truncminus ex k x) (truncminus ex k y) * Lmax is x y)%multmonoid).
  rewrite is3, istruncminus_ex.
  rewrite !(commax _ _ (Lmax _ _ _)), !is2.
  rewrite !(commax _ _ (truncminus _ _ _)), !istruncminus_ex.
  rewrite (iscomm_Lmax _ (_*_)%multmonoid (Lmax _ _ _)).
  rewrite !isassoc_Lmax, !(iscomm_Lmax _ k).
  rewrite <- is4.

  apply (pr2 is1 _ _ x).
  change ((Lmax is (Lmax is x y) k * x)%multmonoid =
     (Lmax is
        (Lmin is (Lmax is x (truncminus ex k x * y))
           (Lmax is y (truncminus ex k y * x))) k * x)%multmonoid).
  rewrite !is2, is3, !is2.
  rewrite assocax, (commax _ y x), <- assocax.
  rewrite istruncminus_ex, is2.

  apply (pr2 is1 _ _ y).
  change ((Lmax is (Lmax is (x * x) (x * y)) (k * x) * y)%multmonoid =
     (Lmax is
        (Lmin is (Lmax is (x * x) (Lmax is (k * y) (x * y)))
           (Lmax is (x * y) (truncminus ex k y * x * x)))
        (k * x) * y)%multmonoid).
  rewrite !is2, is3, !is2.
  rewrite !assocax, (commax _ (truncminus _ _ _)), !assocax, (commax _ _ (truncminus _ _ _)).
  rewrite istruncminus_ex.
  rewrite (commax _ _ (Lmax _ _ _)), is2.
  rewrite (commax _ _ (Lmax _ _ _)), is2.

  rewrite 4!(commax _ _ x).
  rewrite <- (isassoc_Lmax _ _ _ (x * (y * y))%multmonoid).
  rewrite (iscomm_Lmax _ (x * (y * y))%multmonoid (Lmax _ _ _)).

  rewrite <- is4.
  rewrite (iscomm_Lmax _ (x * (x * y))%multmonoid (k * (y * y))%multmonoid), <- is4.
  rewrite !(commax _ k), <- !assocax.
  rewrite <- is3.
  rewrite !(iscomm_Lmax _ _ (x * y * k)%multmonoid), <- !isassoc_Lmax.
  rewrite (Lmax_le_eq_l _ (x * y * k)%multmonoid
                     (Lmin is (y * y) (x * x) * k)%multmonoid).
  reflexivity.
  apply op_le_r.
  exact is3.
  exact H.
Qed.

Lemma truncminus_Lmin_l :
  ∏ k x y : X, truncminus ex (Lmin is x y) k = Lmin is (truncminus ex x k) (truncminus ex y k).
Proof.
  intros k x y.
  apply (pr2 is1 _ _ k).
  simpl.
  rewrite is3, 2!istruncminus_ex.
  apply (pathscomp0 (istruncminus_ex _ _ _)).
  apply is4.
Qed.

End truncminus_pty.

Lemma abgr_truncminus {X : abgr} (is : lattice X) :
  isrdistr (Lmax is) op →
  istruncminus (X := abgrtoabmonoid X) is (λ x y : X, Lmax is 0 (x + grinv X y)).
Proof.
  intros X is H x y.
  rewrite H, assocax, grlinvax, lunax, runax.
  apply iscomm_Lmax.
Qed.

Section truncminus_gt.

Context {X : abmonoid}
        (is : latticewithgt X)
        (ex : extruncminus is)
        (is0 : ∏ x y z : X, Lgt is y z → Lgt is (y + x) (z + x))
        (is1 : ∏ x y z : X, Lgt is (y + x) (z + x) → Lgt is y z).

Lemma truncminus_pos :
  ∏ x y : X, Lgt is x y → Lgt is (truncminus ex x y) 0.
Proof.
  intros x y.
  intros H.
  apply (is1 y).
  rewrite lunax, istruncminus_ex.
  rewrite Lmax_le_eq_l.
  exact H.
  apply Lgt_Lge, H.
Qed.

Lemma truncminus_pos' :
  ∏ x y : X, Lgt is (truncminus ex x y) 0 → Lgt is x y.
Proof.
  intros x y Hgt.
  apply (is0 y) in Hgt.
  rewrite istruncminus_ex, lunax in Hgt.
  rewrite <- (Lmax_le_eq_l is x y).
  exact Hgt.
  apply notLgt_Lle.
  intros H ; revert Hgt.
  apply Lle_notLgt.
  rewrite Lmax_le_eq_r.
  apply isrefl_Lle.
  apply Lgt_Lge.
  exact H.
Qed.

End truncminus_gt.

(** *** Truncated minus and abgrdiff *)

Section abgrdiff_minus.

Context {X : abmonoid}
        {is : lattice X}
        (ex : extruncminus is)
        (is1 : ∏ x y z : X, y + x = z + x → y = z)
        (is2 : isrdistr (Lmax is) op)
        (is3 : isrdistr (Lmin is) op)
        (is4 : isrdistr (Lmax is) (Lmin is)).

Lemma iscomprel_truncminus :
    iscomprelfun (eqrelabgrdiff X) (λ x, truncminus ex (pr1 x) (pr2 x)).
Proof.
  intros x y.
  simple refine (hinhuniv (P := hProppair _ _) _).
  apply (pr2 (pr1 (pr1 X))).
  intros c.
  apply (is1 (pr2 x + pr2 y + pr1 c)).
  rewrite <- 2!assocax, istruncminus_ex.
  rewrite (commax _ (pr2 x)), <- 2!assocax, istruncminus_ex.
  rewrite !is2, (pr2 c), (commax _ (pr2 x)).
  reflexivity.
Qed.

Definition abgrdiff_elt (x : abgrdiff X) : X × X.
Proof.
  split.
  - refine (setquotuniv _ _ _ _ _).
    apply iscomprel_truncminus.
    apply x.
  - refine (setquotuniv _ _ _ _ _).
    apply iscomprel_truncminus.
    apply (grinv (abgrdiff X) x).
Defined.

Lemma abgrdiff_elt_simpl (c : X × X) :
  abgrdiff_elt (setquotpr _ c) = truncminus ex (pr1 c) (pr2 c) ,, truncminus ex (pr2 c) (pr1 c).
Proof.
  intros c.
  unfold abgrdiff_elt.
  unfold grinv ; simpl.
  unfold abgrdiffinv ; simpl.
  rewrite (setquotfuncomm (eqrelabgrdiff X) (eqrelabgrdiff X)).
  rewrite !(setquotunivcomm (eqrelabgrdiff X)).
  reflexivity.
Qed.

Lemma abgrdiff_elt_correct (x : abgrdiff X) :
  setquotpr _ (abgrdiff_elt x) = x.
Proof.
  simple refine (setquotunivprop _ (λ _, _ ,, _) _).
  - apply (pr2 (pr1 (pr1 (abgrdiff X)))).
  - intros c ; simpl.
    refine (iscompsetquotpr (eqrelabgrdiff X) _ _ _).
    rewrite abgrdiff_elt_simpl.
    apply hinhpr.
    exists 0 ; simpl.
    rewrite (commax _ (pr1 c)), !(istruncminus_ex ex).
    now rewrite iscomm_Lmax.
Qed.

Lemma abgrdiff_elt_correct' (x : abgrdiff X) :
  abgrdiff_elt (setquotpr _ (abgrdiff_elt x)) = abgrdiff_elt x.
Proof.
  intros x.
  now rewrite abgrdiff_elt_correct.
Qed.

End abgrdiff_minus.

Close Scope addmonoid.

(** ** lattice and [weq] *)

(** *** Definition *)

Lemma islatticeop_weq {X Y : hSet} (H : weq Y X) {min max : binop X} (is : islatticeop min max) :
  islatticeop (binop_weq_bck H min) (binop_weq_bck H max).
Proof.
  intros.
  split ; [ | split] ; split.
  - apply (isassoc_weq_bck H), (isassoc_Lmin (_,,_,,is)).
  - apply (iscomm_weq_bck H), (iscomm_Lmin (_,,_,,is)).
  - apply (isassoc_weq_bck H), (isassoc_Lmax (_,,_,,is)).
  - apply (iscomm_weq_bck H), (iscomm_Lmax (_,,_,,is)).
  - apply (isabsorb_weq_bck H), (Lmin_absorb (_,,_,,is)).
  - apply (isabsorb_weq_bck H), (Lmax_absorb (_,,_,,is)).
Qed.

Definition lattice_weq {X Y : hSet} (H : weq Y X) (is : lattice X) : lattice Y.
Proof.
  intros X Y H is.
  exists (binop_weq_bck H (Lmin is)), (binop_weq_bck H (Lmax is)).
  apply islatticeop_weq.
  apply (pr2 (pr2 is)).
Defined.

(** *** Value of [Lle] *)

Lemma Lle_correct_weq {X Y : hSet} (H : weq Y X) (is : lattice X) :
  fun_hrel_comp H (Lle is) = Lle (lattice_weq H is).
Proof.
  intros X Y H is.
  apply funextfun ; intros x.
  apply funextfun ; intros y.
  apply hPropUnivalence ; intros Hle.
  - apply pathsinv0, pathsweq1, pathsinv0.
    apply Hle.
  - apply pathsinv0, pathsweq1', pathsinv0.
    apply Hle.
Qed.

(** *** Lattice with strong order *)

Lemma islatticewithgtrel_weq {X Y : hSet} (H : weq Y X) {gt : StrongOrder X} (is : lattice X) :
  islatticewithgtrel is gt →
  islatticewithgtrel (lattice_weq H is) (StrongOrder_bck H gt).
Proof.
  intros X Y H gt is Hgt.
  split ; split.
  - intros Hngt.
    unfold Lle ; simpl.
    unfold binop_weq_bck.
    rewrite (pr1 (pr1 Hgt _ _)).
    apply homotinvweqweq.
    apply Hngt.
  - intros Hle.
    apply (pr2 (pr1 Hgt _ _)).
    unfold Lle ; simpl.
    apply pathsinv0, pathsweq1', pathsinv0.
    apply Hle.
  - simpl ; intros x y z Hx Hy.
    unfold binop_weq_bck, fun_hrel_comp.
    rewrite homotweqinvweq.
    apply (pr1 (pr2 Hgt)).
    exact Hx.
    exact Hy.
  - unfold Lmax ; simpl ; intros x y z Hx Hy.
    unfold binop_weq_bck, fun_hrel_comp.
    rewrite homotweqinvweq.
    apply (pr2 (pr2 Hgt)).
    exact Hx.
    exact Hy.
Qed.
Definition latticewithgt_weq {X Y : hSet} (H : weq Y X) (is : latticewithgt X) :
  latticewithgt Y.
Proof.
  intros X Y H is.
  exists (lattice_weq H is), (StrongOrder_bck H (Lgt is)).
  apply islatticewithgtrel_weq.
  apply (pr2 (pr2 is)).
Defined.

(** *** Lattice with a decidable order *)

Lemma istotal_Lle_weq {X Y : hSet} (H : weq Y X)
      (is : lattice X) (is' : istotal (Lle is)) :
  istotal (Lle (lattice_weq H is)).
Proof.
  intros X Y H is is'.
  intros x y.
  generalize (is' (H x) (H y)).
  apply hinhfun, sumofmaps ; intros Hmin.
  - apply ii1, (pathscomp0 (maponpaths (invmap H) Hmin)), homotinvweqweq.
  - apply ii2, (pathscomp0 (maponpaths (invmap H) Hmin)), homotinvweqweq.
Qed.
Lemma isdecrel_Lle_weq {X Y : hSet} (H : weq Y X)
      (is : lattice X) (is' : isdecrel (Lle is)) :
  isdecrel (Lle (lattice_weq H is)).
Proof.
  intros X Y H is is'.
  intros x y.
  generalize (is' (H x) (H y)).
  apply sumofmaps ; intros Hmin.
  - apply ii1, (pathscomp0 (maponpaths (invmap H) Hmin)), homotinvweqweq.
  - apply ii2.
    intros Hinv ; apply Hmin.
    apply pathsinv0, pathsweq1', pathsinv0, Hinv.
Qed.

Definition latticedec_weq {X Y : hSet} (H : weq Y X) :
  latticedec X → latticedec Y.
Proof.
  intros X Y H is.
  exists (lattice_weq H (lattice_latticedec is)).
  split.
  - apply istotal_Lle_weq.
    apply istotal_latticedec.
  - apply isdecrel_Lle_weq.
    apply isdecrel_latticedec.
Defined.

(** ** lattice in [abmonoid] *)

Open Scope multmonoid.

Lemma abmonoidfrac_setquotpr_equiv {X : abmonoid} {Y : @submonoid X} :
  ∏ (k : Y) (x : X) (y : Y),
  setquotpr (binopeqrelabmonoidfrac X Y) (x,,y) = setquotpr (binopeqrelabmonoidfrac X Y) (x * pr1 k,, @op Y y k).
Proof.
  intros X Y k x y.
  apply iscompsetquotpr, hinhpr.
  exists y ; simpl.
  rewrite !(assocax X) ;
    apply maponpaths.
  rewrite commax, !assocax.
  reflexivity.
Qed.

Definition ispartrdistr {X : abmonoid} (Y : @submonoid X) (opp1 opp2 : binop X) :=
  ∏ (x y : X) (k : Y),
  opp2 (opp1 x y) (pr1 k) = opp1 (opp2 x (pr1 k)) (opp2 y (pr1 k)).

Section abmonoidfrac_lattice.

Context (X : abmonoid)
        (Y : @submonoid X)
        {min max : binop X}
        (Hmin_assoc : isassoc min)
        (Hmin_comm : iscomm min)
        (Hmax_assoc : isassoc max)
        (Hmax_comm : iscomm max)
        (Hmin_max : isabsorb min max)
        (Hmax_min : isabsorb max min)
        (Hmin : ispartrdistr Y min op)
        (Hmax : ispartrdistr Y max op).

(** generic lemmas *)

Local Definition abmonoidfrac_lattice_fun (f : binop X) : binop (X × Y) :=
  λ x y,
  (f (pr1 x * pr1 (pr2 y))%multmonoid (pr1 y * pr1 (pr2 x))%multmonoid ,, @op Y (pr2 x) (pr2 y)).

Local Lemma abmonoidfrac_lattice_def :
  ∏ (f : X → X → X),
  ispartrdistr Y f op →
  iscomprelrelfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y)
                   (abmonoidfrac_lattice_fun f).
Proof.
  intros f Hf.
  intros x y x' y'.
  apply hinhfun2.
  intros c c'.
  unfold abmonoidfrac_lattice_fun.
  change (∑ a0 : Y,
  f (pr1 x * pr1 (pr2 x')) (pr1 x' * pr1 (pr2 x)) *
  pr1 (pr2 y * pr2 y') * pr1 a0 =
  f (pr1 y * pr1 (pr2 y')) (pr1 y' * pr1 (pr2 y)) *
  pr1 (pr2 x * pr2 x') * pr1 a0).
  exists (@op Y (pr1 c) (pr1 c')).
  - do 4 rewrite Hf.
    apply map_on_two_paths.
    + change ((pr1 x * pr1 (pr2 x') * (pr1 (pr2 y) * pr1 (pr2 y')) * (pr1 (pr1 c) * pr1 (pr1 c')))%multmonoid =
  (pr1 y * pr1 (pr2 y') * (pr1 (pr2 x) * pr1 (pr2 x')) * (pr1 (pr1 c) * pr1 (pr1 c')))%multmonoid).
      rewrite (assocax X (pr1 x)), (assocax X (pr1 y)).
      rewrite (commax X (pr1 (pr2 x'))), (commax X (pr1 (pr2 y'))).
      do 2 rewrite <- (assocax X (pr1 x)), <- (assocax X (pr1 y)).
      do 2 rewrite (assocax X (pr1 x * pr1 (pr2 y))%multmonoid), (assocax X (pr1 y * pr1 (pr2 x))%multmonoid).
      do 2 rewrite (commax X _ (pr1 (pr1 c) * _)%multmonoid).
      do 2 rewrite <- (assocax X _ (pr1 (pr1 c) * _)%multmonoid).
      do 2 rewrite <- (assocax X _ (pr1 (pr1 c))%multmonoid).
      rewrite (commax X (pr1 (pr2 y'))).
      apply (maponpaths (λ x, (x * _ * _)%multmonoid)).
      apply (pr2 c).
    + rewrite (commax _ (pr2 y)), (commax _ (pr2 x)), (iscommcarrier Y (pr1 c)).
      change ((pr1 x' * pr1 (pr2 x) * (pr1 (pr2 y') * pr1 (pr2 y)) * (pr1 (pr1 c') * pr1 (pr1 c)))%multmonoid =
  (pr1 y' * pr1 (pr2 y) * (pr1 (pr2 x') * pr1 (pr2 x)) * (pr1 (pr1 c') * pr1 (pr1 c)))%multmonoid).
      rewrite (assocax X (pr1 x')), (assocax X (pr1 y')).
      rewrite (commax X (pr1 (pr2 x))), (commax X (pr1 (pr2 y))).
      do 2 rewrite <- (assocax X (pr1 x')), <- (assocax X (pr1 y')).
      do 2 rewrite (assocax X (pr1 x' * pr1 (pr2 y'))%multmonoid), (assocax X (pr1 y' * pr1 (pr2 x'))%multmonoid).
      do 2 rewrite (commax X _ (pr1 (pr1 c') * _)%multmonoid).
      do 2 rewrite <- (assocax X _ (pr1 (pr1 c') * _)%multmonoid).
      do 2 rewrite <- (assocax X _ (pr1 (pr1 c'))%multmonoid).
      rewrite (commax X (pr1 (pr2 y))).
      apply (maponpaths (λ x, (x * _ * _)%multmonoid)).
      apply (pr2 c').
Qed.

Local Lemma iscomm_abmonoidfrac_def :
  ∏ (f : X → X → X) Hf,
  iscomm f →
  iscomm (X := abmonoidfrac X Y)
         (setquotfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y) _
                      (abmonoidfrac_lattice_def f Hf)).
Proof.
  intros f Hf Hcomm.
  simple refine (setquotuniv2prop _ (λ x y, (_ x y = _ y x) ,, _) _).
  - apply (pr2 (pr1 (pr1 (abmonoidfrac X Y)))).
  - intros x y.
    simpl.
    rewrite !(setquotfun2comm (eqrelabmonoidfrac X Y)).
    unfold abmonoidfrac_lattice_fun.
    rewrite Hcomm, (commax X (pr1 x)), (commax _ (pr2 x)).
    reflexivity.
Qed.
Local Lemma isassoc_abmonoidfrac_def :
  ∏ (f : X → X → X) Hf,
  isassoc f →
  isassoc (X := abmonoidfrac X Y)
         (setquotfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y) _
                      (abmonoidfrac_lattice_def f Hf)).
Proof.
  intros f Hf Hassoc.
  simple refine (setquotuniv3prop _ (λ x y z, (_ (_ x y) z = _ x (_ y z)) ,, _) _).
  - apply (pr2 (pr1 (pr1 (abmonoidfrac X Y)))).
  - intros x y z ; simpl.
    rewrite !(setquotfun2comm (eqrelabmonoidfrac X Y)).
    apply (iscompsetquotpr (eqrelabmonoidfrac X Y)), hinhpr.
    exists (pr2 x).
    apply (maponpaths (λ x, (x * _)%multmonoid)).
    unfold abmonoidfrac_lattice_fun.
    rewrite !rewrite_pr1_tpair, !rewrite_pr2_tpair.
    simpl ; unfold pr1carrier ; simpl.
    rewrite (assocax X (pr1 (pr2 x))).
    apply (maponpaths (λ x: X, op x _)).
    do 2 rewrite Hf.
    rewrite Hassoc.
    do 4 rewrite (assocax X).
    do 2 rewrite (commax X (pr1 (pr2 x))).
    reflexivity.
Qed.

Local Lemma isabsorb_abmonoidfrac_def :
  ∏ f g Hf Hg,
  isabsorb f g →
  isabsorb (X := abmonoidfrac X Y) (setquotfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y) _
                        (abmonoidfrac_lattice_def f Hf))
           (setquotfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y) _
                        (abmonoidfrac_lattice_def g Hg)).
Proof.
  intros f g Hf Hg Habsorb.
  simple refine (setquotuniv2prop _ (λ x y, (_ x (_ x y) = x) ,, _) _).
  - apply (setproperty (abmonoidfrac X Y)).
  - intros x y.
    simpl.
    rewrite !(setquotfun2comm (eqrelabmonoidfrac X Y)).
    unfold abmonoidfrac_lattice_fun.
    apply (iscompsetquotpr (eqrelabmonoidfrac X Y)), hinhpr.
    exists (pr2 x).
    apply (maponpaths (λ x, (x * _)%multmonoid)).
    rewrite !rewrite_pr1_tpair, !rewrite_pr2_tpair.
    simpl ; unfold pr1carrier ; simpl.
    rewrite Hf, Hg, Hg.
    do 3 rewrite (assocax X (pr1 x)).
    rewrite (commax X (pr1 (pr2 y))).
    do 2 rewrite (assocax X (pr1 (pr2 x))).
    do 3 rewrite (commax X (pr1 (pr2 x))).
    apply Habsorb.
Qed.

(** definition of abmonoidfrac_lattice *)

Definition abmonoidfrac_min : binop (abmonoidfrac X Y) :=
  setquotfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y) _
              (abmonoidfrac_lattice_def min Hmin).
Definition abmonoidfrac_max : binop (abmonoidfrac X Y) :=
  setquotfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y) _
              (abmonoidfrac_lattice_def max Hmax).

Lemma iscomm_abmonoidfrac_min :
  iscomm abmonoidfrac_min.
Proof.
  apply iscomm_abmonoidfrac_def.
  apply Hmin_comm.
Qed.

Lemma isassoc_abmonoidfrac_min :
  isassoc abmonoidfrac_min.
Proof.
  apply isassoc_abmonoidfrac_def.
  apply Hmin_assoc.
Qed.

Lemma iscomm_abmonoidfrac_max :
  iscomm abmonoidfrac_max.
Proof.
  apply iscomm_abmonoidfrac_def.
  apply Hmax_comm.
Qed.

Lemma isassoc_abmonoidfrac_max :
  isassoc abmonoidfrac_max.
Proof.
  apply isassoc_abmonoidfrac_def.
  apply Hmax_assoc.
Qed.

Lemma isabsorb_abmonoidfrac_max_min :
  isabsorb abmonoidfrac_max abmonoidfrac_min.
Proof.
  apply isabsorb_abmonoidfrac_def.
  apply Hmax_min.
Qed.

Lemma isabsorb_abmonoidfrac_min_max :
  isabsorb abmonoidfrac_min abmonoidfrac_max.
Proof.
  apply isabsorb_abmonoidfrac_def.
  apply Hmin_max.
Qed.

End abmonoidfrac_lattice.

Lemma abmonoidfrac_islatticeop (X : abmonoid) (Y : @submonoid X) (is : lattice X) :
  ∏ (Hmin : ispartrdistr Y (Lmin is) op) (Hmax : ispartrdistr Y (Lmax is) op),
  islatticeop (abmonoidfrac_min X Y Hmin) (abmonoidfrac_max X Y Hmax).
Proof.
  intros X Y is Hmin Hmax.
  repeat split.
  - apply isassoc_abmonoidfrac_min, isassoc_Lmin.
  - apply iscomm_abmonoidfrac_min, iscomm_Lmin.
  - apply isassoc_abmonoidfrac_max, isassoc_Lmax.
  - apply iscomm_abmonoidfrac_max, iscomm_Lmax.
  - apply isabsorb_abmonoidfrac_min_max, Lmin_absorb.
  - apply isabsorb_abmonoidfrac_max_min, Lmax_absorb.
Qed.

Definition abmonoidfrac_lattice (X : abmonoid) (Y : @submonoid X) (is : lattice X)
           (Hmin : ispartrdistr Y (Lmin is) op) (Hmax : ispartrdistr Y (Lmax is) op) : lattice (abmonoidfrac X Y).
Proof.
  intros X Y is Hmin Hmax.
  mkpair.
  exact (abmonoidfrac_min X Y Hmin).
  mkpair.
  exact (abmonoidfrac_max X Y Hmax).
  apply abmonoidfrac_islatticeop.
Defined.

Lemma ispartbinophrel_Lle (X : abmonoid) (Y : @submonoid X) (is : lattice X)
      (Hmin : ispartrdistr Y (Lmin is) op) :
  ispartbinophrel Y (Lle is).
Proof.
  intros X Y is Hmin.
  split.
  - intros a b c Yc.
    rewrite !(commax _ c).
    unfold Lle ; rewrite <- (Hmin _ _ (c,,Yc)).
    apply (maponpaths (λ x, op x _)).
  - intros a b c Yc.
    unfold Lle ; rewrite <- (Hmin _ _ (c,,Yc)).
    apply (maponpaths (λ x, op x _)).
Qed.

Lemma abmonoidfrac_Lle_1 (X : abmonoid) (Y : @submonoid X) (is : lattice X)
      (Hmin : ispartrdistr _ (Lmin is) op) :
  ∏ (x y : abmonoiddirprod X _),
  abmonoidfracrel X Y (ispartbinophrel_Lle X Y is Hmin)
                  (setquotpr (binopeqrelabmonoidfrac X Y) x)
                  (setquotpr (binopeqrelabmonoidfrac X Y) y) →
  abmonoidfrac_min X Y Hmin (setquotpr (binopeqrelabmonoidfrac X Y) x)
                   (setquotpr (binopeqrelabmonoidfrac X Y) y) =
  setquotpr (binopeqrelabmonoidfrac X Y) x.
Proof.
  intros X Y is Hmin.
  intros x y.
  unfold abmonoidfracrel, quotrel, abmonoidfrac_min.
  rewrite setquotuniv2comm, setquotfun2comm.
  intros H.
  apply iscompsetquotpr.
  revert H.
  apply hinhfun.
  intros c.
  exists (pr1 c).
  simpl in c |- *.
  rewrite (assocax X), (commax _ _ (pr1 (pr1 c))), <- (assocax X).
  rewrite Hmin.
  refine (pathscomp0 _ _).
  refine (maponpaths (λ x, x * _) _).
  apply (pr2 c).
  do 3 rewrite (assocax X) ;
    apply maponpaths.
  do 2 rewrite commax, assocax.
  apply pathsinv0, assocax.
Timeout 10 Qed.
Lemma abmonoidfrac_Lle_2 (X : abmonoid) (Y : @submonoid X) (is : lattice X)
      (Hmin : ispartrdistr _ (Lmin is) op) :
  ∏ (x y : abmonoiddirprod X _),
  abmonoidfrac_min X Y Hmin (setquotpr (binopeqrelabmonoidfrac X Y) x)
                   (setquotpr (binopeqrelabmonoidfrac X Y) y) =
  setquotpr (binopeqrelabmonoidfrac X Y) x
  → abmonoidfracrel X Y (ispartbinophrel_Lle X Y is Hmin)
                    (setquotpr (binopeqrelabmonoidfrac X Y) x)
                    (setquotpr (binopeqrelabmonoidfrac X Y) y).
Proof.
  intros X Y is Hmin.
  intros x y.
  unfold abmonoidfracrel, quotrel, abmonoidfrac_min.
  rewrite setquotuniv2comm, setquotfun2comm.
  intros H.
  generalize (invmap (weqpathsinsetquot _ _ _) H).
  apply hinhfun.
  simpl.
  intros c.
  exists (pr2 x * pr1 c).
  rewrite <- Hmin.
  change (pr1 (pr2 x * pr1 c))%multmonoid
  with (pr1 (pr2 x) * pr1 (pr1 c))%multmonoid.
  rewrite <- assocax.
  refine (pathscomp0 _ _).
  apply (pr2 c).
  do 3 rewrite (assocax X) ;
    apply maponpaths.
  rewrite commax, assocax.
  apply maponpaths.
  apply commax.
Qed.

Lemma abmonoidfrac_Lle (X : abmonoid) (Y : @submonoid X) (is : lattice X)
      (Hmin : ispartrdistr Y (Lmin is) op) (Hmax : ispartrdistr Y (Lmax is) op) :
  ∏ x y : abmonoidfrac X Y, abmonoidfracrel X Y (ispartbinophrel_Lle X Y is Hmin) x y <-> Lle (abmonoidfrac_lattice X Y is Hmin Hmax) x y.
Proof.
  intros X Y is Hmin Hmax.
  simple refine (setquotuniv2prop _ (λ x y, _ ,, _) _).
  - apply isapropdirprod ;
    apply isapropimpl, propproperty.
  - intros x y.
    split.
    + apply abmonoidfrac_Lle_1.
    + apply abmonoidfrac_Lle_2.
Qed.

(** *** lattice with a strong order in [abmonoidfrac] *)

Section abmonoidfrac_latticewithgt.

Context (X : abmonoid)
        (Y : @submonoid X)
        (is : lattice X)
        (gt : StrongOrder X)
        (Hnotgtle : ∏ x y : X, ¬ gt x y → Lle is x y)
        (Hlenotgt : ∏ x y : X, Lle is x y → ¬ gt x y)
        (Hgtmin : ∏ x y z : X, gt x z → gt y z → gt (Lmin is x y) z)
        (Hgtmax : ∏ x y z : X, gt z x → gt z y → gt z (Lmax is x y))

        (Hgt : ispartbinophrel Y gt)
        (Hop : ∏ (x : Y) (y z : X), y * pr1 x = z * pr1 x → y = z)
        (Hmin : ispartrdistr Y (Lmin is) op)
        (Hmax : ispartrdistr Y (Lmax is) op).

Lemma abmonoidfrac_notgtle :
  ∏ (x y : abmonoidfrac X Y),
  ¬ (StrongOrder_abmonoidfrac Y gt Hgt) x y
  → Lle (abmonoidfrac_lattice X Y is Hmin Hmax) x y.
Proof.
  simple refine (setquotuniv2prop (eqrelabmonoidfrac X Y) (λ _ _, _ ,, _) _).
  - apply isapropimpl, propproperty.
  - intros x y H.
    apply abmonoidfrac_Lle.
    unfold abmonoidfracrel, quotrel.
    rewrite setquotuniv2comm.
    apply hinhpr.
    exists (pr2 x).
    apply Hnotgtle.
    intros H0 ; apply H.
    change (abmonoidfracrel X Y Hgt
                            (setquotpr (eqrelabmonoidfrac X Y) x)
                            (setquotpr (eqrelabmonoidfrac X Y) y)).
    unfold abmonoidfracrel, quotrel.
    rewrite setquotuniv2comm.
    apply hinhpr.
    exists (pr2 x).
    exact H0.
Qed.

Lemma abmonoidfrac_lenotgt :
  ∏ (x y : abmonoidfrac X Y),
  Lle (abmonoidfrac_lattice X Y is Hmin Hmax) x y
  → ¬ (StrongOrder_abmonoidfrac Y gt Hgt) x y.
Proof.
  simple refine (setquotuniv2prop (eqrelabmonoidfrac X Y) (λ _ _, _ ,, _) _).
  + apply isapropimpl, isapropimpl, isapropempty.
  + intros x y H.
    apply (pr2 (abmonoidfrac_Lle _ _ _ _ _ _ _)) in H.
    change (abmonoidfracrel X Y Hgt
                            (setquotpr (eqrelabmonoidfrac X Y) x)
                            (setquotpr (eqrelabmonoidfrac X Y) y) → ∅).
    revert H.
    unfold abmonoidfracrel, quotrel.
    do 2 rewrite setquotuniv2comm.
    apply (hinhuniv2 (P := hProppair _ isapropempty)).
    intros c c'.
    refine (Hlenotgt _ _ _ _).
    2: apply (pr2 c').
    unfold Lle.
    rewrite <- Hmin.
    apply (maponpaths (λ x, op x _)).
    apply (Hop (pr1 c)).
    rewrite Hmin.
    apply (pr2 c).
Qed.

Lemma abmonoidfrac_gtmin :
  ∏ (x y z : abmonoidfrac X Y),
  (StrongOrder_abmonoidfrac Y gt Hgt) x z
  → (StrongOrder_abmonoidfrac Y gt Hgt) y z
  → (StrongOrder_abmonoidfrac Y gt Hgt)
      (Lmin (abmonoidfrac_lattice X Y is Hmin Hmax) x y) z.
Proof.
  simple refine (setquotuniv3prop (eqrelabmonoidfrac X Y) (λ _ _ _, _ ,, _) _).
  - apply isapropimpl, isapropimpl, propproperty.
  - intros x y z.
    change (abmonoidfracrel X Y Hgt (setquotpr (eqrelabmonoidfrac X Y) x) (setquotpr (eqrelabmonoidfrac X Y) z)
            → abmonoidfracrel X Y Hgt (setquotpr (eqrelabmonoidfrac X Y) y) (setquotpr (eqrelabmonoidfrac X Y) z)
            → abmonoidfracrel X Y Hgt (abmonoidfrac_min X Y Hmin (setquotpr (eqrelabmonoidfrac X Y) x) (setquotpr (eqrelabmonoidfrac X Y) y)) (setquotpr (eqrelabmonoidfrac X Y) z)).
    unfold abmonoidfrac_min, abmonoidfracrel, quotrel.
    rewrite setquotfun2comm ;
      do 3 rewrite setquotuniv2comm.
    apply hinhfun2.
    intros cx cy.
    unfold abmonoidfrac_lattice_fun.
    rewrite rewrite_pr1_tpair, rewrite_pr2_tpair.
    exists (@op Y (pr1 cx) (pr1 cy)).
    do 2 rewrite Hmin.
    apply Hgtmin.
    + change (gt (pr1 x * pr1 (pr2 y) * pr1 (pr2 z) * (pr1 (pr1 cx) * pr1 (pr1 cy)))
                 (pr1 z * (pr1 (pr2 x) * pr1 (pr2 y)) * (pr1 (pr1 cx) * pr1 (pr1 cy)))).
      rewrite (assocax X (pr1 x)).
      rewrite (commax X (pr1 (pr2 y))).
      rewrite <- (assocax X (pr1 x)), <- (assocax X (pr1 z)).
      rewrite (assocax X (pr1 x * pr1 (pr2 z))%multmonoid), (assocax X (pr1 z * pr1 (pr2 x))%multmonoid).
      generalize (commax X (pr1 (pr2 y)) (pr1 (pr1 cx) * pr1 (pr1 cy))).
      intros ->.
      do 2 rewrite <- (assocax X (pr1 x * pr1 (pr2 z))%multmonoid), <- (assocax X (pr1 z * pr1 (pr2 x))%multmonoid).
      apply (pr2 Hgt).
      apply (pr2 (pr2 y)).
      apply (pr2 Hgt).
      apply (pr2 (pr1 cy)).
      apply (pr2 cx).
    + change (gt (pr1 y * pr1 (pr2 x) * pr1 (pr2 z) * (pr1 (pr1 cx) * pr1 (pr1 cy)))
                 (pr1 z * (pr1 (pr2 x) * pr1 (pr2 y)) * (pr1 (pr1 cx) * pr1 (pr1 cy)))).
      rewrite (commax X (pr1 (pr1 cx))).
      rewrite (assocax X (pr1 y)).
      do 2 rewrite (commax X (pr1 (pr2 x))).
      rewrite <- (assocax X (pr1 y)), <- (assocax X (pr1 z)).
      rewrite (assocax X (pr1 y * pr1 (pr2 z))%multmonoid), (assocax X (pr1 z * pr1 (pr2 y))%multmonoid).
      rewrite (commax X (pr1 (pr2 x))).
      do 2 rewrite <- (assocax X (pr1 y * pr1 (pr2 z))%multmonoid), <- (assocax X (pr1 z * pr1 (pr2 y))%multmonoid).
      apply (pr2 Hgt).
      apply (pr2 (pr2 x)).
      apply (pr2 Hgt).
      apply (pr2 (pr1 cx)).
      apply (pr2 cy).
Qed.

Lemma abmonoidfrac_gtmax :
  ∏ (x y z : abmonoidfrac X Y),
  (StrongOrder_abmonoidfrac Y gt Hgt) z x
  → (StrongOrder_abmonoidfrac Y gt Hgt) z y
    → (StrongOrder_abmonoidfrac Y gt Hgt) z
         (Lmax (abmonoidfrac_lattice X Y is Hmin Hmax) x y).
Proof.
  simple refine (setquotuniv3prop (eqrelabmonoidfrac X Y) (λ _ _ _, _ ,, _) _).
  - apply isapropimpl, isapropimpl, propproperty.
  - intros x y z.
    change (abmonoidfracrel X Y Hgt (setquotpr (eqrelabmonoidfrac X Y) z) (setquotpr (eqrelabmonoidfrac X Y) x)
            → abmonoidfracrel X Y Hgt (setquotpr (eqrelabmonoidfrac X Y) z) (setquotpr (eqrelabmonoidfrac X Y) y)
            → abmonoidfracrel X Y Hgt (setquotpr (eqrelabmonoidfrac X Y) z) (abmonoidfrac_max X Y Hmax (setquotpr (eqrelabmonoidfrac X Y) x) (setquotpr (eqrelabmonoidfrac X Y) y))).
    unfold abmonoidfrac_max, abmonoidfracrel, quotrel.
    rewrite setquotfun2comm ;
      do 3 rewrite setquotuniv2comm.
    apply hinhfun2.
    intros cx cy.
    unfold abmonoidfrac_lattice_fun.
    change (∑ c0 : Y,
  gt
    (pr1 z * pr1 (pr2 x * pr2 y) * pr1 c0)
    (Lmax is (pr1 x * pr1 (pr2 y)) (pr1 y * pr1 (pr2 x)) *
     pr1 (pr2 z) * pr1 c0)).
    exists (@op Y (pr1 cx) (pr1 cy)).
    do 2 rewrite Hmax.
    apply Hgtmax.
    + change (gt (pr1 z * (pr1 (pr2 x) * pr1 (pr2 y)) * (pr1 (pr1 cx) * pr1 (pr1 cy)))
    (pr1 x * pr1 (pr2 y) * pr1 (pr2 z) * (pr1 (pr1 cx) * pr1 (pr1 cy)))).
      rewrite (assocax X (pr1 x)).
      rewrite (commax X (pr1 (pr2 y))).
      rewrite <- (assocax X (pr1 x)), <- (assocax X (pr1 z)).
      rewrite (assocax X (pr1 x * pr1 (pr2 z))%multmonoid), (assocax X (pr1 z * pr1 (pr2 x))%multmonoid).
      generalize (commax X (pr1 (pr2 y)) (pr1 (pr1 cx) * pr1 (pr1 cy))).
      intros ->.
      do 2 rewrite <- (assocax X (pr1 x * pr1 (pr2 z))%multmonoid), <- (assocax X (pr1 z * pr1 (pr2 x))%multmonoid).
      apply (pr2 Hgt).
      apply (pr2 (pr2 y)).
      apply (pr2 Hgt).
      apply (pr2 (pr1 cy)).
      apply (pr2 cx).
    + change (gt (pr1 z * (pr1 (pr2 x) * pr1 (pr2 y)) * (pr1 (pr1 cx) * pr1 (pr1 cy)))
    (pr1 y * pr1 (pr2 x) * pr1 (pr2 z) * (pr1 (pr1 cx) * pr1 (pr1 cy)))).
      rewrite (commax X (pr1 (pr1 cx))).
      rewrite (assocax X (pr1 y)).
      do 2 rewrite (commax X (pr1 (pr2 x))).
      rewrite <- (assocax X (pr1 y)), <- (assocax X (pr1 z)).
      rewrite (assocax X (pr1 y * pr1 (pr2 z))%multmonoid), (assocax X (pr1 z * pr1 (pr2 y))%multmonoid).
      rewrite (commax X (pr1 (pr2 x))).
      do 2 rewrite <- (assocax X (pr1 y * pr1 (pr2 z))%multmonoid), <- (assocax X (pr1 z * pr1 (pr2 y))%multmonoid).
      apply (pr2 Hgt).
      apply (pr2 (pr2 x)).
      apply (pr2 Hgt).
      apply (pr2 (pr1 cx)).
      apply (pr2 cy).
Qed.

End abmonoidfrac_latticewithgt.

Definition abmonoidfrac_latticewithgt (X : abmonoid) (Y : @submonoid X) (is : latticewithgt X)
           (Hgt : ispartbinophrel Y (Lgt is))
           (Hop : ∏ (x : Y) (y z : X), y * pr1 x = z * pr1 x → y = z)
           (Hmin : ispartrdistr Y (Lmin is) op) (Hmax : ispartrdistr Y (Lmax is) op) : latticewithgt (abmonoidfrac X Y).
Proof.
  intros X Y is Hgt Hop Hmin Hmax.
  mkpair.
  refine (abmonoidfrac_lattice _ _ _ _ _).
  exact Hmin.
  exact Hmax.
  mkpair.
  simple refine (StrongOrder_abmonoidfrac _ _ _).
  apply (Lgt is).
  apply Hgt.
  split ; split.
  - apply abmonoidfrac_notgtle.
    apply notLgt_Lle.
  - apply abmonoidfrac_lenotgt.
    apply Lle_notLgt.
    apply Hop.
  - apply abmonoidfrac_gtmin.
    apply Lmin_Lgt.
  - apply abmonoidfrac_gtmax.
    apply Lmax_Lgt.
Defined.

(** *** lattice with a decidable order in [abmonoidfrac] *)

Lemma istotal_Lle_abmonoidfrac {X : abmonoid} (Y : @submonoid X) (is : lattice X) (is' : istotal (Lle is))
           (Hmin : ispartrdistr Y (Lmin is) op) (Hmax : ispartrdistr Y (Lmax is) op) :
  istotal (Lle (abmonoidfrac_lattice X Y is Hmin Hmax)).
Proof.
  intros X Y is is' Hmin Hmax.
  refine (istotallogeqf _ _).
  - apply abmonoidfrac_Lle.
  - apply istotalabmonoidfracrel, is'.
Qed.
Lemma isdecrel_Lle_abmonoidfrac {X : abmonoid} (Y : @submonoid X) (is : lattice X) (is' : isdecrel (Lle is))
           (Hop : ∏ (x : Y) (y z : X), y * pr1 x = z * pr1 x → y = z)
           (Hmin : ispartrdistr Y (Lmin is) op) (Hmax : ispartrdistr Y (Lmax is) op) :
  isdecrel (Lle (abmonoidfrac_lattice X Y is Hmin Hmax)).
Proof.
  intros X Y is is' Hop Hmin Hmax.
  refine (isdecrellogeqf _ _).
  - apply abmonoidfrac_Lle.
  - apply isdecabmonoidfracrel.
    split.
    + clear -Hmin Hop.
      intros x y z Hz ;
        rewrite !(commax X z) ;
        unfold Lle ;
        rewrite <- (Hmin _ _ (z,,Hz)) ;
        apply Hop.
    + clear -Hmin Hop.
      intros x y z Hz ;
        unfold Lle ;
        rewrite <- (Hmin _ _ (z,,Hz)) ;
        apply Hop.
    + apply is'.
Qed.

Definition abmonoidfrac_latticedec {X : abmonoid} (Y : @submonoid X) (is : latticedec X)
           (Hop : ∏ (x : Y) (y z : X), y * pr1 x = z * pr1 x → y = z)
           (Hmin : ispartrdistr Y (Lmin is) op) (Hmax : ispartrdistr Y (Lmax is) op) :
  latticedec (abmonoidfrac X Y).
Proof.
  intros X Y is Hop Hmin Hmax.
  mkpair.
  apply (abmonoidfrac_lattice X Y is Hmin Hmax).
  split.
  - apply istotal_Lle_abmonoidfrac.
    apply istotal_latticedec.
  - apply isdecrel_Lle_abmonoidfrac.
    + apply isdecrel_latticedec.
    + apply Hop.
Defined.

Close Scope multmonoid.

(** ** lattice in [abgrdiff] *)

Open Scope addmonoid.

Lemma abgrdiff_setquotpr_equiv {X : abmonoid} :
  ∏ k x y : X,
  setquotpr (eqrelabgrdiff X) (x,,y) = setquotpr (eqrelabgrdiff X) (x + k,,y + k).
Proof.
  intros X k x y.
  apply iscompsetquotpr, hinhpr.
  exists 0 ; simpl.
  rewrite !(assocax X), !runax, (commax X y).
  reflexivity.
Qed.

Definition abgrdiff_lattice {X : abmonoid}
           (is : lattice X)
           (Hmin : isrdistr (Lmin is) op)
           (Hmax : isrdistr (Lmax is) op) :
  lattice (abgrdiff X) :=
  lattice_weq (weqabgrdiff X)
                (abmonoidfrac_lattice X (totalsubmonoid X) is
                                        (λ (x y : X) (k : totalsubmonoid X), Hmin x y (pr1 k))
                                        (λ (x y : X) (k : totalsubmonoid X), Hmax x y (pr1 k))).

Lemma isbinophrel_abgrdiff_Lle (X : abmonoid) (is : lattice X)
      (Hmin : isrdistr (Lmin is) op) :
  isbinophrel (Lle is).
Proof.
  intros X is Hmin.
  split.
  - intros a b c H.
    rewrite !(commax _ c).
    apply op_le_r.
    exact Hmin.
    exact H.
  - intros a b c H.
    apply op_le_r.
    exact Hmin.
    exact H.
Qed.

Lemma abgrdiff_Lle_1 (X : abmonoid) (is : lattice X)
      (Hmin : isrdistr (Lmin is) op) :
  ∏ (x y : X × X),
  abgrdiffrel X (isbinophrel_abgrdiff_Lle X is Hmin) (setquotpr (eqrelabgrdiff X) x) (setquotpr (eqrelabgrdiff X) y)
  → invmap (weqabgrdiff X)
    (abmonoidfrac_min X (totalsubmonoid X)
       (λ x y k, Hmin x y (pr1 k))
       ((weqabgrdiff X) (setquotpr (eqrelabgrdiff X) x))
       ((weqabgrdiff X) (setquotpr (eqrelabgrdiff X) y))) =
  setquotpr (eqrelabgrdiff X) x.
Proof.
  intros X is Hmin.
  intros x y.
  intros Hle.
  apply pathsinv0, pathsweq1, pathsinv0.
  refine (abmonoidfrac_Lle_1 X (totalsubmonoid X) is (λ _ _ _, Hmin _ _ _) (pr1 x ,, pr2 x ,, tt) (pr1 y ,, pr2 y ,, tt) _).
  revert Hle.
  unfold abgrdiffrel, abmonoidfracrel, quotrel.
  do 2 rewrite setquotuniv2comm.
  apply hinhfun.
  intros c.
  exists (pr1 c ,, tt).
  exact (pr2 c).
Qed.
Lemma abgrdiff_Lle_2 (X : abmonoid) (is : lattice X)
      (Hmin : isrdistr (Lmin is) op) :
  ∏ (x y : X × X),
  invmap (weqabgrdiff X)
    (abmonoidfrac_min X (totalsubmonoid X)
       (λ x y k, Hmin x y (pr1 k))
       ((weqabgrdiff X) (setquotpr (eqrelabgrdiff X) x))
       ((weqabgrdiff X) (setquotpr (eqrelabgrdiff X) y))) =
  setquotpr (eqrelabgrdiff X) x
  → abgrdiffrel X (isbinophrel_abgrdiff_Lle X is Hmin) (setquotpr (eqrelabgrdiff X) x) (setquotpr (eqrelabgrdiff X) y).
Proof.
  intros X is Hmin.
  intros x y Hle.
  apply pathsinv0, pathsweq1', pathsinv0 in Hle.
  generalize (abmonoidfrac_Lle_2 X (totalsubmonoid X) is (λ _ _ _, Hmin _ _ _) (pr1 x ,, pr2 x ,, tt) (pr1 y ,, pr2 y ,, tt) Hle) ; clear Hle.
  unfold abgrdiffrel, abmonoidfracrel, quotrel.
  do 2 rewrite setquotuniv2comm.
  apply hinhfun.
  intros c.
  exists (pr1 (pr1 c)).
  exact (pr2 c).
Qed.
Lemma abgrdiff_Lle (X : abmonoid) (is : lattice X)
      (Hmin : isrdistr (Lmin is) op) (Hmax : isrdistr (Lmax is) op) :
  ∏ x y : abgrdiff X, abgrdiffrel X (isbinophrel_abgrdiff_Lle X is Hmin) x y <-> Lle (abgrdiff_lattice is Hmin Hmax) x y.
Proof.
  intros X is Hmin Hmax.
  simple refine (setquotuniv2prop _ (λ _ _, hProppair _ _) _).
  - apply isapropdirprod ;
    apply isapropimpl, propproperty.
  - intros x y.
    split.
    + apply abgrdiff_Lle_1.
    + apply abgrdiff_Lle_2.
Qed.

Definition abgrdiff_latticewithgt {X : abmonoid} (is : latticewithgt X) (Hgt : isbinophrel (Lgt is))
           (Hop : ∏ x y z : X, y + x = z + x → y = z)
           (Hmin : isrdistr (Lmin is) op) (Hmax : isrdistr (Lmax is) op) :
  latticewithgt (abgrdiff X).
Proof.
  intros X is Hgt Hop Hmin Hmax.
  refine (latticewithgt_weq _ _).
  apply (weqabgrdiff X).
  apply abmonoidfrac_latticewithgt with is.
  - split ; intros x y z Hz.
    + apply (pr1 Hgt).
    + apply (pr2 Hgt).
  - intros x y z.
    apply Hop.
  - intros x y k.
    apply Hmin.
  - intros x y k.
    apply Hmax.
Defined.

Definition abgrdiff_latticedec {X : abmonoid} (is : latticedec X)
           (Hop : ∏ x y z : X, y + x = z + x → y = z)
           (Hmin : isrdistr (Lmin is) op) (Hmax : isrdistr (Lmax is) op) :
  latticedec (abgrdiff X).
Proof.
  intros X is Hop Hmin Hmax.
  refine (latticedec_weq _ _).
  apply (weqabgrdiff X).
  apply abmonoidfrac_latticedec with is.
  - intros x y z.
    apply Hop.
  - intros x y k.
    apply Hmin.
  - intros x y k.
    apply Hmax.
Defined.

Close Scope addmonoid.

(** ** lattice in [commrngfrac] *)

Open Scope rng.

Definition commrngfrac_lattice (X : commrng) (Y : @subabmonoid (rngmultabmonoid X))
           (is : lattice X)
           (Hmin : ispartrdistr Y (Lmin is) op2) (Hmax : ispartrdistr Y (Lmax is) op2) :
  lattice (commrngfrac X Y) :=
  abmonoidfrac_lattice (rngmultabmonoid X) Y is Hmin Hmax.

Definition commrngfrac_latticewithgt (X : commrng) (Y : @subabmonoid (rngmultabmonoid X))
           (is : latticewithgt X)
           (Hgt : ispartbinophrel Y (Lgt is))
           (Hop : ∏ (x : Y) (y z : rngmultabmonoid X),
  (y * pr1 x = z * pr1 x)%rng → y = z)
           (Hmin : ispartrdistr Y (Lmin is) op2)
           (Hmax : ispartrdistr Y (Lmax is) op2) :
  latticewithgt (commrngfrac X Y).
Proof.
  intros X Y is Hgt Hop Hmin Hmax.
  apply (abmonoidfrac_latticewithgt (rngmultabmonoid X) Y is).
  - apply Hgt.
  - apply Hop.
  - apply Hmin.
  - apply Hmax.
Defined.

Definition commrngfrac_latticedec (X : commrng) (Y : @subabmonoid (rngmultabmonoid X))
           (is : latticedec X)
           (Hop : ∏ (x : Y) (y z : rngmultabmonoid X),
  (y * pr1 x = z * pr1 x)%rng → y = z)
           (Hmin : ispartrdistr Y (Lmin is) op2)
           (Hmax : ispartrdistr Y (Lmax is) op2) :
  latticedec (commrngfrac X Y).
Proof.
  intros X Y is Hop Hmin Hmax.
  apply (abmonoidfrac_latticedec Y is).
  - apply Hop.
  - apply Hmin.
  - apply Hmax.
Defined.

(** Lattice in fldfrac' *)

Definition fldfrac'_lattice {X : commrng} R is1 is2 (is : lattice X)
           (Hmin : @ispartrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmin is) op2)
           (Hmax : @ispartrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmax is) op2) :
  lattice (fldfrac' X R is1 is2) :=
  commrngfrac_lattice X (rngpossubmonoid X is1 is2) is Hmin Hmax.

Definition fldfrac'_latticewithgt {X : commrng} R is1 is2
           (is : latticewithgt X)
           (Hgt : ispartbinophrel (rngpossubmonoid X is1 is2) (Lgt is))
           (Hop : ∏ (x : rngpossubmonoid X is1 is2) (y z : rngmultabmonoid X),
 (y * pr1 x = z * pr1 x)%rng → y = z)
           (Hmin : @ispartrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmin is) op2)
           (Hmax : @ispartrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmax is) op2) :
  latticewithgt (fldfrac' X R is1 is2).
Proof.
  intros X R is1 is2 is Hgt Hop Hmin Hmax.
  apply commrngfrac_latticewithgt with is.
  - apply Hgt.
  - apply Hop.
  - apply Hmin.
  - apply Hmax.
Defined.

Definition fldfrac'_latticedec {X : commrng} R is1 is2
           (is : latticedec X)
           (Hop : ∏ (x : rngpossubmonoid X is1 is2) (y z : rngmultabmonoid X),
 (y * pr1 x = z * pr1 x)%rng → y = z)
           (Hmin : @ispartrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmin is) op2)
           (Hmax : @ispartrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmax is) op2) :
  latticedec (fldfrac' X R is1 is2).
Proof.
  intros X R is1 is2 is Hop Hmin Hmax.
  apply commrngfrac_latticedec with is.
  - apply Hop.
  - apply Hmin.
  - apply Hmax.
Defined.

(** Lattice in fldfrac *)

Definition fldfrac_lattice {X : intdom} (is' : isdeceq X) (R : hrel X) (is0 : isbinophrel (X := rigaddabmonoid X) R)
           (is1 : isrngmultgt X R) (is2 : R 1%rng 0%rng) (is3 : isirrefl R) (nc : neqchoice R)
           (is : lattice X)
           (Hmin : @ispartrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmin is) op2)
           (Hmax : @ispartrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmax is) op2) :
  lattice (fldfrac X is') :=
  lattice_weq (weqfldfracgt X is' is0 is1 is2 nc is3)
                (commrngfrac_lattice X (rngpossubmonoid X is1 is2) is Hmin Hmax).

Definition fldfrac_latticewithgt {X : intdom} (is' : isdeceq X) (R : hrel X) (is0 : isbinophrel (X := rigaddabmonoid X) R)
           (is1 : isrngmultgt X R) (is2 : R 1%rng 0%rng) (is3 : isirrefl R) (nc : neqchoice R)
           (is : latticewithgt X)
           (Hgt : ispartbinophrel (rngpossubmonoid X is1 is2) (Lgt is))
           (Hop : ∏ (x : rngpossubmonoid X is1 is2) (y z : rngmultabmonoid X),
 (y * pr1 x = z * pr1 x)%rng → y = z)
           (Hmin : @ispartrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmin is) op2)
           (Hmax : @ispartrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmax is) op2) :
  latticewithgt (fldfrac X is').
Proof.
  intros X is' R is0 is1 is2 is3 nc is Hgt Hop Hmin Hmax.
  apply (latticewithgt_weq (weqfldfracgt X is' is0 is1 is2 nc is3)).
  apply fldfrac'_latticewithgt with is.
  - apply Hgt.
  - apply Hop.
  - apply Hmin.
  - apply Hmax.
Defined.

Definition fldfrac_latticedec {X : intdom} (is' : isdeceq X) (R : hrel X) (is0 : isbinophrel (X := rigaddabmonoid X) R)
          (is1 : isrngmultgt X R) (is2 : R 1%rng 0%rng) (is3 : isirrefl R) (nc : neqchoice R)
          (is : latticedec X)
          (Hop : ∏ (x : rngpossubmonoid X is1 is2) (y z : rngmultabmonoid X),
                 (y * pr1 x = z * pr1 x)%rng → y = z)
          (Hmin : @ispartrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmin is) op2)
          (Hmax : @ispartrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmax is) op2) :
  latticedec (fldfrac X is').
Proof.
  intros X is' R is0 is1 is2 is3 nc is Hop Hmin Hmax.
  apply (latticedec_weq (weqfldfracgt X is' is0 is1 is2 nc is3)).
  apply fldfrac'_latticedec with is.
  - apply Hop.
  - apply Hmin.
  - apply Hmax.
Defined.

Close Scope rng.