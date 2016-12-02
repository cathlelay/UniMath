(** * Lattice *)
(** Catherine Lelay. Nov. 2016 - *)
(**
Definition of a lattice: (Burris, S., & Sankappanavar, H. P. (2006).
A Course in Universal Algebra-With 36 Illustrations. Chapter I)
A lattice is a set with two binary operators min and max such that:
- min and max are associative
- min and max are commutative
- Π x y : X, min x (max x y) = x
- Π x y : X, max x (min x y) = x

In a lattice, we can define a partial order:
- le := λ (x y : X), min is x y = x

Lattice with a strict order:
A lattice with a strict order gt is lattice such that:
- Π (x y : X), (¬ gt x y) <-> le x y
- Π x y z : X, gt x z → gt y z → gt (min x y) z
- Π x y z : X, gt z x → gt z y → gt z (max is x y)

Lattice with a total and decidable order :
- le is total and decidable
- it is a lattice with a strong order *)

Require Export UniMath.Foundations.Algebra.BinaryOperations.
Require Export UniMath.Foundations.Algebra.Monoids_and_Groups.
Require Export UniMath.Foundations.Algebra.Domains_and_Fields.

Unset Automatic Introduction.

(** ** Strong Order *)
(* todo : move it into UniMath.Foundations.Basics.Sets *)

Definition isStrongOrder {X : UU} (R : hrel X) := istrans R × iscotrans R × isirrefl R.
Definition StrongOrder (X : UU) := Σ R : hrel X, isStrongOrder R.
Definition pairStrongOrder {X : UU} (R : hrel X) (is : isStrongOrder R) : StrongOrder X :=
  tpair (fun R : hrel X => isStrongOrder R ) R is.
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

Lemma isStrongOrder_setquot {X : UU} {R : eqrel X} {L : hrel X} (is : iscomprelrel R L) :
  isStrongOrder L → isStrongOrder (quotrel is).
Proof.
  intros X R L is H.
  split ; [ | split].
  - apply istransquotrel, (pr1 H).
  - apply iscotransquotrel, (pr1 (pr2 H)).
  - apply isirreflquotrel, (pr2 (pr2 H)).
Qed.
Definition StrongOrder_setquot {X : UU} {R : eqrel X} {L : StrongOrder X} (is : iscomprelrel R L) : StrongOrder (setquot R) :=
  quotrel is,, isStrongOrder_setquot is (pr2 L).

Lemma isStrongOrder_abgrdiff {X : abmonoid} (gt : hrel X) (Hgt : isbinophrel gt) :
  isStrongOrder gt → isStrongOrder (abgrdiffrel X Hgt).
Proof.
  intros X gt Hgt H.
  split ; [ | split].
  - apply istransabgrdiffrel, (pr1 H).
  - apply iscotransabgrdiffrel, (pr1 (pr2 H)).
  - apply isirreflabgrdiffrel, (pr2 (pr2 H)).
Qed.
Definition StrongOrder_abgrdiff {X : abmonoid} (gt : StrongOrder X) (Hgt : isbinophrel gt) : StrongOrder (abgrdiff X) :=
  abgrdiffrel X Hgt,, isStrongOrder_abgrdiff gt Hgt (pr2 gt).

(** ** Definition *)

Definition islatticeop {X : hSet} (min max : binop X) :=
  ((isassoc min) × (iscomm min))
    × ((isassoc max) × (iscomm max))
    × (Π x y : X, min x (max x y) = x)
    × (Π x y : X, max x (min x y) = x).
Definition islattice (X : hSet) := Σ min max : binop X, islatticeop min max.
Definition lattice := Σ X : setwith2binop, islatticeop (X := X) op1 op2.

Definition pr1lattice : lattice → setwith2binop := pr1.
Coercion pr1lattice : lattice >-> setwith2binop.
Definition mklattice {X : hSet} {min max : binop X} : islatticeop min max → lattice :=
  λ (is : islatticeop min max), (X,, min,, max),, is.

Definition lattice2islattice : Π X : lattice, islattice X :=
  λ X : lattice, op1,, op2,, pr2 X.
Definition islattice2lattice : Π X : hSet, islattice X → lattice :=
λ (X : hSet) (is : islattice X), mklattice (pr2 (pr2 is)).

Definition Lmin {X : hSet} (is : islattice X) : binop X := pr1 is.
Definition Lmax {X : hSet} (is : islattice X) : binop X := pr1 (pr2 is).

Section lattice_pty.

Context {X : hSet}
        (is : islattice X).

Definition isassoc_Lmin : isassoc (Lmin is) :=
  pr1 (pr1 (pr2 (pr2 is))).
Definition iscomm_Lmin : iscomm (Lmin is) :=
  pr2 (pr1 (pr2 (pr2 is))).
Definition isassoc_Lmax : isassoc (Lmax is) :=
  pr1 (pr1 (pr2 (pr2 (pr2 is)))).
Definition iscomm_Lmax : iscomm (Lmax is) :=
  pr2 (pr1 (pr2 (pr2 (pr2 is)))).
Definition Lmin_absorb :
  Π x y : X, Lmin is x (Lmax is x y) = x :=
  pr1 (pr2 (pr2 (pr2 (pr2 is)))).
Definition Lmax_absorb :
  Π x y : X, Lmax is x (Lmin is x y) = x :=
  pr2 (pr2 (pr2 (pr2 (pr2 is)))).

Lemma Lmin_id :
  Π x : X, Lmin is x x = x.
Proof.
  intros x.
  apply (pathscomp0 (b := Lmin is x (Lmax is x (Lmin is x x)))).
  - apply maponpaths, pathsinv0, Lmax_absorb.
  - apply Lmin_absorb.
Qed.
Lemma Lmax_id :
  Π x : X, Lmax is x x = x.
Proof.
  intros x.
  apply (pathscomp0 (b := Lmax is x (Lmin is x (Lmax is x x)))).
  - apply maponpaths, pathsinv0, Lmin_absorb.
  - apply Lmax_absorb.
Qed.

End lattice_pty.

(** lattice weq *)

Definition islattice_weq {X Y : hSet} (H : weq Y X) (is : islattice X) : islattice Y.
Proof.
  intros X Y H is.
  mkpair.
  - intros x y.
    apply (invmap H).
    simple refine (Lmin is _ _).
    apply (pr1weq H x).
    apply (pr1weq H y).
  - mkpair.
    + intros x y.
      apply (invmap H).
      simple refine (Lmax is _ _).
      apply (pr1weq H x).
      apply (pr1weq H y).
    + split ; [ | split] ; split.
      * intros x y z.
        refine (pathscomp0 _ _).
        refine (maponpaths (λ t, invmap H (Lmin is t _)) _).
        apply homotweqinvweq.
        refine (pathscomp0 _ _).
        apply maponpaths, isassoc_Lmin.
        refine (maponpaths (λ t, invmap H (Lmin is _ t)) _).
        apply pathsinv0, homotweqinvweq.
      * intros x y.
        apply maponpaths, iscomm_Lmin.
      * intros x y z.
        refine (pathscomp0 _ _).
        refine (maponpaths (λ t, invmap H (Lmax is t _)) _).
        apply homotweqinvweq.
        refine (pathscomp0 _ _).
        apply maponpaths, isassoc_Lmax.
        refine (maponpaths (λ t, invmap H (Lmax is _ t)) _).
        apply pathsinv0, homotweqinvweq.
      * intros x y.
        apply maponpaths, iscomm_Lmax.
      * intros x y.
        refine (pathscomp0 _ _).
        refine (maponpaths (λ t, invmap H (Lmin is _ t)) _).
        apply homotweqinvweq.
        refine (pathscomp0 _ _).
        apply maponpaths, Lmin_absorb.
        apply homotinvweqweq.
      * intros x y.
        refine (pathscomp0 _ _).
        refine (maponpaths (λ t, invmap H (Lmax is _ t)) _).
        apply homotweqinvweq.
        refine (pathscomp0 _ _).
        apply maponpaths, Lmax_absorb.
        apply homotinvweqweq.
Defined.

(** ** Partial order in a lattice *)

(** [Lle] *)

Definition Lle {X : hSet} (is : islattice X) : hrel X :=
  λ (x y : X), hProppair (Lmin is x y = x) ((pr2 X) (Lmin is x y) x).

Section lattice_le.

Context {X : hSet}
        (is : islattice X).

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
  Π x y : X, Lle is (Lmin is x y) x.
Proof.
  intros x y.
  simpl.
  rewrite iscomm_Lmin, <- isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma Lmin_le_r :
  Π x y : X, Lle is (Lmin is x y) y.
Proof.
  intros x y.
  rewrite iscomm_Lmin.
  apply Lmin_le_l.
Qed.
Lemma Lmin_le_case :
  Π x y z : X, Lle is z x → Lle is z y → Lle is z (Lmin is x y).
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
  Π x y : X, Lle is x (Lmax is x y).
Proof.
  intros x y.
  simpl.
  apply Lmin_absorb.
Qed.
Lemma Lmax_le_r :
  Π x y : X, Lle is y (Lmax is x y).
Proof.
  intros x y.
  rewrite iscomm_Lmax.
  apply Lmax_le_l.
Qed.
Lemma Lmax_le_case :
  isrdistr (Lmax is) (Lmin is)
  → Π x y z : X, Lle is x z → Lle is y z → Lle is (Lmax is x y) z.
Proof.
  intros H x y z <- <-.
  rewrite <- H.
  apply Lmin_le_r.
Qed.

Lemma Lmin_le_eq_l :
  Π x y : X, Lle is x y → Lmin is x y = x.
Proof.
  intros x y H.
  apply H.
Qed.
Lemma Lmin_le_eq_r :
  Π x y : X, Lle is y x → Lmin is x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmin.
  apply H.
Qed.

Lemma Lmax_le_eq_l :
  Π x y : X, Lle is y x → Lmax is x y = x.
Proof.
  intros x y <-.
  rewrite iscomm_Lmin.
  apply Lmax_absorb.
Qed.
Lemma Lmax_le_eq_r :
  Π x y : X, Lle is x y → Lmax is x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmax.
  now apply Lmax_le_eq_l.
Qed.

End lattice_le.

(** [Lge] *)

Definition Lge {X : hSet} (is : islattice X) : hrel X :=
  λ x y : X, Lle is y x.

Section Lge_pty.

Context {X : hSet}
        (is : islattice X).

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
  Π (x y : X), Lge is x (Lmin is x y) :=
  Lmin_le_l is.
Definition Lmin_ge_r :
  Π (x y : X), Lge is y (Lmin is x y) :=
  Lmin_le_r is.
Definition Lmin_ge_case :
  Π (x y z : X),
  Lge is x z → Lge is y z → Lge is (Lmin is x y) z :=
  Lmin_le_case is.

Definition Lmax_ge_l :
  Π (x y : X), Lge is (Lmax is x y) x :=
  Lmax_le_l is.
Definition Lmax_ge_r :
  Π (x y : X), Lge is (Lmax is x y) y :=
  Lmax_le_r is.
Definition Lmax_ge_case :
  isrdistr (Lmax is) (Lmin is)
  → Π x y z : X, Lge is z x → Lge is z y → Lge is z (Lmax is x y) :=
  Lmax_le_case is.

Definition Lmin_ge_eq_l :
  Π (x y : X), Lge is y x → Lmin is x y = x :=
  Lmin_le_eq_l is.
Definition Lmin_ge_eq_r :
  Π (x y : X), Lge is x y → Lmin is x y = y :=
  Lmin_le_eq_r is.

Definition Lmax_ge_eq_l :
  Π (x y : X), Lge is x y → Lmax is x y = x :=
  Lmax_le_eq_l is.
Definition Lmax_ge_eq_r :
  Π (x y : X), Lge is y x → Lmax is x y = y :=
  Lmax_le_eq_r is.

End Lge_pty.

(** ** Lattice with a strong order *)

Definition islatticewithgtrel {X : hSet} (is : islattice X) (gt : StrongOrder X) :=
  (Π x y : X, (¬ (gt x y)) <-> Lle is x y)
    × (Π x y z : X, gt x z → gt y z → gt (Lmin is x y) z)
    × (Π x y z : X, gt z x → gt z y → gt z (Lmax is x y)).

Definition islatticewithgt (X : hSet) :=
  Σ (is : islattice X) (gt : StrongOrder X), islatticewithgtrel is gt.

Definition islattice_islatticewithgt {X : hSet} : islatticewithgt X → islattice X :=
  pr1.
Coercion islattice_islatticewithgt : islatticewithgt >-> islattice.

(** [Lgt] *)

Definition Lgt {X : hSet} (is : islatticewithgt X) : StrongOrder X :=
  pr1 (pr2 is).

Section latticewithgt_pty.

Context {X : hSet}
        (is : islatticewithgt X).

Definition notLgt_Lle :
  Π x y : X, (¬ Lgt is x y) → Lle is x y :=
  λ x y : X, pr1 (pr1 (pr2 (pr2 is)) x y).
Definition Lle_notLgt :
  Π x y : X, Lle is x y → ¬ Lgt is x y :=
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
  Π x y : X, Lgt is x y → Lge is x y.
Proof.
  intros x y H.
  apply notLgt_Lle.
  intro H0.
  eapply isasymm_Lgt.
  exact H.
  exact H0.
Qed.

Lemma istrans_Lgt_Lge :
  Π x y z : X, Lgt is x y → Lge is y z → Lgt is x z.
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
  Π x y z : X, Lge is x y → Lgt is y z → Lgt is x z.
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
  Π x y z : X, Lgt is x z → Lgt is y z → Lgt is (Lmin is x y) z :=
  pr1 (pr2 (pr2 (pr2 is))).

Definition Lmax_Lgt :
  Π x y z : X, Lgt is z x → Lgt is z y → Lgt is z (Lmax is x y) :=
  pr2 (pr2 (pr2 (pr2 is))).

End latticewithgt_pty.

(** ** Lattice with a total order *)

Definition islatticedec (X : hSet) :=
  Σ is : islattice X, istotal (Lle is) × (isdecrel (Lle is)).
Definition islattice_islatticedec {X : hSet} (is : islatticedec X) : islattice X :=
  pr1 is.
Coercion islattice_islatticedec : islatticedec >-> islattice.
Definition istotal_islatticedec {X : hSet} (is : islatticedec X) : istotal (Lle is) :=
  pr1 (pr2 is).
Definition isdecrel_islatticedec {X : hSet} (is : islatticedec X) : isdecrel (Lle is) :=
  pr2 (pr2 is).

Section islatticedec_pty.

Context {X : hSet}
        (is : islatticedec X).

Lemma Lmin_case_strong :
  Π (P : X → UU) (x y : X),
  (Lle is x y → P x) → (Lle is y x → P y) → P (Lmin is x y).
Proof.
  intros P x y Hx Hy.
  generalize (isdecrel_islatticedec is x y).
  apply sumofmaps ; intros H.
  - rewrite Lmin_le_eq_l.
    apply Hx, H.
    exact H.
  - enough (H0 : Lle is y x).
    + rewrite Lmin_le_eq_r.
      apply Hy, H0.
      exact H0.
    + generalize (istotal_islatticedec is x y).
      apply hinhuniv, sumofmaps ; intros H0.
      apply fromempty, H, H0.
      exact H0.
Qed.
Lemma Lmin_case :
  Π (P : X → UU) (x y : X),
  P x → P y → P (Lmin is x y).
Proof.
  intros P x y Hx Hy.
  apply Lmin_case_strong ; intros _.
  - exact Hx.
  - exact Hy.
Qed.

Lemma Lmax_case_strong :
  Π (P : X → UU) (x y : X),
  (Lle is y x → P x) → (Lle is x y → P y) → P (Lmax is x y).
Proof.
  intros P x y Hx Hy.
  generalize (isdecrel_islatticedec is x y).
  apply sumofmaps ; intros H.
  - rewrite Lmax_le_eq_r.
    apply Hy, H.
    exact H.
  - enough (H0 : Lle is y x).
    + rewrite Lmax_le_eq_l.
      apply Hx, H0.
      exact H0.
    + generalize (istotal_islatticedec is x y).
      apply hinhuniv, sumofmaps ; intros H0.
      apply fromempty, H, H0.
      exact H0.
Qed.
Lemma Lmax_case :
  Π (P : X → UU) (x y : X),
  P x → P y → P (Lmax is x y).
Proof.
  intros P x y Hx Hy.
  apply Lmax_case_strong ; intros _.
  - exact Hx.
  - exact Hy.
Qed.

End islatticedec_pty.

(** It is a lattice with a strong order *)

Section islatticedec_gt.

Context {X : hSet}
        (is : islatticedec X).

Definition latticedec_gt_rel : hrel X :=
  λ x y, hneg (Lle is x y).

Lemma latticedec_gt_ge :
  Π x y : X, latticedec_gt_rel x y → Lge is x y.
Proof.
  intros x y Hxy.
  generalize (istotal_islatticedec is x y).
  apply hinhuniv, sumofmaps ; intros H.
  - apply fromempty, Hxy.
    exact H.
  - exact H.
Qed.

Definition latticedec_gt : StrongOrder X.
Proof.
  mkpair.
  apply latticedec_gt_rel.
  split ; [ | split].
  - intros x y z Hxy Hyz Hxz.
    apply Hxy.
    apply istrans_Lle with z.
    apply Hxz.
    apply latticedec_gt_ge.
    exact Hyz.
  - intros x y z Hxz.
    induction (isdecrel_islatticedec is x y) as [Hxy | Hyx].
    + apply hinhpr, ii2.
      intros Hyz.
      apply Hxz.
      apply istrans_Lle with y.
      exact Hxy.
      exact Hyz.
    + apply hinhpr, ii1.
      exact Hyx.
  - intros x Hx.
    apply Hx.
    apply isrefl_Lle.
Defined.

Definition islatticedec_gt : islatticewithgt X.
Proof.
  mkpair.
  apply (pr1 is).
  mkpair.
  apply latticedec_gt.
  split ; split.
  - intros H.
    induction (isdecrel_islatticedec is x y) as [H0 | H0].
    + exact H0.
    + apply fromempty, H.
      exact H0.
  - intros H H0.
    apply H0, H.
  - intros x y z Hxz Hyz.
    apply (Lmin_case is (λ t : X, latticedec_gt t z)).
    + exact Hxz.
    + exact Hyz.
  - intros x y z Hxz Hyz.
    apply (Lmax_case is (latticedec_gt z)).
    + exact Hxz.
    + exact Hyz.
Defined.

End islatticedec_gt.

(** *** Lattice in an abmonoid *)

Local Open Scope addmonoid.

Section lattice_abmonoid.

Context {X : abmonoid}
        (is : islattice X)
        (is0 : Π x y z : X, y + x = z + x → y = z)
        (is1 : isrdistr (Lmax is) op)
        (is2 : isrdistr (Lmin is) op)
        (is3 : isrdistr (Lmin is) (Lmax is)).

Lemma op_le_r :
  Π k x y : X, Lle is x y → Lle is (x + k) (y + k).
Proof.
  intros k x y H.
  unfold Lle ; simpl.
  now rewrite <- is2, H.
Qed.
Lemma op_le_r' :
  Π k x y : X, Lle is (x + k) (y + k) → Lle is x y.
Proof.
  intros k x y H.
  apply (is0 k).
  now rewrite is2, H.
Qed.

End lattice_abmonoid.

(** ** Truncated minus *)

Definition istruncminus {X : abmonoid} (is : islattice X) (minus : binop X) :=
  Π x y : X, minus x y + y = Lmax is x y.

Definition extruncminus {X : abmonoid} (is : islattice X) :=
  Σ minus : binop X, istruncminus is minus.

Definition truncminus {X : abmonoid} {is : islattice X} (ex : extruncminus is) : binop X :=
  pr1 ex.

Lemma istruncminus_ex {X : abmonoid} {is : islattice X} (ex : extruncminus is) :
  Π x y : X, truncminus ex x y + y = Lmax is x y.
Proof.
  intros X is ex.
  apply (pr2 ex).
Qed.

Section truncminus_pty.

Context {X : abmonoid}
        {is : islattice X}
        (ex : extruncminus is)
        (is1 : Π x y z : X, y + x = z + x → y = z)
        (is2 : isrdistr (Lmax is) op)
        (is3 : isrdistr (Lmin is) op)
        (is4 : isrdistr (Lmin is) (Lmax is))
        (is5 : isrdistr (Lmax is) (Lmin is)).

Lemma truncminus_0_r :
  Π x : X, truncminus ex x 0 = Lmax is x 0.
Proof.
  intros x.
  rewrite <- (runax _ (truncminus _ _ _)).
  apply (istruncminus_ex).
Qed.

Lemma truncminus_eq_0 :
  Π x y : X, Lle is x y → truncminus ex x y = 0.
Proof.
  intros x y H.
  apply (is1 y).
  rewrite istruncminus_ex, lunax.
  apply Lmax_le_eq_r, H.
Qed.

Lemma truncminus_0_l_ge0 :
  Π x : X, Lle is 0 x → truncminus ex 0 x = 0.
Proof.
  intros x Hx.
  apply truncminus_eq_0, Hx.
Qed.
Lemma truncminus_0_l_le0 :
  Π x : X, Lle is x 0 → truncminus ex 0 x + x = 0.
Proof.
  intros x Hx.
  rewrite istruncminus_ex.
  apply Lmax_le_eq_l, Hx.
Qed.

Lemma truncminus_ge_0 :
  Π x y : X, Lle is 0 (truncminus ex x y).
Proof.
  intros x y.
  apply (op_le_r' _ is1 is3 y).
  rewrite istruncminus_ex, lunax.
  apply Lmax_ge_r.
Qed.

Lemma truncminus_le :
  Π x y : X,
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
  Π x y, Lle is 0 x → Lle is x y → truncminus ex y (truncminus ex y x) = x.
Proof.
  intros x y Hx Hxy.
  apply (is1 (truncminus ex y x)).
  rewrite (commax _ x), !istruncminus_ex.
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
  Π k x y : X, Lle is x y → Lle is (truncminus ex x k) (truncminus ex y k).
Proof.
  intros k x y <-.
  apply (is1 k).
  rewrite is3, !istruncminus_ex.
  rewrite is4, isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma truncminus_le_l :
  Π k x y : X, Lle is y x → Lle is (truncminus ex k x) (truncminus ex k y).
Proof.
  intros k x y H.
  apply (is1 y).
  rewrite is3, istruncminus_ex.
  apply (is1 x).
  rewrite is3, assocax, (commax _ y), <- assocax, istruncminus_ex.
  rewrite !is2, (commax _ y), <- is4, !(commax _ k), <- is3, H.
  reflexivity.
Qed.

Lemma truncminus_Lmax_l :
  Π (k x y : X),
  truncminus ex (Lmax is x y) k = Lmax is (truncminus ex x k) (truncminus ex y k).
Proof.
  intros k x y.
  apply (is1 k).
  rewrite is2, !istruncminus_ex.
  rewrite !isassoc_Lmax, (iscomm_Lmax _ k), isassoc_Lmax, Lmax_id.
  reflexivity.
Qed.
Lemma truncminus_Lmax_r :
  Π (k x y : X),
  Lle is (Lmin is (y + y) (x + x)) (x + y) →
  truncminus ex k (Lmax is x y) = Lmin is (truncminus ex k x) (truncminus ex k y).
Proof.
  intros k x y H.
  apply (is1 (Lmax is x y)).
  rewrite is3, istruncminus_ex.
  rewrite !(commax _ _ (Lmax _ _ _)), !is2.
  rewrite !(commax _ _ (truncminus _ _ _)), !istruncminus_ex.
  rewrite (iscomm_Lmax _ (_*_)%multmonoid (Lmax _ _ _)).
  rewrite !isassoc_Lmax, !(iscomm_Lmax _ k).
  rewrite <- is4.

  apply (is1 x).
  rewrite !is2, is3, !is2.
  rewrite assocax, (commax _ y x), <- assocax.
  rewrite istruncminus_ex, is2.

  apply (is1 y).
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
  Π k x y : X, truncminus ex (Lmin is x y) k = Lmin is (truncminus ex x k) (truncminus ex y k).
Proof.
  intros k x y.
  apply (is1 k).
  rewrite is3, !istruncminus_ex.
  apply is4.
Qed.

End truncminus_pty.

Lemma abgr_truncminus {X : abgr} (is : islattice X) :
  isrdistr (Lmax is) op →
  istruncminus (X := abgrtoabmonoid X) is (λ x y : X, Lmax is 0 (x + grinv X y)).
Proof.
  intros X is H x y.
  rewrite H, assocax, grlinvax, lunax, runax.
  apply iscomm_Lmax.
Qed.

Definition extruncminuswithgt {X : abmonoid} (is : islatticewithgt X) :=
  Σ (ex : extruncminus is), Π x y : X, Lgt is (truncminus ex x y) 0 → Lgt is x y.
Definition extruncminuswithgt_extruncminus {X : abmonoid} (is : islatticewithgt X) :
  extruncminuswithgt is → extruncminus is := pr1.
Coercion extruncminuswithgt_extruncminus : extruncminuswithgt >-> extruncminus.

Section truncminus_gt.

Context {X : abmonoid}
        (is : islatticewithgt X)
        (ex : extruncminuswithgt is)
        (is0 : Π x y z : X, Lgt is y z → Lgt is (y + x) (z + x))
        (is1 : Π x y z : X, Lgt is (y + x) (z + x) → Lgt is y z).

Lemma truncminus_pos :
  Π x y : X, Lgt is x y → Lgt is (truncminus ex x y) 0.
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
  Π x y : X, Lgt is (truncminus ex x y) 0 → Lgt is x y.
Proof.
  exact (pr2 ex).
Qed.

End truncminus_gt.

(** *** Truncated minus and abgrdiff *)

Section abgrdiff_minus.

Context {X : abmonoid}
        {is : islattice X}
        (ex : extruncminus is)
        (is1 : Π x y z : X, y + x = z + x → y = z)
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

(** ** lattice in abmonoid *)

Lemma abmonoidfrac_setquotpr_equiv {X : abmonoid} {Y : @submonoids X} :
  Π (k : Y) (x : X) (y : Y),
  setquotpr (binopeqrelabmonoidfrac X Y) (x,,y) = setquotpr (binopeqrelabmonoidfrac X Y) (x + pr1 k,, @op Y y k).
Proof.
  intros X Y k x y.
  apply iscompsetquotpr, hinhpr.
  exists y ; simpl.
  rewrite !(assocax X) ;
    apply maponpaths.
  rewrite commax, !assocax.
  reflexivity.
Qed.

Definition issubrdistr {X : abmonoid} (Y : @submonoids X) (opp1 opp2 : binop X) :=
  Π (x y : X) (k : Y),
  opp2 (opp1 x y) (pr1 k) = opp1 (opp2 x (pr1 k)) (opp2 y (pr1 k)).

Section abmonoidfrac_lattice.

Context (X : abmonoid)
        (Y : @submonoids X)
        {min max : binop X}
        (Hmin_assoc : isassoc min)
        (Hmin_comm : iscomm min)
        (Hmax_assoc : isassoc max)
        (Hmax_comm : iscomm max)
        (Hmin_max : Π x y : X, min x (max x y) = x)
        (Hmax_min : Π x y : X, max x (min x y) = x)
        (Hmin : issubrdistr Y min op)
        (Hmax : issubrdistr Y max op).

(** generic lemmas *)

Local Definition abmonoidfrac_lattice_fun (f : binop X) : binop (X × Y) :=
  λ x y,
  (f (pr1 x * pr1 (pr2 y))%multmonoid (pr1 y * pr1 (pr2 x))%multmonoid ,, @op Y (pr2 x) (pr2 y)).

Local Lemma abmonoidfrac_lattice_def :
  Π (f : X → X → X),
  issubrdistr Y f op →
  iscomprelrelfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y)
                   (abmonoidfrac_lattice_fun f).
Proof.
  intros f Hf.
  intros x y x' y'.
  apply hinhfun2.
  intros c c'.
  unfold abmonoidfrac_lattice_fun.
  do 2 rewrite rewrite_pr1_tpair, rewrite_pr2_tpair.
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
  Π (f : X → X → X) Hf,
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
  Π (f : X → X → X) Hf,
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

Lemma isabsorb_abmonoidfrac_def :
  Π f g Hf Hg,
  (Π x y, f x (g x y) = x) →
  Π x y : abmonoidfrac X Y,
          setquotfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y) _
                      (abmonoidfrac_lattice_def f Hf) x
                      (setquotfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y) _
                                   (abmonoidfrac_lattice_def g Hg) x y) = x.
Proof.
  intros f g Hf Hg Habsorb.
  simple refine (setquotuniv2prop _ (λ x y, (_ x (_ x y) = x) ,, _) _).
  - apply (pr2 (pr1 (pr1 (abmonoidfrac X Y)))).
  - intros x y.
    simpl.
    rewrite !(setquotfun2comm (eqrelabmonoidfrac X Y)).
    unfold abmonoidfrac_lattice_fun.
    rewrite !rewrite_pr1_tpair, !rewrite_pr2_tpair.
    apply (iscompsetquotpr (eqrelabmonoidfrac X Y)), hinhpr.
    exists (pr2 x).
    apply (maponpaths (λ x, (x * _)%multmonoid)).
    rewrite !rewrite_pr1_tpair, !rewrite_pr2_tpair.
    simpl ; unfold pr1carrier ; simpl.
    rewrite Hf, Hg, Hg.
    do 3 rewrite (assocax X (pr1 x)).
    rewrite (commax X (pr1 (pr2 y))).
    do 2 rewrite (assocax X (pr1 (pr2 x))).
    do 2 rewrite (commax X (pr1 (pr2 y))).
    apply Habsorb.
Qed.

(** definition of abmonoidfrac_islattice *)

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
  Π x y : abmonoidfrac X Y, abmonoidfrac_max x (abmonoidfrac_min x y) = x.
Proof.
  apply isabsorb_abmonoidfrac_def.
  apply Hmax_min.
Qed.

Lemma isabsorb_abmonoidfrac_min_max :
  Π x y : abmonoidfrac X Y, abmonoidfrac_min x (abmonoidfrac_max x y) = x.
Proof.
  apply isabsorb_abmonoidfrac_def.
  apply Hmin_max.
Qed.

End abmonoidfrac_lattice.

Lemma abmonoidfrac_islatticeop (X : abmonoid) (Y : @submonoids X) (is : islattice X) :
  Π (Hmin : issubrdistr Y (Lmin is) op) (Hmax : issubrdistr Y (Lmax is) op),
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

Definition abmonoidfrac_islattice (X : abmonoid) (Y : @submonoids X) (is : islattice X)
           (Hmin : issubrdistr Y (Lmin is) op) (Hmax : issubrdistr Y (Lmax is) op) : islattice (abmonoidfrac X Y).
Proof.
  intros X Y is Hmin Hmax.
  mkpair.
  exact (abmonoidfrac_min X Y Hmin).
  mkpair.
  exact (abmonoidfrac_max X Y Hmax).
  apply abmonoidfrac_islatticeop.
Defined.

Lemma ispartbinophrel_Lle (X : abmonoid) (Y : @submonoids X) (is : islattice X)
      (Hmin : issubrdistr Y (Lmin is) op) (Hmax : issubrdistr Y (Lmax is) op) :
  ispartbinophrel Y (Lle is).
Proof.
  intros X Y is Hmin Hmax.
  split.
  - intros a b c Yc.
    rewrite !(commax _ c).
    unfold Lle ; rewrite <- (Hmin _ _ (c,,Yc)).
    apply (maponpaths (λ x, op x _)).
  - intros a b c Yc.
    unfold Lle ; rewrite <- (Hmin _ _ (c,,Yc)).
    apply (maponpaths (λ x, op x _)).
Qed.

Lemma abmonoidfrac_Lle (X : abmonoid) (Y : @submonoids X) (is : islattice X)
      (Hmin : issubrdistr Y (Lmin is) op) (Hmax : issubrdistr Y (Lmax is) op) :
  Π x y : abmonoidfrac X Y, abmonoidfracrel X Y (ispartbinophrel_Lle X Y is Hmin Hmax) x y <-> Lle (abmonoidfrac_islattice X Y is Hmin Hmax) x y.
Proof.
  intros X Y is Hmin Hmax.
  simple refine (setquotuniv2prop _ (λ x y, _ ,, _) _).
  - apply isapropdirprod ;
    apply isapropimpl, propproperty.
  - intros x y.
    change (abmonoidfracrel X Y (ispartbinophrel_Lle X Y is Hmin Hmax) (setquotpr (binopeqrelabmonoidfrac X Y) x)
    (setquotpr (binopeqrelabmonoidfrac X Y) y) <->
            abmonoidfrac_min X Y Hmin (setquotpr (binopeqrelabmonoidfrac X Y) x)
    (setquotpr (binopeqrelabmonoidfrac X Y) y) = (setquotpr (binopeqrelabmonoidfrac X Y) x)).
    unfold abmonoidfracrel, quotrel, abmonoidfrac_min.
    rewrite setquotuniv2comm, setquotfun2comm.
    split ; intros H.
    + apply iscompsetquotpr.
      revert H.
      apply hinhfun.
      intros c.
      exists (pr1 c).
      simpl in c |- *.
      rewrite (assocax X), (commax _ _ (pr1 (pr1 c))), <- (assocax X).
      rewrite Hmin.
      refine (pathscomp0 _ _).
      refine (maponpaths (λ x, x + _) _).
      apply (pr2 c).
      do 3 rewrite (assocax X) ;
        apply maponpaths.
      do 2 rewrite commax, assocax.
      apply pathsinv0, assocax.
    + generalize (invmap (weqpathsinsetquot _ _ _) H).
      apply hinhfun.
      simpl.
      intros c.
      exists (pr2 x + pr1 c).
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

(** ** lattice in [commrngfrac] *)

Definition commrngfrac_islattice (X : commrng) (Y : @subabmonoids (rngmultabmonoid X))
           (is : islattice X)
           (Hmin : issubrdistr Y (Lmin is) op2) (Hmax : issubrdistr Y (Lmax is) op2):
  islattice (commrngfrac X Y) :=
  abmonoidfrac_islattice (rngmultabmonoid X) Y is Hmin Hmax.

(** ** lattice in abgrdiff *)

Lemma abgrdiff_setquotpr_equiv {X : abmonoid} :
  Π k x y : X,
  setquotpr (eqrelabgrdiff X) (x,,y) = setquotpr (eqrelabgrdiff X) (x + k,,y + k).
Proof.
  intros X k x y.
  apply iscompsetquotpr, hinhpr.
  exists 0 ; simpl.
  rewrite !(assocax X), !runax, (commax X y).
  reflexivity.
Qed.

Section lattice_abgrdiff.

Context {X : abmonoid}
        {min max : binop X}
        (is : islatticeop min max)
        (Hmin : isrdistr min op)
        (Hmax : isrdistr max op).

(** Link with abmonoidfrac_lattice *)

Local Definition abgrdiff_islattice' : islattice (abgrdiff X).
Proof.
  refine (islattice_weq _ _).
  apply (weqabgrdiff X).
  simple refine (abmonoidfrac_islattice _ _ _ _ _).
  apply (min,,max,,is).
  intros x y k ; apply Hmin.
  intros x y k ; apply Hmax.
Defined.

Local Definition abgrdiff_min' : binop (abgrdiff X) :=
  Lmin abgrdiff_islattice'.
Local Definition abgrdiff_max' : binop (abgrdiff X) :=
  Lmax abgrdiff_islattice'.

(** Definition of min and max *)

Local Definition abgrdiff_lattice_fun (f : binop X) : binop (X × X) :=
  λ x y,
  (f (pr1 x * pr2 y)%multmonoid (pr1 y * pr2 x)%multmonoid ,, (pr2 x * pr2 y)%multmonoid).

Local Lemma abgrdiff_lattice_def :
  Π (f : X → X → X),
  isrdistr f op →
  iscomprelrelfun2 (binopeqrelabgrdiff X) (binopeqrelabgrdiff X)
                   (abgrdiff_lattice_fun f).
Proof.
  intros f Hf.
  generalize (abmonoidfrac_lattice_def X (totalsubmonoid X) f (λ x y k, Hf x y (pr1 k))) ;
  clear Hf ; intros Hf.

  intros x y x' y' H H'.
  refine (hinhfun _ _).
  Focus 2.
  simple refine (Hf _ _ _ _ _ _).
  apply (pr1 x ,, pr2 x ,, tt).
  apply (pr1 y ,, pr2 y ,, tt).
  apply (pr1 x' ,, pr2 x' ,, tt).
  apply (pr1 y' ,, pr2 y' ,, tt).
  clear -H.
  revert H ; apply hinhfun.
  intros c.
  exists (pr1 c ,, tt).
  apply (pr2 c).
  clear -H'.
  revert H' ; apply hinhfun.
  intros c.
  exists (pr1 c ,, tt).
  apply (pr2 c).

  intros c.
  exists (pr1 (pr1 c)).
  apply (pr2 c).
Qed.

Definition abgrdiff_min : binop (abgrdiff X) :=
  setquotfun2 (binopeqrelabgrdiff X) (binopeqrelabgrdiff X) _
              (abgrdiff_lattice_def min Hmin).
Definition abgrdiff_max : binop (abgrdiff X) :=
  setquotfun2 (binopeqrelabgrdiff X) (binopeqrelabgrdiff X) _
              (abgrdiff_lattice_def max Hmax).

Lemma abgrdiff_min_rw :
  Π (x y : abgrdiff X),
  abgrdiff_min x y = abgrdiff_min' x y.
Proof.
  simple refine (setquotuniv2prop _ (λ _ _, _,,_) _).
  - apply (pr2 (pr1 (pr1 (abgrdiff X)))).
  - intros x y.
    reflexivity.
Qed.
Lemma abgrdiff_max_rw :
  Π (x y : abgrdiff X),
  abgrdiff_max x y = abgrdiff_max' x y.
Proof.
  simple refine (setquotuniv2prop _ (λ _ _, _,,_) _).
  - apply (pr2 (pr1 (pr1 (abgrdiff X)))).
  - intros x y.
    reflexivity.
Qed.

(** Properties of a Lattice *)

Lemma isassoc_abgrdiff_min :
  isassoc abgrdiff_min.
Proof.
  intros x y k.
  do 4 rewrite abgrdiff_min_rw.
  unfold abgrdiff_min'.
  apply isassoc_Lmin.
Qed.

Lemma iscomm_abgrdiff_min :
  iscomm abgrdiff_min.
Proof.
  intros x y.
  do 2 rewrite abgrdiff_min_rw.
  unfold abgrdiff_min'.
  apply iscomm_Lmin.
Qed.

Lemma isassoc_abgrdiff_max :
  isassoc abgrdiff_max.
Proof.
  intros x y k.
  do 4 rewrite abgrdiff_max_rw.
  unfold abgrdiff_max'.
  apply isassoc_Lmax.
Qed.

Lemma iscomm_abgrdiff_max :
  iscomm abgrdiff_max.
Proof.
  intros x y.
  do 2 rewrite abgrdiff_max_rw.
  unfold abgrdiff_max'.
  apply iscomm_Lmax.
Qed.

Lemma isabsorb_abgrdiff_min_max :
  Π x y : abgrdiff X, abgrdiff_min x (abgrdiff_max x y) = x.
Proof.
  intros x y.
  rewrite abgrdiff_min_rw, abgrdiff_max_rw.
  unfold abgrdiff_max', abgrdiff_min'.
  apply Lmin_absorb.
Qed.

Lemma isabsorb_abgrdiff_max_min :
  Π x y : abgrdiff X, abgrdiff_max x (abgrdiff_min x y) = x.
Proof.
  intros x y.
  rewrite abgrdiff_min_rw, abgrdiff_max_rw.
  unfold abgrdiff_max', abgrdiff_min'.
  apply Lmax_absorb.
Qed.

Lemma abgrdiff_islatticeop :
  islatticeop abgrdiff_min abgrdiff_max.
Proof.
  split ; [ | split] ; split.
  - apply isassoc_abgrdiff_min.
  - apply iscomm_abgrdiff_min.
  - apply isassoc_abgrdiff_max.
  - apply iscomm_abgrdiff_max.
  - apply isabsorb_abgrdiff_min_max.
  - apply isabsorb_abgrdiff_max_min.
Qed.

End lattice_abgrdiff.

Definition abgrdiff_islattice (X : abmonoid) (is : islattice X)
           (Hmin : isrdistr (Lmin is) op) (Hmax : isrdistr (Lmax is) op) : islattice (abgrdiff X) :=
  _ ,, _ ,, (abgrdiff_islatticeop (pr2 (pr2 is)) Hmin Hmax).

Lemma isbinophrel_abgrdiff_Lle (X : abmonoid) (is : islattice X)
      (Hmin : isrdistr (Lmin is) op) (Hmax : isrdistr (Lmax is) op) :
  isbinophrel (Lle is).
Proof.
  intros X is Hmin Hmax.
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

Lemma abgrdiff_Lle (X : abmonoid) (is : islattice X)
      (Hmin : isrdistr (Lmin is) op) (Hmax : isrdistr (Lmax is) op) :
  Π x y : abgrdiff X, abgrdiffrel X (isbinophrel_abgrdiff_Lle X is Hmin Hmax) x y <-> Lle (abgrdiff_islattice X is Hmin Hmax) x y.
Proof.
  intros X is Hmin Hmax.
  intros x y.
  rewrite <- (homotinvweqweq (weqabgrdiff X) x), <- (homotinvweqweq (weqabgrdiff X) y).
  generalize ((weqabgrdiff X) x) ((weqabgrdiff X) y).
  clear x y ; intros x y.

  generalize (abmonoidfrac_Lle X (totalsubmonoid X) is (λ _ _ _, Hmin _ _ _) (λ _ _ _, Hmax _ _ _) x y) ; intros H.

  change (abgrdiffrel X (isbinophrel_abgrdiff_Lle X is Hmin Hmax)
                      (invmap (weqabgrdiff X) x) (invmap (weqabgrdiff X) y) <->
          abgrdiff_min Hmin (invmap (weqabgrdiff X) x) (invmap (weqabgrdiff X) y) =
          invmap (weqabgrdiff X) x).
  rewrite (abgrdiff_min_rw (pr2 (pr2 is)) Hmin Hmax).
  change (abgrdiffrel X (isbinophrel_abgrdiff_Lle X is Hmin Hmax)
    (invmap (weqabgrdiff X) x) (invmap (weqabgrdiff X) y) <->
  invmap (weqabgrdiff X)
    (abmonoidfrac_min X (totalsubmonoid X)
       (λ (x0 y0 : pr1 X) (k : Σ _ : pr1 X, htrue), Hmin x0 y0 (pr1 k))
       (invmap (invweq (weqabgrdiff X)) (invmap (weqabgrdiff X) x))
       (invmap (invweq (weqabgrdiff X)) (invmap (weqabgrdiff X) y))) =
  invmap (weqabgrdiff X) x).
  rewrite invinv, invinv, homotweqinvweq, homotweqinvweq.

  split ; intros H0.
  - apply maponpaths.
    apply (pr1 H).
    clear -H0.
    revert x y H0.
    simple refine (setquotuniv2prop _ (λ _ _, _ ,, _) _).
    + apply isapropimpl, propproperty.
    + intros x y H ; revert H.
      change (invmap (weqabgrdiff X)
                     (setquotpr (binopeqrelabmonoidfrac X (totalsubmonoid X)) x))
      with (setquotpr (binopeqrelabgrdiff X) (pr1 x ,, pr1 (pr2 x))).
      change (invmap (weqabgrdiff X)
                     (setquotpr (binopeqrelabmonoidfrac X (totalsubmonoid X)) y))
      with (setquotpr (binopeqrelabgrdiff X) (pr1 y ,, pr1 (pr2 y))).
      unfold abmonoidfracrel, abgrdiffrel, quotrel.
      do 2 rewrite setquotuniv2comm.
      apply hinhfun ; intros c.
      exists (pr1 c ,, tt).
      apply (pr2 c).
  - apply pathsweq1' in H0.
    rewrite homotweqinvweq in H0.
    apply (pr2 H) in H0.
    clear -H0.
    revert x y H0.
    simple refine (setquotuniv2prop _ (λ _ _, _ ,, _) _).
    + apply isapropimpl, propproperty.
    + intros x y H ; revert H.
      change (invmap (weqabgrdiff X)
                     (setquotpr (binopeqrelabmonoidfrac X (totalsubmonoid X)) x))
      with (setquotpr (binopeqrelabgrdiff X) (pr1 x ,, pr1 (pr2 x))).
      change (invmap (weqabgrdiff X)
                     (setquotpr (binopeqrelabmonoidfrac X (totalsubmonoid X)) y))
      with (setquotpr (binopeqrelabgrdiff X) (pr1 y ,, pr1 (pr2 y))).
      unfold abmonoidfracrel, abgrdiffrel, quotrel.
      do 2 rewrite setquotuniv2comm.
      apply hinhfun ; intros c.
      exists (pr1 (pr1 c)).
      apply (pr2 c).
Qed.

Section abgrdiff_islatticewithgt.

Context {X : abmonoid}
        (is : islattice X)
        (gt : StrongOrder X)
        (Hgt : isbinophrel gt)
        (Hop : Π x y z : X, y + x = z + x → y = z)
        (Hmin : isrdistr (Lmin is) op)
        (Hmax : isrdistr (Lmax is) op).
Context (Hnotgt_le : Π x y : X, (¬ gt x y) → Lle is x y)
        (Hle_notgt : Π x y : X, Lle is x y → (¬ gt x y))
        (Hmin_gt : Π x y z : X, gt x z → gt y z → gt (Lmin is x y) z)
        (Hmax_gt : Π x y z : X, gt z x → gt z y → gt z (Lmax is x y)).

Lemma abgrdiff_notLgt_Lle :
  Π (x y : abgrdiff X),
  ¬ abgrdiffrel X Hgt x y
  → Lle (abgrdiff_islattice X is Hmin Hmax) x y.
Proof.
  simple refine (setquotuniv2prop _ (λ _ _ , _ ,, _) _).
  - apply isapropimpl, propproperty.
  - intros x y.
    intros H0.
    apply abgrdiff_Lle.
    revert H0.
    unfold abgrdiffrel, quotrel.
    do 2 rewrite setquotuniv2comm.
    intros H0.
    apply hinhpr.
    exists 0.
    apply Hnotgt_le.
    intros H1 ; apply H0.
    apply hinhpr.
    exists 0.
    exact H1.
Qed.

Lemma abgrdiff_Lle_notLgt :
  Π (x y : abgrdiff X),
  Lle (abgrdiff_islattice X is Hmin Hmax) x y
  → ¬ abgrdiffrel X Hgt x y.
Proof.
  simple refine (setquotuniv2prop _ (λ _ _ , _ ,, _) _).
  - apply isapropimpl, isapropimpl, isapropempty.
  - intros x y.
    intros H0 H1.
    generalize (pr2 (abgrdiff_Lle _ _ _ _ _ _) H0).
    revert H1 ; clear H0.
    unfold abgrdiffrel, quotrel.
    do 2 rewrite setquotuniv2comm.
    simple refine (hinhuniv2 (P := _ ,, _) _).
    + apply isapropempty.
    + intros c c'.
      refine (Hle_notgt _ _ _ (pr2 c)).
      apply op_le_r.
      exact Hmin.
      refine (op_le_r' is _ _ (pr1 c') _ _ _).
      exact Hop.
      exact Hmin.
      exact (pr2 c').
Qed.

Lemma abgrdiff_min_gt :
  Π (x y z : abgrdiff X),
  abgrdiffrel X Hgt x z
  → abgrdiffrel X Hgt y z
  → abgrdiffrel X Hgt (abgrdiff_min Hmin x y) z.
Proof.
  simple refine (setquotuniv3prop _ (λ _ _ _ , _ ,, _) _).
  - apply isapropimpl, isapropimpl, propproperty.
  - intros x y z.
    unfold abgrdiffrel, quotrel, abgrdiff_min.
    rewrite setquotfun2comm.
    do 3 rewrite setquotuniv2comm.
    change (abgrdiffrelint X gt x z
   → abgrdiffrelint X gt y z
     → abgrdiffrelint X gt (abgrdiff_lattice_fun (Lmin is) x y) z).
    apply hinhfun2.
    intros c c'.
    unfold abgrdiff_lattice_fun.
    rewrite rewrite_pr1_tpair, rewrite_pr2_tpair.
    exists (pr1 c + pr1 c').
    rewrite !Hmin.
    apply Hmin_gt.
    + do 2 rewrite <- (assocax X _ _ (pr1 c')) ;
      apply (pr2 Hgt).
      do 4 rewrite (assocax X) ;
        do 2 rewrite (commax X (pr2 y)).
      do 3 rewrite <- (assocax X _ _ (pr2 y)) ;
        apply (pr2 Hgt).
      do 2 rewrite <- (assocax X).
      exact (pr2 c).
    + rewrite (commax X (pr1 c)).
      do 2 rewrite <- (assocax X _ _ (pr1 c)) ;
        apply (pr2 Hgt).
      do 4 rewrite (assocax X) ;
        do 2 rewrite (commax X (pr2 x)).
      do 2 rewrite <- (assocax X _ _ (pr2 x)) ;
        apply (pr2 Hgt).
      do 2 rewrite <- (assocax X).
      exact (pr2 c').
Qed.

Lemma abgrdiff_max_gt :
  Π (x y z : abgrdiff X),
  abgrdiffrel X Hgt z x
  → abgrdiffrel X Hgt z y
  → abgrdiffrel X Hgt z (abgrdiff_max Hmax x y).
Proof.
  simple refine (setquotuniv3prop _ (λ _ _ _ , _ ,, _) _).
  - apply isapropimpl, isapropimpl, propproperty.
  - intros x y z.
    unfold abgrdiffrel, quotrel, abgrdiff_max.
    rewrite setquotfun2comm.
    do 3 rewrite setquotuniv2comm.
    change (abgrdiffrelint X gt z x
   → abgrdiffrelint X gt z y
   → abgrdiffrelint X gt z (abgrdiff_lattice_fun (Lmax is) x y)).
    apply hinhfun2.
    intros c c'.
    unfold abgrdiff_lattice_fun.
    rewrite rewrite_pr1_tpair, rewrite_pr2_tpair.
    exists (pr1 c + pr1 c').
    rewrite !Hmax.
    apply Hmax_gt.
    + do 2 rewrite <- (assocax X _ _ (pr1 c')) ;
      apply (pr2 Hgt).
      do 4 rewrite (assocax X) ;
        do 2 rewrite (commax X (pr2 y)).
      do 3 rewrite <- (assocax X _ _ (pr2 y)) ;
        apply (pr2 Hgt).
      do 2 rewrite <- (assocax X).
      exact (pr2 c).
    + rewrite (commax X (pr1 c)).
      do 2 rewrite <- (assocax X _ _ (pr1 c)) ;
        apply (pr2 Hgt).
      do 4 rewrite (assocax X) ;
        do 2 rewrite (commax X (pr2 x)).
      do 2 rewrite <- (assocax X _ _ (pr2 x)) ;
        apply (pr2 Hgt).
      do 2 rewrite <- (assocax X).
      exact (pr2 c').
Qed.

End abgrdiff_islatticewithgt.

Definition abgrdiff_islatticewithgt {X : abmonoid} (is : islatticewithgt X) (Hgt : isbinophrel (Lgt is))
           (Hop : Π x y z : X, y + x = z + x → y = z)
           (Hmin : isrdistr (Lmin is) op) (Hmax : isrdistr (Lmax is) op) :
  islatticewithgt (abgrdiff X).
Proof.
  intros X is Hgt Hop Hmin Hmax.
  mkpair.
  apply (abgrdiff_islattice X is Hmin Hmax).
  mkpair.
  apply (StrongOrder_abgrdiff (Lgt is) Hgt).
  split ; split.
  - apply abgrdiff_notLgt_Lle, notLgt_Lle.
  - apply abgrdiff_Lle_notLgt.
    + apply Hop.
    + apply Lle_notLgt.
  - apply abgrdiff_min_gt, Lmin_Lgt.
  - apply abgrdiff_max_gt, Lmax_Lgt.
Defined.

Definition abgrdiff_islatticedec {X : abmonoid} (is : islatticedec X)
           (Hop : Π x y z : X, y + x = z + x → y = z)
           (Hmin : isrdistr (Lmin is) op) (Hmax : isrdistr (Lmax is) op) :
  islatticedec (abgrdiff X).
Proof.
  intros X is Hop Hmin Hmax.
  mkpair.
  apply (abgrdiff_islattice X is Hmin Hmax).
  split.
  - refine (istotallogeqf _ _).
    + apply abgrdiff_Lle.
    + apply istotalabgrdiffrel, istotal_islatticedec.
  - refine (isdecrellogeqf _ _).
    + apply abgrdiff_Lle.
    + apply isdecabgrdiffrel.
      split.
      * intros x y z.
        rewrite !(commax X z).
        apply op_le_r'.
        exact Hop.
        exact Hmin.
      * intros x y z.
        apply op_le_r'.
        exact Hop.
        exact Hmin.
      * apply isdecrel_islatticedec.
Defined.

(** Lattice in fldfrac' *)

Definition fldfrac'_islattice {X : commrng} R is1 is2 (is : islattice X)
           (Hmin : @issubrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmin is) op2)
           (Hmax : @issubrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmax is) op2) :
  islattice (fldfrac' X R is1 is2) :=
  commrngfrac_islattice X (rngpossubmonoid X is1 is2) is Hmin Hmax.

(** Lattice in fldfrac *)

Definition fldfrac_islattice {X : intdom} (is' : isdeceq X) (R : hrel X) (is0 : isbinophrel (X := rigaddabmonoid X) R)
           (is1 : isrngmultgt X R) (is2 : R 1%rng 0%rng) (is3 : isirrefl R) (nc : neqchoice R)
           (is : islattice X)
           (Hmin : @issubrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmin is) op2)
           (Hmax : @issubrdistr (rngmultabmonoid X) (rngpossubmonoid X is1 is2) (Lmax is) op2) :
  islattice (fldfrac X is') :=
  islattice_weq (weqfldfracgt X is' is0 is1 is2 nc is3)
                (commrngfrac_islattice X (rngpossubmonoid X is1 is2) is Hmin Hmax).
