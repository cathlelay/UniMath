(** * Lattice *)

Require Export UniMath.Foundations.Algebra.Apartness.
Require Export UniMath.Foundations.Algebra.BinaryOperations.
Require Export UniMath.Foundations.Algebra.Monoids_and_Groups.

Unset Automatic Introduction.

Set Default Timeout 5.

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

End so_pty.

Definition isStrongOrder_quotrel {X : UU} {R : eqrel X} {L : hrel X} (is : iscomprelrel R L) :
  isStrongOrder L → isStrongOrder (quotrel is).
Proof.
  intros X R L is H.
  repeat split.
  - apply istransquotrel, (pr1 H).
  - apply iscotransquotrel, (pr1 (pr2 H)).
  - apply isirreflquotrel, (pr2 (pr2 H)).
Defined.

(** ** Definition *)

Definition islatticeop {X : hSet} (min max : binop X) :=
  ((isassoc min) × (iscomm min))
    × ((isassoc max) × (iscomm max))
    × (Π x y : X, min x (max x y) = x)
    × (Π x y : X, max x (min x y) = x).
Definition islattice (X : hSet) := Σ min max : binop X, islatticeop min max.
Definition lattice := Σ X : setwith2binop, islatticeop (X := X) op1 op2.

Definition pr1lattice : lattice -> setwith2binop := pr1.
Coercion pr1lattice : lattice >-> setwith2binop.
Definition mklattice {X : hSet} {min max : binop X} : islatticeop min max -> lattice :=
  λ (is : islatticeop min max), (X,, min,, max),, is.

Definition lattice2islattice : Π X : lattice, islattice X :=
  λ X : lattice, op1,, op2,, pr2 X.
Definition islattice2lattice : Π X : hSet, islattice X → lattice :=
λ (X : hSet) (is : islattice X), mklattice (pr2 (pr2 is)).

Section lattice_pty.

Context {L : hSet}
        (is : islattice L).

Definition Lmin : binop L := pr1 is.
Definition Lmax : binop L := pr1 (pr2 is).

Lemma isassoc_Lmin :
  isassoc Lmin.
Proof.
  exact (pr1 (pr1 (pr2 (pr2 is)))).
Qed.
Lemma iscomm_Lmin :
  iscomm Lmin.
Proof.
  exact (pr2 (pr1 (pr2 (pr2 is)))).
Qed.
Lemma isassoc_Lmax :
  isassoc Lmax.
Proof.
  exact (pr1 (pr1 (pr2 (pr2 (pr2 is))))).
Qed.
Lemma iscomm_Lmax :
  iscomm Lmax.
Proof.
  exact (pr2 (pr1 (pr2 (pr2 (pr2 is))))).
Qed.
Lemma Lmin_absorb :
  Π x y : L, Lmin x (Lmax x y) = x.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 is))))).
Qed.
Lemma Lmax_absorb :
  Π x y : L, Lmax x (Lmin x y) = x.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 is))))).
Qed.

Lemma Lmin_id :
  Π x : L, Lmin x x = x.
Proof.
  intros x.
  apply (pathscomp0 (b := Lmin x (Lmax x (Lmin x x)))).
  - rewrite Lmax_absorb.
    reflexivity.
  - apply Lmin_absorb.
Qed.
Lemma Lmax_id :
  Π x : L, Lmax x x = x.
Proof.
  intros x.
  apply (pathscomp0 (b := Lmax x (Lmin x (Lmax x x)))).
  - rewrite Lmin_absorb.
    reflexivity.
  - apply Lmax_absorb.
Qed.

End lattice_pty.

(** ** Order in a lattice *)

Section lattice_le.

Context {L : hSet}
        (is : islattice L).

Definition Lle : hrel L :=
  λ (x y : L), hProppair (Lmin is x y = x) ((pr2 L) (Lmin is x y) x).

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
  apply pathscomp0 with (2 := Hyx).
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
  Π x y : L, Lle (Lmin is x y) x.
Proof.
  intros x y.
  simpl.
  rewrite iscomm_Lmin, <- isassoc_Lmin, Lmin_id.
  reflexivity.
Qed.
Lemma Lmin_le_r :
  Π x y : L, Lle (Lmin is x y) y.
Proof.
  intros x y.
  rewrite iscomm_Lmin.
  apply Lmin_le_l.
Qed.

Lemma Lmin_ge :
  Π x y z : L, Lle z x → Lle z y → Lle z (Lmin is x y).
Proof.
  intros x y z <- <-.
  simpl.
  rewrite (iscomm_Lmin _ x), <- isassoc_Lmin.
  rewrite (isassoc_Lmin _ _ _ y), Lmin_id.
  rewrite isassoc_Lmin, (iscomm_Lmin _ y).
  rewrite isassoc_Lmin, <- (isassoc_Lmin _ x), Lmin_id.
  apply pathsinv0, isassoc_Lmin.
Qed.

Lemma Lmax_ge_l :
  Π x y : L, Lle x (Lmax is x y).
Proof.
  intros x y.
  simpl.
  apply Lmin_absorb.
Qed.
Lemma Lmax_ge_r :
  Π x y : L, Lle y (Lmax is x y).
Proof.
  intros x y.
  rewrite iscomm_Lmax.
  apply Lmax_ge_l.
Qed.

Lemma Lmax_le :
  isrdistr (Lmax is) (Lmin is)
  → Π x y z : L, Lle x z → Lle y z → Lle (Lmax is x y) z.
Proof.
  intros H x y z <- <-.
  rewrite <- H.
  apply Lmin_le_r.
Qed.

Lemma Lmin_eq_l :
  Π x y : L, Lle x y -> Lmin is x y = x.
Proof.
  intros x y H.
  apply H.
Qed.
Lemma Lmin_eq_r :
  Π x y : L, Lle y x -> Lmin is x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmin.
  apply H.
Qed.

Lemma Lmax_eq_l :
  Π x y : L, Lle y x -> Lmax is x y = x.
Proof.
  intros x y <-.
  rewrite iscomm_Lmin.
  apply Lmax_absorb.
Qed.
Lemma Lmax_eq_r :
  Π x y : L, Lle x y -> Lmax is x y = y.
Proof.
  intros x y H.
  rewrite iscomm_Lmax.
  now apply Lmax_eq_l.
Qed.

End lattice_le.

Definition islatticewithltrel {X : hSet} (is : islattice X) (lt : StrongOrder X) :=
  (Π x y : X, (¬ (lt x y)) <-> Lle is y x)
    × (Π x y z : X, lt z x -> lt z y -> lt z (Lmin is x y))
    × (Π x y z : X, lt x z -> lt y z -> lt (Lmax is x y) z).

Definition islatticewithlt (X : hSet) :=
  Σ (is : islattice X) (lt : StrongOrder X), islatticewithltrel is lt.

Definition islattice_islatticewithlt {X : hSet} : islatticewithlt X → islattice X :=
  pr1.
Coercion islattice_islatticewithlt : islatticewithlt >-> islattice.

Section latticewithlt.

Context {X : hSet}
        (is : islatticewithlt X).

Definition Llt : StrongOrder X :=
  pr1 (pr2 is).

Lemma notLlt_Lle :
  Π x y : X, (¬ (Llt x y)) <-> Lle is y x.
Proof.
  apply (pr1 (pr2 (pr2 is))).
Qed.
Lemma Llt_Lle :
  Π x y : X, Llt x y -> Lle is x y.
Proof.
  intros x y H.
  apply notLlt_Lle.
  intro H0.
  eapply isirrefl_StrongOrder.
  eapply istrans_StrongOrder.
  exact H.
  exact H0.
Qed.

Lemma istrans_Llt_Lle :
  Π x y z : X, Llt x y → Lle is y z → Llt x z.
Proof.
  intros x y z Hlt Hle.
  generalize (iscotrans_StrongOrder _ _ z _ Hlt).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  - exact H.
  - apply fromempty.
    refine (pr2 (notLlt_Lle _ _) _ _).
    exact Hle.
    exact H.
Qed.
Lemma istrans_Lle_Llt :
  Π x y z : X, Lle is x y → Llt y z → Llt x z.
Proof.
  intros x y z Hle Hlt.
  generalize (iscotrans_StrongOrder _ _ x _ Hlt).
  apply hinhuniv.
  apply sumofmaps ; intros H.
  - apply fromempty.
    refine (pr2 (notLlt_Lle _ _) _ _).
    exact Hle.
    exact H.
  - exact H.
Qed.

Lemma Lmin_Llt :
  Π x y z : X, Llt z x -> Llt z y -> Llt z (Lmin is x y).
Proof.
  apply (pr1 (pr2 (pr2 (pr2 is)))).
Qed.
Lemma Lmax_lt  :
  Π x y z : X, Llt x z -> Llt y z -> Llt (Lmax is x y) z.
Proof.
  apply (pr2 (pr2 (pr2 (pr2 is)))).
Qed.

End latticewithlt.

(** ** Lattice with a total order *)

Section lattice_deceq.

Context {L : hSet}
        (is : islattice L)
        (dec : Π x y : L, (Lle is x y) ⨿ (Lle is y x)).

Lemma Lmin_case_strong :
  Π (P : L → UU) (x y : L),
  (Lle is x y → P x) → (Lle is y x → P y) → P (Lmin is x y).
Proof.
  intros P x y Hx Hy.
  induction (dec x y) as [H | H].
  - rewrite H.
    apply Hx, H.
  - rewrite iscomm_Lmin, H.
    apply Hy, H.
Qed.
Lemma Lmin_case :
  Π (P : L → UU) (x y : L),
  P x → P y → P (Lmin is x y).
Proof.
  intros P x y Hx Hy.
  apply Lmin_case_strong ; intros _.
  - exact Hx.
  - exact Hy.
Qed.

Lemma Lmax_case_strong :
  Π (P : L → UU) (x y : L),
  (Lle is y x → P x) → (Lle is x y → P y) → P (Lmax is x y).
Proof.
  intros P x y Hx Hy.
  induction (dec x y) as [H | H].
  - rewrite Lmax_eq_r.
    apply Hy, H.
    exact H.
  - rewrite Lmax_eq_l.
    apply Hx, H.
    exact H.
Qed.
Lemma Lmax_case :
  Π (P : L → UU) (x y : L),
  P x → P y → P (Lmax is x y).
Proof.
  intros P x y Hx Hy.
  apply Lmax_case_strong ; intros _.
  - exact Hx.
  - exact Hy.
Qed.

End lattice_deceq.

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
  apply Lmax_eq_r, H.
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
  apply Lmax_eq_l, Hx.
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
  apply Lmax_le.
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
  rewrite !Lmax_eq_l.
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
  rewrite (Lmax_eq_l _ (x * y * k)%multmonoid
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

Definition extruncminuswithlt {X : abmonoid} (is : islatticewithlt X) :=
  Σ (ex : extruncminus is), Π x y : X, Llt is 0 (truncminus ex y x) → Llt is x y.
Definition extruncminuswithlt_extruncminus {X : abmonoid} (is : islatticewithlt X) :
  extruncminuswithlt is → extruncminus is := pr1.
Coercion extruncminuswithlt_extruncminus : extruncminuswithlt >-> extruncminus.

Section truncminus_lt.

Context {X : abmonoid}
        (is : islatticewithlt X)
        (ex : extruncminuswithlt is)
        (is0 : Π x y z : X, Llt is y z → Llt is (y + x) (z + x))
        (is1 : Π x y z : X, Llt is (y + x) (z + x) → Llt is y z).

Lemma truncminus_pos :
  Π x y : X, Llt is x y → Llt is 0 (truncminus ex y x).
Proof.
  intros x y.
  intros H.
  apply (is1 x).
  rewrite lunax, istruncminus_ex.
  rewrite Lmax_eq_l.
  exact H.
  apply Llt_Lle, H.
Qed.

Lemma truncminus_pos' :
  Π x y : X, Llt is 0 (truncminus ex y x) → Llt is x y.
Proof.
  exact (pr2 ex).
Qed.

End truncminus_lt.

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
  intros x.
  generalize (pr1 (pr2 x)).
  simple refine (hinhuniv (P := hProppair _ _) _).
  apply (pr2 (pr1 (pr1 (abgrdiff X)))).
  intros c ; simpl.
  rewrite <- (setquotl0 (eqrelabgrdiff X) x c).
  refine (iscompsetquotpr (eqrelabgrdiff X) _ _ _).
  rewrite abgrdiff_elt_simpl.
  apply hinhpr.
  exists 0 ; simpl.
  rewrite (commax _ (pr1 (pr1 c))), !(istruncminus_ex ex).
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
        (Hmin : isrdistr min op)
        (Hmax : isrdistr max op).


Local Lemma abmonoidfrac_lattice_def :
  Π (f : X → X → X),
  isrdistr f op →
  iscomprelrelfun2 (binopeqrelabmonoidfrac X Y) (binopeqrelabmonoidfrac X Y)
                   (λ x y,
                    f (pr1 x * pr1 (pr2 y))%multmonoid (pr1 y * pr1 (pr2 x))%multmonoid,,
                      (pr2 x * pr2 y)%multmonoid).
Proof.
  intros f Hf.
  intros x y x' y'.
  apply hinhfun2.
  intros c c'.
  simpl.
  mkpair.
  - apply (@op Y (pr1 c) (pr1 c')).
  - rewrite !Hf.
    apply map_on_two_paths ; simpl.
    + simple refine (pathscomp0 _ _).
      * exact ((pr1 x + pr1 (pr2 y) + pr1 (pr1 c)) + (pr1 (pr2 x') + pr1 (pr2 y') + pr1 (pr1 c'))).
      * rewrite !(assocax X) ;
        apply maponpaths.
        do 2 (rewrite commax, !assocax ;
              apply maponpaths).
        rewrite commax, !assocax.
        reflexivity.
      * refine (pathscomp0 _ _).
        refine (maponpaths (λ x, (x * _)%multmonoid) _).
        apply (pr2 c).
        rewrite !(assocax X) ;
          apply maponpaths.
        (do 3 rewrite commax, !assocax) ;
          apply maponpaths.
        do 2 (rewrite commax, !assocax ;
              apply maponpaths).
        exact (commax _ _ _).
    + simple refine (pathscomp0 _ _).
      * exact ((pr1 x' + pr1 (pr2 y') + pr1 (pr1 c')) + (pr1 (pr2 x) + pr1 (pr2 y) + pr1 (pr1 c))).
      * rewrite !(assocax X) ;
        apply maponpaths.
        (do 2 rewrite commax, !assocax) ;
          apply maponpaths.
        rewrite commax, !assocax.
        reflexivity.
      * refine (pathscomp0 _ _).
        refine (maponpaths (λ x, (x * _)%multmonoid) _).
        apply (pr2 c').
        rewrite !(assocax X) ;
          apply maponpaths.
        do 2 ((do 3 rewrite commax, !assocax) ;
              apply maponpaths).
        rewrite commax, !assocax ;
          apply maponpaths.
        exact (commax _ _ _).
Qed.

Definition abmonoidfrac_min : binop (abmonoidfrac X Y).
Proof.
  simple refine (setquotfun2 _ _ _ _).
  - intros x y.
    split.
    exact (min (pr1 x + pr1 (pr2 y)) (pr1 y + pr1 (pr2 x))).
    exact (pr2 x + pr2 y).
  - apply abmonoidfrac_lattice_def.
    exact Hmin.
Defined.

Definition abmonoidfrac_max : binop (abmonoidfrac X Y).
Proof.
  simple refine (setquotfun2 _ _ _ _).
  - intros x y.
    split.
    exact (max (pr1 x + pr1 (pr2 y)) (pr1 y + pr1 (pr2 x))).
    exact (pr2 x + pr2 y).
  - apply abmonoidfrac_lattice_def.
    exact Hmax.
Defined.

Lemma iscomm_abmonoidfrac_min :
  iscomm abmonoidfrac_min.
Proof.
  intros x y.
  generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
  simple refine (hinhuniv2 (P := _ ,, _) _).
  apply (pr2 (pr1 (pr1 (abmonoidfrac X Y)))).
  intros x' y' ; simpl.
  rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y').
  unfold abmonoidfrac_min.
  rewrite !setquotfun2comm.
  rewrite Hmin_comm, (commax _ (pr2 (pr1 x'))).
  reflexivity.
Qed.

Lemma isassoc_abmonoidfrac_min :
  isassoc abmonoidfrac_min.
Proof.
  intros x y z.
  generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
  simple refine (hinhuniv2 (P := _ ,, _) _).
  apply (pr2 (pr1 (pr1 (abmonoidfrac X Y)))).
  intros x' y'.
  generalize (pr1 (pr2 z)).
  simple refine (hinhuniv _).
  intros z' ; simpl.
  rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y'), <- (setquotl0 _ z z').
  unfold abmonoidfrac_min.
  rewrite !setquotfun2comm.
  rewrite !rewrite_pr1_tpair, !rewrite_pr2_tpair.
  rewrite !Hmin.
  rewrite !Hmin_assoc, !(assocax X), !(assocax Y).
  rewrite (commax _ (pr2 (pr1 x'))), (commax _ (pr1 (pr2 (pr1 x')))).
  reflexivity.
Qed.

Lemma iscomm_abmonoidfrac_max :
  iscomm abmonoidfrac_max.
Proof.
  intros x y.
  generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
  simple refine (hinhuniv2 (P := _ ,, _) _).
  apply (pr2 (pr1 (pr1 (abmonoidfrac X Y)))).
  intros x' y' ; simpl.
  rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y').
  unfold abmonoidfrac_max.
  rewrite !setquotfun2comm.
  rewrite Hmax_comm, (commax _ (pr2 (pr1 x'))).
  reflexivity.
Qed.

Lemma isassoc_abmonoidfrac_max :
  isassoc abmonoidfrac_max.
Proof.
  intros x y z.
  generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
  simple refine (hinhuniv2 (P := _ ,, _) _).
  apply (pr2 (pr1 (pr1 (abmonoidfrac X Y)))).
  intros x' y'.
  generalize (pr1 (pr2 z)).
  simple refine (hinhuniv _).
  intros z' ; simpl.
  rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y'), <- (setquotl0 _ z z').
  unfold abmonoidfrac_max.
  rewrite !setquotfun2comm.
  rewrite !rewrite_pr1_tpair, !rewrite_pr2_tpair.
  rewrite !Hmax.
  rewrite !Hmax_assoc, !(assocax X), !(assocax Y).
  rewrite (commax _ (pr2 (pr1 x'))), (commax _ (pr1 (pr2 (pr1 x')))).
  reflexivity.
Qed.

Lemma isabsorb_abmonoidfrac_max_min :
  Π x y : abmonoidfrac X Y, abmonoidfrac_max x (abmonoidfrac_min x y) = x.
Proof.
  intros x y.
  generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
  simple refine (hinhuniv2 (P := _ ,, _) _).
  apply (pr2 (pr1 (pr1 (abmonoidfrac X Y)))).
  intros x' y' ; simpl.
  rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y').
  unfold abmonoidfrac_max, abmonoidfrac_min.
  rewrite !setquotfun2comm.
  rewrite !rewrite_pr1_tpair, !rewrite_pr2_tpair.
  change (pr1 (pr2 (pr1 x') * pr2 (pr1 y')))%multmonoid with (pr1 (pr2 (pr1 x')) * pr1 (pr2 (pr1 y')))%multmonoid.
  rewrite (commax X (pr1 (pr2 (pr1 x')))), (commax _ (pr2 (pr1 x'))), <- (assocax X), <- Hmax.
  rewrite <- (abmonoidfrac_setquotpr_equiv (pr2 (pr1 x'))).
  rewrite Hmax_min.
  rewrite <- (abmonoidfrac_setquotpr_equiv (pr2 (pr1 y'))).
  rewrite <- tppr.
  reflexivity.
Qed.

Lemma isabsorb_abmonoidfrac_min_max :
  Π x y : abmonoidfrac X Y, abmonoidfrac_min x (abmonoidfrac_max x y) = x.
Proof.
  intros x y.
  generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
  simple refine (hinhuniv2 (P := _ ,, _) _).
  apply (pr2 (pr1 (pr1 (abmonoidfrac X Y)))).
  intros x' y' ; simpl.
  rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y').
  unfold abmonoidfrac_max, abmonoidfrac_min.
  rewrite !setquotfun2comm.
  rewrite !rewrite_pr1_tpair, !rewrite_pr2_tpair.
  change (pr1 (pr2 (pr1 x') * pr2 (pr1 y')))%multmonoid with (pr1 (pr2 (pr1 x')) * pr1 (pr2 (pr1 y')))%multmonoid.
  rewrite (commax X (pr1 (pr2 (pr1 x')))), (commax _ (pr2 (pr1 x'))), <- (assocax X), <- Hmin.
  rewrite <- (abmonoidfrac_setquotpr_equiv (pr2 (pr1 x'))).
  rewrite Hmin_max.
  rewrite <- (abmonoidfrac_setquotpr_equiv (pr2 (pr1 y'))).
  rewrite <- tppr.
  reflexivity.
Qed.

End abmonoidfrac_lattice.

Lemma abmonoidfrac_islatticeop (X : abmonoid) (Y : @submonoids X) (is : islattice X) :
  Π (Hmin : isrdistr (Lmin is) op) (Hmax : isrdistr (Lmax is) op),
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
           (Hmin : isrdistr (Lmin is) op) (Hmax : isrdistr (Lmax is) op) : islattice (abmonoidfrac X Y).
Proof.
  intros X Y is Hmin Hmax.
  mkpair.
  exact (abmonoidfrac_min X Y Hmin).
  mkpair.
  exact (abmonoidfrac_max X Y Hmax).
  apply abmonoidfrac_islatticeop.
Defined.

Lemma ispartbinophrel_Lle (X : abmonoid) (Y : @submonoids X) (is : islattice X)
      (Hmin : isrdistr (Lmin is) op) (Hmax : isrdistr (Lmax is) op) :
  ispartbinophrel Y (Lle is).
Proof.
  intros X Y is Hmin Hmax.
  split.
  - intros a b c Yc.
    rewrite !(commax _ c).
    apply op_le_r.
    exact Hmin.
  - intros a b c Yc.
    apply op_le_r.
    exact Hmin.
Qed.

Lemma abmonoidfrac_Lle (X : abmonoid) (Y : @submonoids X) (is : islattice X)
      (Hmin : isrdistr (Lmin is) op) (Hmax : isrdistr (Lmax is) op) :
  Π x y : abmonoidfrac X Y, abmonoidfracrel X Y (ispartbinophrel_Lle X Y is Hmin Hmax) x y <-> Lle (abmonoidfrac_islattice X Y is Hmin Hmax) x y.
Proof.
  intros X Y is Hmin Hmax.
  intros x y.
  generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
  simple refine (hinhuniv2 (P := _ ,, _) _).
  - apply isapropdirprod ;
    apply isapropimpl, propproperty.
  - intros x' y'.
    change (abmonoidfracrel X Y (ispartbinophrel_Lle X Y is Hmin Hmax) x y <->
            abmonoidfrac_min X Y Hmin x y = x).
    rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y').
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
      rewrite !(assocax X) ;
        apply maponpaths.
      do 2 rewrite commax, assocax.
      reflexivity.
    + generalize (invmap (weqpathsinsetquot _ _ _) H).
      apply hinhfun.
      simpl.
      intros c.
      exists (pr2 (pr1 x') + pr1 c).
      rewrite <- Hmin.
      change (pr1 (pr2 (pr1 x') * pr1 c))%multmonoid
      with (pr1 (pr2 (pr1 x')) * pr1 (pr1 c))%multmonoid.
      rewrite <- assocax.
      refine (pathscomp0 _ _).
      apply (pr2 c).
      rewrite !(assocax X) ;
        apply maponpaths.
      rewrite commax, assocax.
      apply maponpaths.
      apply commax.
Qed.

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

Local Lemma abgrdiff_lattice_help :
  Π (f : X → X → X),
  isrdistr f op →
  iscomprelrelfun2 (binopeqrelabgrdiff X) (binopeqrelabgrdiff X)
                   (λ x y : abmonoiddirprod X X,
                            f (pr1 x + pr2 y) (pr1 y + pr2 x),,
                              (pr2 x + pr2 y)).
Proof.
  intros f Hf.
  intros x y x' y'.
  apply hinhfun2.
  intros c c'.
  simpl.
  mkpair.
  - exact (pr1 c + pr1 c').
  - rewrite !Hf.
    apply map_on_two_paths.
    + simple refine (pathscomp0 _ _).
      * exact ((pr1 x + pr2 y + pr1 c) + (pr2 x' + pr2 y' + pr1 c')).
      * rewrite !assocax ;
        apply maponpaths.
        do 2 (rewrite commax, !assocax ;
              apply maponpaths).
        rewrite commax, !assocax.
        reflexivity.
      * rewrite (pr2 c).
        rewrite !assocax ;
          apply maponpaths.
        (do 3 rewrite commax, !assocax) ;
          apply maponpaths.
        do 2 (rewrite commax, !assocax ;
              apply maponpaths).
        exact (commax _ _ _).
    + simple refine (pathscomp0 _ _).
      * exact ((pr1 x' + pr2 y' + pr1 c') + (pr2 x + pr2 y + pr1 c)).
      * rewrite !assocax ;
        apply maponpaths.
        (do 2 rewrite commax, !assocax) ;
          apply maponpaths.
        rewrite commax, !assocax.
        reflexivity.
      * rewrite (pr2 c').
        rewrite !assocax ;
          apply maponpaths.
        do 2 ((do 3 rewrite commax, !assocax) ;
              apply maponpaths).
        rewrite commax, !assocax ;
          apply maponpaths.
        exact (commax _ _ _).
Qed.

Definition abgrdiff_min : binop (abgrdiff X).
Proof.
  simple refine (setquotfun2 _ _ _ _).
  - intros x y.
    split.
    exact (min (pr1 x + pr2 y) (pr1 y + pr2 x)).
    exact (pr2 x + pr2 y).
  - apply abgrdiff_lattice_help.
    exact Hmin.
Defined.

Definition abgrdiff_max : binop (abgrdiff X).
Proof.
  simple refine (setquotfun2 _ _ _ _).
  - intros x y.
    split.
    exact (max (pr1 x + pr2 y) (pr1 y + pr2 x)).
    exact (pr2 x + pr2 y).
  - apply abgrdiff_lattice_help.
    exact Hmax.
Defined.

Lemma iscomm_abgrdiff_min :
  iscomm abgrdiff_min.
Proof.
  intros x y.
  generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
  simple refine (hinhuniv2 (P := _ ,, _) _).
  apply (pr2 (pr1 (pr1 (abgrdiff X)))).
  intros x' y' ; simpl.
  rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y').
  unfold abgrdiff_min.
  rewrite !setquotfun2comm.
  rewrite (iscomm_Lmin (min,, max,, is)), (commax _ (pr2 (pr1 x'))).
  reflexivity.
Qed.

Lemma isassoc_abgrdiff_min :
  isassoc abgrdiff_min.
Proof.
  intros x y z.
  generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
  simple refine (hinhuniv2 (P := _ ,, _) _).
  apply (pr2 (pr1 (pr1 (abgrdiff X)))).
  intros x' y'.
  generalize (pr1 (pr2 z)).
  simple refine (hinhuniv _).
  intros z' ; simpl.
  rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y'), <- (setquotl0 _ z z').
  unfold abgrdiff_min.
  rewrite !setquotfun2comm.
  rewrite !rewrite_pr1_tpair, !rewrite_pr2_tpair.
  rewrite !Hmin.
  rewrite !(isassoc_Lmin (min,, max,, is)), !assocax.
  rewrite !(commax _ (pr2 (pr1 x'))).
  reflexivity.
Qed.

Lemma iscomm_abgrdiff_max :
  iscomm abgrdiff_max.
Proof.
  intros x y.
  generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
  simple refine (hinhuniv2 (P := _ ,, _) _).
  apply (pr2 (pr1 (pr1 (abgrdiff X)))).
  intros x' y' ; simpl.
  rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y').
  unfold abgrdiff_max.
  rewrite !setquotfun2comm.
  rewrite (iscomm_Lmax (min,, max,, is)), (commax _ (pr2 (pr1 x'))).
  reflexivity.
Qed.

Lemma isassoc_abgrdiff_max :
  isassoc abgrdiff_max.
Proof.
  intros x y z.
  generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
  simple refine (hinhuniv2 (P := _ ,, _) _).
  apply (pr2 (pr1 (pr1 (abgrdiff X)))).
  intros x' y'.
  generalize (pr1 (pr2 z)).
  simple refine (hinhuniv _).
  intros z' ; simpl.
  rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y'), <- (setquotl0 _ z z').
  unfold abgrdiff_max.
  rewrite !setquotfun2comm.
  rewrite !rewrite_pr1_tpair, !rewrite_pr2_tpair.
  rewrite !Hmax.
  rewrite !(isassoc_Lmax (min,, max,, is)), !assocax.
  rewrite !(commax _ (pr2 (pr1 x'))).
  reflexivity.
Qed.

Lemma isabsorb_abgrdiff_max_min :
  Π x y : abgrdiff X, abgrdiff_max x (abgrdiff_min x y) = x.
Proof.
  intros x y.
  generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
  simple refine (hinhuniv2 (P := _ ,, _) _).
  apply (pr2 (pr1 (pr1 (abgrdiff X)))).
  intros x' y' ; simpl.
  rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y').
  unfold abgrdiff_max, abgrdiff_min.
  rewrite !setquotfun2comm.
  rewrite !rewrite_pr1_tpair, !rewrite_pr2_tpair.
  rewrite !(commax _ (pr2 (pr1 x'))), <- assocax, <- Hmax.
  rewrite <- (abgrdiff_setquotpr_equiv (pr2 (pr1 x'))).
  rewrite (Lmax_absorb (min,, max,, is)).
  rewrite !(commax _ (pr2 (pr1 y'))),
  <- (abgrdiff_setquotpr_equiv (pr2 (pr1 y'))).
  rewrite <- tppr.
  reflexivity.
Qed.

Lemma isabsorb_abgrdiff_min_max :
  Π x y : abgrdiff X, abgrdiff_min x (abgrdiff_max x y) = x.
Proof.
  intros x y.
  generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
  simple refine (hinhuniv2 (P := _ ,, _) _).
  apply (pr2 (pr1 (pr1 (abgrdiff X)))).
  intros x' y' ; simpl.
  rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y').
  unfold abgrdiff_max, abgrdiff_min.
  rewrite !setquotfun2comm.
  rewrite !rewrite_pr1_tpair, !rewrite_pr2_tpair.
  rewrite !(commax _ (pr2 (pr1 x'))), <- assocax, <- Hmin.
  rewrite <- (abgrdiff_setquotpr_equiv (pr2 (pr1 x'))).
  rewrite (Lmin_absorb (min,, max,, is)).
  rewrite !(commax _ (pr2 (pr1 y'))),
  <- (abgrdiff_setquotpr_equiv (pr2 (pr1 y'))).
  rewrite <- tppr.
  reflexivity.
Qed.

End lattice_abgrdiff.

Lemma abgrdiff_islatticeop (X : abmonoid) (is : islattice X) :
  Π (Hmin : isrdistr (Lmin is) op) (Hmax : isrdistr (Lmax is) op),
  islatticeop (abgrdiff_min Hmin) (abgrdiff_max Hmax).
Proof.
  intros X is Hmin Hmax.
  repeat split.
  - apply (isassoc_abgrdiff_min (pr2 (pr2 is))).
  - apply (iscomm_abgrdiff_min (pr2 (pr2 is))).
  - apply (isassoc_abgrdiff_max (pr2 (pr2 is))).
  - apply (iscomm_abgrdiff_max (pr2 (pr2 is))).
  - apply (isabsorb_abgrdiff_min_max (pr2 (pr2 is))).
  - apply (isabsorb_abgrdiff_max_min (pr2 (pr2 is))).
Qed.

Definition abgrdiff_islattice (X : abmonoid) (is : islattice X)
           (Hmin : isrdistr (Lmin is) op) (Hmax : isrdistr (Lmax is) op) : islattice (abgrdiff X).
Proof.
  intros X is Hmin Hmax.
  mkpair.
  exact (abgrdiff_min Hmin).
  mkpair.
  exact (abgrdiff_max Hmax).
  apply abgrdiff_islatticeop.
Defined.

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
  generalize (pr1 (pr2 x)) (pr1 (pr2 y)).
  simple refine (hinhuniv2 (P := _ ,, _) _).
  - apply isapropdirprod ;
    apply isapropimpl, propproperty.
  - intros x' y'.
    change (abgrdiffrel X (isbinophrel_abgrdiff_Lle X is Hmin Hmax) x y <->
            abgrdiff_min Hmin x y = x).
    rewrite <- (setquotl0 _ x x'), <- (setquotl0 _ y y').
    unfold abgrdiffrel, quotrel, abgrdiff_min.
    rewrite setquotuniv2comm, setquotfun2comm.
    split ; intros H.
    + apply iscompsetquotpr.
      revert H.
      apply hinhfun.
      intros c.
      exists (pr1 c).
      simpl in c |- *.
      rewrite (assocax X), (commax _ _ (pr1 c)), <- (assocax X).
      rewrite Hmin.
      refine (pathscomp0 _ _).
      refine (maponpaths (λ x, x + _) _).
      apply (pr2 c).
      rewrite !(assocax X) ;
        apply maponpaths.
      do 2 rewrite commax, assocax.
      reflexivity.
    + generalize (invmap (weqpathsinsetquot _ _ _) H).
      apply hinhfun.
      simpl.
      intros c.
      exists (pr2 (pr1 x') + pr1 c).
      rewrite <- Hmin.
      rewrite <- assocax.
      refine (pathscomp0 _ _).
      apply (pr2 c).
      rewrite !(assocax X) ;
        apply maponpaths.
      rewrite commax, assocax.
      apply maponpaths.
      apply commax.
Qed.
