(** * Results about Riemann integrals *)
(** Author: Catherine LELAY. Jan 2016 - *)

Require Export UniMath.Foundations.Algebra.Rigs_and_Rings.
Require Export UniMath.Bourbaki.Filters.
Require Import UniMath.Bourbaki.NormedSpace.
Require Import UniMath.Foundations.Algebra.Apartness.
Require Import UniMath.Foundations.Algebra.ConstructiveStructures.
Require Import UniMath.Foundations.Algebra.Archimedean.
Require Import UniMath.Dedekind.Sets.


Lemma minusSnm :
  ∀ n m : nat, (m ≤ n) -> (S n - m = S (n - m))%nat.
Proof.
  induction n.
  - now destruct m.
  - destruct m ; intros Hm.
    reflexivity.
    apply IHn.
    exact Hm.
Qed.

(** ** Unit interval *)
(** Inspired by the alea library by C. Paulin *)

Definition is_unit_interval {X : setwith2binop} (le lt : hrel X) (H0 : isabmonoidop (BinaryOperations.op1 (X := X))) (addinv : unop X) (H1 : isabmonoidop (BinaryOperations.op2 (X := X))) (div : X -> ∀ y : X, lt (unel_is H0) y -> X) (cst : nat -> X) :=
  isEffectiveOrder le lt
  × isantisymm le
  × (∀ x y : X, le y (addinv x) -> BinaryOperations.op1 (addinv (BinaryOperations.op1 x y)) x = addinv y)
  × (∀ x y : X, addinv (BinaryOperations.op2 x y) = BinaryOperations.op1 (BinaryOperations.op2 (addinv x) y) (addinv y))
  × (lt (unel_is H0) (unel_is H1)) × (∀ x : X, le (unel_is H0) x × le x (unel_is H1))
  × ((unel_is H1) = addinv (unel_is H0)) × (∀ x : X, addinv (addinv x) = x)
  × (∀ x y z : X, le x (addinv y) -> BinaryOperations.op2 (BinaryOperations.op1 x y) z = BinaryOperations.op1 (BinaryOperations.op2 x z) (BinaryOperations.op2 y z))
  × (∀ n : nat, cst n = addinv (natmult (X := setwithbinop1 X ,, pr1 H0) n (cst n)))
  × (∀ x : X, lt (unel_is H0) x -> ∃ n : nat, le (cst n) x)
  × (∀ x y z : X, le x (addinv y) -> lt y z -> lt (BinaryOperations.op1 x y) (BinaryOperations.op1 x z))
  × (∀ x y z : X, lt (BinaryOperations.op1 x y) (BinaryOperations.op1 x z) -> lt y z)
  × (∀ x y z : X, lt (unel_is H0) x -> lt y z -> lt (BinaryOperations.op2 x y) (BinaryOperations.op2 x z))
  × (∀ x y z : X, lt (BinaryOperations.op2 x y) (BinaryOperations.op2 x z) -> lt y z)
  × (∀ x y : X, lt x y -> lt (addinv y) (addinv x))
  × (∀ (x y : X) (Hy : lt (unel_is H0) y), le x y -> BinaryOperations.op2 y (div x y Hy) = x)
  × (∀ (x y : X) (Hy : lt (unel_is H0) y), le y x -> (div x y Hy) = (unel_is H1)).

Definition unit_interval :=
  Σ (X : setwith2binop) (le lt : hrel X) (H0 : isabmonoidop (BinaryOperations.op1 (X := X))) (H1 : isabmonoidop (BinaryOperations.op2 (X := X))) (addinv : unop X) (div : X -> ∀ y : X, lt (unel_is H0) y -> X) (cst : nat -> X), is_unit_interval le lt H0 addinv H1 div  cst.

Definition pr1unit_interval : unit_interval -> setwith2binop := pr1.
Coercion pr1unit_interval : unit_interval >-> setwith2binop.

Section unit_interval.

Context {X : unit_interval}.

Definition UIle : hrel X := pr1 (pr2 X).
Definition UIlt : hrel X := pr1 (pr2 (pr2 X)).

Definition UIaddmonoid : abmonoid :=
  setwithbinop1 X ,, (pr1 (pr2 (pr2 (pr2 X)))).
Definition UImultmonoid : abmonoid :=
  setwithbinop2 X ,, (pr1 (pr2 (pr2 (pr2 (pr2 X))))).

Definition UIzero : X := unel UIaddmonoid.
Definition UIone : X := unel UImultmonoid.

Local Lemma UIaux_1 :
  Σ (addinv : unop X) (div : X -> ∀ y : X, UIlt UIzero y -> X) (cst : nat -> X),
  is_unit_interval UIle UIlt (pr2 UIaddmonoid) addinv (pr2 UImultmonoid) div cst.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 X))))).
Qed.

Definition UIplus : binop X := BinaryOperations.op1.
Definition UIaddinv : unop X := pr1 UIaux_1.
Definition UImult : binop X := BinaryOperations.op2.
Definition UIdiv : X -> ∀ y : X, UIlt UIzero y -> X :=
  pr1 (pr2 UIaux_1).
Definition UIcst : nat -> X :=
  pr1 (pr2 (pr2 UIaux_1)).

Definition UIminus : binop X :=
  λ x y : X, UIaddinv (UIplus (UIaddinv x) y).
Definition UImax : binop X :=
  λ x y : X, UIplus (UIminus x y) y.
Definition UImin : binop X :=
  λ x y : X, UIaddinv (UIplus (UIminus y x) (UIaddinv y)).

Lemma is_unit_interval_UI :
  is_unit_interval UIle UIlt (pr2 UIaddmonoid) UIaddinv (pr2 UImultmonoid) UIdiv UIcst.
Proof.
  exact (pr2 (pr2 (pr2 UIaux_1))).
Qed.

Lemma isEffectiveOrder_UIle_UIlt : isEffectiveOrder UIle UIlt.
Proof.
  exact (pr1 is_unit_interval_UI).
Qed.
Lemma isrefl_UIle : isrefl UIle.
Proof.
  exact (pr2 (pr1 (pr1 isEffectiveOrder_UIle_UIlt))).
Qed.
Lemma isirrefl_UIlt : isirrefl UIlt.
Proof.
  exact (pr2 (pr2 (pr1 isEffectiveOrder_UIle_UIlt))).
Qed.
Lemma isantisymm_UIle : isantisymm UIle.
Proof.
  exact (pr1 (pr2 is_unit_interval_UI)).
Qed.
Lemma not_UIlt_UIle :
  ∀ x y : X, ¬ UIlt x y <-> UIle y x.
Proof.
  exact (pr1 (pr2 isEffectiveOrder_UIle_UIlt)).
Qed.

Lemma UIplus_addinv :
  ∀ x y : X,
    UIle y (UIaddinv x) -> UIplus (UIaddinv (UIplus x y)) x = UIaddinv y.
Proof.
  exact (pr1 (pr2 (pr2 is_unit_interval_UI))).
Qed.

Lemma UImult_addinv:
  ∀ x y : X, UIaddinv (UImult x y) = UIplus (UImult (UIaddinv x) y) (UIaddinv y).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 is_unit_interval_UI)))).
Qed.
Lemma UIlt_zero_one : UIlt UIzero UIone.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 is_unit_interval_UI))))).
Qed.
Lemma UIge_zero :
  ∀ x : X, UIle UIzero x.
Proof.
  intros x.
  apply (pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 is_unit_interval_UI))))) x)).
Qed.
Lemma UIle_one :
  ∀ x : X, UIle x UIone.
Proof.
  intros x.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 is_unit_interval_UI))))) x)).
Qed.
Local Lemma UIaux_2 :
  UIone = UIaddinv UIzero
  × (∀ x : X, UIaddinv (UIaddinv x) = x)
  × (∀ x y z : X,
       UIle x (UIaddinv y) → (UImult (UIplus x y) z) = UIplus (UImult x z) (UImult y z))
  × (∀ n : nat, UIcst n = UIaddinv (natmult (X := UIaddmonoid) n (UIcst n)))
  × (∀ x : X, UIlt UIzero x
              → ∃ n : nat, UIle (UIcst n) x)
  × (∀ x y z : X,
       UIle x (UIaddinv y)
       → UIlt y z → UIlt (UIplus x y) (UIplus x z))
  × (∀ x y z : X, UIlt (UIplus x y) (UIplus x z) → UIlt y z)
  × (∀ x y z : X,
       UIlt UIzero x
       → UIlt y z → UIlt (UImult x y) (UImult x z))
  × (∀ x y z : X, UIlt (UImult x y) (UImult x z) → UIlt y z)
  × (∀ x y : X,
       UIlt x y → UIlt (UIaddinv y) (UIaddinv x))
  × (∀ (x y : X) (Hy : UIlt UIzero y),
       UIle x y → UImult y (UIdiv x y Hy) = x)
  × (∀ (x y : X) (Hy : UIlt UIzero y),
       UIle y x → UIdiv x y Hy = UIone).
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 is_unit_interval_UI)))))).
Qed.
Lemma UIaddinv_zero :
  UIone = UIaddinv UIzero.
Proof.
  exact (pr1 UIaux_2).
Qed.
Lemma isinvol_UIaddinv :
  ∀ x : X, UIaddinv (UIaddinv x) = x.
Proof.
  exact (pr1 (pr2 UIaux_2)).
Qed.
Lemma isldistr_UIplus_mult :
  ∀ x y z : X,
    UIle x (UIaddinv y) → (UImult (UIplus x y) z) = UIplus (UImult x z) (UImult y z).
Proof.
  exact (pr1 (pr2 (pr2 UIaux_2))).
Qed.
Lemma UIcst_carac :
  ∀ n : nat, UIcst n = UIaddinv (natmult (X := UIaddmonoid) n (UIcst n)).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 UIaux_2)))).
Qed.
Lemma isarch_UI :
  ∀ x : X, UIlt UIzero x → ∃ n : nat, UIle (UIcst n) x.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 UIaux_2))))).
Qed.
Lemma UIplus_ltcompat_l :
  ∀ x y z : X,
    UIle x (UIaddinv y)
    → UIlt y z → UIlt (UIplus x y) (UIplus x z).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 UIaux_2)))))).
Qed.
Lemma UIplus_ltcompat_l' :
  ∀ x y z : X, UIlt (UIplus x y) (UIplus x z) → UIlt y z.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 UIaux_2))))))).
Qed.
Lemma UIplus_lecompat_l :
  ∀ x y z : X,
    UIle y z → UIle (UIplus x y) (UIplus x z).
Proof.
  intros x y z H.
  apply not_UIlt_UIle.
  intros H0.
  apply (pr2 (not_UIlt_UIle _ _)) in H.
  apply H ; revert H0.
  apply UIplus_ltcompat_l'.
Qed.
Lemma UIplus_lecompat_l' :
  ∀ x y z : X,
    UIle x (UIaddinv z)
    → UIle (UIplus x y) (UIplus x z) → UIle y z.
Proof.
  intros x y z H0 H.
  apply not_UIlt_UIle.
  intros H1.
  apply (pr2 (not_UIlt_UIle _ _)) in H.
  apply H ; revert H1.
  apply UIplus_ltcompat_l.
  exact H0.
Qed.
Lemma UIplus_eqcompat_l' :
  ∀ x y z : X,
    UIle x (UIaddinv y)
    → UIle x (UIaddinv z)
    → (UIplus x y) = (UIplus x z) → y = z.
Proof.
  intros x y z Hy Hz H.
  apply isantisymm_UIle.
  apply UIplus_lecompat_l' with x.
  exact Hz.
  rewrite H.
  apply isrefl_UIle.
  apply UIplus_lecompat_l' with x.
  exact Hy.
  rewrite H.
  apply isrefl_UIle.
Qed.

Lemma UImult_ltcompat_l :
  ∀ x y z : X,
    UIlt UIzero x
    → UIlt y z → UIlt (UImult x y) (UImult x z).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 UIaux_2)))))))).
Qed.
Lemma UImult_ltcompat_l' :
  ∀ x y z : X, UIlt (UImult x y) (UImult x z) → UIlt y z.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 UIaux_2))))))))).
Qed.
Lemma UIaddinv_lt :
  ∀ x y : X,
    UIlt x y → UIlt (UIaddinv y) (UIaddinv x).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 UIaux_2)))))))))).
Qed.
Lemma UIaddinv_le :
  ∀ x y : X,
    UIle x y → UIle (UIaddinv y) (UIaddinv x).
Proof.
  intros x y H.
  apply not_UIlt_UIle ; intro H0.
  apply (pr2 (not_UIlt_UIle _ _)) in H.
  apply H.
  rewrite <- (isinvol_UIaddinv y), <- (isinvol_UIaddinv x).
  now apply UIaddinv_lt.
Qed.
Lemma UIdiv_carac_1 :
  ∀ (x y : X) (Hy : UIlt UIzero y),
    UIle x y → UImult y (UIdiv x y Hy) = x.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 UIaux_2))))))))))).
Qed.
Lemma UIdiv_carac_2 :
  ∀ (x y : X) (Hy : UIlt UIzero y),
       UIle y x → UIdiv x y Hy = UIone.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 UIaux_2))))))))))).
Qed.

Lemma UIminus_diag :
  ∀ x y : X, UIle x y -> UIminus x y = UIzero.
Proof.
  intros x y H.
  unfold UIminus.
  apply UIaddinv_le in H.
  apply UIplus_addinv in H.
  rewrite isinvol_UIaddinv in H.
  rewrite <- H.


  rewrite <- (isinvol_UIaddinv UIzero), <- UIaddinv_zero.
  rewrite <- H.
  rewrite (commax UIaddmonoid).
  apply UIplus_eqcompat_l' with y.
  rewrite isinvol_UIaddinv.
  admit.
  rewrite <- UIaddinv_zero.
  apply UIle_one.
  rewrite (commax UIaddmonoid).
  rewrite UIplus_addinv.

Qed.
Lemma islabsorb_UIone_mult :
  ∀ x : X, UImult x UIzero = UIzero.
Proof.
Qed.

End unit_interval.

Check UIdiv.

(** ** Pointed Subdivision *)

Definition Sequence_fun {X : UU} (l : Sequence X) (k : nat) : unit ⨿ X :=
  match natlthorgeh k (length l) with
  | ii1 Hk => ii2 (l (k ,, Hk))
  | ii2 Hk => ii1 tt
  end.

Definition Sequence_first {X : UU} (l : Sequence X) : unit ⨿ X :=
  Sequence_fun l O.
Definition Sequence_last {X : UU} (l : Sequence X) : unit ⨿ X :=
  Sequence_fun l (pred (length l)).


Section pointed_subdivision.

Context {X : unit_interval}.

Definition is_pointed_subdivision (lx : Sequence X) (ly : nat -> X) : UU :=
  (Sequence_first lx = ii2 UIzero × Sequence_last lx = ii2 UIone)
    × (∀ (k : nat) (x y : X),
          Sequence_fun lx k = ii2 x -> Sequence_fun lx (S k) = ii2 y -> UIle x (ly k) × UIle (ly k) y).

Definition pointed_subdivision :=
  Σ lx ly, is_pointed_subdivision lx ly.

Definition ps_lx (s : pointed_subdivision) : Sequence X := pr1 s.
Definition ps_ly (s : pointed_subdivision) : (nat -> X) := pr1 (pr2 s).
Definition ps_size (s : pointed_subdivision) : nat := length (pr1 s).
Definition Sequence_step (s : Sequence X) : X.
Proof.
  intros (n,lx).
  induction n.
  - apply UIzero.
  - destruct n.
    + apply UIzero.
    + apply UImax.
      * apply IHn.
        intros m.
        apply lx.
        apply dni_lastelement.
        apply m.
      * apply UIminus.
        apply lx.
        apply lastelement.
        apply lx.
        apply dni_lastelement.
        apply lastelement.
Defined.
Definition ps_step (s : pointed_subdivision) : X :=
  Sequence_step (ps_lx s).

Lemma ps_lx_O (s : pointed_subdivision) : Sequence_first (ps_lx s) = ii2 UIzero.
Proof.
  intros s.
  exact (pr1 (pr1 (pr2 (pr2 s)))).
Qed.
Lemma ps_lx_last (s : pointed_subdivision) : Sequence_last (ps_lx s) = ii2 UIone.
Proof.
  intros s.
  exact (pr2 (pr1 (pr2 (pr2 s)))).
Qed.

Lemma ps_size_ge_2 :
  ∀ s : pointed_subdivision, 2 ≤ ps_size s.
Proof.
  intros (lx,(ly,((H0,H1),Hl))).
  unfold ps_size ; simpl pr1.
  clear -H0 H1.
  destruct lx as [n lx].
  unfold length ; simpl pr1.
  destruct n as [ | n].
  easy.
  destruct n as [ | n].
  apply ii2_injectivity in H0.
  apply ii2_injectivity in H1.
  apply fromempty.
  apply (isirrefl_UIlt (lx (● O)%stn)).
  pattern (lx (● O)%stn) at 1.
  rewrite H0.
  pattern (lx (● O)%stn) at 1.
  rewrite H1.
  exact UIlt_zero_one.
  easy.
Qed.

Definition pointed_subdivision_Chasles (p : X)
           (s1 s2 : pointed_subdivision) : pointed_subdivision.
Proof.
  intros p s1 s2.

  set (f1 := λ x : X, UImult p x).
  set (f2 := λ x : X, UImult (UIaddinv p) x).

  simple refine (tpair _ _ _).
  exists ((ps_size s1 - 1) + ps_size s2)%nat.
  intros k.
  apply (invmap (weqfromcoprodofstn _ _)) in k.
  destruct k as [k | k].
  apply f1.
  apply (pr2 (ps_lx s1)).
  simple refine (tpair _ _ _).
  apply (pr1 k).
  apply natlthlehtrans with (1 := pr2 k).
  apply natminuslehn.
  apply f2.
  apply (pr2 (ps_lx s2)).
  apply k.

  simple refine (tpair _ _ _).
  intros k.
  destruct (natlthorgeh k (ps_size s1)) as [Hk | Hk].
  apply f1.
  apply (ps_ly s1).
  apply k.
  apply f2.
  apply (ps_ly s2).
  apply (k - ps_size s1)%nat.

  repeat split.
  - generalize (ps_lx_O s1).
    unfold Sequence_first, Sequence_fun ; simpl ; intros H.
    destruct natlthorgeh as [H0 | H0].
    destruct natlthorgeh as [H1 | H1].
    unfold invmap ; simpl.
    unfold weqccontrhfiber ; simpl.
    destruct natgthorleh as [H2 | H2] ; simpl.
    assert (UIzero = f1 UIzero).
    { apply pathsinv0.
      Search

  Search nat coprod.

  repeat split.
  - rewrite <- (ps_lx_O l1).
    case natlthorgeh ; intros H.
    + reflexivity.
    + apply nat0gehtois0 in H.
      rewrite H, natminuseqn.
      now rewrite (ps_lx_O l2), <- H, (ps_lx_last l1).
  - intros k Hk.
    case natlthorgeh ; intros H.
    apply fromempty.
    revert H.
    apply natgehtonegnatlth.
    eapply istransnatleh, Hk.
    now apply natgehplusnmn.
    apply ps_lx_last'.
    apply natlehandplusrinv with (ps_size l1).
    eapply istransnatleh, minusplusnmmineq.
    now rewrite natpluscomm.
  - intros k l m Hk Hl.
    repeat destruct natlthorgeh.
    + now apply ps_lx_Chasles.
    + apply fromempty ; revert h0.
      apply natlehtonegnatgth.
      now eapply istransnatleh, Hl.
    + rewrite !Habc, <- assocax.
      pattern b at 2 ;
        rewrite <- (ps_lx_last l1), (ps_lx_Chasles l1 _ l), ps_lx_last.
      reflexivity.
      exact Hk.
      now apply natlthtoleh.
    + rewrite !Habc, assocax.
      pattern b at 3 ;
        rewrite <- (ps_lx_O l2), (ps_lx_Chasles l2 _ (l - ps_size l1)), ps_lx_O.
      reflexivity.
      easy.
      apply natlehandplusrinv with (ps_size l1).
      now rewrite !minusplusnmm.
    + apply fromempty ; revert h1.
      apply natlehtonegnatgth.
      now eapply istransnatleh, Hk.
    + apply fromempty ; revert h0.
      apply natlehtonegnatgth.
      now eapply istransnatleh, Hl.
    + apply fromempty ; revert h1.
      apply natlehtonegnatgth.
      now eapply istransnatleh, Hk.
    + apply ps_lx_Chasles.
      apply natlehandplusrinv with (ps_size l1).
      now rewrite !minusplusnmm.
      apply natlehandplusrinv with (ps_size l1).
      now rewrite !minusplusnmm.
  - intros k.
    case natlthorgeh ; intros Hk1.
    + case natlthorgeh ; intros Hk2.
      * now apply (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 l1)))))).
      * assert (ps_size l1 = S k).
        { apply isantisymmnatgeh.
          now apply natgthtogehsn, Hk1.
          now apply Hk2. }
        rewrite H, minuseq0.
        rewrite ps_lx_O.
        pattern b at 4 6.
        rewrite <- (ps_lx_last l1).
        rewrite H.
        now apply (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 l1)))))).
        apply isreflnatleh.
    + case natlthorgeh ; intros Hk2.
      * apply fromempty.
        revert Hk2.
        apply natgehtonegnatlth.
        now apply natgehtogehs.
      * rewrite minusSnm.
        apply (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 l2)))))).
        exact Hk1.
Defined.

Definition pointed_subdivision_filter (a b : M) (H : ∀ eps : NR, NnMlt NR 0%addmonoid eps -> ∃ (n : nat) (lx : nat -> M), lx O = a × (∀ k : nat, (n ≤ k) -> lx k = b) × (∀ k, (k < n)%nat -> ball (lx k) eps (lx (S k))) × (∀ k l m : nat,
   k ≤ l ->
   l ≤ m ->
   dist (lx k) (lx m) = (dist (lx k) (lx l) * dist (lx l) (lx m))%multmonoid)) : Filter (X := pointed_subdivision a b).
Proof.
  intros a b Hnr.
  simple refine (mkFilter _ _ _ _ _).
  - intros P.
    apply (∃ eps : NR, (NnMlt NR 0%addmonoid eps) × (∀ s, (∀ k : nat, (k < pr1 s)%nat -> ball (pr1 (pr2 s) k) eps (pr1 (pr2 s) (S k))) -> P s)).
  - intros A B H.
    apply hinhfun.
    intros (e,(He0,He)).
    exists e ; split.
    exact He0.
    intros s Hs.
    apply H, He, Hs.
  - generalize (NnM_nottrivial NR).
    apply hinhfun.
    intros (x0,Hx0).
    now exists x0.
  - intros A B.
    apply hinhuniv2.
    intros (ea,(Ha0,Ha)) (eb,(Hb0,Hb)).
    generalize (NnMmin_carac ea eb).
    apply hinhfun.
    intros (e,(Hea,(Heb,He))).
    exists e ; split.
    now apply He.
    intros s Hs.
    split.
    + apply Ha.
      intros k Hk.
      apply ball_le with (1 := Hea).
      now apply Hs.
    + apply Hb.
      intros k Hk.
      apply ball_le with (1 := Heb).
      now apply Hs.
  - intros H ; revert H.
    apply (hinhuniv (P := hProppair _ isapropempty)).
    intros (e,(He0,He)).
    generalize (Hnr e He0).
    apply hinhuniv.
    intros (n,(lx,(Ha,(Hb,Hl)))).
    simple refine (He _ _).
    exists n, lx, lx.
    repeat split.
    exact Ha.
    exact Hb.
    apply (pr2 Hl).
    intros k.
    rewrite dist_0, lunax.
    reflexivity.
    simpl pr1.
    exact (pr1 Hl).
Defined.

End pointed_subdivision.

Section Riemann_sum.

Context {NR : NonnegativeRig}
        {K : absrng NR}.
Context {V : module K}.

Definition Riemann_sum_aux (f : K -> V) (lx ly : nat -> K) : nat -> V :=
  fix Rsum n :=
    match n with
    | O => 0%addmonoid
    | S n => (Rsum n + scal (lx (S n) - lx n)%rng (f (ly n)))%addmonoid
    end.

Lemma Riemann_sum_O :
  ∀ (f : K -> V) (lx ly : nat -> K),
    Riemann_sum_aux f lx ly O = 0%addmonoid.
Proof.
  intros.
  reflexivity.
Qed.
Lemma Riemann_sum_S :
  ∀ (f : K -> V) (lx ly : nat -> K) (n : nat),
    (Riemann_sum_aux f lx ly (S n) = Riemann_sum_aux f lx ly n + scal (lx (S n) - lx n)%rng (f (ly n)))%addmonoid.
Proof.
  intros.
  reflexivity.
Qed.

Lemma Riemann_sum_ext :
  ∀ (f : K -> V) (lx1 lx2 ly1 ly2 : nat -> K) (n : nat),
    (∀ k : nat, k ≤ n -> lx1 k = lx2 k)
    -> (∀ k : nat, (k < n)%nat -> ly1 k = ly2 k)
    -> ∀ k : nat, k ≤ n -> Riemann_sum_aux f lx1 ly1 k = Riemann_sum_aux f lx2 ly2 k.
Proof.
  intros f lx1 lx2 ly1 ly2 n Hlx Hly.
  induction k ; intros Hk.
  - reflexivity.
  - rewrite !Riemann_sum_S.
    rewrite IHk, !Hly, !Hlx.
    reflexivity.
    eapply istransnatleh, Hk.
    now apply natlehnsn.
    exact Hk.
    now apply natlehsntolth.
    eapply istransnatleh, Hk.
    now apply natlehnsn.
Qed.

Definition Riemann_sum {a b : K} (f : K -> V) (s : pointed_subdivision (M := metric_norm (X := absrng_to_NormedModule K)) a b) : V :=
  Riemann_sum_aux f (pr1 (pr2 s)) (pr1 (pr2 (pr2 s))) (pr1 s).

Lemma Riemann_sum_point {a : K} (f : K -> V) (s : pointed_subdivision (M := metric_norm (X := absrng_to_NormedModule K)) a a) :
  Riemann_sum f s = 0%addmonoid.
Proof.
  intros a f s.
  generalize (ps_lx_point s).
  destruct s as (n,(lx,(ly,H))).
  unfold Riemann_sum, ps_lx.
  simpl pr1 ; clear H ; intro H.
  induction n.
  reflexivity.
  rewrite Riemann_sum_S.
  rewrite IHn, !H.
  rewrite rngrinvax1.
  rewrite islabsorb_scal_0.
  apply lunax.
Qed.

(* Lemma Riemann_sum_Chasles {a b c : K} (f : K -> V) s1 s2 H :
  (Riemann_sum f s1 + Riemann_sum f s2 = Riemann_sum f (pointed_subdivision_Chasles (M := metric_norm (X := absrng_to_NormedModule K)) a b c s1 s2 H))%addmonoid.
Proof.
  unfold Riemann_sum.
  intros a b c f (n1,(lx1,(ly1,H1))) (n2,(lx2,(ly2,H2))).
  simpl pr1.
  destruct H1 as [<- (Hlx,_)].
  destruct H2 as [<- (Hc,_)].
  generalize (isreflnatleh n2).
  generalize n2 at -2.
  induction n0 as [ | n] ; intros Hn.
  - rewrite (runax V), natplusr0.
    apply Riemann_sum_ext with n1.
    + intros k Hk.
      destruct natlthorgeh.
      reflexivity.
      rewrite minuseq0.
      now apply Hlx.
      exact Hk.
    + intros k Hk.
      destruct natlthorgeh.
      reflexivity.
      apply fromempty ; revert h.
      now apply natlthtonegnatgeh.
    + now apply isreflnatleh.
  - rewrite <- plus_n_Sm, !Riemann_sum_S.
    rewrite <- IHn, <- (assocax V).
    apply maponpaths.
    destruct natlthorgeh.
    + apply fromempty ; revert h.
      apply natgehtonegnatlth.
      apply natgehtogehs.
      apply natgehplusnmn.
    + destruct natlthorgeh.
      apply fromempty ; revert h0.
      apply natgehtonegnatlth.
      apply natgehplusnmn.
      rewrite minusSnm.
      rewrite natpluscomm, plusminusnmm.
      reflexivity.
      apply natgehplusnmn.
    + eapply istransnatleh, Hn.
      now apply natlehnsn.
Qed.*)

End Riemann_sum.

Section Riemann_integral.

Context {NR : NonnegativeRig}
        {K : absrng NR}.
Context {V : NormedModule K}.
Context (Hnr : ∀ a b : K,
               ∀ eps : NR,
       (NnRlt NR 0 eps ->
       ∃ (n : nat) (lx : nat -> K),
       lx O = a
       × (∀ k : nat, n ≤ k -> lx k = b)
       × (∀ k : nat, (k < n)%nat -> ball (M := metric_norm (X := absrng_to_NormedModule K)) (lx k) eps (lx (S k)))
       × (∀ k l m : nat,
            k ≤ l ->
            l ≤ m ->
            dist (X := metric_norm (X := absrng_to_NormedModule K)) (lx k) (lx m) =
            (dist (X := metric_norm (X := absrng_to_NormedModule K)) (lx k) (lx l) * dist (X := metric_norm (X := absrng_to_NormedModule K)) (lx l) (lx m))%multmonoid))).

Definition is_Rint (f : K -> V) (a b : K) (If : V) :=
  is_lim (Riemann_sum f) (pointed_subdivision_filter (M := metric_norm (X := absrng_to_NormedModule K)) a b (Hnr a b)) If.

Lemma is_Rint_point (f : K -> V) (a : K) :
  is_Rint f a a 0%addmonoid.
Proof.
  intros f a.
  apply (pr2 (is_lim_aux (M := metric_norm) _ _ _)).
  intros (e,He).
  apply hinhpr.
  exists e.
  split.
  exact He.
  intros s Hs.
  rewrite Riemann_sum_point.
  apply ball_center.
  exact He.
Qed.

End Riemann_integral.