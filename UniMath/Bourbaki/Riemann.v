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

Definition is_min {X : hSet} (le : hrel X) (min : binop X) :=
  (iscomm min)
    × (∀ x y, le (min x y) x)
    × (∀ x y, le x y -> min x y = x).

Definition is_addcompl {X : abmonoid} (x1 : X) (le : hrel X) (addcompl : unop X) (min : binop X) :=
  (addcompl 0%addmonoid = x1)
    × (∀ x : X, addcompl (addcompl x) = x)
    × (∀ x y : X, (x + addcompl (x + y))%addmonoid = min x (addcompl y)).

Definition is_troncdiv {X : abmonoid} (x0 : X) (le lt : hrel X) (div : X -> ∀ y : X, lt x0 y -> X) (min : binop X) :=
  (∀ (x y : X) (Hy : lt x0 y), (y * div x y Hy)%multmonoid = min x y).

Definition is_invSn {X : abmonoid} (le lt : hrel X) (invSn : nat -> X) (addcompl : unop X) :=
  (∀ n : nat, invSn n = addcompl (natmult n (invSn n)))
    × (∀ x : X, lt 0%addmonoid x -> ∃ n : nat, le (invSn n) x).


Definition is_unit_interval {X : setwith2binop} (le lt : hrel X) (min : binop X)
           (H0 : isabmonoidop (BinaryOperations.op1 (X := X))) (addcompl : unop X)
           (H1 : isabmonoidop (BinaryOperations.op2 (X := X)))
           (div : X -> ∀ y : X, lt (unel_is H0) y -> X) (invSn : nat -> X) :=
  (isEffectiveOrder le lt)
    × (isantisymm le)
    × (is_min le min)
    × (lt (unel_is H0) (unel_is H1))
    × (∀ x : X, le (unel_is H0) x × le x (unel_is H1))
    × is_addcompl (X := setwithbinop1 X ,, H0) (unel_is H1) le addcompl min
    × is_troncdiv (X := setwithbinop2 X ,, H1) (unel_is H0) le lt div min
    × is_invSn (X := setwithbinop1 X ,, H0) le lt invSn addcompl
    × (∀ x y z : X,
         le x (addcompl y) → ((x + y) * z)%rng = (x * z + y * z)%rng)
    × (∀ x y : X, addcompl (x * y)%rng = (addcompl x * y + addcompl y)%rng)
    × (∀ x y z : X,
         le x (addcompl y) → lt y z → lt (x + y)%rng (x + z)%rng)
    × (∀ x y z : X, lt (x + y)%rng (x + z)%rng → lt y z)
    × (∀ x y : X, lt x y → lt (addcompl y) (addcompl x))
    × (∀ x y z : X,
         lt (unel_is H0) x → lt y z → lt (x * y)%rng (x * z)%rng)
    × (∀ x y z : X, lt (x * y)%rng (x * z)%rng → lt y z).

Definition unit_interval :=
  Σ (X : setwith2binop) (le lt : hrel X) (min : binop X)
    (H0 : isabmonoidop (BinaryOperations.op1 (X := X)))
    (H1 : isabmonoidop (BinaryOperations.op2 (X := X)))
    (addcompl : unop X) (div : X -> ∀ y : X, lt (unel_is H0) y -> X)
    (invSn : nat -> X), is_unit_interval le lt min H0 addcompl H1 div invSn.

Definition pr1unit_interval : unit_interval -> setwith2binop := pr1.
Coercion pr1unit_interval : unit_interval >-> setwith2binop.

Section unit_interval.

Context {X : unit_interval}.

(** Interface *)

Definition UIle : hrel X := pr1 (pr2 X).
Definition UIlt : hrel X := pr1 (pr2 (pr2 X)).
Definition UImin : binop X := pr1 (pr2 (pr2 (pr2 X))).

Local Lemma UI_aux_0 :
  Σ (H0 : isabmonoidop (@BinaryOperations.op1 X))
    (H1 : isabmonoidop (@BinaryOperations.op2 X)) (addcompl : unop X)
    (div : X → ∀ y : X, UIlt (unel_is H0) y → X)
    (invSn : nat → X),
  is_unit_interval UIle UIlt UImin H0 addcompl H1 div invSn.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 X)))).
Qed.

Definition UIaddmonoid : abmonoid :=
  setwithbinop1 X ,, (pr1 UI_aux_0).
Definition UImultmonoid : abmonoid :=
  setwithbinop2 X ,, (pr1 (pr2 UI_aux_0)).

Definition UIzero : X := unel UIaddmonoid.
Definition UIone : X := unel UImultmonoid.
Definition UIplus : binop X := BinaryOperations.op1.
Definition UImult : binop X := BinaryOperations.op2.

Local Lemma UI_aux_1 :
  Σ (addcompl : unop X)
    (div : X → ∀ y : X, UIlt UIzero y → X)
    (invSn : nat → X),
  is_unit_interval UIle UIlt UImin (pr2 UIaddmonoid) addcompl (pr2 UImultmonoid) div invSn.
Proof.
  exact (pr2 (pr2 (UI_aux_0))).
Qed.

Definition UIaddcompl : unop X := pr1 UI_aux_1.
Definition UIdiv : X -> ∀ y : X, UIlt UIzero y -> X := pr1 (pr2 UI_aux_1).
Definition UIinvSn : nat -> X := pr1 (pr2 (pr2 UI_aux_1)).

Definition UIminus : binop X :=
  λ x y : X, UIaddcompl (UIplus (UIaddcompl x) y).
Definition UImax : binop X :=
  λ x y : X, UIplus (UIminus x y) y.

Lemma is_unit_interval_UI :
  is_unit_interval UIle UIlt UImin (pr2 UIaddmonoid) UIaddcompl (pr2 UImultmonoid) UIdiv UIinvSn.
Proof.
  exact (pr2 (pr2 (pr2 UI_aux_1))).
Qed.

(** Order *)

Lemma isEffectiveOrder_UIle_UIlt : isEffectiveOrder UIle UIlt.
Proof.
  exact (pr1 is_unit_interval_UI).
Qed.

Lemma istrans_UIle : istrans UIle.
Proof.
  exact (pr1 (pr1 (pr1 isEffectiveOrder_UIle_UIlt))).
Qed.
Lemma isrefl_UIle : isrefl UIle.
Proof.
  exact (pr2 (pr1 (pr1 isEffectiveOrder_UIle_UIlt))).
Qed.
Lemma isantisymm_UIle : isantisymm UIle.
Proof.
  exact (pr1 (pr2 is_unit_interval_UI)).
Qed.
Lemma istrans_UIlt : istrans UIlt.
Proof.
  exact (pr1 (pr2 (pr1 isEffectiveOrder_UIle_UIlt))).
Qed.
Lemma isirrefl_UIlt : isirrefl UIlt.
Proof.
  exact (pr2 (pr2 (pr1 isEffectiveOrder_UIle_UIlt))).
Qed.

Lemma not_UIlt_UIle :
  ∀ x y : X, ¬ UIlt x y <-> UIle y x.
Proof.
  exact (pr1 (pr2 isEffectiveOrder_UIle_UIlt)).
Qed.
Lemma is_trans_UIlt_UIle :
  ∀ x y z : X, UIlt x y → UIle y z → UIlt x z.
Proof.
  exact (pr1 (pr2 (pr2 isEffectiveOrder_UIle_UIlt))).
Qed.
Lemma is_trans_UIle_UIlt :
  ∀ x y z : X, UIle x y → UIlt y z → UIlt x z.
Proof.
  exact (pr2 (pr2 (pr2 isEffectiveOrder_UIle_UIlt))).
Qed.
Lemma UIlt_zero_one : UIlt UIzero UIone.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 is_unit_interval_UI)))).
Qed.
Lemma UIge_zero :
  ∀ x : X, UIle UIzero x.
Proof.
  intros x.
  apply (pr1 (pr1 (pr2 (pr2 (pr2 (pr2 is_unit_interval_UI)))) _)).
Qed.
Lemma UIle_one :
  ∀ x : X, UIle x UIone.
Proof.
  intros x.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 is_unit_interval_UI)))) _)).
Qed.
Lemma UIlt_UIle :
  ∀ x y : X, UIlt x y -> UIle x y.
Proof.
  intros x y H.
  apply not_UIlt_UIle.
  intros H0.
  apply (isirrefl_UIlt x).
  now apply istrans_UIlt with y.
Qed.

(** minimum *)

Lemma is_min_UImin :
  is_min UIle UImin.
Proof.

Qed.

Local Lemma UI_aux_2 :
  (is_addcompl (X := UIaddmonoid) UIone UIle UIaddcompl UImin)
  × (is_troncdiv (X := UImultmonoid) UIzero UIle UIlt UIdiv UImin)
  × (is_invSn (X := UIaddmonoid) UIle UIlt UIinvSn UIaddcompl)
  × (∀ x y z : X,
       UIle x (UIaddcompl y) → (UImult (UIplus x y) z) = UIplus (UImult x z) (UImult y z))
  × (∀ x y : X,
       UIaddcompl (UImult x y) = UIplus (UImult (UIaddcompl x) y) (UIaddcompl y))
  × (∀ x y z : X,
       UIle x (UIaddcompl y)
       → UIlt y z → UIlt (UIplus x y) (UIplus x z))
  × (∀ x y z : X, UIlt (UIplus x y) (UIplus x z) → UIlt y z)
  × (∀ x y : X, UIlt x y → UIlt (UIaddcompl y) (UIaddcompl x))
  × (∀ x y z : X,
       UIlt UIzero x
       → UIlt y z → UIlt (UImult x y) (UImult x z))
  × (∀ x y z : X,
       UIlt (UImult x y) (UImult x z) → UIlt y z).
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 is_unit_interval_UI))))).
Qed.


(** addition and addcompl *)

Lemma is_addcompl_UIaddcompl :
  is_addcompl (X := UIaddmonoid) UIone UIle UIaddcompl.
Proof.
  exact (pr1 UIaux_2).
Qed.
Lemma isinvol_UIaddcompl :
  ∀ x : X, UIaddcompl (UIaddcompl x) = x.
Proof.
  exact (pr1 is_addcompl_UIaddcompl).
Qed.
Lemma UIaddcompl_zero :
  UIaddcompl UIzero = UIone.
Proof.
  exact (pr1 (pr2 is_addcompl_UIaddcompl)).
Qed.
Lemma UIaddcompl_one :
  UIaddcompl UIone = UIzero.
Proof.
  rewrite <- UIaddcompl_zero.
  apply isinvol_UIaddcompl.
Qed.
Lemma UIplus_addcompl :
  ∀ x y : X,
    UIle y (UIaddcompl x) -> UIplus (UIaddcompl (UIplus x y)) x = UIaddcompl y.
Proof.
  exact (pr2 (pr2 (pr2 is_addcompl_UIaddcompl))).
Qed.
Lemma UIplus_eq_one :
  ∀ x y : X,
    UIle (UIaddcompl x) y -> UIplus x y = UIone.
Proof.
  exact (pr1 (pr2 (pr2 is_addcompl_UIaddcompl))).
Qed.

Lemma UImin_aux :
  ∀ x y : X, UImin x y = UIaddcompl (UIplus (UIminus y x) (UIaddcompl y)).
Proof.
  intros x y.
Qed.

Lemma UIminus_eq_zero :
  ∀ x y : X, UIle x y -> UIminus x y = UIzero.
Proof.
  intros x y H.
  unfold UIminus.
  rewrite <- (isinvol_UIaddcompl UIzero), UIaddcompl_zero.
  apply maponpaths.
  apply UIplus_eq_one.
  now rewrite isinvol_UIaddcompl.
Qed.

Lemma is_troncdiv_UIdiv :
  is_troncdiv (X := UImultmonoid) UIzero UIle UIlt UIdiv.
Proof.
  exact (pr1 (pr2 UIaux_2)).
Qed.
Lemma UImult_UIdiv :
  ∀ (x y : X) (Hy : UIlt UIzero y),
    UIle x y → UImult y (UIdiv x y Hy) = x.
Proof.
  exact (pr1 is_troncdiv_UIdiv).
Qed.
Lemma UIdiv_eq_one :
  ∀ (x y : UImultmonoid) (Hy : UIlt UIzero y),
    UIle y x → UIdiv x y Hy = UIone.
Proof.
  exact (pr2 is_troncdiv_UIdiv).
Qed.

Lemma is_invSn_UIinvSn :
  is_invSn (X := UIaddmonoid) UIle UIlt UIinvSn UIaddcompl.
Proof.
  exact (pr1 (pr2 (pr2 UIaux_2))).
Qed.
Lemma UIinvSn_addcompl :
  ∀ n : nat, UIinvSn n = UIaddcompl (natmult (X := UIaddmonoid) n (UIinvSn n)).
Proof.
  exact (pr1 is_invSn_UIinvSn).
Qed.
Lemma isarchUI :
  ∀ x : X, UIlt UIzero x → ∃ n : nat, UIle (UIinvSn n) x.
Proof.
  exact (pr2 is_invSn_UIinvSn).
Qed.

Lemma isrdistr_UIplus_mult :
  ∀ x y z : X,
    UIle x (UIaddcompl y) → (UImult (UIplus x y) z) = UIplus (UImult x z) (UImult y z).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 UIaux_2)))).
Qed.

Lemma UImult_addcompl:
  ∀ x y : X, UIaddcompl (UImult x y) = UIplus (UImult (UIaddcompl x) y) (UIaddcompl y).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 UIaux_2))))).
Qed.

Lemma UIplus_ltcompat_l :
  ∀ x y z : X,
    UIle x (UIaddcompl y)
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
    UIle x (UIaddcompl z)
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
    UIle x (UIaddcompl y)
    → UIle x (UIaddcompl z)
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

Lemma UIaddcompl_lt :
  ∀ x y : X,
    UIlt x y → UIlt (UIaddcompl y) (UIaddcompl x).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 UIaux_2)))))))).
Qed.
Lemma UIaddcompl_le :
  ∀ x y : X,
    UIle x y → UIle (UIaddcompl y) (UIaddcompl x).
Proof.
  intros x y H.
  apply not_UIlt_UIle ; intro H0.
  apply (pr2 (not_UIlt_UIle _ _)) in H.
  apply H.
  rewrite <- (isinvol_UIaddcompl y), <- (isinvol_UIaddcompl x).
  now apply UIaddcompl_lt.
Qed.

Lemma UImult_ltcompat_l :
  ∀ x y z : X,
    UIlt UIzero x
    → UIlt y z → UIlt (UImult x y) (UImult x z).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 UIaux_2))))))))).
Qed.
Lemma UImult_ltcompat_l' :
  ∀ x y z : X, UIlt (UImult x y) (UImult x z) → UIlt y z.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 UIaux_2))))))))).
Qed.
Lemma UImult_lecompat_l :
  ∀ x y z : X,
    UIle y z → UIle (UImult x y) (UImult x z).
Proof.
  intros x y z H.
  apply not_UIlt_UIle ; intros H0.
  apply (pr2 (not_UIlt_UIle _ _)) in H.
  apply H ; revert H0.
  apply UImult_ltcompat_l'.
Qed.
Lemma UImult_lecompat_l' :
  ∀ x y z : X,
    UIlt UIzero x
    → UIle (UImult x y) (UImult x z) → UIle y z.
Proof.
  intros x y z Hpos H.
  apply not_UIlt_UIle ; intros H0.
  apply (pr2 (not_UIlt_UIle _ _)) in H.
  apply H ; revert H0.
  now apply UImult_ltcompat_l.
Qed.

Lemma UImult_one_l :
  ∀ x : X, UImult x UIone = x.
Proof.
  intros x.
  apply (runax UImultmonoid).
Qed.

Lemma UImult_zero_l :
  ∀ x : X, UImult UIzero x = UIzero.
Proof.
  intros x.
  apply isantisymm_UIle.
  pattern UIzero at 2 ;
    rewrite <- (runax UImultmonoid UIzero).
  apply UImult_lecompat_l.
  apply UIle_one.
  apply UIge_zero.
Qed.
Lemma UImult_zero_r :
  ∀ x : X, UImult x UIzero = UIzero.
Proof.
  intros x.
  pattern UIzero at 2 ;
    rewrite <- (UImult_zero_l x).
  apply (commax UImultmonoid).
Qed.

Lemma UImult_addcompl_l :
  ∀ x y : X, UImult (UIaddcompl x) y = UIminus y (UImult x y).
Proof.
  intros x y.
  unfold UIminus.
  pattern y at 2 ;
    rewrite <- (lunax UImultmonoid y).
  change (unel _) with UIone.
  rewrite UImult_addcompl, UIaddcompl_one.
  rewrite UImult_zero_l.
  rewrite (lunax UIaddmonoid).
  apply (UIplus_eqcompat_l' (UImult x y)).
  { apply UIplus_lecompat_l' with (UImult (UIaddcompl x) y).
    rewrite isinvol_UIaddcompl.
    apply isrefl_UIle.
    rewrite (UIplus_eq_one _ (UIaddcompl _)).
    apply UIle_one.
    apply isrefl_UIle. }
  { rewrite isinvol_UIaddcompl.
    pattern (UImult x y) at 1 ;
      rewrite <- (runax UIaddmonoid (UImult x y)), (commax UIaddmonoid (UIaddcompl _)).
    apply UIplus_lecompat_l.
    apply UIge_zero. }
  rewrite !(commax UIaddmonoid (UImult x y)), (commax UIaddmonoid (UIaddcompl y)).
  change BinaryOperations.op with UIplus.
  rewrite UIplus_addcompl.
  rewrite <- isrdistr_UIplus_mult, UIplus_eq_one.
  now rewrite isinvol_UIaddcompl, (lunax UImultmonoid).
  rewrite isinvol_UIaddcompl.
  apply isrefl_UIle.
  apply isrefl_UIle.
  apply UIaddcompl_le.
  pattern y at 2 ;
    rewrite <- (runax UImultmonoid y), (commax UImultmonoid x).
  apply UImult_lecompat_l.
  apply UIle_one.
Qed.
Lemma isrdistr_UIminus_UImult :
  ∀ x y z : X, UIle y x -> UImult (UIminus x y) z = UIminus (UImult x z) (UImult y z).
Proof.
  intros x y z H.
  unfold UIminus.
  rewrite UImult_addcompl_l, UImult_addcompl ; unfold UIminus.
  apply maponpaths.
  rewrite isrdistr_UIplus_mult.
  rewrite (commax UIaddmonoid), !(assocax UIaddmonoid).
  apply maponpaths.
  apply commax.
  apply UIaddcompl_le.
  exact H.
Qed.

Lemma UIplus_zero_r :
  ∀ x : X, UIplus x UIzero = x.
Proof.
  intros x.
  apply (runax UIaddmonoid).
Qed.

Lemma paths_UIle :
  ∀ x y : X, x = y -> UIle x y.
Proof.
  intros x _ <-.
  apply isrefl_UIle.
Qed.

Lemma UImin_le_l :
  ∀ x y : X, UIle (UImin x y) x.
Proof.
  intros x y.
  unfold UImin, UIminus.
  rewrite UIplus_addcompl.
Qed.

Lemma UImin_gt :
  ∀ k x y : X, UIlt k x -> UIlt k y -> UIlt k (UImin x y).
Proof.
  intros k x y Hx Hy.
  unfold UImin.
  rewrite <- (isinvol_UIaddcompl k).
  apply UIaddcompl_lt.
  apply UIplus_ltcompat_l' with y.
  rewrite (commax UIaddmonoid), (assocax UIaddmonoid), (UIplus_eq_one _ y).

Qed.


End unit_interval.

(** ** Pointed Subdivision *)

Definition Sequence_fun {X : UU} (l : Sequence X) (k : nat) : unit ⨿ X :=
  match natgthorleh (length l) k with
  | ii1 Hk => ii2 (l (k ,, Hk))
  | ii2 Hk => ii1 tt
  end.
Lemma Sequence_fun_ii1 {X : UU} :
  ∀ (l : Sequence X) k,
    (length l ≤ k) -> Sequence_fun l k = ii1 tt.
Proof.
  intros X l k Hk.
  unfold Sequence_fun.
  destruct natgthorleh as [H | H].
  apply fromempty ; revert H.
  now apply natlehneggth.
  reflexivity.
Qed.
Lemma Sequence_fun_ii2 {X : UU} :
  ∀ (l : Sequence X) k (Hk : length l > k),
    Sequence_fun l k = ii2 (l (k ,, Hk)).
Proof.
  intros X l k Hk.
  unfold Sequence_fun.
  destruct natgthorleh as [H | H].
  apply maponpaths, maponpaths.
  now apply subtypeEquality_prop.
  apply fromempty ; revert Hk.
  now apply natlehneggth.
Qed.
Lemma Sequence_fun_ii2' {X : UU} :
  ∀ (l : Sequence X) k x,
    Sequence_fun l k = ii2 x -> length l > k.
Proof.
  intros X l k x.
  unfold Sequence_fun.
  now destruct natgthorleh as [H | H] ;
    intros Hk.
Qed.

Definition Sequence_first {X : UU} (l : Sequence X) : unit ⨿ X :=
  Sequence_fun l O.
Definition Sequence_last {X : UU} (l : Sequence X) : unit ⨿ X :=
  Sequence_fun l (length l - 1).


Section pointed_subdivision.

Context {X : unit_interval}.

Definition is_pointed_subdivision (lx : Sequence X) (ly : nat -> X) : UU :=
  (Sequence_first lx = ii2 UIzero × Sequence_last lx = ii2 UIone)
    × (∀ (k : nat) x y, Sequence_fun lx k = ii2 x -> Sequence_fun lx (S k) = ii2 y -> UIle x (ly k) × UIle (ly k) y).

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
Lemma ps_between (s : pointed_subdivision) :
  ∀ (k : nat) (x y : X),
    Sequence_fun (ps_lx s) k = ii2 x -> Sequence_fun (ps_lx s) (S k) = ii2 y
    -> UIle x (ps_ly s k) × UIle (ps_ly s k) y.
Proof.
  intro s.
  exact (pr2 (pr2 (pr2 s))).
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

Definition tocoprodofstn n m : stn (n + m)%nat -> coprod (stn n) (stn m).
Proof.
  intros n m k.
  destruct (natgthorleh n (pr1 k)) as [Hk | Hk].
  - apply (ii1 (pr1 k ,, Hk)).
  - apply ii2.
    simple refine (tpair _ _ _).
    apply (pr1 k - n)%nat.
    abstract (apply natlthandplusrinv with n ;
      rewrite minusplusnmm, (natpluscomm m n) ;
      [ apply (pr2 k) | apply Hk ]).
Defined.

Definition pointed_subdivision_Chasles (p : X)
           (s1 s2 : pointed_subdivision) : pointed_subdivision.
Proof.
  intros p s1 s2.

  set (f1 := λ x : X, UImult p x).
  set (f2 := λ x : X, UIplus p (UImult (UIaddcompl p) x)).

  simple refine (tpair _ _ _).
  exists ((ps_size s1 - 1) + ps_size s2)%nat.
  intros k.
  apply tocoprodofstn in k.
  destruct k as [k | k].
  apply f1.
  apply (pr2 (ps_lx s1)).
  simple refine (tpair _ _ _).
  apply (pr1 k).
  abstract apply natlthlehtrans with (1 := pr2 k), natminuslehn.
  apply f2.
  apply (pr2 (ps_lx s2)).
  apply k.

  simple refine (tpair _ _ _).
  intros k.
  destruct (natgthorleh (ps_size s1 - 1) k) as [Hk | Hk].
  apply f1.
  apply (ps_ly s1).
  apply k.
  apply f2.
  apply (ps_ly s2).
  apply (k - (ps_size s1 - 1))%nat.

  split ; [split | ] ; simpl.
  - generalize (ps_lx_O s1).
    unfold Sequence_first, Sequence_fun ; simpl ; intros H.
    destruct natgthorleh as [H0 | H0] ; [ | easy].
    apply ii2_injectivity in H.
    destruct natgthorleh as [H1 | H1].
    unfold tocoprodofstn ; simpl.
    destruct natgthorleh as [H2 | H2] ; simpl.
    + assert (UIzero = f1 UIzero).
      { unfold f1.
        pattern (@UIzero X) at 1 ;
          rewrite <- (UImult_zero_l p).
        apply (commax UImultmonoid). }
      rewrite X0, <- H ; clear X0.
      apply maponpaths, maponpaths, maponpaths.
      now apply subtypeEquality_prop.
    + apply fromempty ; revert H2.
      apply natlthtonegnatgeh.
      apply natlthlehtrans with (2 - 1)%nat.
      reflexivity.
      apply natgehandminusr, ps_size_ge_2.
    + apply fromempty ; revert H1.
      apply natlthtonegnatgeh.
      apply natlthlehtrans with (2 - 1 + 2)%nat.
      reflexivity.
      apply natlehandplus.
      apply natgehandminusr, ps_size_ge_2.
      apply ps_size_ge_2.
  - generalize (ps_lx_last s2).
    unfold Sequence_last, Sequence_fun ; simpl ; intros H.
    destruct natgthorleh as [H0 | H0] ; [ | easy].
    apply ii2_injectivity in H.
    destruct natgthorleh as [H1 | H1].
    assert (∀ n m, 0 < m -> ((n+m) - 1)%nat= (n + (m - 1))%nat).
    { destruct m ; simpl ; intro.
      now apply fromempty.
      now rewrite natplusnsm ; simpl ; rewrite !natminuseqn. }
    revert H1 ;
      rewrite (X0 _ (ps_size s2)) ; clear X0 ; [intros H1 | ].
    2: apply natlthlehtrans with 2%nat ;
      [ reflexivity
      | apply ps_size_ge_2 ].
    unfold tocoprodofstn.
    destruct natgthorleh as [H2 | H2] ; simpl.
    + apply fromempty ; revert H2.
      apply natlehneggth.
      now apply natlehnplusnm.
    + assert (UIone = f2 UIone).
      { unfold f2.
        apply pathsinv0.
        apply UIplus_eq_one.
        rewrite UImult_one_l.
        apply isrefl_UIle. }
      rewrite X0, <- H ; clear X0 H.
      apply maponpaths, maponpaths, maponpaths.
      revert H0.
      rewrite <- (plusminusnmm ((length (ps_lx s2) - 1)) (ps_size s1 - 1)), natpluscomm.
      intros H0.
      now apply subtypeEquality_prop.
    + apply fromempty ; revert H1.
      apply natlthtonegnatgeh.
      assert (0 < (ps_size s1 - 1 + ps_size s2)).
      apply natlthlehtrans with (2 - 1 + 2)%nat.
      reflexivity.
      apply natlehandplus.
      apply natgehandminusr, ps_size_ge_2.
      apply ps_size_ge_2.
      destruct (ps_size s1 - 1 + ps_size s2)%nat.
      easy.
      simpl (_-_) ; rewrite natminuseqn.
      now apply natlthnsn.
  - intros k x y.
    unfold Sequence_fun ; simpl.
    destruct natgthorleh as [H | H] ; [ | easy].
    destruct natgthorleh as [H0 | H0] ; [ | easy].
    unfold tocoprodofstn ; simpl.
    destruct natgthorleh as [H1 | H1].
    destruct natgthorleh as [H2 | H2].
    + intros Hx Hy.
      apply ii2_injectivity in Hx.
      apply ii2_injectivity in Hy.
      rewrite <- Hx, <- Hy ;
        clear x y Hx Hy.
      split.
      * apply UImult_lecompat_l.
        refine (pr1 (ps_between s1 _ _ _ _ _)).
        apply Sequence_fun_ii2.
        simple refine (Sequence_fun_ii2 _ _ _).
        rewrite <- (minusplusnmm _ 1).
        apply natgthtogthp1, H2.
        apply istransnatgeh with 2.
        apply ps_size_ge_2.
        reflexivity.
      * apply UImult_lecompat_l.
        refine (pr2 (ps_between s1 _ _ _ _ _)).
        simple refine (Sequence_fun_ii2 _ _ _).
        rewrite <- (minusplusnmm _ 1).
        apply natgthtogthp1, H1.
        apply istransnatgeh with 2.
        apply ps_size_ge_2.
        reflexivity.
        apply Sequence_fun_ii2.
    + assert (Hk : ps_size s1 - 1 = S k).
      { apply isantisymmnatgeh.
        now apply natgthtogehsn.
        exact H2. }
      intros Hx Hy.
      apply ii2_injectivity in Hx.
      apply ii2_injectivity in Hy.
      rewrite <- Hx, <- Hy ;
        clear x y Hx Hy.
      split.
      * apply UImult_lecompat_l.
        refine (pr1 (ps_between s1 _ _ _ _ _)).
        apply Sequence_fun_ii2.
        simple refine (Sequence_fun_ii2 _ _ _).
        rewrite <- Hk.
        apply (natgthandplusrinv _ _ 1).
        rewrite minusplusnmm.
        apply natltplusS.
        apply istransnatgeh with 2.
        apply ps_size_ge_2.
        reflexivity.
      * revert H0 H2.
        rewrite Hk ; intros.
        apply istrans_UIle with (f1 UIone).
        apply UImult_lecompat_l, UIle_one.
        { apply istrans_UIle with (f2 UIzero).
          unfold f2, f1.
          rewrite UImult_one_l, UImult_zero_r.
          rewrite UIplus_zero_r.
          apply isrefl_UIle.

          apply UIplus_lecompat_l, UImult_lecompat_l, paths_UIle.
          apply (ii2_injectivity (P := unit)).
          rewrite <- (ps_lx_O s2).
          unfold Sequence_first.
          assert (H3 : 0 < ps_size s2).
          { apply natlthlehtrans with 2.
            reflexivity.
            apply ps_size_ge_2. }
          rewrite (Sequence_fun_ii2 (ps_lx s2) _ H3).
          apply maponpaths, maponpaths.
          apply subtypeEquality_prop ; simpl.
          apply pathsinv0, minuseq0, H2. }
    + destruct natgthorleh as [H2 | H2].
      apply fromempty ; revert H1.
      apply natgthnegleh.
      now apply istransnatgth with (2 := natgthsnn _).
      assert (n : Σ n, ps_size s1 - 1 = S n).
      { generalize (ps_size_ge_2 s1).
        destruct (ps_size s1) ; [easy | ].
        destruct n ; [easy | ].
        intros _.
        now exists n. }
      intros Hx.
      revert H0 H2 ;
        rewrite (pr2 n) ;
        intros H0 H2 Hy.
      apply ii2_injectivity in Hx.
      apply ii2_injectivity in Hy.
      rewrite <- Hx, <- Hy ;
        clear x y Hx Hy.
      split.
      * apply UIplus_lecompat_l, UImult_lecompat_l.
        refine (pr1 (ps_between s2 _ _ _ _ _)).
        rewrite <- (pr2 n).
        apply Sequence_fun_ii2.
        simple refine (Sequence_fun_ii2 _ _ _).
        rewrite <- minusSnm.
        apply (natgthandplusrinv _ _ (S (pr1 n))).
        rewrite minusplusnmm.
        rewrite natpluscomm.
        exact H0.
        exact H2.
        rewrite <- (pr2 n).
        exact H1.
      * apply UIplus_lecompat_l, UImult_lecompat_l.
        refine (pr2 (ps_between s2 _ _ _ _ _)).
        simple refine (Sequence_fun_ii2 _ _ _).
        apply (natgthandplusrinv _ _ (S (pr1 n))).
        rewrite minusplusnmm.
        rewrite natpluscomm.
        rewrite <- (pr2 n).
        exact H.
        rewrite <- (pr2 n).
        exact H1.
        rewrite <- minusSnm.
        apply Sequence_fun_ii2.
        rewrite <- (pr2 n).
        exact H1.
Defined.

Definition pointed_subdivision_filter : Filter (X := pointed_subdivision).
Proof.
  simple refine (mkFilter _ _ _ _ _).
  - intros P.
    apply (∃ eps : X, (UIlt UIzero eps) × (∀ s, UIlt (ps_step s) eps -> P s)).
  - intros A B H.
    apply hinhfun.
    intros (e,(He0,He)).
    exists e ; split.
    exact He0.
    intros s Hs.
    apply H, He, Hs.
  - apply hinhpr.
    exists UIone ; split.
    apply UIlt_zero_one.
    easy.
  - intros A B.
    apply hinhfun2.
    intros (ea,(Ha0,Ha)) (eb,(Hb0,Hb)).
    exists (UImin ea eb) ; split.

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