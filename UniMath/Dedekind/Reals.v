(** * A library about decidable Dedekind Cuts *)
(** Author: Catherine LELAY. Oct 2015 - *)
(** Additional results about Dedekind cuts which cannot be proved *)
(** without decidability *)

Require Import UniMath.Dedekind.Complements.
Require Import UniMath.Dedekind.Sets.
Require Import UniMath.Dedekind.NonnegativeRationals.
Require Export UniMath.Dedekind.NonnegativeReals.

Open Scope NR_scope.

(** ** Definition *)

(** *** [commrng] *)

Definition hr_commrng : commrng := commrigtocommrng NonnegativeReals.

Definition NR_to_hr : NonnegativeReals × NonnegativeReals -> hr_commrng
  := setquotpr (binopeqrelabgrfrac (rigaddabmonoid NonnegativeReals)).

Definition nat_to_hr (n : nat) : hr_commrng :=
  NR_to_hr (nat_to_NonnegativeReals n,,0).

Lemma NR_to_hr_inside :
  ∀ x : NonnegativeReals × NonnegativeReals, pr1 (NR_to_hr x) x.
Proof.
  intros x.
  apply hinhpr ; simpl.
  exists 0 ; reflexivity.
Qed.

Local Lemma iscomprelfun_NRminus :
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 x + pr2 y = pr1 y + pr2 x
    -> pr1 x - pr2 x = pr1 y - pr2 y.
Proof.
  intros x y H.
  apply (plusNonnegativeReals_eqcompat_l (pr2 x)).
  rewrite <- maxNonnegativeReals_minus_plus.
  apply (plusNonnegativeReals_eqcompat_l (pr2 y)).
  rewrite isrdistr_max_plusNonnegativeReals, H.
  rewrite (iscomm_plusNonnegativeReals (pr2 x) (pr2 y)), <- isrdistr_max_plusNonnegativeReals, maxNonnegativeReals_minus_plus.
  now rewrite !isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 x)).
Qed.

Definition hr_to_NR (x : hr_commrng) : NonnegativeReals × NonnegativeReals.
Proof.
  simple refine (setquotuniv _ (_,,_) _ _).
  - apply isasetdirprod ;
    apply (pr2 (pr1 (pr1 (pr1 NonnegativeReals)))).
  - intros x.
    apply (pr1 x - pr2 x ,, pr2 x - pr1 x).
  - intros x y.
    apply hinhuniv'.
    refine (isasetdirprod _ _ _ _ _ _) ;
    apply (pr2 (pr1 (pr1 (pr1 NonnegativeReals)))).
    intros (c,H).
    apply dirprodeq.
    + apply iscomprelfun_NRminus.
      apply (plusNonnegativeReals_eqcompat_l c).
      exact H.
    + apply (iscomprelfun_NRminus (pr2 x ,, pr1 x) (pr2 y ,, pr1 y)).
      simpl.
      rewrite (iscomm_plusNonnegativeReals (pr2 x)), (iscomm_plusNonnegativeReals (pr2 y)).
      apply (plusNonnegativeReals_eqcompat_l c), pathsinv0.
      exact H.
Defined.

Definition hr_to_NRpos (x : hr_commrng) : NonnegativeReals := pr1 (hr_to_NR x).
Definition hr_to_NRneg (x : hr_commrng) : NonnegativeReals := pr2 (hr_to_NR x).

Lemma hr_to_NR_correct :
  ∀ (x : hr_commrng), pr1 x (hr_to_NR x).
Proof.
  intros X.
  generalize (pr1 (pr2 X)).
  apply hinhuniv.
  intros x.
  pattern X at 2.
  rewrite <- (setquotl0 _ X x).
  unfold hr_to_NR.
  rewrite setquotunivcomm.
  generalize (pr2 x).
  apply (pr1 (pr2 (pr2 X))).
  apply hinhpr.
  exists 0 ; simpl.
  change ((pr1 (pr1 x) + (pr2 (pr1 x) - pr1 (pr1 x))%NR + 0%NR) =
   ((pr1 (pr1 x) - pr2 (pr1 x))%NR + pr2 (pr1 x) + 0%NR)).
  rewrite !isrunit_zero_plusNonnegativeReals.
  rewrite iscomm_plusNonnegativeReals, <- !maxNonnegativeReals_minus_plus.
  now apply iscomm_maxNonnegativeReals.
Qed.
Lemma hr_to_NRpos_correct :
  ∀ (X : hr_commrng) (x : NonnegativeReals × NonnegativeReals), pr1 X x -> hr_to_NRpos X <= pr1 x.
Proof.
  intros X x Hx.
  rewrite <- (setquotl0 _ X (x,,Hx)).
  unfold hr_to_NRpos, hr_to_NR.
  rewrite setquotunivcomm.
  apply minusNonnegativeReals_le.
Qed.
Lemma hr_to_NRneg_correct :
  ∀ (X : hr_commrng) (x : NonnegativeReals × NonnegativeReals), pr1 X x -> hr_to_NRneg X <= pr2 x.
Proof.
  intros X x Hx.
  rewrite <- (setquotl0 _ X (x,,Hx)).
  unfold hr_to_NRneg, hr_to_NR.
  rewrite setquotunivcomm.
  apply minusNonnegativeReals_le.
Qed.

Lemma hr_to_NR_bij :
  ∀ x : hr_commrng, NR_to_hr (hr_to_NR x) = x.
Proof.
  intros x.
  unfold NR_to_hr.
  pattern x at 2.
  apply (setquotl0 _ x ((hr_to_NR x),,(hr_to_NR_correct x))).
Qed.

(** Caracterisation of equality *)

(*Lemma hr_inside_carac :
  ∀ X : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 X y -> pr1 x + pr2 y = pr1 y + pr2 x.
Proof.
  intros X x y Hx Hy.
  generalize (pr2 (pr2 (pr2 X)) _ _ Hx Hy).
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))).
  simpl ; intros (c,H).
  apply (plusNonnegativeReals_eqcompat_l c).
  exact H.
Qed.
Lemma hr_inside_carac' :
  ∀ X : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 x + pr2 y = pr1 y + pr2 x -> pr1 X x -> pr1 X y.
Proof.
  intros X x y Heq Hx.
  apply (pr1 (pr2 (pr2 X)) x y).
  apply hinhpr.
  exists 0 ; simpl.
  change (pr1 x + pr2 y + 0 = pr1 y + pr2 x + 0).
  now rewrite !isrunit_zero_plusNonnegativeReals.
  exact Hx.
Qed.*)

Lemma NR_to_hr_eq :
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 x + pr2 y = pr1 y + pr2 x <-> NR_to_hr x = NR_to_hr y.
Proof.
  intros x y.
  split ; intros H.
  - apply iscompsetquotpr.
    apply hinhpr.
    exists 0.
    apply_pr2 plusNonnegativeReals_eqcompat_l.
    exact H.
  - generalize (invmap (weqpathsinsetquot _ _ _) H) ; clear H.
    apply hinhuniv'.
    apply (pr2 (pr1 (pr1 (pr1 NonnegativeReals)))).
    intros (c).
    apply plusNonnegativeReals_eqcompat_l.
Qed.

(*Lemma hr_eq_carac :
  ∀ X Y : hr_commrng,
    X = Y ->
    ∀ x y : NonnegativeReals × NonnegativeReals,
      pr1 X x -> pr1 Y y -> pr1 x + pr2 y = pr1 y + pr2 x.
Proof.
  intros X Y ->.
  apply hr_inside_carac.
Qed.
Lemma hr_eq_carac' :
  ∀ X Y : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 Y y -> pr1 x + pr2 y = pr1 y + pr2 x -> X = Y.
Proof.
  intros X Y x y Hx Hy Heq.
  apply subtypeEquality.
  - intros Z.
    now apply isapropiseqclass.
  - apply funextfunax ; simpl ; intro t.
    apply weqtopathshProp, logeqweq.
    + intros Ht.
      revert Hy.
      apply hr_inside_carac'.
      apply plusNonnegativeReals_eqcompat_r with (pr2 x).
      rewrite <- isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 x)), <- Heq, isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 y)), <-! isassoc_plusNonnegativeReals.
      apply_pr2 plusNonnegativeReals_eqcompat_l.
      rewrite (iscomm_plusNonnegativeReals (pr2 x)).
      now apply (hr_inside_carac X).
    + intros Ht.
      revert Hx.
      apply hr_inside_carac'.
      apply plusNonnegativeReals_eqcompat_r with (pr2 y).
      rewrite <- isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 y)), Heq, isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (pr2 x)), <-! isassoc_plusNonnegativeReals.
      apply_pr2 plusNonnegativeReals_eqcompat_l.
      rewrite (iscomm_plusNonnegativeReals (pr2 y)).
      now apply (hr_inside_carac Y).
Qed.

Lemma NR_to_hr_unique :
  ∀ X : hr_commrng, ∀ x: NonnegativeReals × NonnegativeReals, pr1 X x -> NR_to_hr x = X.
Proof.
  intros X x Hx.
  apply (hr_eq_carac' _ _ x x).
  - apply hinhpr.
    now exists 0.
  - exact Hx.
  - reflexivity.
Qed.*)

(** *** Constants and Operations *)

(** 0 *)

Lemma hr_to_NR_zero :
  hr_to_NR 0%rng = (0,,0).
Proof.
  unfold rngunel1, unel_is ; simpl.
  unfold hr_to_NR.
  rewrite setquotunivcomm ; simpl.
  rewrite !minusNonnegativeReals_eq_zero.
  reflexivity.
  apply isrefl_leNonnegativeReals.
Qed.

(*Lemma hr_zero_carac :
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 (0%rng : hr_commrng) x -> pr2 x = pr1 x.
Proof.
  intros x.
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))) ; simpl.
  intros (c,Hx).
  apply (plusNonnegativeReals_eqcompat_r 0).
  apply (plusNonnegativeReals_eqcompat_l c).
  rewrite (iscomm_plusNonnegativeReals _ (pr1 x)).
  exact Hx.
Qed.
Lemma hr_zero_carac' :
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr2 x = pr1 x -> pr1 (0%rng : hr_commrng) x.
Proof.
  intros x Hx.
  apply hinhpr ; simpl.
  exists 0.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  rewrite iscomm_plusNonnegativeReals.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  exact Hx.
Qed.*)

(** 1 *)

Lemma hr_to_NR_one :
  hr_to_NR 1%rng = (1,,0).
Proof.
  unfold rngunel2, unel_is ; simpl.
  unfold rigtorngunel2, hr_to_NR.
  rewrite setquotunivcomm ; simpl.
  erewrite <- minusNonnegativeReals_correct_r.
  rewrite minusNonnegativeReals_eq_zero.
  reflexivity.
  apply isnonnegative_NonnegativeReals.
  apply pathsinv0, isrunit_zero_plusNonnegativeReals.
Qed.

(*Lemma hr_one_carac :
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 (1%rng : hr_commrng) x -> 1 + pr2 x = pr1 x.
Proof.
  intros x.
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))) ; simpl.
  intros (c,Hx).
  rewrite isrunit_zero_plusNonnegativeReals in Hx.
  apply (plusNonnegativeReals_eqcompat_l c).
  exact Hx.
Qed.
Lemma hr_one_carac' :
  ∀ x : NonnegativeReals × NonnegativeReals,
    1 + pr2 x = pr1 x -> pr1 (1%rng : hr_commrng) x.
Proof.
  intros x Hx.
  apply hinhpr ; simpl.
  exists 0.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  rewrite isrunit_zero_plusNonnegativeReals.
  exact Hx.
Qed.*)

(** plus *)

Lemma NR_to_hr_plus :
  ∀ x y : NonnegativeReals × NonnegativeReals,
    (NR_to_hr x + NR_to_hr y)%rng = NR_to_hr (pr1 x + pr1 y ,, pr2 x + pr2 y).
Proof.
  intros x y.
  unfold BinaryOperations.op1 ; simpl.
  unfold rigtorngop1 ; simpl.
  unfold NR_to_hr.
  apply (setquotfun2comm (binopeqrelabgrfrac (rigaddabmonoid NonnegativeReals)) (binopeqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
Qed.

(*Lemma hr_plus_carac :
  ∀ X Y : hr_commrng,
  ∀ z : NonnegativeReals × NonnegativeReals,
    pr1 (X + Y)%rng z ->
    ∀ x y : NonnegativeReals × NonnegativeReals,
      pr1 X x -> pr1 Y y ->
      pr1 x + pr1 y + pr2 z = pr1 z + pr2 x + pr2 y.
Proof.
  intros X Y z Hz x y Hx Hy.
  revert Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  rewrite <- (NR_to_hr_unique _ _ Hy).
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))) ; simpl.
  intros (c,Hz).
  rewrite <-! isassoc_plusNonnegativeReals in Hz.
  apply (plusNonnegativeReals_eqcompat_l c).
  exact Hz.
Qed.
Lemma hr_plus_carac' :
  ∀ X Y : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 Y y ->
    ∀ z : NonnegativeReals × NonnegativeReals,
      pr1 x + pr1 y + pr2 z = pr1 z + pr2 x + pr2 y ->
      pr1 (X + Y)%rng z.
Proof.
  intros X Y x y Hx Hy z Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  rewrite <- (NR_to_hr_unique _ _ Hy).
  apply hinhpr ; simpl.
  exists 0.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  rewrite <-!isassoc_plusNonnegativeReals.
  exact Hz.
Qed.*)

(** opp *)

Lemma NR_to_hr_opp :
  ∀ x : NonnegativeReals × NonnegativeReals,
    (- NR_to_hr x)%rng = NR_to_hr (pr2 x ,, pr1 x).
Proof.
  intros x.
  unfold rnginv1, grinv_is ; simpl.
  unfold abgrfracinv.
  unfold NR_to_hr.
  apply (setquotfuncomm (binopeqrelabgrfrac (rigaddabmonoid NonnegativeReals)) (binopeqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
Qed.

(*Lemma hr_opp_carac :
  ∀ X : hr_commrng,
  ∀ z : NonnegativeReals × NonnegativeReals,
    pr1 (- X)%rng z ->
    ∀ x : NonnegativeReals × NonnegativeReals,
      pr1 X x ->
      pr2 x + pr2 z = pr1 z + pr1 x.
Proof.
  intros X z Hz x Hx.
  revert Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))) ; simpl.
  intros (c,Hz).
  apply (plusNonnegativeReals_eqcompat_l c).
  exact Hz.
Qed.
Lemma hr_opp_carac' :
  ∀ X : hr_commrng,
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 X x ->
    ∀ z : NonnegativeReals × NonnegativeReals,
      pr2 x + pr2 z = pr1 z + pr1 x ->
      pr1 (- X)%rng z.
Proof.
  intros X x Hx z Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  apply hinhpr ; simpl.
  exists 0.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  exact Hz.
Qed.*)

(** minus *)

Lemma NR_to_hr_minus :
  ∀ x y : NonnegativeReals × NonnegativeReals,
    (NR_to_hr x - NR_to_hr y)%rng = NR_to_hr (pr1 x + pr2 y ,, pr2 x + pr1 y).
Proof.
  intros x y.
  rewrite NR_to_hr_opp, NR_to_hr_plus.
  reflexivity.
Qed.

(*Lemma hr_minus_carac :
  ∀ X Y : hr_commrng,
  ∀ z : NonnegativeReals × NonnegativeReals,
    pr1 (X - Y)%rng z ->
    ∀ x y : NonnegativeReals × NonnegativeReals,
      pr1 X x -> pr1 Y y ->
      pr1 x + pr2 y + pr2 z = pr1 z + pr2 x + pr1 y.
Proof.
  intros X Y z Hz x y Hx Hy.
  revert Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  rewrite <- (NR_to_hr_unique _ _ Hy).
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))) ; simpl.
  intros (c,Hz).
  rewrite <-! isassoc_plusNonnegativeReals in Hz.
  apply (plusNonnegativeReals_eqcompat_l c).
  exact Hz.
Qed.
Lemma hr_minus_carac' :
  ∀ X Y : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 Y y ->
    ∀ z : NonnegativeReals × NonnegativeReals,
      pr1 x + pr2 y + pr2 z = pr1 z + pr2 x + pr1 y ->
      pr1 (X - Y)%rng z.
Proof.
  intros X Y x y Hx Hy z Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  rewrite <- (NR_to_hr_unique _ _ Hy).
  apply hinhpr ; simpl.
  exists 0.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  rewrite <-!isassoc_plusNonnegativeReals.
  exact Hz.
Qed.*)

(** mult *)

Lemma NR_to_hr_mult :
  ∀ x y : NonnegativeReals × NonnegativeReals,
    (NR_to_hr x * NR_to_hr y)%rng = NR_to_hr (pr1 x * pr1 y + pr2 x * pr2 y ,, pr1 x * pr2 y + pr2 x * pr1 y).
Proof.
  intros x y.
  unfold BinaryOperations.op2 ; simpl.
  unfold rigtorngop2 ; simpl.
  unfold NR_to_hr.
  apply (setquotfun2comm (binopeqrelabgrfrac (rigaddabmonoid NonnegativeReals)) (binopeqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
Qed.

(* Lemma hr_mult_carac :
  ∀ X Y : hr_commrng,
  ∀ z : NonnegativeReals × NonnegativeReals,
    pr1 (X * Y)%rng z ->
    ∀ x y : NonnegativeReals × NonnegativeReals,
      pr1 X x -> pr1 Y y ->
      pr1 x * pr1 y + pr2 x * pr2 y + pr2 z = pr1 z + pr1 x * pr2 y + pr2 x * pr1 y.
Proof.
  intros X Y z Hz x y Hx Hy.
  revert Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  rewrite <- (NR_to_hr_unique _ _ Hy).
  apply (hinhuniv (P := hProppair _ (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _))) ; simpl.
  intros (c,Hz).
  rewrite <-! isassoc_plusNonnegativeReals in Hz.
  apply (plusNonnegativeReals_eqcompat_l c).
  exact Hz.
Qed.
Lemma hr_mult_carac' :
  ∀ X Y : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 Y y ->
    ∀ z : NonnegativeReals × NonnegativeReals,
      pr1 x * pr1 y + pr2 x * pr2 y + pr2 z = pr1 z + pr1 x * pr2 y + pr2 x * pr1 y ->
      pr1 (X * Y)%rng z.
Proof.
  intros X Y x y Hx Hy z Hz.
  rewrite <- (NR_to_hr_unique _ _ Hx).
  rewrite <- (NR_to_hr_unique _ _ Hy).
  apply hinhpr ; simpl.
  exists 0.
  apply_pr2 plusNonnegativeReals_eqcompat_l.
  rewrite <-!isassoc_plusNonnegativeReals.
  exact Hz.
Qed.*)

(** *** Order *)
(** [hr_lt_rel] *)

Local Lemma isbinophrel_ltNonnegativeReals :
  isbinophrel (X := rigaddabmonoid NonnegativeReals) ltNonnegativeReals.
Proof.
  split.
  - intros x y z Hlt.
    apply plusNonnegativeReals_ltcompat_r, Hlt.
  - intros x y z Hlt.
    apply plusNonnegativeReals_ltcompat_l, Hlt.
Qed.
Definition hr_lt_rel : hrel hr_commrng
  := rigtorngrel NonnegativeReals isbinophrel_ltNonnegativeReals.

Lemma NR_to_hr_lt :
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 x + pr2 y < pr1 y + pr2 x
    <-> hr_lt_rel (NR_to_hr x) (NR_to_hr y).
Proof.
  intros x y.
  split.
  - intros H.
    apply hinhpr ; exists 0 ; simpl.
    apply plusNonnegativeReals_ltcompat_l, H.
  - apply hinhuniv ; intros H.
    apply_pr2 (plusNonnegativeReals_ltcompat_l (pr1 H)).
    exact (pr2 H).
Qed.

(*Lemma hr_lt_carac :
  ∀ X Y : hr_commrng,
    hr_lt_rel X Y ->
    ∀ x y : NonnegativeReals × NonnegativeReals,
      pr1 X x -> pr1 Y y -> pr1 x + pr2 y < pr1 y + pr2 x.
Proof.
  intros X Y Hlt x y Hx Hy.
  revert Hlt.
  rewrite <- (NR_to_hr_unique _ _ Hx),  <- (NR_to_hr_unique _ _ Hy).
  unfold hr_lt_rel, rigtorngrel, abgrfracrel, quotrel.
  rewrite (setquotuniv2comm (eqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
  apply hinhuniv ; intros (c,Hlt).
  apply_pr2 (plusNonnegativeReals_ltcompat_l c).
  exact Hlt.
Qed.
Lemma hr_lt_carac' :
  ∀ X Y : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 Y y -> pr1 x + pr2 y < pr1 y + pr2 x -> hr_lt_rel X Y.
Proof.
  intros X Y x y Hx Hy Hlt.
  rewrite <- (NR_to_hr_unique _ _ Hx),  <- (NR_to_hr_unique _ _ Hy).
  unfold hr_lt_rel, rigtorngrel, abgrfracrel, quotrel.
  rewrite (setquotuniv2comm (eqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
  apply hinhpr ; exists 0.
  apply (plusNonnegativeReals_ltcompat_l 0).
  exact Hlt.
Qed.*)

(** [hr_le_rel] *)

Local Lemma isbinophrel_leNonnegativeReals :
  isbinophrel (X := rigaddabmonoid NonnegativeReals) leNonnegativeReals.
Proof.
  split.
  - intros x y z Hlt.
    apply plusNonnegativeReals_lecompat_r, Hlt.
  - intros x y z Hlt.
    apply plusNonnegativeReals_lecompat_l, Hlt.
Qed.
Definition hr_le_rel : hrel hr_commrng
  := rigtorngrel NonnegativeReals isbinophrel_leNonnegativeReals.

Lemma NR_to_hr_le :
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 x + pr2 y <= pr1 y + pr2 x
    <-> hr_le_rel (NR_to_hr x) (NR_to_hr y).
Proof.
  intros x y.
  split.
  - intros H.
    apply hinhpr ; exists 0 ; simpl.
    apply plusNonnegativeReals_lecompat_l, H.
  - apply hinhuniv ; intros H.
    apply_pr2 (plusNonnegativeReals_lecompat_l (pr1 H)).
    exact (pr2 H).
Qed.

(*Lemma hr_le_carac :
  ∀ X Y : hr_commrng,
    hr_le_rel X Y ->
    ∀ x y : NonnegativeReals × NonnegativeReals,
      pr1 X x -> pr1 Y y -> pr1 x + pr2 y <= pr1 y + pr2 x.
Proof.
  intros X Y Hlt x y Hx Hy.
  revert Hlt.
  rewrite <- (NR_to_hr_unique _ _ Hx),  <- (NR_to_hr_unique _ _ Hy).
  unfold hr_le_rel, rigtorngrel, abgrfracrel, quotrel.
  rewrite (setquotuniv2comm (eqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
  apply hinhuniv ; intros (c,Hlt).
  apply_pr2 (plusNonnegativeReals_lecompat_l c).
  exact Hlt.
Qed.
Lemma hr_le_carac' :
  ∀ X Y : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 Y y -> pr1 x + pr2 y <= pr1 y + pr2 x -> hr_le_rel X Y.
Proof.
  intros X Y x y Hx Hy Hlt.
  rewrite <- (NR_to_hr_unique _ _ Hx),  <- (NR_to_hr_unique _ _ Hy).
  unfold hr_le_rel, rigtorngrel, abgrfracrel, quotrel.
  rewrite (setquotuniv2comm (eqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
  apply hinhpr ; exists 0.
  apply (plusNonnegativeReals_lecompat_l 0).
  exact Hlt.
Qed.*)

(** Theorems about order *)

Lemma hr_notlt_le :
  ∀ X Y, ¬ hr_lt_rel X Y <-> hr_le_rel Y X.
Proof.
  intros x y.
  rewrite <- (hr_to_NR_bij x), <- (hr_to_NR_bij y).
  split ; intro H.
  - apply NR_to_hr_le.
    apply notlt_leNonnegativeReals.
    intro H0 ; apply H.
    apply NR_to_hr_lt.
    exact H0.
  - intro H0.
    refine (pr2 (notlt_leNonnegativeReals _ _) _ _).
    refine (pr2 (NR_to_hr_le _ _) _).
    apply H.
    apply_pr2 NR_to_hr_lt.
    exact H0.
Qed.

Lemma isantisymm_hr_le :
  isantisymm hr_le_rel.
Proof.
  apply isantisymmabgrfracrel.
  intros X Y Hxy Hyx.
  apply isantisymm_leNonnegativeReals.
  now split.
Qed.

Lemma isStrongOrder_hr_lt : isStrongOrder hr_lt_rel.
Proof.
  split.
  - apply istransabgrfracrel.
    exact istrans_ltNonnegativeReals.
  - apply isirreflabgrfracrel.
    exact isirrefl_ltNonnegativeReals.
Qed.
Lemma iscotrans_hr_lt :
  iscotrans hr_lt_rel.
Proof.
  apply iscotransabgrfracrel.
  exact iscotrans_ltNonnegativeReals.
Qed.

Lemma hr_ispositive_carac :
  ∀ X : hr_commrng,
    hr_lt_rel 0%rng X ->
    Σ x : NonnegativeReals, hr_to_NR X = (x ,, 0) × 0 < x.
Proof.
  intros X Hlt.
  rewrite <- (hr_to_NR_bij X), <- (hr_to_NR_bij 0%rng), hr_to_NR_zero in Hlt.
  generalize (pr2 (NR_to_hr_lt _ _) Hlt) ; simpl.
  rewrite islunit_zero_plusNonnegativeReals, isrunit_zero_plusNonnegativeReals.
  clear Hlt ; intro Hlt.
  exists (pr1 (hr_to_NR X)) ; split.
  rewrite <- (hr_to_NR_bij X).
  revert Hlt.
  generalize (hr_to_NR X) ; intros x Hlt.
  unfold hr_to_NR, NR_to_hr.
  rewrite setquotunivcomm.
  apply maponpaths, minusNonnegativeReals_eq_zero.
  now apply lt_leNonnegativeReals.
  eapply istrans_le_lt_ltNonnegativeReals, Hlt.
  apply isnonnegative_NonnegativeReals.
Qed.
Lemma hr_ispositive_carac' :
  ∀ X : hr_commrng,
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 X x ->
    pr2 x < pr1 x ->
    hr_lt_rel 0%rng X.
Proof.
  intros X x Hx Hlt.
  rewrite <- (setquotl0 _ X (x,,Hx)).
  rewrite <- (hr_to_NR_bij 0%rng), hr_to_NR_zero.
  apply hinhpr ; simpl.
  exists 0.
  rewrite islunit_zero_plusNonnegativeReals, !isrunit_zero_plusNonnegativeReals.
  exact Hlt.
Qed.

Lemma hr_isnonnegative_carac :
  ∀ X : hr_commrng,
    hr_le_rel 0%rng X ->
    Σ x : NonnegativeReals, hr_to_NR X = (x ,, 0).
Proof.
  intros X Hle.
  rewrite <- (hr_to_NR_bij X), <- (hr_to_NR_bij 0%rng), hr_to_NR_zero in Hle.
  generalize (pr2 (NR_to_hr_le _ _) Hle) ; simpl.
  rewrite islunit_zero_plusNonnegativeReals, isrunit_zero_plusNonnegativeReals.
  clear Hle ; intro Hle.
  exists (pr1 (hr_to_NR X)).
  rewrite <- (hr_to_NR_bij X).
  revert Hle.
  generalize (hr_to_NR X) ; intros x Hlt.
  unfold hr_to_NR, NR_to_hr.
  rewrite setquotunivcomm.
  now apply maponpaths, minusNonnegativeReals_eq_zero.
Qed.
Lemma hr_isnonnegative_carac' :
  ∀ X : hr_commrng,
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 X x ->
    pr2 x <= pr1 x ->
    hr_le_rel 0%rng X.
Proof.
  intros X x Hx Hle.
  rewrite <- (setquotl0 _ X (x,,Hx)).
  rewrite <- (hr_to_NR_bij 0%rng), hr_to_NR_zero.
  apply hinhpr ; simpl.
  exists 0.
  rewrite islunit_zero_plusNonnegativeReals, !isrunit_zero_plusNonnegativeReals.
  exact Hle.
Qed.

Lemma hr_isnegative_carac :
  ∀ X : hr_commrng,
    hr_lt_rel X 0%rng ->
    Σ x : NonnegativeReals, hr_to_NR X = (0 ,, x) × 0 < x.
Proof.
  intros X Hlt.
  rewrite <- (hr_to_NR_bij X), <- (hr_to_NR_bij 0%rng), hr_to_NR_zero in Hlt.
  generalize (pr2 (NR_to_hr_lt _ _) Hlt) ; simpl.
  rewrite islunit_zero_plusNonnegativeReals, isrunit_zero_plusNonnegativeReals.
  clear Hlt ; intro Hlt.
  exists (pr2 (hr_to_NR X)) ; split.
  rewrite <- (hr_to_NR_bij X).
  revert Hlt.
  generalize (hr_to_NR X) ; intros x Hlt.
  unfold hr_to_NR, NR_to_hr.
  rewrite setquotunivcomm.
  apply (maponpaths (λ x, x,,_)), minusNonnegativeReals_eq_zero.
  now apply lt_leNonnegativeReals.
  eapply istrans_le_lt_ltNonnegativeReals, Hlt.
  apply isnonnegative_NonnegativeReals.
Qed.
Lemma hr_isnegative_carac' :
  ∀ X : hr_commrng,
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 X x ->
    pr1 x < pr2 x ->
    hr_lt_rel X 0%rng.
Proof.
  intros X x Hx Hlt.
  rewrite <- (setquotl0 _ X (x,,Hx)).
  rewrite <- (hr_to_NR_bij 0%rng), hr_to_NR_zero.
  apply hinhpr ; simpl.
  exists 0.
  rewrite islunit_zero_plusNonnegativeReals, !isrunit_zero_plusNonnegativeReals.
  exact Hlt.
Qed.

Lemma hr_isnonpositive_carac :
  ∀ X : hr_commrng,
    hr_le_rel X 0%rng ->
    Σ x : NonnegativeReals, hr_to_NR X = (0 ,, x).
Proof.
  intros X Hle.
  rewrite <- (hr_to_NR_bij X), <- (hr_to_NR_bij 0%rng), hr_to_NR_zero in Hle.
  generalize (pr2 (NR_to_hr_le _ _) Hle) ; simpl.
  rewrite islunit_zero_plusNonnegativeReals, isrunit_zero_plusNonnegativeReals.
  clear Hle ; intro Hle.
  exists (pr2 (hr_to_NR X)).
  rewrite <- (hr_to_NR_bij X).
  revert Hle.
  generalize (hr_to_NR X) ; intros x Hlt.
  unfold hr_to_NR, NR_to_hr.
  rewrite setquotunivcomm.
  now apply (maponpaths (λ x, x,,_)), minusNonnegativeReals_eq_zero.
Qed.
Lemma hr_isnonpositive_carac' :
  ∀ X : hr_commrng,
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 X x ->
    pr1 x <= pr2 x ->
    hr_le_rel X 0%rng.
Proof.
  intros X x Hx Hle.
  rewrite <- (setquotl0 _ X (x,,Hx)).
  rewrite <- (hr_to_NR_bij 0%rng), hr_to_NR_zero.
  apply hinhpr ; simpl.
  exists 0.
  rewrite islunit_zero_plusNonnegativeReals, !isrunit_zero_plusNonnegativeReals.
  exact Hle.
Qed.

Lemma hr_plus_ltcompat_l :
  ∀ x y z : hr_commrng, hr_lt_rel y z <-> hr_lt_rel (y+x)%rng (z+x)%rng.
Proof.
  intros X Y Z.
  rewrite <- (hr_to_NR_bij X), <- (hr_to_NR_bij Y), <- (hr_to_NR_bij Z).
  rewrite !NR_to_hr_plus.
  split ; intro Hlt.
  - apply NR_to_hr_lt ; simpl.
    rewrite !(iscomm_plusNonnegativeReals _ (pr1 (hr_to_NR X))), !isassoc_plusNonnegativeReals.
    apply plusNonnegativeReals_ltcompat_r.
    rewrite <- ! isassoc_plusNonnegativeReals.
    apply plusNonnegativeReals_ltcompat_l.
    now apply_pr2 NR_to_hr_lt.
  - apply NR_to_hr_lt ; simpl.
    apply_pr2 (plusNonnegativeReals_ltcompat_l (pr2 (hr_to_NR X))).
    apply_pr2 (plusNonnegativeReals_ltcompat_r (pr1 (hr_to_NR X))).
    rewrite <- ! isassoc_plusNonnegativeReals.
    rewrite !(iscomm_plusNonnegativeReals (pr1 (hr_to_NR X))), !(isassoc_plusNonnegativeReals (_ + pr1 (hr_to_NR X))).
    now apply_pr2_in NR_to_hr_lt Hlt.
Qed.
Lemma hr_plus_ltcompat_r :
  ∀ x y z : hr_commrng, hr_lt_rel y z <-> hr_lt_rel (x + y)%rng (x + z)%rng.
Proof.
  intros x y z.
  rewrite !(rngcomm1 _ x).
  apply hr_plus_ltcompat_l.
Qed.

Lemma hr_plus_lecompat_l :
  ∀ x y z : hr_commrng, hr_le_rel y z <-> hr_le_rel (y + x)%rng (z + x)%rng.
Proof.
  intros x y z ; split ; intro Hle.
  - apply hr_notlt_le.
    apply_pr2_in hr_notlt_le Hle.
    intro Hlt ; apply Hle.
    apply_pr2 (hr_plus_ltcompat_l x).
    exact Hlt.
  - apply hr_notlt_le.
    apply_pr2_in hr_notlt_le Hle.
    intro Hlt ; apply Hle.
    apply hr_plus_ltcompat_l.
    exact Hlt.
Qed.
Lemma hr_plus_lecompat_r :
  ∀ x y z : hr_commrng, hr_le_rel y z <-> hr_le_rel (x + y)%rng (x + z)%rng.
Proof.
  intros x y z.
  rewrite !(rngcomm1 _ x).
  apply hr_plus_lecompat_l.
Qed.

Lemma hr_mult_ltcompat_l :
  ∀ x y z : hr_commrng, hr_lt_rel 0%rng x -> hr_lt_rel y z -> hr_lt_rel (y * x)%rng (z * x)%rng.
Proof.
  intros X Y Z Hx0 Hlt.
  apply hr_ispositive_carac in Hx0.
  rewrite <- (hr_to_NR_bij X), (pr1 (pr2 Hx0)), <- (hr_to_NR_bij Y), <- (hr_to_NR_bij Z).
  rewrite !NR_to_hr_mult ; simpl pr1 ; simpl pr2.
  rewrite !israbsorb_zero_multNonnegativeReals, !isrunit_zero_plusNonnegativeReals, !islunit_zero_plusNonnegativeReals.
  apply NR_to_hr_lt ; simpl.
  rewrite <- !isrdistr_plus_multNonnegativeReals.
  apply multNonnegativeReals_ltcompat_l.
  exact (pr2 (pr2 Hx0)).
  apply_pr2 NR_to_hr_lt.
  now rewrite !hr_to_NR_bij.
Qed.
Lemma hr_mult_ltcompat_l' :
  ∀ x y z : hr_commrng, hr_le_rel 0%rng x -> hr_lt_rel (y * x)%rng (z * x)%rng -> hr_lt_rel y z.
Proof.
  intros X Y Z Hx0.
  apply hr_isnonnegative_carac in Hx0.
  rewrite <- (hr_to_NR_bij X), (pr2 Hx0), <- (hr_to_NR_bij Y), <- (hr_to_NR_bij Z).
  rewrite !NR_to_hr_mult ; simpl pr1 ; simpl pr2.
  rewrite !israbsorb_zero_multNonnegativeReals, !isrunit_zero_plusNonnegativeReals, !islunit_zero_plusNonnegativeReals.
  intros Hlt.
  apply NR_to_hr_lt.
  apply multNonnegativeReals_ltcompat_l' with (pr1 Hx0).
  rewrite !isrdistr_plus_multNonnegativeReals.
  now apply_pr2_in NR_to_hr_lt Hlt.
Qed.
Lemma hr_mult_ltcompat_r' :
  ∀ x y z : hr_commrng, hr_le_rel 0%rng x -> hr_lt_rel (x * y)%rng (x * z)%rng -> hr_lt_rel y z.
Proof.
  intros x y z.
  rewrite !(rngcomm2 _ x).
  apply hr_mult_ltcompat_l'.
Qed.

Lemma hr_mult_lecompat_l :
  ∀ x y z : hr_commrng, hr_le_rel 0%rng x -> hr_le_rel y z -> hr_le_rel (y * x)%rng (z * x)%rng.
Proof.
  intros x y z Hx0 Hle.
  apply hr_notlt_le.
  apply_pr2_in hr_notlt_le Hle.
  intro Hlt ; apply Hle.
  apply (hr_mult_ltcompat_l' x).
  exact Hx0.
  exact Hlt.
Qed.
Lemma hr_mult_lecompat_l' :
  ∀ x y z : hr_commrng, hr_lt_rel 0%rng x -> hr_le_rel (y * x)%rng (z * x)%rng -> hr_le_rel y z.
Proof.
  intros x y z Hx0 Hle.
  apply hr_notlt_le.
  apply_pr2_in hr_notlt_le Hle.
  intro Hlt ; apply Hle.
  apply (hr_mult_ltcompat_l x).
  exact Hx0.
  exact Hlt.
Qed.
Lemma hr_mult_lecompat_r :
  ∀ x y z : hr_commrng, hr_le_rel 0%rng x -> hr_le_rel y z -> hr_le_rel (x * y)%rng (x * z)%rng.
Proof.
  intros x y z.
  rewrite !(rngcomm2 _ x).
  apply hr_mult_lecompat_l.
Qed.
Lemma hr_mult_lecompat_r' :
  ∀ x y z : hr_commrng, hr_lt_rel 0%rng x -> hr_le_rel (x * y)%rng (x * z)%rng -> hr_le_rel y z.
Proof.
  intros x y z.
  rewrite !(rngcomm2 _ x).
  apply hr_mult_lecompat_l'.
Qed.

(** *** Appartness *)

Local Lemma isbinophrel_apNonnegativeReals :
  isbinophrel (X := rigaddabmonoid NonnegativeReals) apNonnegativeReals.
Proof.
  split.
  - intros x y z Hlt.
    apply plusNonnegativeReals_apcompat_r, Hlt.
  - intros x y z Hlt.
    apply plusNonnegativeReals_apcompat_l, Hlt.
Qed.
Definition hr_ap_rel : hrel hr_commrng
  := rigtorngrel NonnegativeReals isbinophrel_apNonnegativeReals.

Lemma NR_to_hr_ap :
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 x + pr2 y ≠ pr1 y + pr2 x
    <-> hr_ap_rel (NR_to_hr x) (NR_to_hr y).
Proof.
  intros x y.
  split.
  - intros H.
    apply hinhpr ; exists 0 ; simpl.
    apply plusNonnegativeReals_apcompat_l, H.
  - apply hinhuniv ; intros H.
    apply_pr2 (plusNonnegativeReals_apcompat_l (pr1 H)).
    exact (pr2 H).
Qed.

(*Lemma hr_ap_carac :
  ∀ X Y : hr_commrng,
    hr_ap_rel X Y ->
    ∀ x y : NonnegativeReals × NonnegativeReals,
      pr1 X x -> pr1 Y y -> pr1 x + pr2 y ≠ pr1 y + pr2 x.
Proof.
  intros X Y Hlt x y Hx Hy.
  revert Hlt.
  rewrite <- (NR_to_hr_unique _ _ Hx),  <- (NR_to_hr_unique _ _ Hy).
  unfold hr_ap_rel, rigtorngrel, abgrfracrel, quotrel.
  rewrite (setquotuniv2comm (eqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
  apply hinhuniv ; intros (c,Hlt).
  apply_pr2 (plusNonnegativeReals_apcompat_l c).
  exact Hlt.
Qed.
Lemma hr_ap_carac' :
  ∀ X Y : hr_commrng,
  ∀ x y : NonnegativeReals × NonnegativeReals,
    pr1 X x -> pr1 Y y -> pr1 x + pr2 y ≠ pr1 y + pr2 x -> hr_ap_rel X Y.
Proof.
  intros X Y x y Hx Hy Hlt.
  rewrite <- (NR_to_hr_unique _ _ Hx),  <- (NR_to_hr_unique _ _ Hy).
  unfold hr_ap_rel, rigtorngrel, abgrfracrel, quotrel.
  rewrite (setquotuniv2comm (eqrelabgrfrac (rigaddabmonoid NonnegativeReals))).
  apply hinhpr ; exists 0.
  apply (plusNonnegativeReals_apcompat_l 0).
  exact Hlt.
Qed.*)

(** Theorems about apartness *)

Lemma hr_ap_lt :
  ∀ X Y : hr_commrng, hr_ap_rel X Y <-> (hr_lt_rel X Y) ⨿ (hr_lt_rel Y X).
Proof.
  intros X Y.
  rewrite <-  (hr_to_NR_bij X), <- (hr_to_NR_bij Y).
  split ; intro Hap.
  - apply_pr2_in NR_to_hr_ap Hap.
    destruct Hap as [Hlt | Hlt].
    + now left ; apply NR_to_hr_lt.
    + now right ; apply NR_to_hr_lt.
  - apply NR_to_hr_ap.
    destruct Hap as [Hlt | Hlt].
    + now left ; apply_pr2 NR_to_hr_lt.
    + now right ; apply_pr2 NR_to_hr_lt.
Qed.

Lemma istightap_hr_ap : istightap hr_ap_rel.
Proof.
  repeat split.
  - intros X Hap.
    rewrite <- (hr_to_NR_bij X) in Hap.
    apply_pr2_in NR_to_hr_ap Hap.
    revert Hap.
    now apply isirrefl_apNonnegativeReals.
  - intros X Y.
    rewrite <- (hr_to_NR_bij X), <- (hr_to_NR_bij Y).
    intros Hap.
    apply NR_to_hr_ap.
    apply issymm_apNonnegativeReals.
    now apply_pr2 NR_to_hr_ap.
  - intros X Y Z Hap.
    apply hr_ap_lt in Hap.
    destruct Hap as [Hlt|Hlt].
    + apply (iscotrans_hr_lt X Y Z) in Hlt.
      revert Hlt ; apply hinhfun ; intros [Hlt|Hlt].
      * left ; apply_pr2 hr_ap_lt.
        now left.
      * right ; apply_pr2 hr_ap_lt.
        now left.
    + apply (iscotrans_hr_lt _ Y _) in Hlt.
      revert Hlt ; apply hinhfun ; intros [Hlt|Hlt].
      * right ; apply_pr2 hr_ap_lt.
        now right.
      * left ; apply_pr2 hr_ap_lt.
        now right.
  - intros X Y Hap.
    apply isantisymm_hr_le.
    + apply hr_notlt_le.
      intro Hlt ; apply Hap.
      apply_pr2 hr_ap_lt.
      now right.
    + apply hr_notlt_le.
      intro Hlt ; apply Hap.
      apply_pr2 hr_ap_lt.
      now left.
Qed.

(** Structures *)

Lemma hr_to_NR_ap_0 :
  ∀ (x : hr_commrng),
    (hr_ap_rel x 0%rng <-> ((pr1 (hr_to_NR x) ≠ 0) ⨿ (pr2 (hr_to_NR x) ≠ 0))).
Proof.
  intros x.
  split.
  - intros Hap.
    apply hr_ap_lt in Hap.
    destruct Hap as [Hlt | Hlt].
    + right.
      apply hr_isnegative_carac in Hlt.
      rewrite (pr1 (pr2 Hlt)).
      right.
      now apply (pr2 (pr2 Hlt)).
    + left.
      apply hr_ispositive_carac in Hlt.
      rewrite (pr1 (pr2 Hlt)).
      right.
      now apply (pr2 (pr2 Hlt)).
  - intro Hlt.
    rewrite <- (hr_to_NR_bij x), <- (hr_to_NR_bij 0%rng), hr_to_NR_zero.
    apply NR_to_hr_ap.
    rewrite islunit_zero_plusNonnegativeReals, isrunit_zero_plusNonnegativeReals.
    revert Hlt.
    rewrite <- (hr_to_NR_bij x).
    generalize (hr_to_NR x) ; clear x ; intros x.
    unfold hr_to_NR, NR_to_hr.
    rewrite setquotunivcomm ; simpl ; intros Hlt.
    destruct Hlt as [Hap | Hap].
    + rewrite (minusNonnegativeReals_eq_zero (pr2 x)).
      exact Hap.
      apply lt_leNonnegativeReals.
      apply_pr2 ispositive_minusNonnegativeReals.
      now apply ispositive_apNonnegativeReals.
    + rewrite (minusNonnegativeReals_eq_zero (pr1 x)).
      now apply issymm_apNonnegativeReals, Hap.
      apply lt_leNonnegativeReals.
      apply_pr2 ispositive_minusNonnegativeReals.
      now apply ispositive_apNonnegativeReals.
Qed.

Lemma islapbinop_plus : islapbinop (X := _,,_,,istightap_hr_ap) BinaryOperations.op1.
Proof.
  intros X Y Z.
  unfold tightapSet_rel ; simpl pr1.
  intro Hap.
  apply_pr2 hr_ap_lt.
  apply hr_ap_lt in Hap.
  destruct Hap as [Hlt | Hlt].
  - left.
    apply_pr2 (hr_plus_ltcompat_l X).
    exact Hlt.
  - right.
    apply_pr2 (hr_plus_ltcompat_l X).
    exact Hlt.
Qed.
Lemma israpbinop_plus : israpbinop (X := _,,_,,istightap_hr_ap) BinaryOperations.op1.
Proof.
  intros X Y Z Hap.
  apply islapbinop_plus with X.
  rewrite !(rngcomm1 _ _ X).
  exact Hap.
Qed.

Lemma islapbinop_mult : islapbinop (X := _,,_,,istightap_hr_ap) BinaryOperations.op2.
Proof.
  intros X Y Z.
  unfold tightapSet_rel ; simpl pr1.
  intro Hap.
  generalize (hr_to_NR X) (hr_to_NR Y) (hr_to_NR Z) ; intros (x,(Hx,_)) (y,(Hy,_)) (z,(Hz,_)).
  eapply hr_ap_carac in Hap.
  Focus 2.
  eapply hr_mult_carac'.
  exact Hy.
  exact Hx.
  instantiate (1 := (pr1 y * pr1 x + pr2 y * pr2 x ,, pr1 y * pr2 x + pr2 y * pr1 x)).
  simpl pr1 ; simpl pr2 ; rewrite !isassoc_plusNonnegativeReals.
  reflexivity.
  Focus 2.
  eapply hr_mult_carac'.
  exact Hz.
  exact Hx.
  instantiate (1 := (pr1 z * pr1 x + pr2 z * pr2 x ,, pr1 z * pr2 x + pr2 z * pr1 x)).
  simpl pr1 ; simpl pr2 ; rewrite !isassoc_plusNonnegativeReals.
  reflexivity.
  simpl pr1 in Hap ; simpl pr2 in Hap.
  eapply hr_ap_carac'.
  exact Hy.
  exact Hz.
  cut ((pr1 y * pr1 x + pr2 y * pr2 x + (pr1 z * pr2 x + pr2 z * pr1 x))
       = (pr1 y + pr2 z) * pr1 x + (pr2 y + pr1 z) * pr2 x).
  intro H ; simpl in Hap,H ; rewrite H in Hap ; clear H.
  cut ((pr1 z * pr1 x + pr2 z * pr2 x + (pr1 y * pr2 x + pr2 y * pr1 x))
       = (pr1 z + pr2 y) * pr1 x + (pr2 z + pr1 y) * pr2 x).
  intro H ; simpl in H,Hap ; rewrite H in Hap ; clear H.
  apply ap_plusNonnegativeReals in Hap.
  revert Hap ; apply hinhuniv ; intros [Hap | Hap].
  - apply ap_multNonnegativeReals in Hap.
    revert Hap ; apply hinhuniv ; intros [Hap | Hap].
    + exact Hap.
    + now apply fromempty, (isirrefl_apNonnegativeReals (pr1 x)), Hap .
  - apply ap_multNonnegativeReals in Hap.
    revert Hap ; apply hinhuniv ; intros [Hap | Hap].
    + rewrite (iscomm_plusNonnegativeReals (pr1 z)), iscomm_plusNonnegativeReals.
      now apply issymm_apNonnegativeReals, Hap.
    + now apply fromempty, (isirrefl_apNonnegativeReals (pr2 x)), Hap.
  - rewrite !isrdistr_plus_multNonnegativeReals.
    rewrite !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    do 2 rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
    reflexivity.
  - rewrite !isrdistr_plus_multNonnegativeReals.
    rewrite !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    do 2 rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
    reflexivity.
Qed.
Lemma israpbinop_mult : israpbinop (X := _,,_,,istightap_hr_ap) BinaryOperations.op2.
Proof.
  intros X Y Z Hap.
  apply islapbinop_mult with X.
  rewrite !(rngcomm2 _ _ X).
  exact Hap.
Qed.

Lemma hr_ap_0_1 :
  isnonzeroCR hr_commrng (hr_ap_rel,, istightap_hr_ap).
Proof.
  apply hinhpr ; simpl pr1 ; simpl.
  exists 0 ; simpl.
  change (1 + 0 + 0 ≠ 0 + 0 + 0).
  rewrite !isrunit_zero_plusNonnegativeReals.
  apply isnonzeroNonnegativeReals.
Qed.

Lemma hr_islinv_neg :
  ∀ (x : NonnegativeReals) (Hap : x ≠ 0),
   (NR_to_hr (0%NR,, invNonnegativeReals x Hap) * NR_to_hr (0%NR,, x))%rng = 1%rng.
Proof.
  intros x Hap.
  eapply hr_eq_carac'.
  - eapply hr_mult_carac'.
    now apply NR_to_hr_inside.
    now apply NR_to_hr_inside.
    simpl pr1 ; simpl pr2.
    rewrite  !islabsorb_zero_multNonnegativeReals, israbsorb_zero_multNonnegativeReals, !isrunit_zero_plusNonnegativeReals, !islunit_zero_plusNonnegativeReals.
    rewrite islinv_invNonnegativeReals.
    apply hr_one_carac.
    now apply NR_to_hr_inside.
  - now apply NR_to_hr_inside.
  - reflexivity.
Qed.
Lemma hr_isrinv_neg :
  ∀ (x : NonnegativeReals) (Hap : x ≠ 0),
   (NR_to_hr (0%NR,, x) * NR_to_hr (0%NR,, invNonnegativeReals x Hap))%rng = 1%rng.
Proof.
  intros x Hap.
  rewrite rngcomm2.
  now apply (hr_islinv_neg x Hap).
Qed.

Lemma hr_islinv_pos :
  ∀ (x : NonnegativeReals) (Hap : x ≠ 0),
   (NR_to_hr (invNonnegativeReals x Hap,,0%NR) * NR_to_hr (x,,0%NR))%rng = 1%rng.
Proof.
  intros x Hap.
  eapply hr_eq_carac'.
  - eapply hr_mult_carac'.
    now apply NR_to_hr_inside.
    now apply NR_to_hr_inside.
    simpl pr1 ; simpl pr2.
    rewrite  !islabsorb_zero_multNonnegativeReals, israbsorb_zero_multNonnegativeReals, !isrunit_zero_plusNonnegativeReals.
    rewrite islinv_invNonnegativeReals.
    apply hr_one_carac.
    now apply NR_to_hr_inside.
  - now apply NR_to_hr_inside.
  - reflexivity.
Qed.
Lemma hr_isrinv_pos :
  ∀ (x : NonnegativeReals) (Hap : x ≠ 0),
   (NR_to_hr (x,, 0%NR) * NR_to_hr (invNonnegativeReals x Hap,, 0%NR))%rng = 1%rng.
Proof.
  intros x Hap.
  rewrite rngcomm2.
  now apply (hr_islinv_pos x Hap).
Qed.

Lemma hr_ex_inv :
  ∀ x : hr_commrng,
    hr_ap_rel x 0%rng -> multinvpair hr_commrng x.
Proof.
  intros X Hap.
  destruct (pr1 (hr_ap_lt _ _) Hap) as [x|x] ; simpl.
  - apply hr_isnegative_carac in x.
    rewrite <- (NR_to_hr_unique _ _ (pr1 (pr2 x))).
    eexists ; split.
    + refine (hr_islinv_neg _ _).
      apply_pr2 ispositive_apNonnegativeReals.
      exact (pr2 (pr2 x)).
    + refine (hr_isrinv_neg _ _).
  - apply hr_ispositive_carac in x.
    rewrite <- (NR_to_hr_unique _ _ (pr1 (pr2 x))).
    eexists ; split.
    + refine (hr_islinv_pos _ _).
      apply_pr2 ispositive_apNonnegativeReals.
      exact (pr2 (pr2 x)).
    + exact (hr_isrinv_pos _ _).
Defined.

Definition hr_ConstructiveField : ConstructiveField.
Proof.
  exists hr_commrng.
  exists (_,,istightap_hr_ap).
  repeat split.
  - exact islapbinop_plus.
  - exact israpbinop_plus.
  - exact islapbinop_mult.
  - exact israpbinop_mult.
  - exact hr_ap_0_1.
  - exact hr_ex_inv.
Defined.

(** ** hr_abs *)

Definition hr_abs (x : hr_ConstructiveField) : NonnegativeReals :=
  maxNonnegativeReals (pr1 (pr1 (hr_to_NR x))) (pr2 (pr1 (hr_to_NR x))).

Lemma hr_abs_pty1 :
  ∀ X : hr_ConstructiveField,
  ∀ x : NonnegativeReals × NonnegativeReals,
    pr1 X x -> (hr_abs X <= maxNonnegativeReals (pr1 x) (pr2 x)).
Proof.
  intros X x Hx.
  unfold hr_abs.
  destruct (hr_to_NR X) as (y,(Hy,Hle)).
  simpl pr1.
  apply maxNonnegativeReals_le.
  - apply istrans_leNonnegativeReals with (pr1 x).
    now apply Hle.
    apply maxNonnegativeReals_le_l.
  - apply istrans_leNonnegativeReals with (pr2 x).
    apply (pr2 (Hle _ Hx)).
    apply maxNonnegativeReals_le_r.
Qed.
Lemma hr_abs_opp :
  ∀ x : hr_ConstructiveField, hr_abs (- x)%rng = hr_abs x.
Proof.
  intros X.
  apply isantisymm_leNonnegativeReals ; split.
  - apply maxNonnegativeReals_le.
    + eapply istrans_leNonnegativeReals, maxNonnegativeReals_le_r.
      apply (pr2 (pr2 (hr_to_NR (- X)%rng)) (pr2 (pr1 (hr_to_NR X)),,pr1 (pr1 (hr_to_NR X)))).
      destruct (hr_to_NR X) as (x,(Hx,Hx')) ; simpl pr1.
      eapply hr_opp_carac'.
      exact Hx.
      reflexivity.
    + eapply istrans_leNonnegativeReals, maxNonnegativeReals_le_l.
      apply (fun H => pr2 ((pr2 (pr2 (hr_to_NR (- X)%rng)) (pr2 (pr1 (hr_to_NR X)),,pr1 (pr1 (hr_to_NR X)))) H)).
      destruct (hr_to_NR X) as (x,(Hx,Hx')) ; simpl pr1.
      eapply hr_opp_carac'.
      exact Hx.
      reflexivity.
  - apply maxNonnegativeReals_le.
    + eapply istrans_leNonnegativeReals, maxNonnegativeReals_le_r.
      apply (pr2 (pr2 (hr_to_NR (X))) (pr2 (pr1 (hr_to_NR (- X)%rng)),,pr1 (pr1 (hr_to_NR (-X)%rng)))).
      destruct (hr_to_NR (- X)%rng) as (x,(Hx,Hx')) ; simpl pr1.
      assert (X = (- - X)%rng).
      { apply pathsinv0, rngminusminus. }
      rewrite X0.
      eapply hr_opp_carac'.
      exact Hx.
      reflexivity.
    + eapply istrans_leNonnegativeReals, maxNonnegativeReals_le_l.
      apply (fun H => pr2 ((pr2 (pr2 (hr_to_NR (X))) (pr2 (pr1 (hr_to_NR (- X)%rng)),,pr1 (pr1 (hr_to_NR (-X)%rng)))) H) ).
      destruct (hr_to_NR (- X)%rng) as (x,(Hx,Hx')) ; simpl pr1.
      assert (X = (- - X)%rng).
      { apply pathsinv0, rngminusminus. }
      rewrite X0.
      eapply hr_opp_carac'.
      exact Hx.
      reflexivity.
Qed.

(** ** Archimedean *)

Lemma nat_to_hr_O :
  nat_to_hr O = 0%rng.
Proof.
  unfold nat_to_hr.
  rewrite nat_to_NonnegativeReals_O.
  refine (hr_eq_carac' _ _ _ _ _ _ _).
  - apply NR_to_hr_inside.
  - apply NR_to_hr_inside.
  - simpl.
    reflexivity.
Qed.

Lemma nat_to_hr_S :
  ∀ n : nat, nat_to_hr (S n) = (1 + nat_to_hr n)%rng.
Proof.
  intros n.
  unfold nat_to_hr.
  rewrite nat_to_NonnegativeReals_Sn, iscomm_plusNonnegativeReals.
  refine (hr_eq_carac' _ _ _ _ _ _ _).
  - apply NR_to_hr_inside.
  - refine (hr_plus_carac' _ _ _ _ _ _ _ _).
    + apply NR_to_hr_inside.
    + apply NR_to_hr_inside.
    + instantiate (1 := (1 + nat_to_NonnegativeReals n)%NR ,, 0%NR).
      simpl.
      rewrite !isrunit_zero_plusNonnegativeReals.
      reflexivity.
  - reflexivity.
Qed.

Lemma hr_archimedean :
  ∀ x : hr_ConstructiveField, ∃ n : nat, hr_lt_rel x (nat_to_hr n).
Proof.
  intros X.
  set (x := hr_to_NR X).
  generalize (NonnegativeReals_Archimedean (pr1 (pr1 x))).
  apply hinhfun.
  intros n.
  exists (pr1 n).
  apply (hr_lt_carac' X (nat_to_hr (pr1 n)) (pr1 x) (nat_to_NonnegativeReals (pr1 n) ,, 0)).
  - exact (pr1 (pr2 x)).
  - apply hinhpr.
    exists 0.
    reflexivity.
  - simpl pr1 ; simpl pr2.
    eapply istrans_lt_le_ltNonnegativeReals, plusNonnegativeReals_le_l.
    rewrite isrunit_zero_plusNonnegativeReals.
    exact (pr2 n).
Qed.

(** ** Completeness *)

Definition Cauchy_seq (u : nat -> hr_ConstructiveField) : hProp.
Proof.
  intro u.
  apply (hProppair (∀ c : NonnegativeReals, 0 < c -> ∃ N : nat, ∀ n m : nat, N ≤ n -> N ≤ m -> hr_abs (u m - u n)%rng < c)).
  apply impred_isaprop ; intro.
  apply isapropimpl.
  apply pr2.
Defined.

Lemma Cauchy_seq_pr1 (u : nat -> hr_ConstructiveField) :
  let x := λ n : nat, pr1 (pr1 (hr_to_NR (u n))) in
  Cauchy_seq u -> NonnegativeReals.Cauchy_seq x.
Proof.
  intros u x.
  set (y := λ n : nat, pr2 (pr1 (hr_to_NR (u n)))) ; simpl in y.
  assert (Hxy : ∀ n, NR_to_hr (x n ,, y n) = u n).
  { intros n.
    apply NR_to_hr_unique.
    unfold x, y ; rewrite <- tppr.
    apply (pr1 (pr2 (hr_to_NR (u n)))). }
  intros Cu c Hc.
  generalize (Cu c Hc).
  apply hinhfun ; intros (N,Hu).
  exists N ; intros n m Hn Hm.
  specialize (Hu _ _ Hn Hm).
  split.
  - apply (plusNonnegativeReals_ltcompat_r (x m)) in Hu.
    apply istrans_le_lt_ltNonnegativeReals with (x m + hr_abs (u m - u n)%rng).
    2: exact Hu.
    eapply istrans_leNonnegativeReals.
    2: apply plusNonnegativeReals_lecompat_r.
    2: apply maxNonnegativeReals_le_r.
    destruct (hr_to_NR (u m - u n)%rng) as (z,(Hz,Hz')) ; simpl pr1.
    eapply (hr_minus_carac (u m) (u n)) in Hz.
    2: rewrite <- Hxy ; apply NR_to_hr_inside.
    2: rewrite <- Hxy ; apply NR_to_hr_inside.
    simpl in Hz.
    apply ((pr2 (pr2 (hr_to_NR (u n)))) (x m + pr2 z ,, y m + pr1 z)).
    generalize (pr1 (pr2 (hr_to_NR (u n)))).
    apply hr_inside_carac' ; simpl pr1 ; simpl pr2.
    rewrite <- isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (x n)), (iscomm_plusNonnegativeReals (y m + x n)), <-isassoc_plusNonnegativeReals.
    rewrite <- Hz.
    rewrite !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    apply iscomm_plusNonnegativeReals.
  - apply (plusNonnegativeReals_ltcompat_r (x n)) in Hu.
    apply istrans_le_lt_ltNonnegativeReals with (x n + hr_abs (u m - u n)%rng).
    2: exact Hu.
    eapply istrans_leNonnegativeReals.
    2: apply plusNonnegativeReals_lecompat_r.
    2: apply maxNonnegativeReals_le_l.
    destruct (hr_to_NR (u m - u n)%rng) as (z,(Hz,Hz')) ; simpl pr1.
    eapply (hr_minus_carac (u m) (u n)) in Hz.
    2: rewrite <- Hxy ; apply NR_to_hr_inside.
    2: rewrite <- Hxy ; apply NR_to_hr_inside.
    simpl in Hz.
    apply ((pr2 (pr2 (hr_to_NR (u m)))) (x n + pr1 z ,, y n + pr2 z)).
    generalize (pr1 (pr2 (hr_to_NR (u m)))).
    apply hr_inside_carac'.
    simpl pr1 ; simpl pr2.
    rewrite <- !isassoc_plusNonnegativeReals.
    change (pr1 (pr1 (hr_to_NR (u m)))) with (x m).
    rewrite Hz.
    rewrite iscomm_plusNonnegativeReals, <- !isassoc_plusNonnegativeReals.
    reflexivity.
Qed.
Lemma Cauchy_seq_pr2 (u : nat -> hr_ConstructiveField) :
  let y := λ n : nat, pr2 (pr1 (hr_to_NR (u n))) in
  Cauchy_seq u -> NonnegativeReals.Cauchy_seq y.
Proof.
  intros u y ; simpl in y.
  set (x := λ n : nat, pr1 (pr1 (hr_to_NR (u n)))).
  assert (Hxy : ∀ n, NR_to_hr (x n ,, y n) = u n).
  { intros n.
    apply NR_to_hr_unique.
    unfold x, y ; rewrite <- tppr.
    apply (pr1 (pr2 (hr_to_NR (u n)))). }
  intros Cu c Hc.
  generalize (Cu c Hc).
  apply hinhfun ; intros (N,Hu).
  exists N ; intros n m Hn Hm.
  specialize (Hu _ _ Hn Hm).
  split.
  - apply (plusNonnegativeReals_ltcompat_r (y m)) in Hu.
    apply istrans_le_lt_ltNonnegativeReals with (y m + hr_abs (u m - u n)%rng).
    2: exact Hu.
    eapply istrans_leNonnegativeReals.
    2: apply plusNonnegativeReals_lecompat_r.
    2: apply maxNonnegativeReals_le_l.
    destruct (hr_to_NR (u m - u n)%rng) as (z,(Hz,Hz')) ; simpl pr1.
    revert Hz.
    rewrite <- ! Hxy ; apply hinhuniv ; intros (d) ;
    simpl.
    change ((x m + y n + pr2 z + d = pr1 z + (y m + x n) + d)%NR -> (y n <= y m + pr1 z)%NR) ; intro Hd.
    apply (fun H => pr2 (((pr2 (pr2 (hr_to_NR (u n)))) (x m + pr2 z ,, y m + pr1 z)) H)).
    rewrite <- Hxy ; apply hinhpr ; simpl.
    exists d.
    rewrite <- isassoc_plusNonnegativeReals, (iscomm_plusNonnegativeReals (x n)), (iscomm_plusNonnegativeReals (y m + x n)).
    change ((pr1 z + (y m + x n))%NR + d)%rng
    with (pr1 z + (y m + x n) + d)%NR.
    rewrite <- Hd.
    rewrite !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_r.
    rewrite <- !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_l.
    apply iscomm_plusNonnegativeReals.
  - apply (plusNonnegativeReals_ltcompat_r (y n)) in Hu.
    apply istrans_le_lt_ltNonnegativeReals with (y n + hr_abs (u m - u n)%rng).
    2: exact Hu.
    eapply istrans_leNonnegativeReals.
    2: apply plusNonnegativeReals_lecompat_r.
    2: apply maxNonnegativeReals_le_r.
    destruct (hr_to_NR (u m - u n)%rng) as (z,(Hz,Hz')) ; simpl pr1.
    revert Hz.
    rewrite <- ! Hxy ; apply hinhuniv ; intros (d,Hd) ;
    simpl in Hd.
    apply (fun H => pr2 (((pr2 (pr2 (hr_to_NR (u m)))) (x n + pr1 z ,, y n + pr2 z)) H)).
    rewrite <- Hxy ; apply hinhpr ; simpl.
    exists d.
    rewrite <- !isassoc_plusNonnegativeReals.
    change ((x m + y n + pr2 z)%NR + d)%rng
    with (x m + y n + pr2 z + d)%rng.
    simpl in Hd |- * ; rewrite Hd.
    rewrite <- !isassoc_plusNonnegativeReals.
    apply_pr2 plusNonnegativeReals_eqcompat_l.
    now rewrite iscomm_plusNonnegativeReals, !isassoc_plusNonnegativeReals.
Qed.

Definition is_lim_seq (u : nat -> hr_ConstructiveField) (l : hr_ConstructiveField) : hProp.
Proof.
  intros u l.
  apply (hProppair (∀ c : NonnegativeReals, 0 < c -> ∃ N : nat, ∀ n : nat, N ≤ n -> hr_abs (u n - l)%rng < c)).
  apply impred_isaprop ; intro.
  apply isapropimpl.
  apply pr2.
Defined.
Definition ex_lim_seq (u : nat -> hr_ConstructiveField) := Σ l, is_lim_seq u l.

Lemma Cauchy_seq_impl_ex_lim_seq (u : nat -> hr_ConstructiveField) :
  Cauchy_seq u -> ex_lim_seq u.
Proof.
  intros u Cu.
  set (x := λ n, pr1 (pr1 (hr_to_NR (u n)))).
  set (y := λ n, pr2 (pr1 (hr_to_NR (u n)))) ; simpl in y.
  assert (Hxy : ∀ n, NR_to_hr (x n ,, y n) = u n).
  { intros n.
    apply NR_to_hr_unique.
    unfold x, y ; rewrite <- tppr.
    apply (pr1 (pr2 (hr_to_NR (u n)))). }
  generalize (Cauchy_seq_impl_ex_lim_seq x (Cauchy_seq_pr1 u Cu)).
  set (lx := Cauchy_lim_seq x (Cauchy_seq_pr1 u Cu)) ; clearbody lx ; intro Hx.
  generalize (Cauchy_seq_impl_ex_lim_seq y (Cauchy_seq_pr2 u Cu)).
  set (ly := Cauchy_lim_seq y (Cauchy_seq_pr2 u Cu)) ; clearbody ly ; intro Hy.
  exists (NR_to_hr (lx,,ly)).
  intros c Hc.
  apply ispositive_halfNonnegativeReals in Hc.
  generalize (Hx _ Hc) (Hy _ Hc) ;
    apply hinhfun2 ; clear Hy Hx ;
    intros (Nx,Hx) (Ny,Hy).
  exists (max Nx Ny) ; intros n Hn.
  rewrite <- Hxy ; simpl pr1.
  apply maxNonnegativeReals_lt.
  - destruct hr_to_NR as (z,(Hz',Hz)) ; simpl pr1 ; clear Hz'.
    eapply istrans_le_lt_ltNonnegativeReals.
    assert (Hlim : pr1 (NR_to_hr (x n,, y n) - NR_to_hr (lx,, ly))%rng (x n + ly ,, y n + lx)).
    { apply hinhpr ; exists 0 ; reflexivity. }
    apply_pr2_in hr_repres Hlim.
    apply (Hz _ Hlim).
    simpl pr1.
    apply_pr2 (plusNonnegativeReals_ltcompat_r (y n + lx)).
    rewrite iscomm_plusNonnegativeReals, <- maxNonnegativeReals_minus_plus.
    apply maxNonnegativeReals_lt.
    + rewrite (double_halfNonnegativeReals c), (iscomm_plusNonnegativeReals (y n)), (isassoc_plusNonnegativeReals lx (y n)), <- (isassoc_plusNonnegativeReals (y n)), (iscomm_plusNonnegativeReals (y n)), <- !isassoc_plusNonnegativeReals, (isassoc_plusNonnegativeReals (lx + _)).
      apply plusNonnegativeReals_ltcompat.
      apply Hx.
      apply istransnatleh with (2 := Hn).
      apply max_le_l.
      apply_pr2 Hy.
      apply istransnatleh with (2 := Hn).
      apply max_le_r.
    + apply plusNonnegativeReals_lt_r .
      now apply_pr2 ispositive_halfNonnegativeReals.
  - destruct hr_to_NR as (z,(Hz',Hz)) ; simpl pr1 ; clear Hz'.
    eapply istrans_le_lt_ltNonnegativeReals.
    assert (Hlim : pr1 (NR_to_hr (x n,, y n) - NR_to_hr (lx,, ly))%rng (x n + ly ,, y n + lx)).
    { apply hinhpr ; exists 0 ; reflexivity. }
    apply_pr2_in hr_repres Hlim.
    apply_pr2 (Hz _ Hlim).
    simpl pr2.
    apply_pr2 (plusNonnegativeReals_ltcompat_r (x n + ly)).
    rewrite iscomm_plusNonnegativeReals, <- maxNonnegativeReals_minus_plus.
    apply maxNonnegativeReals_lt.
    + rewrite (double_halfNonnegativeReals c), (iscomm_plusNonnegativeReals (x n)), (isassoc_plusNonnegativeReals ly (x n)), <- (isassoc_plusNonnegativeReals (x n)), (iscomm_plusNonnegativeReals (x n)), <- !isassoc_plusNonnegativeReals, (isassoc_plusNonnegativeReals (ly + _)).
      apply plusNonnegativeReals_ltcompat.
      apply Hy.
      apply istransnatleh with (2 := Hn).
      apply max_le_r.
      apply_pr2 Hx.
      apply istransnatleh with (2 := Hn).
      apply max_le_l.
    + apply plusNonnegativeReals_lt_r .
      now apply_pr2 ispositive_halfNonnegativeReals.
Qed.

(** * Interface for Reals *)

Definition Reals : ConstructiveField := hr_ConstructiveField.

(** ** Operations and relations *)

Definition Rap : hrel Reals := CFap.
Definition Rlt : hrel Reals := hr_lt_rel.
Definition Rgt : hrel Reals := λ x y : Reals, Rlt y x.
Definition Rle : hrel Reals := hr_le_rel.
Definition Rge : hrel Reals := λ x y : Reals, Rle y x.

Definition Rzero : Reals := CFzero.
Definition Rplus : binop Reals := CFplus.
Definition Ropp : unop Reals := CFopp.
Definition Rminus : binop Reals := CFminus.

Definition Rone : Reals := CFone.
Definition Rmult : binop Reals := CFmult.
Definition Rinv : ∀ x : Reals, (Rap x Rzero) -> Reals := CFinv.
Definition Rdiv : Reals -> ∀ y : Reals, (Rap y Rzero) -> Reals := CFdiv.

Definition Rtwo : Reals := Rplus Rone Rone.
Definition Rabs : Reals -> NonnegativeReals := hr_abs.

Definition NRNRtoR : NonnegativeReals -> NonnegativeReals -> Reals := λ (x y : NonnegativeReals), NR_to_hr (x,,y).
Definition RtoNRNR : Reals -> NonnegativeReals × NonnegativeReals := λ x : Reals, pr1 (hr_to_NR x).

Delimit Scope R_scope with R.
Open Scope R_scope.

Infix "≠" := Rap : R_scope.
Infix "<" := Rlt : R_scope.
Infix ">" := Rgt : R_scope.
Infix "<=" := Rle : R_scope.
Infix ">=" := Rge : R_scope.

Notation "0" := Rzero : R_scope.
Notation "1" := Rone : R_scope.
Notation "2" := Rtwo : R_scope.
Infix "+" := Rplus : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Infix "-" := Rminus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "/ x" := (Rinv (pr1 x) (pr2 x)) : R_scope.
Notation "x / y" := (Rdiv x (pr1 y) (pr2 y)) : R_scope.

(** ** NRNRtoR and RtoNRNR *)

Lemma NRNRtoR_RtoNRNR :
  ∀ x : Reals, NRNRtoR (pr1 (RtoNRNR x)) (pr2 (RtoNRNR x)) = x.
Proof.
  intros X.
  unfold RtoNRNR.
  destruct (hr_to_NR X) as ((x,y),(Hx,Hle)).
  simpl pr1 ; simpl pr2.
  apply (setquotl0 _ X ((x,,y),,Hx)).
Qed.

Lemma RtoNRNR_NRNRtoR :
  ∀ x y : NonnegativeReals,
    (RtoNRNR (NRNRtoR x y)) = ((x - y)%NR ,, (y - x)%NR).
Proof.
  intros X Y.
  unfold RtoNRNR.
  destruct (hr_to_NR _) as ((x,y),(Hx,Hle)).
  apply dirprodeq ;
  simpl pr1 ; simpl pr2 ;
  apply isantisymm_leNonnegativeReals ;
  split.
  - refine (pr1 (Hle ((X - Y)%NR ,, (Y - X)%NR) _)).
    apply hinhpr.
    exists 0%NR.
    change  ((X + (Y - X) + 0)%NR = ((X - Y) + Y + 0)%NR).
    rewrite (iscomm_plusNonnegativeReals X), <- !maxNonnegativeReals_minus_plus, iscomm_maxNonnegativeReals.
    reflexivity.
  - apply_pr2 (plusNonnegativeReals_lecompat_l Y).
    rewrite <- maxNonnegativeReals_minus_plus.
    apply maxNonnegativeReals_le.
    * revert Hx.
      apply hinhuniv.
      intros (c).
      change ((X + y + c)%NR = (x + Y + c)%NR -> (X <= (x + Y)%NR)%NR).
      intros Hx.
      apply_pr2 (plusNonnegativeReals_lecompat_l c).
      rewrite <- Hx.
      apply plusNonnegativeReals_lecompat_l, plusNonnegativeReals_le_l.
    * apply plusNonnegativeReals_le_r.
  - refine (pr2 (Hle ((X - Y)%NR ,, (Y - X)%NR) _)).
    apply hinhpr.
    exists 0%NR.
    change  ((X + (Y - X) + 0)%NR = ((X - Y) + Y + 0)%NR).
    rewrite (iscomm_plusNonnegativeReals X), <- !maxNonnegativeReals_minus_plus, iscomm_maxNonnegativeReals.
    reflexivity.
  - apply_pr2 (plusNonnegativeReals_lecompat_l X).
    rewrite <- maxNonnegativeReals_minus_plus.
    apply maxNonnegativeReals_le.
    * revert Hx.
      apply hinhuniv.
      intros (c).
      change ((X + y + c)%NR = (x + Y + c)%NR -> (Y <= (y + X)%NR)%NR).
      intros Hx.
      apply_pr2 (plusNonnegativeReals_lecompat_l c).
      rewrite (iscomm_plusNonnegativeReals y), Hx.
      apply plusNonnegativeReals_lecompat_l, plusNonnegativeReals_le_r.
    * apply plusNonnegativeReals_le_r.
Qed.

Lemma NRNRtoR_inside :
  ∀ x y : NonnegativeReals, pr1 (NRNRtoR x y) (x,,y).
Proof.
  intros x y.
  apply hinhpr.
  exists 0%NR ; simpl.
  reflexivity.
Qed.

Lemma RtoNRNR_le_pr1 :
  ∀ (X : Reals) (x y : NonnegativeReals), pr1 X (x,,y) -> (pr1 (RtoNRNR X) <= x)%NR.
Proof.
  intros X x y HX.
  exact (pr1 (pr2 (pr2 (hr_to_NR X)) (x,,y) HX)).
Qed.
Lemma RtoNRNR_le_pr2 :
  ∀ (X : Reals) (x y : NonnegativeReals), pr1 X (x,,y) -> (pr2 (RtoNRNR X) <= y)%NR.
Proof.
  intros X x y HX.
  exact (pr2 (pr2 (pr2 (hr_to_NR X)) (x,,y) HX)).
Qed.

Lemma NRNRtoR_zero :
  NRNRtoR 0%NR 0%NR = 0.
Proof.
  unfold NRNRtoR, NR_to_hr.
  refine (setquotl0 _ 0 (_,,_)).
  apply hinhpr.
  exists 0%NR ; simpl.
  reflexivity.
Qed.
Lemma NRNRtoR_one :
  NRNRtoR 1%NR 0%NR = 1.
Proof.
  unfold NRNRtoR, NR_to_hr.
  refine (setquotl0 _ 1 (_,,_)).
  apply hinhpr.
  exists 0%NR ; simpl.
  reflexivity.
Qed.

Lemma NRNRtoR_eq :
  ∀ x x' y y' : NonnegativeReals,
    (x + y' = x' + y)%NR <->
    NRNRtoR x y = NRNRtoR x' y'.
Proof.
  intros x x' y y'.
  split ; intro H.
  - refine (hr_eq_carac' _ _ _ _ _ _ _).
    apply NRNRtoR_inside.
    apply NRNRtoR_inside.
    exact H.
  - refine (hr_eq_carac _ _ _ (_,,_) (_,,_) _ _).
    exact H.
    apply NRNRtoR_inside.
    apply NRNRtoR_inside.
Qed.
Lemma NRNRtoR_ap :
  ∀ x x' y y' : NonnegativeReals,
    (x + y' ≠ x' + y)%NR <->
    NRNRtoR x y ≠ NRNRtoR x' y'.
Proof.
  intros x x' y y'.
  split ; intro H.
  - refine (hr_ap_carac' _ _ _ _ _ _ _).
    apply NRNRtoR_inside.
    apply NRNRtoR_inside.
    exact H.
  - refine (hr_ap_carac _ _ _ (_,,_) (_,,_) _ _).
    exact H.
    apply NRNRtoR_inside.
    apply NRNRtoR_inside.
Qed.
Lemma NRNRtoR_lt :
  ∀ x x' y y' : NonnegativeReals,
    (x + y' < x' + y)%NR <->
    NRNRtoR x y < NRNRtoR x' y'.
Proof.
  intros x x' y y'.
  split ; intro H.
  - refine (hr_lt_carac' _ _ _ _ _ _ _).
    apply NRNRtoR_inside.
    apply NRNRtoR_inside.
    exact H.
  - refine (hr_lt_carac _ _ _ (_,,_) (_,,_) _ _).
    exact H.
    apply NRNRtoR_inside.
    apply NRNRtoR_inside.
Qed.
Lemma NRNRtoR_le :
  ∀ x x' y y' : NonnegativeReals,
    (x + y' <= x' + y)%NR <->
    NRNRtoR x y <= NRNRtoR x' y'.
Proof.
  intros x x' y y'.
  split ; intro H.
  - refine (hr_le_carac' _ _ _ _ _ _ _).
    apply NRNRtoR_inside.
    apply NRNRtoR_inside.
    exact H.
  - refine (hr_le_carac _ _ _ (_,,_) (_,,_) _ _).
    exact H.
    apply NRNRtoR_inside.
    apply NRNRtoR_inside.
Qed.

Lemma NRNRtoR_plus :
  ∀ x x' y y' : NonnegativeReals, NRNRtoR (x + x')%NR (y + y')%NR = NRNRtoR x y + NRNRtoR x' y'.
Proof.
  intros x x' y y'.
  unfold NRNRtoR, NR_to_hr.
  refine (setquotl0 _ _ (_,,_)).
  apply hinhpr.
  exists 0%NR ; simpl.
  reflexivity.
Qed.
Lemma NRNRtoR_opp :
  ∀ x y : NonnegativeReals, NRNRtoR y x = - NRNRtoR x y.
Proof.
  intros x y.
  unfold NRNRtoR, NR_to_hr.
  refine (setquotl0 _ _ (_,,_)).
  apply hinhpr.
  exists 0%NR ; simpl.
  reflexivity.
Qed.
Lemma NRNRtoR_minus :
  ∀ x x' y y' : NonnegativeReals, NRNRtoR (x + y')%NR (y + x')%NR = NRNRtoR x y - NRNRtoR x' y'.
Proof.
  intros x x' y y'.
  unfold NRNRtoR, NR_to_hr.
  refine (setquotl0 _ _ (_,,_)).
  apply hinhpr.
  exists 0%NR ; simpl.
  reflexivity.
Qed.
Lemma NRNRtoR_mult :
  ∀ x x' y y' : NonnegativeReals, NRNRtoR (x * x' + y * y')%NR (x * y' + y * x')%NR = NRNRtoR x y * NRNRtoR x' y'.
Proof.
  intros x x' y y'.
  unfold NRNRtoR, NR_to_hr.
  refine (setquotl0 _ _ (_,,_)).
  apply hinhpr.
  exists 0%NR ; simpl.
  reflexivity.
Qed.
Lemma NRNRtoR_inv_pos :
  ∀ (x : NonnegativeReals) Hrn Hr,
    NRNRtoR (invNonnegativeReals x Hrn) 0%NR = Rinv (NRNRtoR x 0%NR) Hr.
Proof.
  intros x Hrn Hr.
  rewrite <- (isrunit_CFone_CFmult (NRNRtoR (invNonnegativeReals x Hrn) 0%NR)), <- (isrunit_CFone_CFmult (Rinv (NRNRtoR x 0%NR) Hr)).
  rewrite <- (isrinv_CFinv (X := Reals) (NRNRtoR x 0%NR) Hr).
  rewrite <- !(isassoc_CFmult (X := Reals)).
  apply (maponpaths (λ x, (x * _)%CF)).
  rewrite <- NRNRtoR_mult.
  unfold Rinv.
  rewrite (islinv_CFinv (X := Reals) _ Hr).
  rewrite !israbsorb_zero_multNonnegativeReals, islabsorb_zero_multNonnegativeReals.
  rewrite !isrunit_zero_plusNonnegativeReals.
  rewrite islinv_invNonnegativeReals.
  apply NRNRtoR_one.
Qed.
Lemma NRNRtoR_inv_neg :
  ∀ (x : NonnegativeReals) Hrn Hr,
    NRNRtoR 0%NR (invNonnegativeReals x Hrn) = Rinv (NRNRtoR 0%NR x) Hr.
Proof.
  intros x Hrn Hr.
  rewrite <- (isrunit_CFone_CFmult (NRNRtoR 0%NR (invNonnegativeReals x Hrn))), <- (isrunit_CFone_CFmult (Rinv (NRNRtoR 0%NR x) Hr)).
  rewrite <- (isrinv_CFinv (X := Reals) (NRNRtoR 0%NR x) Hr).
  rewrite <- !(isassoc_CFmult (X := Reals)).
  apply (maponpaths (λ x, (x * _)%CF)).
  rewrite <- NRNRtoR_mult.
  unfold Rinv.
  rewrite (islinv_CFinv (X := Reals) _ Hr).
  rewrite !israbsorb_zero_multNonnegativeReals, islabsorb_zero_multNonnegativeReals.
  rewrite !islunit_zero_plusNonnegativeReals.
  rewrite islinv_invNonnegativeReals.
  apply NRNRtoR_one.
Qed.

(** ** Theorems about apartness and order *)

Lemma ispositive_Rone : 0 < 1.
Proof.
  rewrite <- NRNRtoR_zero, <- NRNRtoR_one.
  apply NRNRtoR_lt.
  rewrite !isrunit_zero_plusNonnegativeReals.
  apply ispositive_apNonnegativeReals.
  apply isnonzeroNonnegativeReals.
Qed.

Lemma isirrefl_Rlt :
  ∀ x : Reals, ¬ (x < x).
Proof.
  exact (pr2 isStrongOrder_hr_lt).
Qed.
Lemma istrans_Rlt :
  ∀ x y z : Reals, x < y -> y < z -> x < z.
Proof.
  exact (pr1 isStrongOrder_hr_lt).
Qed.
Lemma iscotrans_Rlt :
  ∀ (x y z : Reals), (x < z) -> (x < y) ∨ (y < z).
Proof.
  exact iscotrans_hr_lt.
Qed.

Lemma Rplus_ltcompat_l:
  ∀ x y z : Reals, y < z <-> (y + x) < (z + x).
Proof.
  exact hr_plus_ltcompat_l.
Qed.
Lemma Rplus_ltcompat_r:
  ∀ x y z : Reals, y < z <-> (x + y) < (x + z).
Proof.
  exact hr_plus_ltcompat_r.
Qed.
Lemma Rmult_ltcompat_l:
  ∀ x y z : Reals,
    0 < x -> y < z -> (y * x) < (z * x).
Proof.
  exact hr_mult_ltcompat_l.
Qed.
Lemma Rmult_ltcompat_l':
  ∀ x y z : Reals,
    0 <= x -> (y * x) < (z * x) -> y < z.
Proof.
  exact hr_mult_ltcompat_l'.
Qed.
Lemma Rmult_ltcompat_r:
  ∀ x y z : Reals,
    0 < x -> y < z -> (x * y) < (x * z).
Proof.
  intros x y z.
  rewrite !(iscomm_CFmult x).
  now apply Rmult_ltcompat_l.
Qed.
Lemma Rmult_ltcompat_r':
  ∀ x y z : Reals,
    0 <= x -> (x * y) < (x * z) -> y < z.
Proof.
  exact hr_mult_ltcompat_r'.
Qed.

Lemma Rarchimedean:
  ∀ x : Reals, ∃ n : nat, x < NRNRtoR (nat_to_NonnegativeReals n) 0%NR.
Proof.
  exact hr_archimedean.
Qed.

Lemma notRlt_Rle :
  ∀ x y : Reals, ¬ (x < y) <-> (y <= x).
Proof.
  exact hr_notlt_le.
Qed.
Lemma Rlt_Rle :
  ∀ x y : Reals, x < y -> x <= y.
Proof.
  intros x y H.
  apply notRlt_Rle.
  intros H0.
  refine (isirrefl_Rlt _ _).
  refine (istrans_Rlt _ _ _ _ _).
  exact H.
  exact H0.
Qed.
Lemma isantisymm_Rle :
  ∀ x y : Reals, x <= y -> y <= x -> x = y.
Proof.
  exact isantisymm_hr_le.
Qed.
Lemma istrans_Rle :
  ∀ x y z : Reals, x <= y -> y <= z -> x <= z.
Proof.
  intros x y z Hxy Hyz.
  apply notRlt_Rle ; intro H.
  generalize (iscotrans_Rlt _ y _ H).
  apply hinhuniv'.
  exact isapropempty.
  intros [ | ].
  apply_pr2 notRlt_Rle.
  exact Hyz.
  apply_pr2 notRlt_Rle.
  exact Hxy.
Qed.
Lemma istrans_Rle_lt :
  ∀ x y z : Reals, x <= y -> y < z -> x < z.
Proof.
  intros x y z Hxy Hyz.
  generalize (iscotrans_Rlt _ x _ Hyz).
  apply hinhuniv.
  intros [ H | H ].
  apply fromempty.
  revert H.
  apply_pr2 notRlt_Rle.
  exact Hxy.
  exact H.
Qed.
Lemma istrans_Rlt_le :
  ∀ x y z : Reals, x < y -> y <= z -> x < z.
Proof.
  intros x y z Hxy Hyz.
  generalize (iscotrans_Rlt _ z _ Hxy).
  apply hinhuniv.
  intros [ H | H ].
  exact H.
  apply fromempty.
  revert H.
  apply_pr2 notRlt_Rle.
  exact Hyz.
Qed.

Lemma Rplus_lecompat_l:
  ∀ x y z : Reals, y <= z <-> (y + x) <= (z + x).
Proof.
  exact hr_plus_lecompat_l.
Qed.
Lemma Rplus_lecompat_r:
  ∀ x y z : Reals, y <= z <-> (x + y) <= (x + z).
Proof.
  exact hr_plus_lecompat_r.
Qed.
Lemma Rmult_lecompat_l:
  ∀ x y z : Reals,
    0 <= x -> y <= z -> (y * x) <= (z * x).
Proof.
  exact hr_mult_lecompat_l.
Qed.
Lemma Rmult_lecompat_l':
  ∀ x y z : Reals,
    0 < x -> (y * x) <= (z * x) -> y <= z.
Proof.
  exact hr_mult_lecompat_l'.
Qed.
Lemma Rmult_lecompat_r:
  ∀ x y z : Reals,
    0 <= x -> y <= z -> (x * y) <= (x * z).
Proof.
  exact hr_mult_lecompat_r.
Qed.
Lemma Rmult_lecompat_r':
  ∀ x y z : Reals,
    0 < x -> (x * y) <= (x * z) -> y <= z.
Proof.
  exact hr_mult_lecompat_r'.
Qed.

Lemma Rap_Rlt:
  ∀ x y : Reals, x ≠ y <-> (x < y) ⨿ (y < x).
Proof.
  exact hr_ap_lt.
Qed.

Lemma isnonzeroReals : (1 ≠ 0).
Proof.
  exact isnonzeroCF.
Qed.

Lemma isirrefl_Rap :
  ∀ x : Reals, ¬ (x ≠ x).
Proof.
  exact isirrefl_CFap.
Qed.
Lemma issymm_Rap :
  ∀ (x y : Reals), (x ≠ y) -> (y ≠ x).
Proof.
  exact issymm_CFap.
Qed.
Lemma iscotrans_Rap :
  ∀ (x y z : Reals), (x ≠ z) -> (x ≠ y) ∨ (y ≠ z).
Proof.
  exact iscotrans_CFap.
Qed.
Lemma istight_Rap :
  ∀ (x y : Reals), ¬ (x ≠ y) -> x = y.
Proof.
  exact istight_CFap.
Qed.

Lemma apRplus :
  ∀ (x x' y y' : Reals),
    (x + y ≠ x' + y') -> (x ≠ x') ∨ (y ≠ y').
Proof.
  exact apCFplus.
Qed.
Lemma Rplus_apcompat_l :
  ∀ x y z : Reals,
    y + x ≠ z + x <-> y ≠ z.
Proof.
  exact CFplus_apcompat_l.
Qed.
Lemma Rplus_apcompat_r :
  ∀ x y z : Reals,
    x + y ≠ x + z <-> y ≠ z.
Proof.
  exact CFplus_apcompat_r.
Qed.

Lemma apRmult:
  ∀ (x x' y y' : Reals),
  (x * y ≠ x' * y') -> (x ≠ x') ∨ (y ≠ y').
Proof.
  apply apCFmult.
Qed.
Lemma Rmult_apcompat_l:
  ∀ (x y z : Reals), (y * x ≠ z * x) -> (y ≠ z).
Proof.
  exact CFmult_apcompat_l.
Qed.
Lemma Rmult_apcompat_l':
  ∀ (x y z : Reals),
    (x ≠ 0) -> (y ≠ z) -> (y * x ≠ z * x).
Proof.
  exact CFmult_apcompat_l'.
Qed.
Lemma Rmult_apcompat_r:
  ∀ (x y z : Reals), (x * y ≠ x * z) -> (y ≠ z).
Proof.
  exact CFmult_apcompat_r.
Qed.
Lemma Rmult_apcompat_r':
  ∀ (x y z : Reals),
    (x ≠ 0) -> (y ≠ z) -> (x * y ≠ x * z).
Proof.
  exact CFmult_apcompat_r'.
Qed.
Lemma RmultapRzero:
  ∀ (x y : Reals),
    (x * y ≠ 0) -> (x ≠ 0) ∧ (y ≠ 0).
Proof.
  exact CFmultapCFzero.
Qed.

(** ** Algrebra *)

Lemma islunit_Rzero_Rplus :
  forall x : Reals, 0 + x = x.
Proof.
  exact islunit_CFzero_CFplus.
Qed.
Lemma isrunit_Rzero_Rplus :
  ∀ x : Reals, x + 0 = x.
Proof.
  exact isrunit_CFzero_CFplus.
Qed.
Lemma isassoc_Rplus :
  ∀ x y z : Reals, x + y + z = x + (y + z).
Proof.
  exact isassoc_CFplus.
Qed.
Lemma islinv_Ropp :
  ∀ x : Reals, - x + x = 0.
Proof.
  exact islinv_CFopp.
Qed.
Lemma isrinv_Ropp :
  ∀ x : Reals, x + - x = 0.
Proof.
  exact isrinv_CFopp.
Qed.

Lemma iscomm_Rplus :
  ∀ x y : Reals, x + y = y + x.
Proof.
  exact iscomm_CFplus.
Qed.
Lemma islunit_Rone_Rmult :
  ∀ x : Reals, 1 * x = x.
Proof.
  exact islunit_CFone_CFmult.
Qed.
Lemma isrunit_Rone_Rmult :
  ∀ x : Reals, x * 1 = x.
Proof.
  exact isrunit_CFone_CFmult.
Qed.
Lemma isassoc_Rmult :
  ∀ x y z : Reals, x * y * z = x * (y * z).
Proof.
  exact isassoc_CFmult.
Qed.
Lemma iscomm_Rmult :
  ∀ x y : Reals, x * y = y * x.
Proof.
  exact iscomm_CFmult.
Qed.
Lemma islinv_Rinv :
  ∀ (x : Reals) (Hx0 : x ≠ 0),
    (Rinv x Hx0) * x = 1.
Proof.
  exact islinv_CFinv.
Qed.
Lemma isrinv_Rinv :
  ∀ (x : Reals) (Hx0 : x ≠ 0),
    x * (Rinv x Hx0) = 1.
Proof.
  exact isrinv_CFinv.
Qed.
Lemma islabsorb_Rzero_Rmult :
  ∀ x : Reals, 0 * x = 0.
Proof.
  exact islabsorb_CFzero_CFmult.
Qed.
Lemma israbsorb_Rzero_Rmult :
  ∀ x : Reals, x * 0 = 0.
Proof.
  exact israbsorb_CFzero_CFmult.
Qed.
Lemma isldistr_Rplus_Rmult :
  ∀ x y z : Reals, z * (x + y) = z * x + z * y.
Proof.
  exact isldistr_CFplus_CFmult.
Qed.
Lemma isrdistr_Rplus_Rmult :
  ∀ x y z : Reals, (x + y) * z = x * z + y * z.
Proof.
  exact isrdistr_CFplus_CFmult.
Qed.

(** ** Rabs *)

Lemma istriangle_Rabs :
  ∀ x y : Reals, (Rabs (x + y)%R <= Rabs x + Rabs y)%NR.
Proof.
  intros x y.
  pattern x at 1 ;
    rewrite <- (NRNRtoR_RtoNRNR x) ;
    pattern y at 1 ;
    rewrite <- (NRNRtoR_RtoNRNR y).
  apply maxNonnegativeReals_le.
  - refine (istrans_leNonnegativeReals _ _ _ _ _).
    refine (RtoNRNR_le_pr1 _ _ _ _).
    rewrite <- NRNRtoR_plus.
    apply NRNRtoR_inside.
    apply plusNonnegativeReals_lecompat.
    now apply maxNonnegativeReals_le_l.
    now apply maxNonnegativeReals_le_l.
  - refine (istrans_leNonnegativeReals _ _ _ _ _).
    refine (RtoNRNR_le_pr2 _ _ _ _).
    rewrite <- NRNRtoR_plus.
    apply NRNRtoR_inside.
    apply plusNonnegativeReals_lecompat.
    now apply maxNonnegativeReals_le_r.
    now apply maxNonnegativeReals_le_r.
Qed.

Transparent Dcuts_le_rel.
(* todo :
- more theorems in NonnegativeReals.v
- change the definition oh hr_abs *)

Lemma Rabs_submult :
  ∀ x y : Reals, (Rabs (x * y)%R <= Rabs x * Rabs y)%NR.
Proof.
  intros x y.
  pattern x at 1 ;
    rewrite <- (NRNRtoR_RtoNRNR x) ;
    pattern y at 1 ;
    rewrite <- (NRNRtoR_RtoNRNR y).
  rewrite <- NRNRtoR_mult.
  change (Rabs x) with (maxNonnegativeReals (pr1 (RtoNRNR x)) (pr2 (RtoNRNR x))).
  change (Rabs y) with (maxNonnegativeReals (pr1 (RtoNRNR y)) (pr2 (RtoNRNR y))).
  set (Hx := NRNRtoR_inside (pr1 (RtoNRNR x)) (pr2 (RtoNRNR x))).
  set (Hy := NRNRtoR_inside (pr1 (RtoNRNR y)) (pr2 (RtoNRNR y))).
  clearbody Hx Hy ;
    rewrite NRNRtoR_RtoNRNR in Hx ;
    rewrite NRNRtoR_RtoNRNR in Hy.
  set (Hx1 := RtoNRNR_le_pr1 x).
  set (Hx2 := RtoNRNR_le_pr2 x).
  set (Hy1 := RtoNRNR_le_pr1 y).
  set (Hy2 := RtoNRNR_le_pr2 y).
  clearbody Hx1 Hx2 Hy1 Hy2 ;
    destruct (RtoNRNR x) as [x1 x2] ;
    destruct (RtoNRNR y) as [y1 y2].
  simpl pr1 in *|- * ; simpl pr2 in * |- *.
  assert (Hx' : pr1 x ((x1 - x2)%NR ,, (x2 - x1)%NR)).
  { revert Hx.
    apply (pr1 (pr2 (pr2 x))).
    apply hinhpr.
    exists 0%NR.
    simpl.
    rewrite (rigcomm1 NonnegativeReals x1).
    rewrite <- !maxNonnegativeReals_minus_plus, iscomm_maxNonnegativeReals.
    reflexivity. }
  assert (Hy' : pr1 y ((y1 - y2)%NR ,, (y2 - y1)%NR)).
  { revert Hy.
    apply (pr1 (pr2 (pr2 y))).
    apply hinhpr.
    exists 0%NR.
    simpl.
    rewrite (rigcomm1 NonnegativeReals y1).
    rewrite <- !maxNonnegativeReals_minus_plus, iscomm_maxNonnegativeReals.
    reflexivity. }
  specialize (Hx1 _ _ Hx') ; specialize (Hx2 _ _ Hx') ;
  specialize (Hy1 _ _ Hy') ; specialize (Hy2 _ _ Hy').
  clear x y Hx Hy Hx' Hy'.
  apply maxNonnegativeReals_le.
  - refine (istrans_leNonnegativeReals _ _ _ _ _).
    refine (RtoNRNR_le_pr1 _ _ _ _).
    apply NRNRtoR_inside.
    rewrite isldistr_max_multNonnegativeReals, !isrdistr_max_multNonnegativeReals.
    refine (istrans_leNonnegativeReals _ _ _ _ _).
    2: apply maxNonnegativeReals_le.
    2: eapply istrans_leNonnegativeReals, maxNonnegativeReals_le_l.
    2: apply maxNonnegativeReals_le_l.
    2: eapply istrans_leNonnegativeReals, maxNonnegativeReals_le_r.
    2: apply maxNonnegativeReals_le_r.
    rewrite Dcuts_max_plus.
    apply isrefl_leNonnegativeReals.
    intros H.
    assert (H0 : x2 = 0%NR).
    { revert H.
      apply hinhuniv'.
      exact (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _).
      intros (r,(_)).
      apply hinhuniv'.
      exact (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _).
      intros ((r1,r2)) ; simpl fst ; simpl snd ; intros (->,(Xr1,Yr1)) ; clear Yr1 r2.
      specialize (Hx1 _ Xr1).
      apply le0_NonnegativeReals.
      eapply istrans_leNonnegativeReals.
      apply Hx2.
      intros r.
      apply hinhuniv.
      intros (r2,(Xr2,_)).
      specialize (Hx2 _ Xr2).
      apply fromempty.
      apply (isirrefl_ltNonnegativeReals x1).
      apply istrans_ltNonnegativeReals with x2 ;
        apply_pr2 ispositive_minusNonnegativeReals ;
        apply hinhpr.
      exists r2.
      split.
      apply Dcuts_zero_empty.
      exact Hx2.
      exists r1.
      split.
      apply Dcuts_zero_empty.
      exact Hx1. }
    rewrite H0.
    now apply islabsorb_zero_multNonnegativeReals.
  - refine (istrans_leNonnegativeReals _ _ _ _ _).
    refine (RtoNRNR_le_pr2 _ _ _ _).
    apply NRNRtoR_inside.
    rewrite isldistr_max_multNonnegativeReals, !isrdistr_max_multNonnegativeReals.
    refine (istrans_leNonnegativeReals _ _ _ _ _).
    2: apply maxNonnegativeReals_le.
    2: eapply istrans_leNonnegativeReals, maxNonnegativeReals_le_r.
    2: apply maxNonnegativeReals_le_l.
    2: eapply istrans_leNonnegativeReals, maxNonnegativeReals_le_l.
    2: apply maxNonnegativeReals_le_r.
    rewrite Dcuts_max_plus.
    apply isrefl_leNonnegativeReals.
    intros H.
    assert (H0 : x2 = 0%NR).
    { revert H.
      apply hinhuniv'.
      exact (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _).
      intros (r,(_)).
      apply hinhuniv'.
      exact (pr2 (pr1 (pr1 (pr1 NonnegativeReals))) _ _).
      intros ((r1,r2)) ; simpl fst ; simpl snd ; intros (->,(Xr1,Yr1)) ; clear Yr1 r2.
      specialize (Hx1 _ Xr1).
      apply le0_NonnegativeReals.
      eapply istrans_leNonnegativeReals.
      apply Hx2.
      intros r.
      apply hinhuniv.
      intros (r2,(Xr2,_)).
      specialize (Hx2 _ Xr2).
      apply fromempty.
      apply (isirrefl_ltNonnegativeReals x1).
      apply istrans_ltNonnegativeReals with x2 ;
        apply_pr2 ispositive_minusNonnegativeReals ;
        apply hinhpr.
      exists r2.
      split.
      apply Dcuts_zero_empty.
      exact Hx2.
      exists r1.
      split.
      apply Dcuts_zero_empty.
      exact Hx1. }
    rewrite H0.
    now apply islabsorb_zero_multNonnegativeReals.
Qed.
