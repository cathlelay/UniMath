(** * Results about Normed Spaces *)
(** Author: Catherine LELAY. Jan 2016 - *)

Require Import UniMath.Foundations.Algebra.Apartness.
Require Export UniMath.Foundations.Algebra.Rigs_and_Rings.
Require Export UniMath.Topology.Filters.
Require Import UniMath.Analysis.MetricSpace.
Require Import UniMath.RealNumbers.Sets.

(** ** Nonnegative Rig *)

Definition isNonnegativeRig {X : rig} (is : islattice X) (lt : StrongOrder X) :=
  (ex_minus (X := rigaddabmonoid X) is)
    × islatticelt (_ ,, is) lt
    × isbinophrel (X := rigaddabmonoid X) lt
    × isinvbinophrel (X := rigaddabmonoid X) lt
    × isrigmultgt X (λ x y, lt y x)
    × (Π x : X, Lle (L := _,,is) 0%rig x)
    × (lt 0%rig 1%rig)
    × (Π x : X,
         Σ y : X,
         Lle (L := _,,is) (y + y)%rig x
             × (lt 0%rig x → lt 0%rig y)).

Definition NonnegativeRig :=
  Σ (X : rig) (is : islattice X) (lt : StrongOrder X), isNonnegativeRig is lt.

Definition pr1NonnegativeRig : NonnegativeRig -> rig := pr1.
Coercion pr1NonnegativeRig : NonnegativeRig >-> rig.

Definition NonnegativeRig_to_NonnegativeAddMonoid : NonnegativeRig -> NonnegativeMonoid.
Proof.
  intros X.
  exists (rigaddabmonoid (pr1 X)).
  exists (pr1 (pr2 X)).
  exists (pr1 (pr2 (pr2 X))).
  split.
  apply (pr1 (pr2 (pr2 (pr2 X)))).
  split.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
  split.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
  split.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
  split.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))))).
  split.
  apply hinhpr.
  exists (1%rig : X).
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))))).
  apply (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))))).
Defined.

Definition NnRap (X : NonnegativeRig) : tightap X :=
  NnMap (NonnegativeRig_to_NonnegativeAddMonoid X).
Definition NnRle (X : NonnegativeRig) : PartialOrder X :=
  NnMle (NonnegativeRig_to_NonnegativeAddMonoid X).
Definition NnRlt (X : NonnegativeRig) : StrongOrder X :=
  NnMlt (NonnegativeRig_to_NonnegativeAddMonoid X).
Definition NnRminus {X : NonnegativeRig} : binop X :=
  NnMminus (X := NonnegativeRig_to_NonnegativeAddMonoid X).
Definition NnRmin {X : NonnegativeRig} : binop X :=
  NnMmin (X := NonnegativeRig_to_NonnegativeAddMonoid X).
Definition NnRmax {X : NonnegativeRig} : binop X :=
  NnMmax (X := NonnegativeRig_to_NonnegativeAddMonoid X).
Definition NnRhalf {X : NonnegativeRig} : unop X :=
  NnMhalf (X := NonnegativeRig_to_NonnegativeAddMonoid X).

Local Notation "0" := (0%rig).
Local Notation "1" := (1%rig).
Local Notation "x + y" := ((x + y)%rig).
Local Notation "x - y" := (NnRminus x y).
Local Notation "x * y" := ((x * y)%rig).
Local Notation "x ≠ y" := (NnRap _ x y).
Local Notation "x <= y" :=  (NnRle _ x y).
Local Notation "x < y" :=  (NnRlt _ x y).

Section NonnegativeRig_pty.

Context {X : NonnegativeRig}.

Lemma isirrefl_NnRap : isirrefl (NnRap X).
Proof.
  exact (pr1 (pr1 (pr2 (NnRap X)))).
Qed.

Lemma istight_NnRap : istight (NnRap X).
Proof.
  exact (pr2 (pr2 (NnRap X))).
Qed.
Lemma istotal_NnRlt :
  Π x y : X, x ≠ y <-> (x < y) ⨿ (y < x).
Proof.
  intros x y.
  apply (istotal_NnMlt (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.

Lemma isrefl_NnRle :
  Π x : X, x <= x.
Proof.
  intros x.
  apply (isrefl_Lle (L := _,,(pr1 (pr2 X)))).
Qed.

Lemma isirrefl_NnRlt :
  Π x : X, ¬ (x < x).
Proof.
  intros x.
  apply (isirrefl_NnMlt (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.

Lemma istrans_NnRlt :
  Π x y z : X, x < y -> y < z -> x < z.
Proof.
  apply istrans_StrongOrder.
Qed.
Lemma iscotrans_NnRlt :
  Π x y z : X, x < z -> x < y ∨ y < z.
Proof.
  apply iscotrans_StrongOrder.
Qed.
Lemma istrans_NnRle :
  Π x y z : X, x <= y -> y <= z -> x <= z.
Proof.
  exact (pr1 (pr1 (pr2 (NnRle _)))).
Qed.
Lemma istrans_NnRle_lt :
  Π x y z : X, x <= y -> y < z -> x < z.
Proof.
  intros x y z.
  apply (istrans_NnMle_lt (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma istrans_NnRlt_le :
  Π x y z : X, x < y -> y <= z -> x < z.
Proof.
  intros x y z.
  apply (istrans_NnMlt_le (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.

Lemma notNnRlt_le :
  Π x y : X, (¬ (x < y)) <-> (y <= x).
Proof.
  intros x y.
  apply (notNnMlt_le (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma NnRlt_le :
  Π x y : X, x < y -> x <= y.
Proof.
  intros x y H.
  apply notNnRlt_le.
  intros H0.
  eapply isirrefl_NnRlt.
  eapply istrans_NnRlt.
  exact H.
  exact H0.
Qed.

Lemma isnonnegative_NnR :
  Π x : X, 0 <= x.
Proof.
  intros x.
  apply (isnonnegative_NnM (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma isnonnegative_NnR' :
  Π x : X, ¬ (x < 0).
Proof.
  intros x.
  apply (pr2 (notNnRlt_le _ _)).
  now apply isnonnegative_NnR.
Qed.

Lemma NnRplus_lt_l :
  Π k x y : X, x < y -> k + x < k + y.
Proof.
  intros k x y.
  apply (pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.
Lemma NnRplus_lt_r :
  Π k x y : X, x < y -> x + k < y + k.
Proof.
  intros k x y.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.

Lemma NnRplus_le_l :
  Π k x y : X, k + x <= k + y -> x <= y.
Proof.
  intros k x y Hle.
  apply notNnRlt_le.
  intro Hlt.
  apply (pr2 (notNnRlt_le _ _)) in Hle.
  apply Hle.
  now apply NnRplus_lt_l.
Qed.
Lemma NnRplus_le_r :
  Π k x y : X, x + k <= y + k -> x <= y.
Proof.
  intros k x y Hle.
  apply notNnRlt_le.
  intro Hlt.
  apply (pr2 (notNnRlt_le _ _)) in Hle.
  apply Hle.
  now apply NnRplus_lt_r.
Qed.

Lemma NnRmult_lt :
  Π a b c d : X,
    a < b -> c < d -> ((a * d) + (b * c)) < ((a * c) + (b * d)).
Proof.
  intros a b c d.
  rewrite !(rigcomm1 X (a * _)%rig) .
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))).
Qed.
Lemma NnRmult_lt_0 :
  Π x y : X, 0 < x -> 0 < y -> 0 < x * y.
Proof.
  intros x y Hx Hy.
  generalize (NnRmult_lt _ _ _ _ Hx Hy).
  now rewrite !rigmult0x, rigmultx0, !riglunax1.
Qed.
Lemma NnRmult_lt_l :
  Π k x y : X, 0 < k -> x < y -> k * x < k * y.
Proof.
  intros k x y Hk H.
  generalize (NnRmult_lt _ _ _ _ Hk H).
  now rewrite !rigmult0x, !riglunax1.
Qed.
Lemma NnRmult_lt_r :
  Π k x y : X, 0 < k -> x < y -> x * k < y * k.
Proof.
  intros k x y Hk H.
  generalize (NnRmult_lt _ _ _ _ H Hk).
  now rewrite !rigmultx0, rigrunax1, riglunax1.
Qed.

Lemma NnRmult_le_l :
  Π k x y : X, 0 < k -> k * x <= k * y -> x <= y.
Proof.
  intros k x y Hk Hle.
  apply notNnRlt_le.
  intro Hlt.
  apply (pr2 (notNnRlt_le _ _)) in Hle.
  apply Hle.
  now apply NnRmult_lt_l.
Qed.
Lemma NnRmult_le_r :
  Π k x y : X, 0 < k -> x * k <= y * k -> x <= y.
Proof.
  intros k x y Hk Hle.
  apply notNnRlt_le.
  intro Hlt.
  apply (pr2 (notNnRlt_le _ _)) in Hle.
  apply Hle.
  now apply NnRmult_lt_r.
Qed.

Lemma NnRap_lt_0 :
  Π x : X, x ≠ 0 -> 0 < x.
Proof.
  intros x Hx.
  apply istotal_NnRlt in Hx.
  destruct Hx as [Hx | Hx].
  apply fromempty.
  revert Hx.
  now apply isnonnegative_NnR'.
  exact Hx.
Qed.
Lemma NnRlt_ap :
  Π x y : X, x < y -> x ≠ y.
Proof.
  intros x y H.
  apply (pr2 (istotal_NnRlt _ _)).
  now left.
Qed.

Lemma isantisymm_NnRle :
  Π x y : X, x <= y -> y <= x -> x = y.
Proof.
  intros x y Hge Hle.
  apply istight_NnRap.
  intros Hap.
  apply istotal_NnRlt in Hap.
  destruct Hap as [Hlt | Hlt].
  revert Hlt.
  apply (pr2 (notNnRlt_le _ _)), Hle.
  revert Hlt.
  apply (pr2 (notNnRlt_le _ _)), Hge.
Qed.

Lemma NnR_nottrivial :
  (0 : X) < 1.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))))).
Qed.

Lemma NnRmin_le_l :
  Π (x y : X), (NnRmin x y) <= x.
Proof.
  apply (NnMmin_le_l (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma NnRmin_le_r :
  Π (x y : X), (NnRmin x y) <= y.
Proof.
  apply (NnMmin_le_r (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma NnRmin_gt:
  Π (x y z : X),
    z < x → z < y → z < (NnRmin x y).
Proof.
  apply (NnMmin_gt (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma NnRmax_le_l :
  Π (x y : X), x <= (NnRmax x y).
Proof.
  apply (NnMmax_le_l (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma NnRmax_le_r :
  Π (x y : X), y <= (NnRmax x y).
Proof.
  apply (NnMmax_le_r (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma NnRmax_gt:
  Π (x y z : X),
    x < z → y < z → (NnRmax x y) < z.
Proof.
  apply (NnMmax_gt (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma iscomm_NnRmin :
  iscomm (NnRmin (X := X)).
Proof.
  apply (iscomm_NnMmin (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma isassoc_NnRmin :
  isassoc (NnRmin (X := X)).
Proof.
  apply (isassoc_NnMmin (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma NnRmin_eq_l:
  Π (x y : X), x <= y → NnRmin x y = x.
Proof.
  apply (NnMmin_eq_l (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma NnMmin_eq_r:
  Π (x y : X), y <= x → NnRmin x y = y.
Proof.
  apply (NnMmin_eq_r (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.

Lemma iscomm_NnRmax :
  iscomm (NnRmax (X := X)).
Proof.
  apply (iscomm_NnMmax (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma isassoc_NnRmax :
  isassoc (NnRmax (X := X)).
Proof.
  apply (isassoc_NnMmax (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma NnRmax_eq_l:
  Π (x y : X), y <= x → NnRmax x y = x.
Proof.
  apply (NnMmax_eq_l (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma NnMmax_eq_r:
  Π (x y : X), x <= y → NnRmax x y = y.
Proof.
  apply (NnMmax_eq_r (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.

Lemma NnRminus_lt_pos:
  Π (x y : X),
    y < x → 0%rig < (NnRminus x y).
Proof.
  apply (NnMminus_lt_pos (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma NnRminus_plus:
  Π (x y : X),
  (NnRminus x y + y)%rig = NnRmax x y.
Proof.
  apply (NnMminus_plus (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.

Lemma NnRhalf_carac:
  Π (x : X),
    (NnRhalf x + NnRhalf x)%rig <= x.
Proof.
  apply (NnMhalf_carac (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.
Lemma NnRhalf_pos:
  Π (x : X),
    0 < x → 0 < (NnRhalf x).
Proof.
  apply (NnMhalf_pos (X := NonnegativeRig_to_NonnegativeAddMonoid X)).
Qed.

End NonnegativeRig_pty.

(** ** Definition of module *)

Definition ismodule (K : rng) (X : abgr) (ap : tightap X) (scal : K -> X -> X) :=
  (isbinophrel ap)
  × (Π (a : K) (x y : X), scal a (x + y)%addmonoid = (scal a x + scal a y)%addmonoid)
  × (Π (a b : K) (x : X), scal (a + b) x = (scal a x + scal b x)%addmonoid)
  × (Π (a b : K) (x : X), scal (a * b) x = scal a (scal b x))
  × (Π x : X, scal (- (1))%rng x = grinv _ x).
Definition module (K : rng) :=
  Σ (X : abgr) (ap : tightap X) (scal : K -> X -> X), ismodule K X ap scal.
Definition pr1module (K : rng) : (module K) -> abgr := pr1.
Coercion pr1module : module >-> abgr.


Section Module_pty.

Context {K : rng} {X : module K}.

Definition Map : tightap X :=
  pr1 (pr2 X).
Definition scal : K -> X -> X :=
  pr1 (pr2 (pr2 X)).

Lemma Mplus_ap_l :
  Π k x y : X, Map x y -> Map (k + x)%addmonoid (k + y)%addmonoid.
Proof.
  intros k x y.
  apply (pr1 (pr1 (pr2 (pr2 (pr2 X))))).
Qed.
Lemma Mplus_ap_r :
  Π k x y : X, Map x y -> Map (x + k)%addmonoid (y + k)%addmonoid.
Proof.
  intros k x y.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 X))))).
Qed.

Lemma isldistr_scal :
  Π (a : K) (x y : X), scal a (x + y)%addmonoid = (scal a x + scal a y)%addmonoid.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
Qed.
Lemma isrdistr_scal :
  Π (a b : K) (x : X), scal (a + b) x = (scal a x + scal b x)%addmonoid.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
Qed.

Lemma isassoc_scal :
  Π (a b : K) (x : X), scal (a * b) x = scal a (scal b x).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.

Lemma scal_m1 :
  Π x : X, scal (- (1))%rng x = grinv _ x.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.

Lemma islunit_scal_1 :
  Π x : X, scal 1%rng x = x.
Proof.
  intros x.
  rewrite <- (rnglunax2 _ 1%rng).
  rewrite <- rngmultminusminus.
  rewrite isassoc_scal.
  rewrite !scal_m1.
  apply grinvinv.
Qed.

Lemma islabsorb_scal_0 :
  Π x : X, scal 0%rng x = 0%addmonoid.
Proof.
  intros x.
  rewrite <- (rnglinvax1 _ 1%rng).
  rewrite isrdistr_scal.
  rewrite scal_m1, islunit_scal_1.
  apply grlinvax.
Qed.
Lemma israbsorb_scal_0 :
  Π k : K, scal k 0%addmonoid = 0%addmonoid.
Proof.
  intros k.
  pattern (0%addmonoid : X) at 1.
  rewrite <- (grlinvax _ 0%addmonoid).
  rewrite <- scal_m1.
  rewrite isldistr_scal.
  rewrite <- isassoc_scal.
  rewrite rngrmultminus.
  rewrite rngrunax2.
  pattern k at 1.
  rewrite <- (rnglunax2 _ k).
  rewrite <- rnglmultminus.
  rewrite isassoc_scal.
  rewrite scal_m1.
  apply grlinvax.
Qed.

End Module_pty.

(** ** Ring with absolute value *)

Definition isabsrng (NR : NonnegativeRig) (K : rng) (ap : tightap K) (abs : K -> NR) :=
  (isbinophrel (X := rngaddabgr K) ap)
  × (Π x : K, ap x 0%rng <-> 0 < abs x)
  × (abs (- (1))%rng = 1)
  × (Π (x y : K), abs (x + y)%rng <= abs x + abs y)
  × (Π (x y : K), abs (x * y)%rng <= abs x * abs y).
Definition absrng (NR : NonnegativeRig) :=
  Σ (K : rng) (ap : tightap K) (abs : K -> NR), isabsrng NR K ap abs.

Definition absrngtorng {NR : NonnegativeRig} (K : absrng NR) : rng := (pr1 K).
Coercion absrngtorng : absrng >-> rng.

Section absrng_pty.

Context {NR : NonnegativeRig} {K : absrng NR}.

Definition absrng_ap : tightap K := (pr1 (pr2 K)).
Definition abs : K -> NR := (pr1 (pr2 (pr2 K))).

Lemma issepp_abs :
  Π x : K, absrng_ap x 0%rng <-> 0 < abs x.
Proof.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 K))))).
Qed.
Lemma abs_0 :
  abs 0%rng = 0.
Proof.
  apply istight_NnRap.
  intro H.
  apply NnRap_lt_0 in H.
  apply (pr2 (issepp_abs _)) in H.
  revert H.
  apply (isirrefltightapSet (X := (pr1 (pr1 (pr1 K))) ,, absrng_ap)).
Qed.
Lemma abs_m1 :
  abs (-(1))%rng = 1.
Proof.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 K)))))).
Qed.
Lemma istriangle_abs :
  Π (x y : K), abs (x + y)%rng <= abs x + abs y.
Proof.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 K))))))).
Qed.
Lemma issubmult_abs :
  Π (x y : K), abs (x * y)%rng <= abs x * abs y.
Proof.
  apply (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 K))))))).
Qed.

Lemma abs_1 :
  abs 1%rng = 1.
Proof.
  apply isantisymm_NnRle.
  - rewrite <- (rngrunax2 K 1%rng).
    rewrite <- rngmultminusminus.
    eapply istrans_NnRle.
    apply issubmult_abs.
    rewrite abs_m1.
    rewrite rigrunax2.
    apply isrefl_NnRle.
  - apply NnRmult_le_l with (abs (- (1))%rng).
    rewrite abs_m1.
    apply NnR_nottrivial.
    eapply istrans_NnRle, issubmult_abs.
    rewrite (rngrunax2 K), rigrunax2.
    apply isrefl_NnRle.
Qed.

End absrng_pty.

(** ** Definition of normed module *)

Section NormedModule.

Context {NR : NonnegativeRig}.
Context {K : absrng NR}.
Context {X : module K}.
Context (norm : X -> NR).

Definition issepp_isnorm : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (Π x : X, (Map x 0%addmonoid) <-> (0 < norm x)).
  apply impred_isaprop ; intros x.
  apply isapropdirprod.
  apply isapropimpl.
  apply propproperty.
  apply isapropimpl.
  apply propproperty.
Defined.

Definition istriangle_isnorm : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (Π x y : X, (norm (x + y)%addmonoid) <= (norm x + norm y)).
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply propproperty.
Defined.

Definition issubmult_isnorm : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (Π (k : K) (x : X), norm (scal k x) <= (abs k * norm x)).
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply propproperty.
Defined.

End NormedModule.

Definition isnorm {NR : NonnegativeRig} {K : absrng NR} {X : module K} (norm : X -> NR) : hProp :=
  issepp_isnorm norm ∧ istriangle_isnorm norm ∧ issubmult_isnorm norm.

Definition NormedModule {NR : NonnegativeRig} (K : absrng NR) :=
  Σ (X : module K) (norm : X -> NR), isnorm norm.

Definition pr1NormedModule {NR : NonnegativeRig} (K : absrng NR) : NormedModule K -> module K := pr1.
Coercion pr1NormedModule : NormedModule >-> module.

Definition norm {NR : NonnegativeRig} {K : absrng NR} {X : NormedModule K} : (X -> NR) := pr1 (pr2 X).

Definition absrng_to_NormedModule {NR : NonnegativeRig} (K : absrng NR) : NormedModule K.
Proof.
  intros NR K.
  simple refine (tpair _ _ _).
  - simple refine (tpair _ _ _).
    apply rngaddabgr, (pr1 K).
    simple refine (tpair _ _ _).
    apply absrng_ap.
    simple refine (tpair _ _ _).
    intros x y.
    apply (x * y)%rng.
    repeat split ; simpl.
    + exact (pr1 (pr1 (pr2 (pr2 (pr2 K))))).
    + exact (pr2 (pr1 (pr2 (pr2 (pr2 K))))).
    + intros a x y.
      now apply (rngldistr K).
    + intros a b x.
      now apply (rngrdistr K).
    + intros a b x.
      now apply (rngassoc2 K).
    + intros x.
      rewrite rnglmultminus, rnglunax2.
      reflexivity.
  - simple refine (tpair _ _ _).
    apply abs.
    repeat split.
    + exact (pr1 (issepp_abs x)).
    + exact (pr2 (issepp_abs x)).
    + exact istriangle_abs.
    + exact issubmult_abs.
Defined.

Section NormedModule_pty.

Context {NR : NonnegativeRig}
        {K : absrng NR}
        {X : NormedModule K}.

Lemma issepp_norm :
  Π x : X, (Map x 0%addmonoid) <-> (0 < norm x).
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 X))).
Qed.
Lemma istriangle_norm :
  Π x y : X, (norm (x + y)%addmonoid) <= (norm x + norm y).
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 (pr2 X)))).
Qed.
Lemma issubmult_norm :
  Π (k : K) (x : X), norm (scal k x) <= (abs k * norm x).
Proof.
  intros.
  now apply (pr2 (pr2 (pr2 (pr2 X)))).
Qed.

Lemma norm_grinv :
  Π x : X, norm (grinv X x) = norm x.
Proof.
  assert (Π x : X, norm (grinv X x) <= norm x).
  { intros x.
    rewrite <- scal_m1.
    eapply istrans_NnRle.
    apply issubmult_norm.
    rewrite abs_m1.
    rewrite riglunax2.
    apply isrefl_NnRle. }
  intros x.
  apply isantisymm_NnRle.
  now apply X0.
  pattern x at 1.
  rewrite <- (grinvinv _ x).
  now apply X0.
Qed.

Lemma grinvop :
  Π (x y : X), grinv X (x + y)%addmonoid = (grinv X y + grinv X x)%addmonoid.
Proof.
  intros.
  apply (pr2 (pr2 Map)).
  intro Hap.
  apply (Mplus_ap_l (x + y)%addmonoid) in Hap.
  revert Hap.
  rewrite grrinvax, assocax, <- (assocax _ y), grrinvax, lunax, grrinvax.
  apply (pr1 (pr1 (pr2 Map))).
Qed.

End NormedModule_pty.

(** ** Metric space on Normed Modules *)

Section dist_norm.

Context {NR : NonnegativeRig}
        {K : absrng NR}
        {X : NormedModule K}.

Definition metric_norm : MetricSet (NonnegativeRig_to_NonnegativeAddMonoid NR).
Proof.
  simple refine (tpair _ _ _).
  simple refine (tpair _ _ _).
  apply (pr1 (pr1 (pr1 (pr1 X)))).
  apply Map.
  simple refine (tpair _ _ _).
  intros x y.
  apply (norm (X := X)).
  apply (x + grinv X y)%addmonoid.
  repeat split.
  - intros x y.
    rewrite <- norm_grinv.
    rewrite (grinvop (X := X)).
    rewrite grinvinv.
    reflexivity.
  - intros Hap.
    simpl.
    apply issepp_norm.
    rewrite <- (grrinvax X y).
    apply Mplus_ap_r.
    apply Hap.
  - simpl.
    intro Hlt.
    rewrite <- (runax X x), <- (lunax X y).
    change (Map (x + unel X)%addmonoid (unel X + y)%addmonoid).
    pattern (unel X) at 1.
    rewrite <- (grlinvax X y).
    rewrite <- (assocax X).
    apply (Mplus_ap_r y).
    apply (pr2 (issepp_norm _)).
    apply Hlt.
  - intros x y z ; simpl.
    eapply istrans_NnRle, istriangle_norm.
    rewrite assocax, <- (assocax _ (grinv X y)).
    rewrite grlinvax, lunax.
    apply isrefl_NnRle.
Defined.

End dist_norm.

(** ** Limits in a Normed Module *)

Definition locally {NR : NonnegativeRig} {K : absrng NR} {X : NormedModule K} (x : X) : Filter X :=
  MSlocally (M := metric_norm) x.

(** *** Limit of a filter *)

Definition is_filter_lim {NR : NonnegativeRig} {K : absrng NR} {X : NormedModule K} (F : Filter X) (x : X) :=
  is_filter_MSlim (M := metric_norm) F x.
Definition ex_filter_lim {NR : NonnegativeRig} {K : absrng NR} {X : NormedModule K} (F : Filter X) :=
  ∃ (x : X), is_filter_lim F x.

(** *** Limit of a function *)

Definition is_lim {X : UU} {NR : NonnegativeRig} {K : absrng NR} {V : NormedModule K} (f : X -> V) (F : Filter X) (x : V) :=
  filterlim f F (locally x).
Definition ex_lim {X : UU} {NR : NonnegativeRig} {K : absrng NR} {V : NormedModule K} (f : X -> V) (F : Filter X) :=
  ∃ (x : V), is_lim f F x.

Lemma is_lim_aux {X : UU} {NR : NonnegativeRig} {K : absrng NR} {V : NormedModule K} (f : X → V) (F : Filter X) (x : V) :
  is_lim f F x <->
  (Π eps : NR, 0%rig < eps -> F (λ y : X, ball (M := metric_norm) x eps (f y))).
Proof.
  intros X NR K V f F x.
  split ; intros H.
  - apply (pr1 (is_MSlim_aux (M := metric_norm) f F x)).
    intros P Hp.
    apply H, Hp.
  - intros P Hp.
    apply (pr2 (is_MSlim_aux (M := metric_norm) f F x)).
    intros e.
    apply H.
    apply Hp.
Qed.

(** *** Continuity *)

Definition continuous_at {NR : NonnegativeRig} {K : absrng NR} {U V : NormedModule K} (f : U -> V) (x : U) :=
  is_lim f (locally x) (f x).
Definition continuous_on {NR : NonnegativeRig} {K : absrng NR} {U V : NormedModule K} (dom : U -> hProp) (f : U -> V) :=
  Π (x : U) (H : dom x) H,
    is_lim f (FilterDom (locally x) dom H) (f x).

Definition continuous_subtypes {NR : NonnegativeRig} {K : absrng NR} {U V : NormedModule K} (dom : U -> hProp) (f : (Σ x : U, dom x) -> V) :=
  Π (x : Σ x : U, dom x) H,
    is_lim f (FilterSubtype (locally (pr1 x)) dom H) (f x).
Definition continuous {NR : NonnegativeRig} {K : absrng NR} {U V : NormedModule K} (f : U -> V) :=
  Π x : U, continuous_at f x.

(** *** Continuity for 2 variable functions *)

Definition continuous2d_at {NR : NonnegativeRig} {K : absrng NR} {U V W : NormedModule K} (f : U -> V -> W) (x : U) (y : V) :=
  is_lim (λ z : U × V, f (pr1 z) (pr2 z)) (FilterDirprod (locally x) (locally y)) (f x y).
Definition continuous2d_on {NR : NonnegativeRig} {K : absrng NR} {U V W : NormedModule K} (f : U -> V -> W) (dom : U -> V -> hProp) :=
  Π x y Hz, is_lim (λ z : U × V, f (pr1 z) (pr2 z)) (FilterDom (FilterDirprod (locally x) (locally y)) (λ z : U × V, dom (pr1 z) (pr2 z)) Hz) (f x y).
Definition continuous2d {NR : NonnegativeRig} {K : absrng NR} {U V W : NormedModule K} (f : U -> V -> W) :=
  Π (x : U) (y : V), continuous2d_at f x y.

(** *** Lemmas of continuity *)

Lemma continuous_grinv {NR : NonnegativeRig} {K : absrng NR} {X : NormedModule K} :
  continuous (grinv X).
Proof.
  intros NR K X x.
  apply (pr2 (is_lim_aux _ _ _)).
  intros e He.
  eapply Filter_imply, MSlocally_ball, He.
  intros y Hy.
  apply ball_symm.
  eapply istrans_NnRle_lt, Hy.
  unfold dist ; simpl pr1.
  rewrite (grinvinv X).
  rewrite (commax X).
  apply isrefl_NnRle.
Qed.

Lemma continuous_plus {NR : NonnegativeRig} {K : absrng NR} {X : NormedModule K} :
  continuous2d (λ x y : X, (x + y)%addmonoid).
Proof.
  intros NR K X x y.
  apply (pr2 (is_lim_aux _ _ _)).
  intros e He.
  apply hinhpr.
  exists (ball (M := metric_norm) x (NnRhalf e)), (ball (M := metric_norm) y (NnRhalf e)).
  repeat split.
  apply MSlocally_ball, NnRhalf_pos, He.
  apply MSlocally_ball, NnRhalf_pos, He.
  intros x' y' ; unfold ball ; simpl.
  change (NnMlt (NonnegativeRig_to_NonnegativeAddMonoid NR)) with (NnRlt NR).
  intros Hx Hy.
  eapply istrans_NnRlt_le, NnRhalf_carac.
  eapply istrans_NnRlt, NnRplus_lt_r, Hx.
  eapply istrans_NnRle_lt, NnRplus_lt_l, Hy.
  unfold dist ; simpl pr1.
  eapply istrans_NnRle, istriangle_norm.
  rewrite !(assocax X).
  rewrite (commax X (grinv X x')), !(assocax X).
  rewrite (grinvop (X := X)).
  apply isrefl_NnRle.
Qed.
