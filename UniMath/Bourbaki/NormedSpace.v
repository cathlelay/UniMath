(** * Results about Normed Spaces *)
(** Author: Catherine LELAY. Jan 2016 - *)

Require Export UniMath.Foundations.Algebra.Rigs_and_Rings.
Require Export UniMath.Bourbaki.Filters.
Require Import UniMath.Bourbaki.MetricSpace.
Require Import UniMath.Dedekind.Sets.

(** ** Nonnegative Rig *)

Definition isNonnegativeRig {X : rig} (ap ge gt : hrel X) :=
  isConstructiveTotalEffectiveOrder ap ge gt
  × isbinophrel (X := rigaddabmonoid X) gt
  × isrigmultgt X gt
  × (∀ x : X, ge x 0%rig)
  × (gt 1%rig 0%rig)
  × (∀ x y : X, ∃ min : X, is_min ge gt x y min)
  × (∀ (x y : X) (Hxy : gt x y), ∃ minus : X, is_minus (X := rigaddabmonoid X) gt x y minus Hxy).

Definition NonnegativeRig :=
  Σ (X : rig) (ap gt ge : hrel X), isNonnegativeRig ap gt ge.

Definition pr1NonnegativeRig : NonnegativeRig -> rig := pr1.
Coercion pr1NonnegativeRig : NonnegativeRig >-> rig.

Definition NnRap (X : NonnegativeRig) : tightap X :=
  pr1 (pr2 X) ,, pr1 (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
Definition NnRge (X : NonnegativeRig) : PartialOrder X :=
  pr1 (pr2 (pr2 X)),,
      pr1 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X))))))),,
      pr1 (pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X))))))).
Definition NnRgt (X : NonnegativeRig) : StrongOrder X :=
  pr1 (pr2 (pr2 (pr2 X))) ,, pr1 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))).

Local Notation "0" := (0%rig).
Local Notation "1" := (1%rig).
Local Notation "x + y" := ((x + y)%rig).
Local Notation "x * y" := ((x * y)%rig).
Local Notation "x ≠ y" := (NnRap _ x y).
Local Notation "x >= y" :=  (NnRge _ x y).
Local Notation "x > y" :=  (NnRgt _ x y).

Definition NonnegativeRig_to_NonnegativeAddMonoid (X : NonnegativeRig) :
  NonnegativeMonoid.
Proof.
  intros X.
  simple refine (tpair _ _ _).
  - apply (abmonoidtomonoid (rigaddabmonoid X)).
  - exists (NnRap X), (NnRge X), (NnRgt X).
    split.
    apply (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
    split.
    apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
    repeat split.
    apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))).
    apply hinhpr.
    exists 1.
    apply (pr2  (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))).
    apply (pr1 (pr2 (pr2  (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))))).
    apply (pr2 (pr2 (pr2  (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))))).
Defined.

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
Lemma istotal_NnRgt :
  ∀ x y : X, x ≠ y <-> (x > y) ⨿ (y > x).
Proof.
  exact (pr2 (pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))).
Qed.

Lemma isrefl_NnRge :
  ∀ x : X, x >= x.
Proof.
  intros x.
  apply (pr2 (pr1 (pr2 (NnRge _)))).
Qed.

Lemma istrans_NnRgt :
  ∀ x y z : X, x > y -> y > z -> x > z.
Proof.
  apply istrans_StrongOrder.
Qed.
Lemma istrans_NnRge :
  ∀ x y z : X, x >= y -> y >= z -> x >= z.
Proof.
  exact (pr1 (pr1 (pr2 (NnRge _)))).
Qed.
Lemma istrans_NnRge_gt :
  ∀ x y z : X, x >= y -> y > z -> x > z.
Proof.
  apply (pr2 (pr2 (pr2 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))))))).
Qed.
Lemma istrans_NnRgt_ge :
  ∀ x y z : X, x > y -> y >= z -> x > z.
Proof.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))))))).
Qed.

Lemma NnRgt_ge :
  ∀ x y : X, x > y -> x >= y.
Proof.
  exact (pr1 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X)))))))))).
Qed.
Lemma notNnRgt_ge :
  ∀ x y : X, (¬ (x > y)) <-> (y >= x).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 X))))))))))).
Qed.

Lemma isnonnegative_NnR :
  ∀ x : X, x >= 0.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))).
Qed.
Lemma isnonnegative_NnR' :
  ∀ x : X, ¬ (0 > x).
Proof.
  intros x.
  apply (pr2 (notNnRgt_ge _ _)).
  now apply isnonnegative_NnR.
Qed.

Lemma NnRplus_gt_l :
  ∀ k x y : X, x > y -> k + x > k + y.
Proof.
  intros k x y.
  apply (pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.
Lemma NnRplus_gt_r :
  ∀ k x y : X, x > y -> x + k > y + k.
Proof.
  intros k x y.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.

Lemma NnRplus_ge_l :
  ∀ k x y : X, k + x >= k + y -> x >= y.
Proof.
  intros k x y Hge.
  apply notNnRgt_ge.
  intro Hgt.
  apply (pr2 (notNnRgt_ge _ _)) in Hge.
  apply Hge.
  now apply NnRplus_gt_l.
Qed.
Lemma NnRplus_ge_r :
  ∀ k x y : X, x + k >= y + k -> x >= y.
Proof.
  intros k x y Hge.
  apply notNnRgt_ge.
  intro Hgt.
  apply (pr2 (notNnRgt_ge _ _)) in Hge.
  apply Hge.
  now apply NnRplus_gt_r.
Qed.

Lemma NnRmult_gt :
  ∀ a b c d : X,
    a > b -> c > d -> ((a * c) + (b * d)) > ((a * d) + (b * c)).
Proof.
  intros x y Hx Hy.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.
Lemma NnRmult_gt_0 :
  ∀ x y : X, x > 0 -> y > 0 -> x * y > 0.
Proof.
  intros x y Hx Hy.
  generalize (NnRmult_gt _ _ _ _ Hx Hy).
  now rewrite !rigmult0x, rigmultx0, !rigrunax1.
Qed.
Lemma NnRmult_gt_l :
  ∀ k x y : X, k > 0 -> x > y -> k * x > k * y.
Proof.
  intros k x y Hk H.
  generalize (NnRmult_gt _ _ _ _ Hk H).
  now rewrite !rigmult0x, !rigrunax1.
Qed.
Lemma NnRmult_gt_r :
  ∀ k x y : X, k > 0 -> x > y -> x * k > y * k.
Proof.
  intros k x y Hk H.
  generalize (NnRmult_gt _ _ _ _ H Hk).
  now rewrite !rigmultx0, rigrunax1, riglunax1.
Qed.

Lemma NnRmult_ge_l :
  ∀ k x y : X, k > 0 -> k * x >= k * y -> x >= y.
Proof.
  intros k x y Hk Hge.
  apply notNnRgt_ge.
  intro Hgt.
  apply (pr2 (notNnRgt_ge _ _)) in Hge.
  apply Hge.
  now apply NnRmult_gt_l.
Qed.
Lemma NnRmult_ge_r :
  ∀ k x y : X, k > 0 -> x * k >= y * k -> x >= y.
Proof.
  intros k x y Hk Hge.
  apply notNnRgt_ge.
  intro Hgt.
  apply (pr2 (notNnRgt_ge _ _)) in Hge.
  apply Hge.
  now apply NnRmult_gt_r.
Qed.

Lemma NnRap_gt_0 :
  ∀ x : X, x ≠ 0 -> x > 0.
Proof.
  intros x Hx.
  apply istotal_NnRgt in Hx.
  destruct Hx as [Hx | Hx].
  exact Hx.
  apply fromempty.
  revert Hx.
  now apply isnonnegative_NnR'.
Qed.
Lemma NnRgt_ap :
  ∀ x y : X, x > y -> x ≠ y.
Proof.
  intros x y H.
  apply (pr2 (istotal_NnRgt _ _)).
  now left.
Qed.

Lemma isantisymm_NnRge :
  ∀ x y : X, x >= y -> y >= x -> x = y.
Proof.
  intros x y Hge Hle.
  apply istight_NnRap.
  intros Hap.
  apply istotal_NnRgt in Hap.
  destruct Hap as [Hgt | Hgt].
  revert Hgt.
  apply (pr2 (notNnRgt_ge _ _)), Hle.
  revert Hgt.
  apply (pr2 (notNnRgt_ge _ _)), Hge.
Qed.

Lemma NnR_nottrivial :
  1 > (0 : X).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))))).
Qed.

Lemma NnRmin_carac :
  ∀ x y : X, ∃ min : X,
    x >= min × y >= min × (∀ z : X, x > z -> y > z -> min > z).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))))).
Qed.

Lemma NnRminus_carac :
  ∀ (x y : X), x > y -> ∃ minus : X, minus > 0 × x = y + minus.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))))))).
Qed.

End NonnegativeRig_pty.

(** ** Definition of module *)

Definition ismodule (K : rng) (X : abgr) (ap : tightap X) (scal : K -> X -> X) :=
  (isbinophrel ap)
  × (∀ (a : K) (x y : X), scal a (x + y)%addmonoid = (scal a x + scal a y)%addmonoid)
  × (∀ (a b : K) (x : X), scal (a + b) x = (scal a x + scal b x)%addmonoid)
  × (∀ (a b : K) (x : X), scal (a * b) x = scal a (scal b x))
  × (∀ x : X, scal (- (1))%rng x = grinv _ x).
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
  ∀ k x y : X, Map x y -> Map (k + x)%addmonoid (k + y)%addmonoid.
Proof.
  intros k x y.
  apply (pr1 (pr1 (pr2 (pr2 (pr2 X))))).
Qed.
Lemma Mplus_ap_r :
  ∀ k x y : X, Map x y -> Map (x + k)%addmonoid (y + k)%addmonoid.
Proof.
  intros k x y.
  apply (pr2 (pr1 (pr2 (pr2 (pr2 X))))).
Qed.

Lemma isldistr_scal :
  ∀ (a : K) (x y : X), scal a (x + y)%addmonoid = (scal a x + scal a y)%addmonoid.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 X))))).
Qed.
Lemma isrdistr_scal :
  ∀ (a b : K) (x : X), scal (a + b) x = (scal a x + scal b x)%addmonoid.
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 X)))))).
Qed.

Lemma isassoc_scal :
  ∀ (a b : K) (x : X), scal (a * b) x = scal a (scal b x).
Proof.
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.

Lemma scal_m1 :
  ∀ x : X, scal (- (1))%rng x = grinv _ x.
Proof.
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 X))))))).
Qed.

Lemma islunit_scal_1 :
  ∀ x : X, scal 1%rng x = x.
Proof.
  intros x.
  rewrite <- (rnglunax2 _ 1%rng).
  rewrite <- rngmultminusminus.
  rewrite isassoc_scal.
  rewrite !scal_m1.
  apply grinvinv.
Qed.

Lemma islabsorb_scal_0 :
  ∀ x : X, scal 0%rng x = 0%addmonoid.
Proof.
  intros x.
  rewrite <- (rnglinvax1 _ 1%rng).
  rewrite isrdistr_scal.
  rewrite scal_m1, islunit_scal_1.
  apply grlinvax.
Qed.
Lemma israbsorb_scal_0 :
  ∀ k : K, scal k 0%addmonoid = 0%addmonoid.
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
  × (∀ x : K, ap x 0%rng <-> abs x > 0)
  × (abs (- (1))%rng = 1)
  × (∀ (x y : K), abs x + abs y >= abs (x + y)%rng)
  × (∀ (x y : K), abs x * abs y >= abs (x * y)%rng).
Definition absrng {NR : NonnegativeRig} :=
  Σ (K : rng) (ap : tightap K) (abs : K -> NR), isabsrng NR K ap abs.

Definition absrngtorng {NR : NonnegativeRig} (K : absrng (NR := NR)) : rng := (pr1 K).
Coercion absrngtorng : absrng >-> rng.

Section absrng_pty.

Context {NR : NonnegativeRig} {K : absrng (NR := NR)}.

Definition absrng_ap : tightap K := (pr1 (pr2 K)).
Definition abs : K -> NR := (pr1 (pr2 (pr2 K))).

Lemma issepp_abs :
  ∀ x : K, absrng_ap x 0%rng <-> abs x > 0.
Proof.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 K))))).
Qed.
Lemma abs_0 :
  abs 0%rng = 0.
Proof.
  apply istight_NnRap.
  intro H.
  apply NnRap_gt_0 in H.
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
  ∀ (x y : K), abs x + abs y >= abs (x + y)%rng.
Proof.
  apply (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 K))))))).
Qed.
Lemma issubmult_abs :
  ∀ (x y : K), abs x * abs y >= abs (x * y)%rng.
Proof.
  apply (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 K))))))).
Qed.

Lemma abs_1 :
  abs 1%rng = 1.
Proof.
  apply isantisymm_NnRge.
  - apply NnRmult_ge_l with (abs (- (1))%rng).
    rewrite abs_m1.
    apply NnR_nottrivial.
    eapply istrans_NnRge.
    apply issubmult_abs.
    rewrite (rngrunax2 K), rigrunax2.
    apply isrefl_NnRge.
  - rewrite <- (rngrunax2 K 1%rng).
    rewrite <- rngmultminusminus.
    eapply istrans_NnRge, issubmult_abs.
    rewrite abs_m1.
    rewrite rigrunax2.
    apply isrefl_NnRge.
Qed.

End absrng_pty.

(** ** Definition of normed module *)

Section NormedModule.

Context {NR : NonnegativeRig}.
Context {K : absrng (NR := NR)}.
Context {X : module K}.
Context (norm : X -> NR).

Definition issepp_isnorm : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ x : X, (Map x 0%addmonoid) <-> (norm x > 0)).
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
  apply (∀ x y : X, (norm x + norm y) >= (norm (x + y)%addmonoid)).
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply propproperty.
Defined.

Definition issubmult_isnorm : hProp.
Proof.
  simple refine (hProppair _ _).
  apply (∀ (k : K) (x : X), (abs k * norm x) >= norm (scal k x)).
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply propproperty.
Defined.

End NormedModule.

Definition isnorm {NR : NonnegativeRig} {K : absrng (NR := NR)} {X : module K} (norm : X -> NR) : hProp :=
  issepp_isnorm norm ∧ istriangle_isnorm norm ∧ issubmult_isnorm norm.

Definition NormedModule {NR : NonnegativeRig} (K : absrng (NR := NR)) :=
  Σ (X : module K) (norm : X -> NR), isnorm norm.

Definition pr1NormedModule {NR : NonnegativeRig} (K : absrng (NR := NR)) : NormedModule K -> module K := pr1.
Coercion pr1NormedModule : NormedModule >-> module.

Definition norm {NR : NonnegativeRig} {K : absrng (NR := NR)} {X : NormedModule K} : (X -> NR) := pr1 (pr2 X).

Definition absrng_to_NormedModule {NR : NonnegativeRig} (K : absrng (NR := NR)) : NormedModule K.
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
        {K : absrng (NR := NR)}
        {X : NormedModule K}.

Lemma issepp_norm :
  ∀ x : X, (Map x 0%addmonoid) <-> (norm x > 0).
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 X))).
Qed.
Lemma istriangle_norm :
  ∀ x y : X, (norm x + norm y) >= (norm (x + y)%addmonoid).
Proof.
  intros.
  now apply (pr1 (pr2 (pr2 (pr2 X)))).
Qed.
Lemma issubmult_norm :
  ∀ (k : K) (x : X), (abs k * norm x) >= norm (scal k x).
Proof.
  intros.
  now apply (pr2 (pr2 (pr2 (pr2 X)))).
Qed.

Lemma norm_grinv :
  ∀ x : X, norm (grinv X x) = norm x.
Proof.
  assert (∀ x : X, norm x >= norm (grinv X x)).
  { intros x.
    rewrite <- scal_m1.
    eapply istrans_NnRge.
    2: apply issubmult_norm.
    rewrite abs_m1.
    rewrite riglunax2.
    apply isrefl_NnRge. }
  intros x.
  apply isantisymm_NnRge.
  pattern x at 2.
  rewrite <- (grinvinv _ x).
  now apply X0.
  now apply X0.
Qed.

Lemma grinvop :
  ∀ (x y : X), grinv X (x + y)%addmonoid = (grinv X y + grinv X x)%addmonoid.
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
        {K : absrng (NR := NR)}
        {X : NormedModule K}.

Definition metric_norm : MetricSet (NR := NonnegativeRig_to_NonnegativeAddMonoid NR).
Proof.
  simple refine (tpair _ _ _).
  simple refine (tpair _ _ _).
  apply (pr1 (pr1 (pr1 (pr1 X)))).
  apply Map.
  simple refine (tpair _ _ _).
  intros x y.
  apply (norm (X := X) (x + grinv X y)%addmonoid).
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
    intro Hgt.
    rewrite <- (runax X x), <- (lunax X y).
    change (Map (x + unel X)%addmonoid (unel X + y)%addmonoid).
    pattern (unel X) at 1.
    rewrite <- (grlinvax X y).
    rewrite <- (assocax X).
    apply (Mplus_ap_r y).
    apply (pr2 (issepp_norm _)).
    apply Hgt.
  - intros x y z ; simpl.
    eapply istrans_NnRge.
    apply istriangle_norm.
    rewrite assocax, <- (assocax _ (grinv X y)).
    rewrite grlinvax, lunax.
    apply isrefl_NnRge.
Defined.

End dist_norm.

(** ** Limits in a Normed Module *)

Definition locally {NR : NonnegativeRig} {K : absrng (NR := NR)} {X : NormedModule K} (x : X) : Filter (X := X) :=
  locally (M := metric_norm) x.

(** *** Limit of a filter *)

Definition is_filter_lim {NR : NonnegativeRig} {K : absrng (NR := NR)} {X : NormedModule K} (F : Filter) (x : X) :=
  filter_le (locally x) F.
Definition ex_filter_lim {NR : NonnegativeRig} {K : absrng (NR := NR)} {X : NormedModule K} (F : Filter) :=
  ∃ (x : X), is_filter_lim F x.

(** *** Limit of a function *)

Definition is_lim {X : UU} {NR : NonnegativeRig} {K : absrng (NR := NR)} {V : NormedModule K} (f : X -> V) (F : Filter) (x : V) :=
  filterlim f F (locally x).
Definition ex_lim {X : UU} {NR : NonnegativeRig} {K : absrng (NR := NR)} {V : NormedModule K} (f : X -> V) (F : Filter) :=
  ∃ (x : V), is_lim f F x.

(** *** Continuity *)

Definition continuous_at {NR : NonnegativeRig} {K : absrng (NR := NR)} {U V : NormedModule K} (f : U -> V) (x : U) :=
  is_lim f (locally x) (f x).
Definition continuous_on {NR : NonnegativeRig} {K : absrng (NR := NR)} {U V : NormedModule K} (dom : U -> hProp) (f : U -> V) :=
  ∀ (x : U) (H : dom x) H,
    is_lim f (filter_dom (locally x) dom H) (f x).

Definition continuous_subtypes {NR : NonnegativeRig} {K : absrng (NR := NR)} {U V : NormedModule K} (dom : U -> hProp) (f : (Σ x : U, dom x) -> V) :=
  ∀ (x : Σ x : U, dom x) H,
    is_lim f (filter_subtypes (locally (pr1 x)) dom H) (f x).
Definition continuous {NR : NonnegativeRig} {K : absrng (NR := NR)} {U V : NormedModule K} (f : U -> V) :=
  ∀ x : U, continuous_at f x.

(** *** Continuity for 2 variable functions *)

Definition continuous2d_at {NR : NonnegativeRig} {K : absrng (NR := NR)} {U V W : NormedModule K} (f : U -> V -> W) (x : U) (y : V) :=
  is_lim (λ z : U × V, f (pr1 z) (pr2 z)) (filter_prod (locally x) (locally y)) (f x y).
Definition continuous2d_on {NR : NonnegativeRig} {K : absrng (NR := NR)} {U V W : NormedModule K} (f : U -> V -> W) (dom : U -> V -> hProp) :=
  ∀ x y Hz, is_lim (λ z : U × V, f (pr1 z) (pr2 z)) (filter_dom (filter_prod (locally x) (locally y)) (λ z : U × V, dom (pr1 z) (pr2 z)) Hz) (f x y).
Definition continuous2d {NR : NonnegativeRig} {K : absrng (NR := NR)} {U V W : NormedModule K} (f : U -> V -> W) :=
  ∀ (x : U) (y : V), continuous2d_at f x y.

(** *** Lemmas of continuity *)

Lemma continuous_grinv {NR : NonnegativeRig} {K : absrng (NR := NR)} {X : NormedModule K} :
  continuous (grinv X).
Proof.
  intros NR K X x P.
  apply hinhuniv.
  intros (O,(Ho,Op)).
  revert Ho.
  apply hinhfun.
  intros (eps,->).
  exists (ball (M := metric_norm) (grinv X x) (pr1 eps)).
  split.
  apply hinhpr.
  now exists eps.
  intros t Ht.
  rewrite <- (grinvinv X t).
  apply Op.
  apply ball_symm.
  unfold ball ; simpl.
  eapply istrans_NnRgt_ge.
  apply Ht.
  unfold dist ; simpl.
  rewrite (commax X).
  apply isrefl_NnRge.
Qed.

Lemma continuous_plus {NR : NonnegativeRig} {K : absrng (NR := NR)} {X : NormedModule K} :
  continuous2d (λ x y : X, (x + y)%addmonoid).
Proof.
  intros NR K X x y P.
  apply hinhuniv.
  intros (Ax,(Ay,(Hx,(Hy,Ha)))).
  revert Hx Hy.
  apply hinhuniv2.
  intros (Ox,(Hox,Hpx)) (Oy,(Hoy,Hpy)).
  revert Hox Hoy.
  apply hinhuniv2.
  intros (ex,->) (ey,->).
  generalize (NnRmin_carac (pr1 ex) (pr1 ey)).
  apply hinhfun ; intros (min,(Hex,(Hey,Hmin))).
  exists (ball (M := metric_norm) (x + y)%addmonoid min).
  split.
  apply hinhpr.
  simple refine (tpair _ _ _).
  simple refine (tpair _ _ _).
  apply min.
  apply Hmin.
  apply (pr2 ex).
  apply (pr2 ey).
  reflexivity.
  intros t Ht.
  rewrite <- (runax X t).
  rewrite <- (grlinvax X y).
  rewrite <- (assocax X).
  apply (Ha (t + grinv X y)%addmonoid y).
  apply Hpx.
  unfold ball ; simpl.
  eapply istrans_NnRge_gt.
  apply Hex.
  eapply istrans_NnRgt_ge.
  apply Ht.
  unfold dist ; simpl.
  rewrite (grinvop (X := X)), grinvinv.
  rewrite (assocax X).
  apply isrefl_NnRge.
  apply Hpy.
  apply ball_center.
  apply (pr2 ey).
Qed.