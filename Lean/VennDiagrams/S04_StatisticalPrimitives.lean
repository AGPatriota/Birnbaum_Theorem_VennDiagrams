import VennDiagrams.S03_LikelihoodProcedures
import Mathlib

/-!
# S04 — Finite statistical primitives

This module gives exact, finite definitions for the statistical objects used
in the manuscript: probability models and their effective supports, induced
models, ancillary statistics, unbiased estimators and UMVUE outputs,
likelihood-ratio p-values, posterior normalizers, confidence regions, and
componentwise products of procedures.

All probability masses are real numbers.  The extended likelihood ratio is
`ENNReal`-valued; consequently it has exactly the conventions used in the
paper: `0 / 0 = 0`, while `a / 0 = ⊤` when `a > 0`.
-/

open Set Finset
open scoped BigOperators ENNReal

namespace VennDiagrams

universe u v w

/-! ## Finite models, effective support, and inference bases -/

/-- A finite statistical model with exact real-valued probability masses.
Both the parameter and sample types are explicitly finite and nonempty. -/
structure FiniteModel (Theta : Type u) (X : Type v)
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X] where
  pmf : Theta → X → ℝ
  pmf_nonneg : ∀ theta x, 0 ≤ pmf theta x
  pmf_sum_one : ∀ theta, ∑ x, pmf theta x = 1

/-- On a finite sample space with measurable singletons, probability
measures are determined exactly by their real-valued singleton PMFs. -/
theorem finiteProbabilityMeasures_eq_iff_singletonPMF
    {X : Type v} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (mu nu : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure mu] [MeasureTheory.IsProbabilityMeasure nu] :
    mu = nu ↔ ∀ x, mu.real {x} = nu.real {x} :=
  MeasureTheory.ext_iff_measureReal_singleton

variable {Theta : Type u} {X : Type v} {Y : Type w}
variable [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]

/-- The actual sample space: observations having positive mass for at least
one parameter value. -/
def effectiveSupport (E : FiniteModel Theta X) : Set X :=
  {x | ∃ theta, 0 < E.pmf theta x}

@[simp] theorem mem_effectiveSupport_iff (E : FiniteModel Theta X) (x : X) :
    x ∈ effectiveSupport E ↔ ∃ theta, 0 < E.pmf theta x :=
  Iff.rfl

/-- Normalization guarantees that a finite model has an effective outcome. -/
theorem effectiveSupport_nonempty (E : FiniteModel Theta X) :
    (effectiveSupport E).Nonempty := by
  classical
  let theta : Theta := Classical.choice inferInstance
  by_contra h
  have hn : ∀ x theta, ¬ 0 < E.pmf theta x := by
    intro x psi hpos
    exact h ⟨x, psi, hpos⟩
  have hz : ∀ x, E.pmf theta x = 0 := by
    intro x
    exact le_antisymm (le_of_not_gt (hn x theta)) (E.pmf_nonneg theta x)
  have hsum : (∑ x, E.pmf theta x) = 0 := by
    simp [hz]
  linarith [E.pmf_sum_one theta]

/-- Outcomes admitted as inference bases for one fixed model. -/
abbrev InferenceBase (E : FiniteModel Theta X) :=
  {x : X // x ∈ effectiveSupport E}

/-- Inference bases for a normalized finite model form a nonempty type. -/
noncomputable instance inferenceBaseNonempty (E : FiniteModel Theta X) :
    Nonempty (InferenceBase E) :=
  (effectiveSupport_nonempty E).to_subtype

/-- An inference base when the model itself is allowed to vary (with fixed
finite parameter and ambient sample types). -/
structure FiniteInferenceBase (Theta : Type u) (X : Type v)
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X] where
  model : FiniteModel Theta X
  outcome : X
  outcome_effective : outcome ∈ effectiveSupport model

namespace FiniteInferenceBase

/-- The observed likelihood carried by a finite inference base. -/
def likelihood (I : FiniteInferenceBase Theta X) : Theta → ℝ :=
  fun theta ↦ I.model.pmf theta I.outcome

theorem exists_likelihood_pos (I : FiniteInferenceBase Theta X) :
    ∃ theta, 0 < I.likelihood theta :=
  I.outcome_effective

end FiniteInferenceBase

/-! ## Statistics and induced models -/

section Induced

/-- The mass function induced by a statistic on a finite sample space. -/
noncomputable def inducedPMF (E : FiniteModel Theta X) (T : X → Y)
    (theta : Theta) (y : Y) : ℝ :=
  by
    classical
    exact ∑ x ∈ Finset.univ.filter (fun x ↦ T x = y), E.pmf theta x

theorem inducedPMF_nonneg (E : FiniteModel Theta X) (T : X → Y)
    (theta : Theta) (y : Y) : 0 ≤ inducedPMF E T theta y := by
  classical
  exact Finset.sum_nonneg fun x _ ↦ E.pmf_nonneg theta x

/-- Summing the masses of all fibers recovers the mass of the original
sample space. -/
theorem inducedPMF_sum_one [Fintype Y] (E : FiniteModel Theta X) (T : X → Y)
    (theta : Theta) : ∑ y, inducedPMF E T theta y = 1 := by
  classical
  simpa [inducedPMF, E.pmf_sum_one theta] using
    (Finset.sum_fiberwise (s := Finset.univ) T (E.pmf theta))

/-- A finite statistic therefore induces another normalized finite model. -/
noncomputable def inducedModel [Fintype Y] [Nonempty Y]
    (E : FiniteModel Theta X) (T : X → Y) :
    FiniteModel Theta Y where
  pmf := inducedPMF E T
  pmf_nonneg := inducedPMF_nonneg E T
  pmf_sum_one := inducedPMF_sum_one E T

/-- A statistic is ancillary when its induced distribution is independent of
the parameter. -/
def Ancillary (E : FiniteModel Theta X) (A : X → Y) : Prop :=
  ∀ theta psi a, inducedPMF E A theta a = inducedPMF E A psi a

theorem ancillary_iff_exists_common_pmf (E : FiniteModel Theta X) (A : X → Y) :
    Ancillary E A ↔
      ∃ q : Y → ℝ, ∀ theta a, inducedPMF E A theta a = q a := by
  constructor
  · intro h
    let theta0 : Theta := Classical.choice inferInstance
    exact ⟨inducedPMF E A theta0, fun theta a ↦ h theta theta0 a⟩
  · rintro ⟨q, hq⟩ theta psi a
    exact (hq theta a).trans (hq psi a).symm

theorem inducedPMF_const_eq (E : FiniteModel Theta X) (a0 a : Y) (theta : Theta)
    (h : a0 = a) : inducedPMF E (fun _ ↦ a0) theta a = 1 := by
  classical
  subst a
  simp [inducedPMF, E.pmf_sum_one]

theorem inducedPMF_const_ne (E : FiniteModel Theta X) (a0 a : Y) (theta : Theta)
    (h : a0 ≠ a) : inducedPMF E (fun _ ↦ a0) theta a = 0 := by
  classical
  simp [inducedPMF, h]

/-- Every constant statistic is ancillary. -/
theorem ancillary_const (E : FiniteModel Theta X) (a0 : Y) :
    Ancillary E (fun _ ↦ a0) := by
  intro theta psi a
  by_cases h : a0 = a
  · rw [inducedPMF_const_eq E a0 a theta h,
      inducedPMF_const_eq E a0 a psi h]
  · rw [inducedPMF_const_ne E a0 a theta h,
      inducedPMF_const_ne E a0 a psi h]

end Induced

/-! ## Unbiased estimators and UMVUE output sets -/

/-- The finite expectation of a real-valued statistic. -/
def expectation (E : FiniteModel Theta X) (h : X → ℝ) (theta : Theta) : ℝ :=
  ∑ x, h x * E.pmf theta x

/-- Unbiasedness for a specified real-valued parameter functional.  Taking
`parameter` to be the inclusion realizes the paper's case `Theta ⊆ ℝ`. -/
def UnbiasedEstimator (E : FiniteModel Theta X) (parameter : Theta → ℝ)
    (h : X → ℝ) : Prop :=
  ∀ theta, expectation E h theta = parameter theta

/-- The class `H_E` of all unbiased estimators. -/
def unbiasedEstimators (E : FiniteModel Theta X) (parameter : Theta → ℝ) :
    Set (X → ℝ) :=
  {h | UnbiasedEstimator E parameter h}

/-- Mean squared error at a parameter value.  For an unbiased estimator this
is its variance around the target value. -/
def meanSquaredError (E : FiniteModel Theta X) (parameter : Theta → ℝ)
    (h : X → ℝ) (theta : Theta) : ℝ :=
  ∑ x, (h x - parameter theta) ^ 2 * E.pmf theta x

theorem meanSquaredError_nonneg (E : FiniteModel Theta X) (parameter : Theta → ℝ)
    (h : X → ℝ) (theta : Theta) :
    0 ≤ meanSquaredError E parameter h theta := by
  unfold meanSquaredError
  exact Finset.sum_nonneg fun x _ ↦
    mul_nonneg (sq_nonneg _) (E.pmf_nonneg theta x)

/-- A member of the paper's class `T_E`: an unbiased estimator whose MSE is
no larger than that of any unbiased competitor at every parameter value. -/
def IsUMVUE (E : FiniteModel Theta X) (parameter : Theta → ℝ)
    (h : X → ℝ) : Prop :=
  UnbiasedEstimator E parameter h ∧
    ∀ g, UnbiasedEstimator E parameter g →
      ∀ theta, meanSquaredError E parameter h theta ≤
        meanSquaredError E parameter g theta

/-- The class `T_E` of uniformly minimum-variance unbiased estimators. -/
def umvueCandidates (E : FiniteModel Theta X) (parameter : Theta → ℝ) :
    Set (X → ℝ) :=
  {h | IsUMVUE E parameter h}

/-- The set of all UMVUE estimates reported at an observed sample point. -/
def umvueOutput (E : FiniteModel Theta X) (parameter : Theta → ℝ) (x : X) :
    Set ℝ :=
  {r | ∃ h, h ∈ umvueCandidates E parameter ∧ r = h x}

@[simp] theorem mem_umvueOutput_iff (E : FiniteModel Theta X)
    (parameter : Theta → ℝ) (x : X) (r : ℝ) :
    r ∈ umvueOutput E parameter x ↔
      ∃ h, IsUMVUE E parameter h ∧ r = h x :=
  Iff.rfl

theorem umvueCandidate_unbiased (E : FiniteModel Theta X)
    (parameter : Theta → ℝ) {h : X → ℝ}
    (hh : h ∈ umvueCandidates E parameter) :
    UnbiasedEstimator E parameter h :=
  hh.1

/-! ## Finite maxima and the extended likelihood ratio -/

/-- The maximum of a real-valued function over an explicitly nonempty finite
set. -/
noncomputable def finiteMaximum {A : Type*} [Fintype A]
    (s : Finset A) (hs : s.Nonempty) (f : A → ℝ) : ℝ :=
  (s.image f).max' (hs.image f)

theorem le_finiteMaximum {A : Type*} [Fintype A]
    (s : Finset A) (hs : s.Nonempty) (f : A → ℝ) {a : A} (ha : a ∈ s) :
    f a ≤ finiteMaximum s hs f := by
  classical
  unfold finiteMaximum
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

theorem finiteMaximum_le {A : Type*} [Fintype A]
    (s : Finset A) (hs : s.Nonempty) (f : A → ℝ) {b : ℝ}
    (h : ∀ a ∈ s, f a ≤ b) : finiteMaximum s hs f ≤ b := by
  classical
  unfold finiteMaximum
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
  exact h a ha

theorem exists_eq_finiteMaximum {A : Type*} [Fintype A]
    (s : Finset A) (hs : s.Nonempty) (f : A → ℝ) :
    ∃ a ∈ s, f a = finiteMaximum s hs f := by
  classical
  have hmem : (s.image f).max' (hs.image f) ∈ s.image f :=
    Finset.max'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨a, ha, hfa⟩
  exact ⟨a, ha, hfa⟩

theorem finiteMaximum_nonneg {A : Type*} [Fintype A]
    (s : Finset A) (hs : s.Nonempty) (f : A → ℝ)
    (h : ∀ a ∈ s, 0 ≤ f a) : 0 ≤ finiteMaximum s hs f := by
  rcases hs with ⟨a, ha⟩
  exact (h a ha).trans (le_finiteMaximum s ⟨a, ha⟩ f ha)

/-- A real-valued function on a finite nonempty parameter type attains its
maximum.  In particular, the paper's finite MLE set is never empty. -/
theorem maximizerSet_nonempty_of_finite (f : Theta → ℝ) :
    (maximizerSet f).Nonempty := by
  classical
  let hU : (Finset.univ : Finset Theta).Nonempty := Finset.univ_nonempty
  rcases exists_eq_finiteMaximum Finset.univ hU f with ⟨theta, _, htheta⟩
  refine ⟨theta, ?_⟩
  intro psi
  rw [htheta]
  exact le_finiteMaximum Finset.univ hU f (Finset.mem_univ psi)

/-- A genuine two-cell finite partition.  Nonemptiness of both cells is kept
explicit because both maxima in the likelihood ratio require it. -/
structure ParameterPartition (Theta : Type u) [Fintype Theta] where
  nullPart : Finset Theta
  alternativePart : Finset Theta
  null_nonempty : nullPart.Nonempty
  alternative_nonempty : alternativePart.Nonempty
  disjoint : ∀ {theta : Theta}, theta ∈ nullPart → theta ∈ alternativePart → False
  exhaustive : ∀ theta, theta ∈ nullPart ∨ theta ∈ alternativePart

namespace ParameterPartition

omit [Nonempty Theta] in
theorem mem_null_or_alternative (P : ParameterPartition Theta) (theta : Theta) :
    theta ∈ P.nullPart ∨ theta ∈ P.alternativePart :=
  P.exhaustive theta

omit [Nonempty Theta] in
theorem not_mem_alternative_of_mem_null (P : ParameterPartition Theta) {theta : Theta}
    (h : theta ∈ P.nullPart) : theta ∉ P.alternativePart :=
  fun halt ↦ P.disjoint h halt

end ParameterPartition

/-- Maximum likelihood over a nonempty finite parameter subset. -/
noncomputable def maxLikelihoodOn (E : FiniteModel Theta X) (H : Finset Theta)
    (hH : H.Nonempty) (x : X) : ℝ :=
  finiteMaximum H hH (fun theta ↦ E.pmf theta x)

theorem maxLikelihoodOn_nonneg (E : FiniteModel Theta X) (H : Finset Theta)
    (hH : H.Nonempty) (x : X) : 0 ≤ maxLikelihoodOn E H hH x := by
  apply finiteMaximum_nonneg
  intro theta _
  exact E.pmf_nonneg theta x

/-- The paper's likelihood ratio.  `ENNReal` supplies an infinite value and
has the desired conventions for a zero denominator. -/
noncomputable def extendedLikelihoodRatio (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) : ENNReal :=
  ENNReal.ofReal (maxLikelihoodOn E P.nullPart P.null_nonempty x) /
    ENNReal.ofReal
      (maxLikelihoodOn E P.alternativePart P.alternative_nonempty x)

theorem extendedLikelihoodRatio_zero_zero (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X)
    (hnull : maxLikelihoodOn E P.nullPart P.null_nonempty x = 0)
    (halt : maxLikelihoodOn E P.alternativePart P.alternative_nonempty x = 0) :
    extendedLikelihoodRatio E P x = 0 := by
  simp [extendedLikelihoodRatio, hnull, halt]

theorem extendedLikelihoodRatio_pos_div_zero (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X)
    (hnull : 0 < maxLikelihoodOn E P.nullPart P.null_nonempty x)
    (halt : maxLikelihoodOn E P.alternativePart P.alternative_nonempty x = 0) :
    extendedLikelihoodRatio E P x = ⊤ := by
  unfold extendedLikelihoodRatio
  rw [halt, ENNReal.ofReal_zero]
  exact ENNReal.div_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hnull))

theorem extendedLikelihoodRatio_of_denominator_pos (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X)
    (halt : 0 < maxLikelihoodOn E P.alternativePart P.alternative_nonempty x) :
    extendedLikelihoodRatio E P x =
      ENNReal.ofReal
        (maxLikelihoodOn E P.nullPart P.null_nonempty x /
          maxLikelihoodOn E P.alternativePart P.alternative_nonempty x) := by
  exact (ENNReal.ofReal_div_of_pos halt).symm

/-! ## Lower-tail likelihood-ratio p-values -/

/-- Outcomes whose likelihood ratio is no larger than the observed one. -/
noncomputable def lowerTailRegion (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) : Finset X :=
  by
    classical
    exact Finset.univ.filter
      (fun y ↦ extendedLikelihoodRatio E P y ≤ extendedLikelihoodRatio E P x)

@[simp] theorem mem_lowerTailRegion_iff (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x y : X) :
    y ∈ lowerTailRegion E P x ↔
      extendedLikelihoodRatio E P y ≤ extendedLikelihoodRatio E P x := by
  classical
  simp [lowerTailRegion]

theorem observed_mem_lowerTailRegion (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) : x ∈ lowerTailRegion E P x := by
  simp

/-- Null probability of the lower likelihood-ratio tail. -/
noncomputable def lowerTailProbability (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) (theta : Theta) : ℝ :=
  ∑ y ∈ lowerTailRegion E P x, E.pmf theta y

theorem lowerTailProbability_nonneg (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) (theta : Theta) :
    0 ≤ lowerTailProbability E P x theta := by
  unfold lowerTailProbability
  exact Finset.sum_nonneg fun y _ ↦ E.pmf_nonneg theta y

theorem lowerTailProbability_le_one (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) (theta : Theta) :
    lowerTailProbability E P x theta ≤ 1 := by
  unfold lowerTailProbability
  calc
    ∑ y ∈ lowerTailRegion E P x, E.pmf theta y ≤
        ∑ y, E.pmf theta y :=
      Finset.sum_le_univ_sum_of_nonneg (fun y ↦ E.pmf_nonneg theta y)
    _ = 1 := E.pmf_sum_one theta

/-- The lower-tail LR p-value: the largest null tail probability. -/
noncomputable def lowerTailLRPValue (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) : ℝ :=
  finiteMaximum P.nullPart P.null_nonempty
    (lowerTailProbability E P x)

/-- The finite LR p-value always belongs to the unit interval. -/
theorem lowerTailLRPValue_mem_Icc (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) :
    lowerTailLRPValue E P x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply finiteMaximum_nonneg
    intro theta _
    exact lowerTailProbability_nonneg E P x theta
  · apply finiteMaximum_le
    intro theta _
    exact lowerTailProbability_le_one E P x theta

theorem lowerTailLRPValue_nonneg (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) :
    0 ≤ lowerTailLRPValue E P x :=
  (lowerTailLRPValue_mem_Icc E P x).1

theorem lowerTailLRPValue_le_one (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) :
    lowerTailLRPValue E P x ≤ 1 :=
  (lowerTailLRPValue_mem_Icc E P x).2

/-- The finite lower-tail LR construction is a valid p-value under every
null parameter: its rejection probability is at most the chosen level. -/
theorem lowerTailLRPValue_superuniform (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (theta : Theta) (htheta : theta ∈ P.nullPart)
    (alpha : ℝ) (halpha : 0 ≤ alpha) :
    ∑ x ∈ Finset.univ.filter (fun x ↦ lowerTailLRPValue E P x ≤ alpha),
      E.pmf theta x ≤ alpha := by
  classical
  let s := Finset.univ.filter (fun x ↦ lowerTailLRPValue E P x ≤ alpha)
  change ∑ x ∈ s, E.pmf theta x ≤ alpha
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx, hmax⟩ :=
      s.exists_max_image (extendedLikelihoodRatio E P) hs
    have hsub : s ⊆ lowerTailRegion E P x := by
      intro y hy
      exact (mem_lowerTailRegion_iff E P x y).2 (hmax y hy)
    calc
      ∑ y ∈ s, E.pmf theta y ≤ lowerTailProbability E P x theta := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro y _ _
        exact E.pmf_nonneg theta y
      _ ≤ lowerTailLRPValue E P x :=
        le_finiteMaximum P.nullPart P.null_nonempty _ htheta
      _ ≤ alpha := (Finset.mem_filter.mp hx).2
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simpa using halpha

/-- The paper uses strict rejection; it too has size at most `alpha`. -/
theorem lowerTailLRPValue_strict_rejection_bound (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (theta : Theta) (htheta : theta ∈ P.nullPart)
    (alpha : ℝ) (halpha : 0 ≤ alpha) :
    ∑ x ∈ Finset.univ.filter (fun x ↦ lowerTailLRPValue E P x < alpha),
      E.pmf theta x ≤ alpha := by
  classical
  calc
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x ↦ lowerTailLRPValue E P x ≤ alpha),
        E.pmf theta x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ x, le_of_lt (Finset.mem_filter.mp hx).2⟩
      · intro x _ _
        exact E.pmf_nonneg theta x
    _ ≤ alpha := lowerTailLRPValue_superuniform E P theta htheta alpha halpha

/-! ## Positive posterior denominators -/

/-- A strictly positive prior and an effective observation make the finite
posterior denominator strictly positive. -/
theorem posteriorNormalizer_pos_of_positive_prior (E : FiniteModel Theta X)
    (prior : Theta → ℝ) (hprior : ∀ theta, 0 < prior theta)
    {x : X} (hx : x ∈ effectiveSupport E) :
    0 < posteriorNormalizer (fun theta ↦ E.pmf theta x) prior := by
  classical
  rcases hx with ⟨theta0, htheta0⟩
  unfold posteriorNormalizer
  apply Finset.sum_pos'
  · intro theta _
    exact mul_nonneg (E.pmf_nonneg theta x) (le_of_lt (hprior theta))
  · exact ⟨theta0, Finset.mem_univ theta0, mul_pos htheta0 (hprior theta0)⟩

theorem posteriorNormalizer_ne_zero_of_positive_prior (E : FiniteModel Theta X)
    (prior : Theta → ℝ) (hprior : ∀ theta, 0 < prior theta)
    {x : X} (hx : x ∈ effectiveSupport E) :
    posteriorNormalizer (fun theta ↦ E.pmf theta x) prior ≠ 0 :=
  ne_of_gt (posteriorNormalizer_pos_of_positive_prior E prior hprior hx)

theorem posteriorMass_nonneg_of_positive_prior (E : FiniteModel Theta X)
    (prior : Theta → ℝ) (hprior : ∀ theta, 0 < prior theta)
    {x : X} (hx : x ∈ effectiveSupport E) (theta : Theta) :
    0 ≤ posteriorMass (fun psi ↦ E.pmf psi x) prior theta := by
  unfold posteriorMass
  exact div_nonneg
    (mul_nonneg (E.pmf_nonneg theta x) (le_of_lt (hprior theta)))
    (le_of_lt (posteriorNormalizer_pos_of_positive_prior E prior hprior hx))

omit [Nonempty Theta] in
/-- Posterior masses sum to one once the normalizing constant is nonzero. -/
theorem sum_posteriorMass_eq_one (likelihood prior : Theta → ℝ)
    (hden : posteriorNormalizer likelihood prior ≠ 0) :
    ∑ theta, posteriorMass likelihood prior theta = 1 := by
  simp only [posteriorMass]
  rw [← Finset.sum_div]
  exact div_self hden

/-- Under the positivity hypothesis used in the manuscript, posterior event
probabilities really take values in `[0,1]`. -/
theorem posteriorProbability_mem_Icc_of_positive_prior
    (E : FiniteModel Theta X) (prior : Theta → ℝ)
    (hprior : ∀ theta, 0 < prior theta) {x : X}
    (hx : x ∈ effectiveSupport E) (H : Finset Theta) :
    posteriorProbability (fun theta ↦ E.pmf theta x) prior H ∈
      Set.Icc (0 : ℝ) 1 := by
  have hmass : ∀ theta,
      0 ≤ posteriorMass (fun psi ↦ E.pmf psi x) prior theta :=
    fun theta ↦ posteriorMass_nonneg_of_positive_prior E prior hprior hx theta
  constructor
  · unfold posteriorProbability
    exact Finset.sum_nonneg fun theta _ ↦ hmass theta
  · unfold posteriorProbability
    calc
      ∑ theta ∈ H, posteriorMass (fun psi ↦ E.pmf psi x) prior theta ≤
          ∑ theta, posteriorMass (fun psi ↦ E.pmf psi x) prior theta :=
        Finset.sum_le_univ_sum_of_nonneg hmass
      _ = 1 := sum_posteriorMass_eq_one _ _
        (posteriorNormalizer_ne_zero_of_positive_prior E prior hprior hx)

/-- The paper's stated generality: a nonnegative prior together with its
explicitly positive denominator makes every posterior event probability lie
in `[0,1]`; individual prior masses may be zero. -/
theorem posteriorProbability_mem_Icc_of_nonnegative_prior
    (E : FiniteModel Theta X) (prior : Theta → ℝ)
    (hprior : ∀ theta, 0 ≤ prior theta) (x : X)
    (hden : 0 < posteriorNormalizer (fun theta ↦ E.pmf theta x) prior)
    (H : Finset Theta) :
    posteriorProbability (fun theta ↦ E.pmf theta x) prior H ∈
      Set.Icc (0 : ℝ) 1 := by
  have hmass : ∀ theta,
      0 ≤ posteriorMass (fun psi ↦ E.pmf psi x) prior theta := by
    intro theta
    unfold posteriorMass
    exact div_nonneg (mul_nonneg (E.pmf_nonneg theta x) (hprior theta))
      (le_of_lt hden)
  constructor
  · unfold posteriorProbability
    exact Finset.sum_nonneg fun theta _ ↦ hmass theta
  · unfold posteriorProbability
    calc
      ∑ theta ∈ H, posteriorMass (fun psi ↦ E.pmf psi x) prior theta ≤
          ∑ theta, posteriorMass (fun psi ↦ E.pmf psi x) prior theta :=
        Finset.sum_le_univ_sum_of_nonneg hmass
      _ = 1 := sum_posteriorMass_eq_one _ _ (ne_of_gt hden)

theorem FiniteInferenceBase.posteriorNormalizer_pos
    (I : FiniteInferenceBase Theta X) (prior : Theta → ℝ)
    (hprior : ∀ theta, 0 < prior theta) :
    0 < posteriorNormalizer I.likelihood prior :=
  posteriorNormalizer_pos_of_positive_prior I.model prior hprior
    I.outcome_effective

/-! ## Confidence regions and their relation-valued procedure -/

/-- Coverage probability of a set-valued confidence rule at `theta`. -/
noncomputable def coverageProbability (E : FiniteModel Theta X)
    (CR : X → Set Theta) (theta : Theta) : ℝ :=
  by
    classical
    exact ∑ x ∈ Finset.univ.filter (fun x ↦ theta ∈ CR x), E.pmf theta x

open Classical in
/-- The filtered finite sum is exactly the indicator formula displayed in
the manuscript's confidence-region definition. -/
theorem coverageProbability_eq_sum_indicator (E : FiniteModel Theta X)
    (CR : X → Set Theta) (theta : Theta) :
    coverageProbability E CR theta =
      ∑ x, E.pmf theta x * (if theta ∈ CR x then 1 else 0) := by
  classical
  simp [coverageProbability, Finset.sum_filter, mul_ite]

theorem coverageProbability_nonneg (E : FiniteModel Theta X)
    (CR : X → Set Theta) (theta : Theta) :
    0 ≤ coverageProbability E CR theta := by
  unfold coverageProbability
  exact Finset.sum_nonneg fun x _ ↦ E.pmf_nonneg theta x

theorem coverageProbability_le_one (E : FiniteModel Theta X)
    (CR : X → Set Theta) (theta : Theta) :
    coverageProbability E CR theta ≤ 1 := by
  classical
  unfold coverageProbability
  calc
    ∑ x ∈ Finset.univ.filter (fun x ↦ theta ∈ CR x), E.pmf theta x ≤
        ∑ x, E.pmf theta x :=
      Finset.sum_le_univ_sum_of_nonneg (fun x ↦ E.pmf_nonneg theta x)
    _ = 1 := E.pmf_sum_one theta

/-- At least nominal `1 - alpha` coverage at every parameter value. -/
def HasCoverage (E : FiniteModel Theta X) (alpha : ℝ)
    (CR : X → Set Theta) : Prop :=
  ∀ theta, 1 - alpha ≤ coverageProbability E CR theta

theorem coverageProbability_full (E : FiniteModel Theta X) (theta : Theta) :
    coverageProbability E (fun _ ↦ Set.univ) theta = 1 := by
  classical
  simp [coverageProbability, E.pmf_sum_one]

/-- The full parameter space is always a confidence region at nonnegative
significance level. -/
theorem fullConfidenceRegion_hasCoverage (E : FiniteModel Theta X)
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    HasCoverage E alpha (fun _ ↦ Set.univ) := by
  intro theta
  rw [coverageProbability_full]
  linarith

/-- The manuscript's relation-valued frequentist procedure.  At an inference
base it contains the observed output of every rule with nominal coverage for
that base's model. -/
noncomputable def confidenceProcedure (alpha : ℝ) :
    Procedure (FiniteInferenceBase Theta X) (Set Theta) :=
  {p | ∃ CR : X → Set Theta,
    HasCoverage p.1.model alpha CR ∧ p.2 = CR p.1.outcome}

@[simp] theorem mem_output_confidenceProcedure_iff (alpha : ℝ)
    (I : FiniteInferenceBase Theta X) (R : Set Theta) :
    R ∈ output (confidenceProcedure (Theta := Theta) (X := X) alpha) I ↔
      ∃ CR : X → Set Theta,
        HasCoverage I.model alpha CR ∧ R = CR I.outcome :=
  Iff.rfl

theorem confidenceProcedure_output_nonempty {alpha : ℝ} (halpha : 0 ≤ alpha)
    (I : FiniteInferenceBase Theta X) :
    (output (confidenceProcedure (Theta := Theta) (X := X) alpha) I).Nonempty := by
  refine ⟨Set.univ, ?_⟩
  exact ⟨fun _ ↦ Set.univ, fullConfidenceRegion_hasCoverage I.model halpha, rfl⟩

/-! ## Product procedures and componentwise preservation -/

/-- Pair every output of the first procedure with every output of the second. -/
def productProcedure {I : Type*} {A : Type*} {B : Type*}
    (EvA : Procedure I A) (EvB : Procedure I B) : Procedure I (A × B) :=
  {p | p.2.1 ∈ output EvA p.1 ∧ p.2.2 ∈ output EvB p.1}

@[simp] theorem output_productProcedure {I : Type*} {A : Type*} {B : Type*}
    (EvA : Procedure I A) (EvB : Procedure I B) (i : I) :
    output (productProcedure EvA EvB) i = output EvA i ×ˢ output EvB i := by
  ext p
  rfl

/-- Preservation is closed under forming composite reports. -/
theorem productProcedure_preserves {I : Type*} {A : Type*} {B : Type*}
    {D : StatisticalRelation I} {EvA : Procedure I A} {EvB : Procedure I B}
    (hA : Preserves EvA D) (hB : Preserves EvB D) :
    Preserves (productProcedure EvA EvB) D := by
  intro i j hij
  simp only [output_productProcedure, hA hij, hB hij]

/-- For procedures with nonempty fibers, preservation of a product is
equivalent to preservation of each component. -/
theorem productProcedure_preserves_iff_of_nonempty
    {I : Type*} {A : Type*} {B : Type*}
    {D : StatisticalRelation I} {EvA : Procedure I A} {EvB : Procedure I B}
    (hA_nonempty : ∀ i, (output EvA i).Nonempty)
    (hB_nonempty : ∀ i, (output EvB i).Nonempty) :
    Preserves (productProcedure EvA EvB) D ↔
      Preserves EvA D ∧ Preserves EvB D := by
  constructor
  · intro hprod
    constructor
    · intro i j hij
      ext a
      constructor
      · intro hai
        rcases hB_nonempty i with ⟨b, hbi⟩
        have hp : (a, b) ∈ output (productProcedure EvA EvB) i := ⟨hai, hbi⟩
        have hp' : (a, b) ∈ output (productProcedure EvA EvB) j := by
          rw [← hprod hij]
          exact hp
        exact hp'.1
      · intro haj
        rcases hB_nonempty j with ⟨b, hbj⟩
        have hp : (a, b) ∈ output (productProcedure EvA EvB) j := ⟨haj, hbj⟩
        have hp' : (a, b) ∈ output (productProcedure EvA EvB) i := by
          rw [hprod hij]
          exact hp
        exact hp'.1
    · intro i j hij
      ext b
      constructor
      · intro hbi
        rcases hA_nonempty i with ⟨a, hai⟩
        have hp : (a, b) ∈ output (productProcedure EvA EvB) i := ⟨hai, hbi⟩
        have hp' : (a, b) ∈ output (productProcedure EvA EvB) j := by
          rw [← hprod hij]
          exact hp
        exact hp'.2
      · intro hbj
        rcases hA_nonempty j with ⟨a, haj⟩
        have hp : (a, b) ∈ output (productProcedure EvA EvB) j := ⟨haj, hbj⟩
        have hp' : (a, b) ∈ output (productProcedure EvA EvB) i := by
          rw [hprod hij]
          exact hp
        exact hp'.2
  · rintro ⟨hA, hB⟩
    exact productProcedure_preserves hA hB

end VennDiagrams
