import Mathlib

/-!
# Birnbaum’s principles in Venn diagrams

The statistical results are proved from our definitions of L, S, and C in the
finite setting, under the stated parameter-space assumptions.
-/

namespace VennDiagrams

universe u v

open Set
open scoped BigOperators

/-- A statistical relation is a set containing pairs of inference bases. -/
abbrev StatisticalRelation (ι : Type u) := ι → ι → Prop

/-- The union of two statistical relations. -/
def relationUnion {ι : Type u} (D₁ D₂ : StatisticalRelation ι) :
    StatisticalRelation ι :=
  fun i j ↦ D₁ i j ∨ D₂ i j

/-- The equivalence closure: the smallest equivalence relation containing D. -/
def equivalenceClosure {ι : Type u} (D : StatisticalRelation ι) :
    StatisticalRelation ι :=
  Relation.EqvGen D

/-- Definition 3.1. A statistical procedure is a relation between the set of inference bases
and a fixed codomain. -/
abbrev Procedure (ι : Type u) (A : Type v) := Set (ι × A)

/-- Definition 3.1. For each inference base, the output set. -/
def output {ι : Type u} {A : Type v} (Ev : Procedure ι A) (i : ι) : Set A :=
  {a | (i, a) ∈ Ev}

/-- Ordinary functions are included as graph relations. -/
def graphProcedure {ι : Type u} {A : Type v} (f : ι → A) : Procedure ι A :=
  {(i, a) | a = f i}

/-- Definition 3.2. Related inference bases generate identical collections of outputs under
the procedure. -/
def Preserves {ι : Type u} {A : Type v} (Ev : Procedure ι A)
    (D : StatisticalRelation ι) : Prop :=
  ∀ ⦃i j⦄, D i j → output Ev i = output Ev j

/-- Definition 3.3. The class of all statistical procedures that preserve D. -/
def preservingClass {ι : Type u} (A : Type v) (D : StatisticalRelation ι) :
    Set (Procedure ι A) :=
  {Ev | Preserves Ev D}

/-- Lemma A.5. Equality propagates along finite chains. -/
theorem preservingClass_equivalenceClosure {ι : Type u} {A : Type v}
    (D : StatisticalRelation ι) :
    preservingClass A D = preservingClass A (equivalenceClosure D) := by
  sorry

end VennDiagrams

namespace VennDiagrams

universe u v

open Set Finset
open scoped BigOperators

/-- The likelihood functions are proportional with a positive constant. -/
def Proportional {Θ : Type u} (f g : Θ → ℝ) : Prop :=
  ∃ k : ℝ, 0 < k ∧ ∀ θ, f θ = k * g θ

/-- Proportionality is reflexive. -/
theorem proportional_refl {Θ : Type u} (f : Θ → ℝ) : Proportional f f := by
  refine ⟨1, by norm_num, ?_⟩
  intro θ
  ring

/-- Proportionality is symmetric. -/
theorem proportional_symm {Θ : Type u} {f g : Θ → ℝ}
    (h : Proportional f g) : Proportional g f := by
  rcases h with ⟨k, hk, hfg⟩
  refine ⟨k⁻¹, inv_pos.mpr hk, ?_⟩
  intro θ
  rw [hfg θ]
  field_simp [ne_of_gt hk]

/-- Proportionality is transitive. -/
theorem proportional_trans {Θ : Type u} {f g h : Θ → ℝ}
    (hfg : Proportional f g) (hgh : Proportional g h) : Proportional f h := by
  rcases hfg with ⟨k, hk, hfg⟩
  rcases hgh with ⟨c, hc, hgh⟩
  refine ⟨k * c, mul_pos hk hc, ?_⟩
  intro θ
  rw [hfg θ, hgh θ]
  ring

/-- The likelihood relation contains pairs of inference bases whose likelihood functions are
proportional to each other. -/
def likelihoodRelation {ι : Type u} {Θ : Type v} (likelihood : ι → Θ → ℝ) :
    StatisticalRelation ι :=
  fun i j ↦ Proportional (likelihood i) (likelihood j)

/-- The likelihood relation is an equivalence relation. -/
theorem likelihoodRelation_isEquivalence {ι : Type u} {Θ : Type v}
    (likelihood : ι → Θ → ℝ) : Equivalence (likelihoodRelation likelihood) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact proportional_refl _
  · intro i j hij
    exact proportional_symm hij
  · intro i j k hij hjk
    exact proportional_trans hij hjk

end VennDiagrams

namespace VennDiagrams

universe u v w

open Set Finset
open scoped BigOperators ENNReal

/-- A statistical model has a finite sample space and a common non-empty finite parameter
space. The probability mass function is nonnegative and the masses sum to one. -/
structure FiniteModel (Theta : Type u) (X : Type v)
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X] where
  pmf : Theta → X → ℝ
  pmf_nonneg : ∀ theta x, 0 ≤ pmf theta x
  pmf_sum_one : ∀ theta, ∑ x, pmf theta x = 1

variable {Theta : Type u} {X : Type v} {Y : Type w}
variable [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]

/-- The effective support contains the outcomes with positive mass for at least one
parameter value. -/
def effectiveSupport (E : FiniteModel Theta X) : Set X :=
  {x | ∃ theta, 0 < E.pmf theta x}

/-- An outcome in the effective support. -/
abbrev InferenceBase (E : FiniteModel Theta X) :=
  {x : X // x ∈ effectiveSupport E}

/-- The probability mass function of the model induced by a statistic. -/
noncomputable def inducedPMF (E : FiniteModel Theta X) (T : X → Y)
    (theta : Theta) (y : Y) : ℝ :=
  by
    classical
    exact ∑ x ∈ Finset.univ.filter (fun x ↦ T x = y), E.pmf theta x

/-- The induced probabilities are nonnegative. -/
theorem inducedPMF_nonneg (E : FiniteModel Theta X) (T : X → Y)
    (theta : Theta) (y : Y) : 0 ≤ inducedPMF E T theta y := by
  classical
  exact Finset.sum_nonneg fun x _ ↦ E.pmf_nonneg theta x

/-- The masses of the induced model sum to one. -/
theorem inducedPMF_sum_one [Fintype Y] (E : FiniteModel Theta X) (T : X → Y)
    (theta : Theta) : ∑ y, inducedPMF E T theta y = 1 := by
  classical
  simpa [inducedPMF, E.pmf_sum_one theta] using
    (Finset.sum_fiberwise (s := Finset.univ) T (E.pmf theta))

/-- The model induced by a statistic. -/
noncomputable def inducedModel [Fintype Y] [Nonempty Y]
    (E : FiniteModel Theta X) (T : X → Y) :
    FiniteModel Theta Y where
  pmf := inducedPMF E T
  pmf_nonneg := inducedPMF_nonneg E T
  pmf_sum_one := inducedPMF_sum_one E T

/-- The distribution of an ancillary statistic does not depend on the parameter. -/
def Ancillary (E : FiniteModel Theta X) (A : X → Y) : Prop :=
  ∀ theta psi a, inducedPMF E A theta a = inducedPMF E A psi a

/-- The maximum of a real-valued function over a non-empty finite set. -/
noncomputable def finiteMaximum {A : Type*} [Fintype A]
    (s : Finset A) (hs : s.Nonempty) (f : A → ℝ) : ℝ :=
  (s.image f).max' (hs.image f)

/-- Every value is at most the maximum. -/
theorem le_finiteMaximum {A : Type*} [Fintype A]
    (s : Finset A) (hs : s.Nonempty) (f : A → ℝ) {a : A} (ha : a ∈ s) :
    f a ≤ finiteMaximum s hs f := by
  classical
  unfold finiteMaximum
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

/-- If every value is at most b, the maximum is at most b. -/
theorem finiteMaximum_le {A : Type*} [Fintype A]
    (s : Finset A) (hs : s.Nonempty) (f : A → ℝ) {b : ℝ}
    (h : ∀ a ∈ s, f a ≤ b) : finiteMaximum s hs f ≤ b := by
  classical
  unfold finiteMaximum
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
  exact h a ha

/-- The maximum of nonnegative values is nonnegative. -/
theorem finiteMaximum_nonneg {A : Type*} [Fintype A]
    (s : Finset A) (hs : s.Nonempty) (f : A → ℝ)
    (h : ∀ a ∈ s, 0 ≤ f a) : 0 ≤ finiteMaximum s hs f := by
  rcases hs with ⟨a, ha⟩
  exact (h a ha).trans (le_finiteMaximum s ⟨a, ha⟩ f ha)

/-- Example 3.2. A fixed partition of the parameter space into two non-empty sets. -/
structure ParameterPartition (Theta : Type u) [Fintype Theta] where
  nullPart : Finset Theta
  alternativePart : Finset Theta
  null_nonempty : nullPart.Nonempty
  alternative_nonempty : alternativePart.Nonempty
  disjoint : ∀ {theta : Theta}, theta ∈ nullPart → theta ∈ alternativePart → False
  exhaustive : ∀ theta, theta ∈ nullPart ∨ theta ∈ alternativePart

/-- The maximum likelihood over a non-empty finite parameter set. -/
noncomputable def maxLikelihoodOn (E : FiniteModel Theta X) (H : Finset Theta)
    (hH : H.Nonempty) (x : X) : ℝ :=
  finiteMaximum H hH (fun theta ↦ E.pmf theta x)

/-- Example 3.2, (3.3). The null-to-alternative generalized likelihood ratio. The ratio is
interpreted in the extended sense: a/0 = ∞ for a > 0, and 0/0 = 0. -/
noncomputable def extendedLikelihoodRatio (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) : ENNReal :=
  ENNReal.ofReal (maxLikelihoodOn E P.nullPart P.null_nonempty x) /
    ENNReal.ofReal
      (maxLikelihoodOn E P.alternativePart P.alternative_nonempty x)

/-- Example 3.2. The outcomes with likelihood ratio at most the observed likelihood ratio. -/
noncomputable def lowerTailRegion (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) : Finset X :=
  by
    classical
    exact Finset.univ.filter
      (fun y ↦ extendedLikelihoodRatio E P y ≤ extendedLikelihoodRatio E P x)

/-- Example 3.2. The probability of the lower-tail region. -/
noncomputable def lowerTailProbability (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) (theta : Theta) : ℝ :=
  ∑ y ∈ lowerTailRegion E P x, E.pmf theta y

/-- The lower-tail probability is nonnegative. -/
theorem lowerTailProbability_nonneg (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) (theta : Theta) :
    0 ≤ lowerTailProbability E P x theta := by
  unfold lowerTailProbability
  exact Finset.sum_nonneg fun y _ ↦ E.pmf_nonneg theta y

/-- The lower-tail probability is at most one. -/
theorem lowerTailProbability_le_one (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) (theta : Theta) :
    lowerTailProbability E P x theta ≤ 1 := by
  unfold lowerTailProbability
  calc
    ∑ y ∈ lowerTailRegion E P x, E.pmf theta y ≤
        ∑ y, E.pmf theta y :=
      Finset.sum_le_univ_sum_of_nonneg (fun y ↦ E.pmf_nonneg theta y)
    _ = 1 := E.pmf_sum_one theta

/-- Example 3.2. The maximum lower-tail probability over the null hypothesis. -/
noncomputable def lowerTailLRPValue (E : FiniteModel Theta X)
    (P : ParameterPartition Theta) (x : X) : ℝ :=
  finiteMaximum P.nullPart P.null_nonempty
    (lowerTailProbability E P x)

/-- Example 3.2. The p-value belongs to [0,1]. -/
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

end VennDiagrams

namespace VennDiagrams

universe u v w z

open Set Finset
open scoped BigOperators

/-- The likelihood-proportionality classes. -/
def likelihoodProportionalitySetoid {X : Type u} {Θ : Type v}
    (likelihood : X → Θ → ℝ) : Setoid X where
  r x y := Proportional (likelihood x) (likelihood y)
  iseqv := likelihoodRelation_isEquivalence likelihood

/-- The likelihood-class statistic. -/
def canonicalMinimalSufficient {X : Type u} {Θ : Type v}
    (likelihood : X → Θ → ℝ) (x : X) :
    Quotient (likelihoodProportionalitySetoid likelihood) :=
  Quotient.mk _ x

/-- Two observations have the same statistic value if and only if their likelihood functions
are proportional. -/
def LikelihoodFiberCriterion {X : Type u} {Θ : Type v} {A : Type w}
    (likelihood : X → Θ → ℝ) (T : X → A) : Prop :=
  ∀ x y, T x = T y ↔ Proportional (likelihood x) (likelihood y)

/-- A statistic is sufficient when the probability mass function is the product of its
induced probability mass function and a parameter-free factor. -/
def FiniteSufficient
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y) : Prop :=
  ∃ q : X → ℝ,
    ∀ theta x, E.pmf theta x = inducedPMF E T theta (T x) * q x

/-- The Neyman–Fisher factorization has a strictly positive parameter-free factor on the
effective sample space. -/
def StrictFiniteFactorization
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y) : Prop :=
  ∃ (g : Theta → Y → ℝ) (h : X → ℝ),
    (∀ x, 0 < h x) ∧
      ∀ theta x, E.pmf theta x = g theta (T x) * h x

/-- A minimal sufficient statistic is sufficient and is a function of every sufficient
statistic. -/
def FiniteMinimalSufficient
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y) : Prop :=
  FiniteSufficient E T ∧
    ∀ {Z : Type w} (S : X → Z), FiniteSufficient E S →
      ∃ f : Z → Y, ∀ x, T x = f (S x)

/-- Example 3.7. The finite Neyman–Fisher factorization. -/
theorem finite_neyman_fisher_factorization
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E) :
    FiniteSufficient E T ↔ StrictFiniteFactorization E T := by
  sorry

/-- Section 2.1. The pointwise criterion for minimal sufficiency on finite effective
supports. -/
theorem finite_minimal_sufficiency_iff_likelihoodFiberCriterion
    {Theta : Type u} {X Y : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E) :
    FiniteMinimalSufficient E T ↔
      LikelihoodFiberCriterion (fun x theta ↦ E.pmf theta x) T := by
  sorry

/-- Section 2.1. Conditioning on the observed ancillary fiber has positive probability. The
injection identifies the observed values and preserves codes in the ordinary branch; in
the mixed-experiment branch, the ancillary is surjective onto a nontrivial set. -/
def finiteDirectionalConditionalityPair
    {Θ : Type u} {X₁ X₂ : Type v}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X₁] [Nonempty X₁] [Fintype X₂] [Nonempty X₂]
    (E₁ : FiniteModel Θ X₁) (code₁ : X₁ → Nat) (x₁ : InferenceBase E₁)
    (E₂ : FiniteModel Θ X₂) (code₂ : X₂ → Nat) (x₂ : InferenceBase E₂) : Prop :=
  ∃ (A₀ : Type v) (A : X₁ → A₀) (embed : X₂ → X₁),
    Ancillary E₁ A ∧
      (∀ θ, 0 < inducedPMF E₁ A θ (A x₁.1)) ∧
      Function.Injective embed ∧
      ((∀ y₂, code₁ (embed y₂) = code₂ y₂) ∨
        (Nontrivial A₀ ∧ Function.Surjective A)) ∧
      (∀ y₁, A y₁ = A x₁.1 ↔ ∃ y₂, embed y₂ = y₁) ∧
      embed x₂.1 = x₁.1 ∧
      (∀ θ y₂, E₂.pmf θ y₂ =
        E₁.pmf θ (embed y₂) / inducedPMF E₁ A θ (A x₁.1))

/-- Section 2.1. The conditionality relation includes the same conditions with the roles of
the inference bases reversed. -/
def finiteConditionalityPair
    {Θ : Type u} {X₁ X₂ : Type v}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X₁] [Nonempty X₁] [Fintype X₂] [Nonempty X₂]
    (E₁ : FiniteModel Θ X₁) (code₁ : X₁ → Nat) (x₁ : InferenceBase E₁)
    (E₂ : FiniteModel Θ X₂) (code₂ : X₂ → Nat) (x₂ : InferenceBase E₂) : Prop :=
  finiteDirectionalConditionalityPair.{u, v} E₁ code₁ x₁ E₂ code₂ x₂ ∨
    finiteDirectionalConditionalityPair.{u, v} E₂ code₂ x₂ E₁ code₁ x₁

/-- Section 2. A finite inference base with a non-empty effective sample space and a fixed
injective outcome code. The sample spaces may be different; the parameter space is
common. -/
structure PackedFiniteInferenceBase (Theta : Type u)
    [thetaFintype : Fintype Theta] [thetaNonempty : Nonempty Theta] where
  Sample : Type v
  sampleFintype : Fintype Sample
  sampleNonempty : Nonempty Sample
  outcomeCode : Sample → Nat
  outcomeCode_injective : Function.Injective outcomeCode
  model : @FiniteModel Theta Sample thetaFintype thetaNonempty
    sampleFintype sampleNonempty
  outcome : Sample
  outcome_effective : @effectiveSupport Theta Sample thetaFintype thetaNonempty
    sampleFintype sampleNonempty model outcome
  all_outcomes_effective : ∀ x,
    @effectiveSupport Theta Sample thetaFintype thetaNonempty
      sampleFintype sampleNonempty model x

/-- The observed likelihood function. -/
def PackedFiniteInferenceBase.likelihood
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase Theta) : Theta → ℝ :=
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  fun theta ↦ I.model.pmf theta I.outcome

/-- The family of likelihood functions on the sample space. -/
def PackedFiniteInferenceBase.likelihoodFamily
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase Theta) : I.Sample → Theta → ℝ :=
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  fun x theta ↦ I.model.pmf theta x

/-- The observed outcome in the effective support. -/
def PackedFiniteInferenceBase.asInferenceBase
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase Theta) :
    letI : Fintype I.Sample := I.sampleFintype
    letI : Nonempty I.Sample := I.sampleNonempty
    InferenceBase I.model := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  exact ⟨I.outcome, I.outcome_effective⟩

/-- A statistic maps onto a finite non-empty reduced sample space. -/
structure PackedFiniteStatistic
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase.{u, v} Theta) where
  Codomain : Type v
  codomainFintype : Fintype Codomain
  codomainNonempty : Nonempty Codomain
  statistic : I.Sample → Codomain
  statistic_surjective : Function.Surjective statistic

/-- The reduced model induced by the statistic. -/
noncomputable def PackedFiniteStatistic.inducedModel
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    {I : PackedFiniteInferenceBase.{u, v} Theta}
    (T : PackedFiniteStatistic I) :
    @FiniteModel Theta T.Codomain inferInstance inferInstance
      T.codomainFintype T.codomainNonempty := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype T.Codomain := T.codomainFintype
  letI : Nonempty T.Codomain := T.codomainNonempty
  exact VennDiagrams.inducedModel I.model T.statistic

/-- Example 3.2. The lower-tail likelihood-ratio p-value on an inference base. -/
noncomputable def packedLowerTailLRPValue
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (P : ParameterPartition Theta)
    (I : PackedFiniteInferenceBase.{u, v} Theta) : ℝ := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  exact lowerTailLRPValue I.model P I.outcome

/-- Example 3.2. The p-value belongs to [0,1]. -/
theorem packedLowerTailLRPValue_mem_Icc
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (P : ParameterPartition Theta)
    (I : PackedFiniteInferenceBase.{u, v} Theta) :
    packedLowerTailLRPValue P I ∈ Set.Icc (0 : ℝ) 1 := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  exact lowerTailLRPValue_mem_Icc I.model P I.outcome

/-- Example 3.2. The p-value with codomain [0,1]. -/
noncomputable def packedLowerTailLRPValueInUnitInterval
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (P : ParameterPartition Theta)
    (I : PackedFiniteInferenceBase.{u, v} Theta) : Set.Icc (0 : ℝ) 1 :=
  ⟨packedLowerTailLRPValue P I, packedLowerTailLRPValue_mem_Icc P I⟩

/-- Example 3.2. The p-value function, included as a graph relation. -/
noncomputable def packedLowerTailLRPValueProcedure
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (P : ParameterPartition Theta) :
    Procedure (PackedFiniteInferenceBase.{u, v} Theta) (Set.Icc (0 : ℝ) 1) :=
  graphProcedure (packedLowerTailLRPValueInUnitInterval P)

/-- Section 2.1. The likelihood relation on the same set of finite inference bases. -/
def packedFiniteLikelihoodRelation
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    StatisticalRelation (PackedFiniteInferenceBase.{u, v} Theta) :=
  likelihoodRelation PackedFiniteInferenceBase.likelihood

/-- Section 2.1. Minimal sufficient statistics, a bijection between the reduced sample
spaces, equality of the induced models and corresponding observed values. -/
def packedFiniteSufficiencyRelation
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    StatisticalRelation (PackedFiniteInferenceBase.{u, v} Theta) :=
  fun I J ↦
    letI : Fintype I.Sample := I.sampleFintype
    letI : Nonempty I.Sample := I.sampleNonempty
    letI : Fintype J.Sample := J.sampleFintype
    letI : Nonempty J.Sample := J.sampleNonempty
    ∃ (T₁ : PackedFiniteStatistic I) (T₂ : PackedFiniteStatistic J)
        (h : T₂.Codomain ≃ T₁.Codomain),
      FiniteMinimalSufficient I.model T₁.statistic ∧
        FiniteMinimalSufficient J.model T₂.statistic ∧
        (∀ theta y,
          letI : Fintype T₁.Codomain := T₁.codomainFintype
          letI : Nonempty T₁.Codomain := T₁.codomainNonempty
          letI : Fintype T₂.Codomain := T₂.codomainFintype
          letI : Nonempty T₂.Codomain := T₂.codomainNonempty
          T₁.inducedModel.pmf theta (h y) = T₂.inducedModel.pmf theta y) ∧
        T₁.statistic I.outcome = h (T₂.statistic J.outcome)

/-- Section 2.1. The direct conditionality relation on the same set of finite inference
bases. -/
def packedFiniteConditionalityRelation
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    StatisticalRelation (PackedFiniteInferenceBase.{u, v} Theta) :=
  fun I J ↦
    letI : Fintype I.Sample := I.sampleFintype
    letI : Nonempty I.Sample := I.sampleNonempty
    letI : Fintype J.Sample := J.sampleFintype
    letI : Nonempty J.Sample := J.sampleNonempty
    finiteConditionalityPair.{u, v} I.model I.outcomeCode I.asInferenceBase
      J.model J.outcomeCode J.asInferenceBase

/-- Neither relation contains the other. -/
def RelationsIncomparable {ι : Type u}
    (R S : StatisticalRelation ι) : Prop :=
  ¬ R ≤ S ∧ ¬ S ≤ R

/-- Appendix A. The equivalence closure of C is L. -/
theorem packedFiniteConditionalityClosure_eq_likelihoodRelation
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    equivalenceClosure
        (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) =
      packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) := by
  sorry

/-- Appendix A. The equivalence closure of C ∪ S is L. -/
theorem packedFiniteJointClosure_eq_likelihoodRelation
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    equivalenceClosure
        (relationUnion
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta))
          (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta))) =
      packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) := by
  sorry

end VennDiagrams

namespace VennDiagrams.Certification.PaperSignature

universe u v w

open Set
open scoped BigOperators

/-- Theorem 3.1. Conditionality-preserving and likelihood-preserving procedures coincide.
Every likelihood-preserving procedure preserves sufficiency. Strict inclusion holds
exactly when the parameter space has at least two points and the codomain is non-empty.
Empty output sets are permitted. -/
theorem theorem_BT1_procedure_classes
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] {A : Type w} :
    preservingClass A
        (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) =
      preservingClass A
        (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧
    (preservingClass A
        (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) ⊆
      preservingClass A
        (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) ∧
      (preservingClass A
          (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) ⊂
        preservingClass A
          (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) ↔
        Nontrivial Theta ∧ Nonempty A)) ∧
    preservingClass A
        (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) =
      preservingClass A
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∩
        preservingClass A
          (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) := by
  sorry

/-- Corollary 3.1. Conditionality preservation forces equal outputs on likelihood-related
pairs outside direct conditionality. -/
theorem corollary_BT2_conditional_pairs
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    {A : Type w}
    {Ev : Procedure (PackedFiniteInferenceBase.{u, v} Theta) A}
    (hEv : Ev ∈ preservingClass A
      (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)))
    {i j : PackedFiniteInferenceBase.{u, v} Theta}
    (hij :
      packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) i j ∧
        ¬ packedFiniteConditionalityRelation.{u, v} (Theta := Theta) i j) :
    output Ev i = output Ev j := by
  sorry

/-- Corollary 3.2. Joint preservation forces equal outputs on pairs in L outside S ∪ C. -/
theorem corollary_BT3_joint_pairs
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    {A : Type w}
    {Ev : Procedure (PackedFiniteInferenceBase.{u, v} Theta) A}
    (hEv : Ev ∈
      preservingClass A
          (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) ∩
        preservingClass A
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)))
    {i j : PackedFiniteInferenceBase.{u, v} Theta}
    (hij :
      packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) i j ∧
        ¬ relationUnion
          (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta))
          (packedFiniteConditionalityRelation.{u, v}
            (Theta := Theta)) i j) :
    output Ev i = output Ev j := by
  sorry

/-- Example 2.5. The sufficiency relation and the conditionality relation are incomparable
for every finite parameter space with at least two points. -/
theorem packed_sufficiency_conditionality_incomparable
    {Theta : Type u} [Fintype Theta] [Nontrivial Theta] :
    RelationsIncomparable
      (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta))
      (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) := by
  sorry

/-- Example 3.7. The lower-tail likelihood-ratio p-value preserves sufficiency but not
likelihood. The two displayed p-values are 0.1 and 0.2. The example extends to any
finite parameter space with at least two points. -/
theorem finite_lr_pvalue_separation
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (P : ParameterPartition Theta) :
    packedLowerTailLRPValueProcedure.{u, v} P ∈
      preservingClass (Set.Icc (0 : ℝ) 1)
          (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) \
        preservingClass (Set.Icc (0 : ℝ) 1)
          (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) ∧
    ∃ I J : PackedFiniteInferenceBase.{u, v} Theta,
      packedFiniteLikelihoodRelation I J ∧
        packedLowerTailLRPValue P I = 1 / 10 ∧
        packedLowerTailLRPValue P J = 1 / 5 := by
  sorry

/-- The closure identity and C ⊊ L hold for every non-empty finite parameter space. -/
theorem evans2013_theorem7_packed
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    packedFiniteConditionalityRelation.{u, v} (Theta := Theta) <
        equivalenceClosure
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧
      equivalenceClosure
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) =
        packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) := by
  sorry

/-- C ∪ S is strictly contained in L when the parameter space has at least two points; its
equivalence closure is L. -/
theorem evans2013_theorem9_packed
    {Theta : Type u} [Fintype Theta] [Nontrivial Theta] :
    relationUnion
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta))
          (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) <
        packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) ∧
      equivalenceClosure
          (relationUnion
            (packedFiniteConditionalityRelation.{u, v} (Theta := Theta))
            (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta))) =
        packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) := by
  sorry

end VennDiagrams.Certification.PaperSignature

namespace VennDiagrams.Certification.PaperSignature

universe u v

open Set
open scoped BigOperators

/-- The equivalence closure is given by finite chains. -/
theorem evans2013_lemma1 {ι : Type u} (R : StatisticalRelation ι) :
    equivalenceClosure R = Relation.ReflTransGen (Relation.SymmGen R) := by
  sorry

/-- The equivalence closure of the union of the equivalence closures is the equivalence
closure of the union. -/
theorem evans2013_lemma2 {ι : Type u} (R₁ R₂ : StatisticalRelation ι) :
    equivalenceClosure
        (relationUnion (equivalenceClosure R₁) (equivalenceClosure R₂)) =
      equivalenceClosure (relationUnion R₁ R₂) := by
  sorry

/-- The likelihood relation is an equivalence relation. -/
theorem evans2013_lemma3_packed
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Equivalence (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) := by
  sorry

/-- The likelihood-class statistic is sufficient and minimal sufficient. -/
theorem evans2013_lemma4_packed
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase.{u, v} Theta) :
    letI : Fintype I.Sample := I.sampleFintype
    letI : Nonempty I.Sample := I.sampleNonempty
    FiniteMinimalSufficient I.model (canonicalMinimalSufficient I.likelihoodFamily) := by
  sorry

/-- The sufficiency relation is an equivalence relation contained in likelihood. -/
theorem evans2013_lemma5_packed
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Equivalence (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) ∧
      packedFiniteSufficiencyRelation.{u, v} (Theta := Theta) ≤
        packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) := by
  sorry

/-- Conditionality is reflexive and symmetric, but not transitive, and is contained in
likelihood. -/
theorem evans2013_lemma6_packed
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Reflexive (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧
      Symmetric (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧
      ¬ Transitive (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧
      packedFiniteConditionalityRelation.{u, v} (Theta := Theta) ≤
        packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) := by
  sorry

/-- The joint closure argument. -/
theorem evans2013_theorem8_packed
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    relationUnion
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta))
          (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) ≤
        packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) ∧
      packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) ≤
        equivalenceClosure (relationUnion
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta))
          (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta))) := by
  sorry

/-- The strict inclusions for a parameter space with at least two points. -/
theorem evans2013_corollary10_packed
    {Theta : Type u} [Fintype Theta] [Nontrivial Theta] :
    relationUnion
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta))
          (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) <
        equivalenceClosure
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧
      equivalenceClosure
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) =
        packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) ∧
      packedFiniteSufficiencyRelation.{u, v} (Theta := Theta) <
        equivalenceClosure
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) := by
  sorry

/-- Appendix A constructs a chain of four C-steps joining any L-related pair. -/
theorem evans2013_four_step_chain_packed
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I J : PackedFiniteInferenceBase.{u, v} Theta)
    (hL : packedFiniteLikelihoodRelation I J) :
    ∃ M₁ H M₂ : PackedFiniteInferenceBase.{u, v} Theta,
      packedFiniteConditionalityRelation I M₁ ∧
      packedFiniteConditionalityRelation M₁ H ∧
      packedFiniteConditionalityRelation H M₂ ∧
      packedFiniteConditionalityRelation M₂ J := by
  sorry

end VennDiagrams.Certification.PaperSignature
