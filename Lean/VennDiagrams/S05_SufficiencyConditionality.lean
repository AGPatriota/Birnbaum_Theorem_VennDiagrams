import VennDiagrams.S01_Relations
import VennDiagrams.S03_LikelihoodProcedures
import VennDiagrams.S04_StatisticalPrimitives
import Mathlib

/-!
# S05 — Sufficiency and conditionality

This module isolates the structural claims about the sufficiency and
conditionality relations.  The canonical minimal-sufficient statistic is the
quotient by positive likelihood proportionality.  Conditionality is kept
directional until an explicit reflexive symmetric closure is taken, so the
hypotheses needed to place it inside the likelihood relation remain visible.

The packed section formalizes Evans's finite auxiliary-experiment argument:
the equivalence closure of conditionality is the likelihood relation,
sufficiency is contained in likelihood, and adjoining sufficiency does not
enlarge that closure.

The final sections prove the finite Neyman--Fisher factorization theorem,
identify the likelihood-class statistic as genuinely sufficient and minimal
sufficient on an effective sample space, and derive the likelihood-ratio
lower-tail reduction rather than accepting it as an external interface.
-/

open Set Finset
open scoped BigOperators

namespace VennDiagrams

universe u v w z

/-! ## The canonical likelihood-class statistic -/

/-- The setoid whose classes are the positive-proportionality classes of the
observed likelihood vectors. -/
def likelihoodProportionalitySetoid {X : Type u} {Θ : Type v}
    (likelihood : X → Θ → ℝ) : Setoid X where
  r x y := Proportional (likelihood x) (likelihood y)
  iseqv := likelihoodRelation_isEquivalence likelihood

/-- The canonical statistic that sends an outcome to its positive
likelihood-proportionality class. -/
def canonicalMinimalSufficient {X : Type u} {Θ : Type v}
    (likelihood : X → Θ → ℝ) (x : X) :
    Quotient (likelihoodProportionalitySetoid likelihood) :=
  Quotient.mk _ x

/-- The likelihood-fiber criterion: two observations have the same statistic
value exactly when their likelihood functions are positively proportional.
This criterion is proved below to characterize genuine minimal sufficiency
for finite models whose ambient sample space is its effective support. -/
def LikelihoodFiberCriterion {X : Type u} {Θ : Type v} {A : Type w}
    (likelihood : X → Θ → ℝ) (T : X → A) : Prop :=
  ∀ x y, T x = T y ↔ Proportional (likelihood x) (likelihood y)

/-- Backwards-compatible name for `LikelihoodFiberCriterion`.  Unlike the
genuine finite notion `FiniteMinimalSufficient` below, this abbreviation by
itself states only the pointwise likelihood-fiber criterion. -/
abbrev IsLikelihoodMinimalSufficient {X : Type u} {Θ : Type v} {A : Type w}
    (likelihood : X → Θ → ℝ) (T : X → A) : Prop :=
  LikelihoodFiberCriterion likelihood T

/-- Exact fiber characterization of the canonical minimal-sufficient
statistic. -/
@[simp] theorem canonicalMinimalSufficient_eq_iff
    {X : Type u} {Θ : Type v} (likelihood : X → Θ → ℝ) (x y : X) :
    canonicalMinimalSufficient likelihood x =
        canonicalMinimalSufficient likelihood y ↔
      Proportional (likelihood x) (likelihood y) := by
  exact Quotient.eq

/-- The quotient statistic satisfies the likelihood-fiber criterion by
construction. -/
theorem canonicalMinimalSufficient_isLikelihoodMinimalSufficient
    {X : Type u} {Θ : Type v} (likelihood : X → Θ → ℝ) :
    IsLikelihoodMinimalSufficient likelihood
      (canonicalMinimalSufficient likelihood) := by
  intro x y
  exact canonicalMinimalSufficient_eq_iff likelihood x y

/-- Compatibility form of the exact likelihood-fiber criterion. -/
theorem isLikelihoodMinimalSufficient_iff
    {X : Type u} {Θ : Type v} {A : Type w}
    (likelihood : X → Θ → ℝ) (T : X → A) :
    IsLikelihoodMinimalSufficient likelihood T ↔
      ∀ x y, T x = T y ↔ Proportional (likelihood x) (likelihood y) :=
  Iff.rfl

/-- An injective relabelling of the canonical quotient has exactly the same
fibers, and hence satisfies the same likelihood-fiber criterion. -/
theorem injective_relabel_canonicalMinimalSufficient
    {X : Type u} {Θ : Type v} {A : Type w}
    (likelihood : X → Θ → ℝ)
    (relabel : Quotient (likelihoodProportionalitySetoid likelihood) → A)
    (hrelabel : Function.Injective relabel) :
    IsLikelihoodMinimalSufficient likelihood
      (relabel ∘ canonicalMinimalSufficient likelihood) := by
  intro x y
  rw [Function.comp_apply, Function.comp_apply, hrelabel.eq_iff]
  exact canonicalMinimalSufficient_eq_iff likelihood x y

/-! ## Genuine finite sufficiency and minimal sufficiency

The definitions and proof architecture in this section are the finite,
pointwise specialization of Cavalcante--Patriota's version-robust treatment
of sufficiency and minimal sufficiency.  They are re-proved here for
`FiniteModel`; the companion has no dependency on the reference project.
-/

/-- A statistic is sufficient for a finite model when its conditional mass
inside each statistic fiber is independent of the parameter. -/
def FiniteSufficient
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y) : Prop :=
  ∃ q : X → ℝ,
    ∀ theta x, E.pmf theta x = inducedPMF E T theta (T x) * q x

/-- Pointwise finite Neyman--Fisher factorization.  The parameter-free factor
is strictly positive on the effective sample space used by the paper. -/
def StrictFiniteFactorization
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y) : Prop :=
  ∃ (g : Theta → Y → ℝ) (h : X → ℝ),
    (∀ x, 0 < h x) ∧
      ∀ theta x, E.pmf theta x = g theta (T x) * h x

/-- Genuine finite minimal sufficiency: `T` is sufficient and factors through
every other sufficient statistic on the same model. -/
def FiniteMinimalSufficient
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y) : Prop :=
  FiniteSufficient E T ∧
    ∀ {Z : Type w} (S : X → Z), FiniteSufficient E S →
      ∃ f : Z → Y, ∀ x, T x = f (S x)

/-- Sum of a parameter-free factor over one statistic fiber. -/
noncomputable def finiteFiberWeight
    {X : Type v} {Y : Type w} [Fintype X]
    (T : X → Y) (h : X → ℝ) (y : Y) : ℝ := by
  classical
  exact ∑ x ∈ Finset.univ.filter (fun x ↦ T x = y), h x

/-- Under a pointwise factorization, each induced mass is the
parameter-dependent factor times the total parameter-free fiber weight. -/
theorem inducedPMF_eq_factorization
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y)
    (g : Theta → Y → ℝ) (h : X → ℝ)
    (hfactor : ∀ theta x, E.pmf theta x = g theta (T x) * h x)
    (theta : Theta) (y : Y) :
    inducedPMF E T theta y = g theta y * finiteFiberWeight T h y := by
  classical
  unfold inducedPMF finiteFiberWeight
  calc
    (∑ x ∈ Finset.univ.filter (fun x ↦ T x = y), E.pmf theta x) =
        ∑ x ∈ Finset.univ.filter (fun x ↦ T x = y),
          g theta y * h x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hfactor, (Finset.mem_filter.mp hx).2]
    _ = g theta y *
        ∑ x ∈ Finset.univ.filter (fun x ↦ T x = y), h x := by
      rw [Finset.mul_sum]

/-- A sum of strictly positive factors is positive on every inhabited fiber. -/
theorem finiteFiberWeight_pos_at
    {X : Type v} {Y : Type w} [Fintype X]
    (T : X → Y) (h : X → ℝ) (hpos : ∀ x, 0 < h x) (x : X) :
    0 < finiteFiberWeight T h (T x) := by
  classical
  unfold finiteFiberWeight
  apply Finset.sum_pos'
  · intro y hy
    exact le_of_lt (hpos y)
  · refine ⟨x, ?_, hpos x⟩
    simp

/-- The finite factorization theorem, forward direction. -/
theorem strictFiniteFactorization_implies_sufficient
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y)
    (hF : StrictFiniteFactorization E T) :
    FiniteSufficient E T := by
  rcases hF with ⟨g, h, hpos, hfactor⟩
  refine ⟨fun x ↦ h x / finiteFiberWeight T h (T x), ?_⟩
  intro theta x
  rw [hfactor, inducedPMF_eq_factorization E T g h hfactor]
  have hweight : finiteFiberWeight T h (T x) ≠ 0 :=
    ne_of_gt (finiteFiberWeight_pos_at T h hpos x)
  field_simp

/-- On an effective sample space, finite sufficiency supplies a strictly
positive parameter-free Neyman--Fisher factor. -/
theorem sufficient_implies_strictFiniteFactorization
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E)
    (hS : FiniteSufficient E T) :
    StrictFiniteFactorization E T := by
  rcases hS with ⟨q, hq⟩
  have hqpos : ∀ x, 0 < q x := by
    intro x
    rcases hall x with ⟨theta, htheta⟩
    rw [hq theta x] at htheta
    have hinduced : 0 ≤ inducedPMF E T theta (T x) :=
      inducedPMF_nonneg E T theta (T x)
    nlinarith
  exact ⟨fun theta y ↦ inducedPMF E T theta y, q, hqpos, hq⟩

/-- Finite Neyman--Fisher factorization theorem on the effective sample
space used throughout the packed development. -/
theorem finite_neyman_fisher_factorization
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E) :
    FiniteSufficient E T ↔ StrictFiniteFactorization E T := by
  exact ⟨sufficient_implies_strictFiniteFactorization E T hall,
    strictFiniteFactorization_implies_sufficient E T⟩

/-- A chosen representative of a statistic value, with a harmless default
outside the statistic's range. -/
noncomputable def finiteStatisticRepresentative
    {X : Type v} {Y : Type w} [Nonempty X] (T : X → Y) (y : Y) : X := by
  classical
  exact if h : ∃ x, T x = y then Classical.choose h
    else Classical.choice inferInstance

theorem finiteStatisticRepresentative_spec
    {X : Type v} {Y : Type w} [Nonempty X] (T : X → Y) (x : X) :
    T (finiteStatisticRepresentative T (T x)) = T x := by
  classical
  have hex : ∃ z : X, T z = T x := ⟨x, rfl⟩
  simp only [finiteStatisticRepresentative, dif_pos hex]
  exact Classical.choose_spec hex

/-- Exact likelihood fibers give a strictly positive finite factorization. -/
theorem likelihoodFiberCriterion_implies_strictFiniteFactorization
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y)
    (hT : LikelihoodFiberCriterion (fun x theta ↦ E.pmf theta x) T) :
    StrictFiniteFactorization E T := by
  have hprop : ∀ x, Proportional (fun theta ↦ E.pmf theta x)
      (fun theta ↦ E.pmf theta (finiteStatisticRepresentative T (T x))) := by
    intro x
    apply (hT x (finiteStatisticRepresentative T (T x))).mp
    exact (finiteStatisticRepresentative_spec T x).symm
  choose k hk using hprop
  refine ⟨fun theta y ↦ E.pmf theta (finiteStatisticRepresentative T y),
    k, fun x ↦ (hk x).1, ?_⟩
  intro theta x
  simpa [mul_comm] using (hk x).2 theta

/-- The likelihood-fiber criterion implies genuine finite sufficiency. -/
theorem likelihoodFiberCriterion_implies_finiteSufficient
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y)
    (hT : LikelihoodFiberCriterion (fun x theta ↦ E.pmf theta x) T) :
    FiniteSufficient E T :=
  strictFiniteFactorization_implies_sufficient E T
    (likelihoodFiberCriterion_implies_strictFiniteFactorization E T hT)

/-- Every fiber of a sufficient statistic consists of proportional
likelihoods on an effective sample space. -/
theorem sufficient_fiber_implies_proportional
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E)
    (hS : FiniteSufficient E T) {x y : X} (hxy : T x = T y) :
    Proportional (fun theta ↦ E.pmf theta x)
      (fun theta ↦ E.pmf theta y) := by
  rcases hS with ⟨q, hq⟩
  have hqpos : ∀ z, 0 < q z := by
    intro z
    rcases hall z with ⟨theta, htheta⟩
    rw [hq theta z] at htheta
    have hinduced : 0 ≤ inducedPMF E T theta (T z) :=
      inducedPMF_nonneg E T theta (T z)
    nlinarith
  refine ⟨q x / q y, div_pos (hqpos x) (hqpos y), ?_⟩
  intro theta
  change E.pmf theta x = q x / q y * E.pmf theta y
  rw [hq theta x, hq theta y, hxy]
  field_simp [ne_of_gt (hqpos y)]

noncomputable def finiteMinimalFactorMap
    {X : Type v} {Y Z : Type w} [Nonempty X]
    (T : X → Y) (S : X → Z) (z : Z) : Y :=
  T (finiteStatisticRepresentative S z)

theorem finiteMinimalFactorMap_spec
    {X : Type v} {Y Z : Type w} [Nonempty X]
    (T : X → Y) (S : X → Z)
    (hfib : ∀ {x y}, S x = S y → T x = T y) (x : X) :
    T x = finiteMinimalFactorMap T S (S x) := by
  unfold finiteMinimalFactorMap
  apply hfib
  exact (finiteStatisticRepresentative_spec S x).symm

/-- The likelihood-fiber criterion gives genuine finite minimal sufficiency
on an effective sample space. -/
theorem likelihoodFiberCriterion_implies_finiteMinimalSufficient
    {Theta : Type u} {X : Type v} {Y : Type w}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E)
    (hT : LikelihoodFiberCriterion (fun x theta ↦ E.pmf theta x) T) :
    FiniteMinimalSufficient E T := by
  refine ⟨likelihoodFiberCriterion_implies_finiteSufficient E T hT, ?_⟩
  intro Z S hS
  have hfib : ∀ {x y}, S x = S y → T x = T y := by
    intro x y hxy
    apply (hT x y).mpr
    exact sufficient_fiber_implies_proportional E S hall hS hxy
  exact ⟨finiteMinimalFactorMap T S, finiteMinimalFactorMap_spec T S hfib⟩

/-- Genuine finite minimal sufficiency implies the likelihood-fiber
criterion on an effective sample space. -/
theorem finiteMinimalSufficient_implies_likelihoodFiberCriterion
    {Theta : Type u} {X Y : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E)
    (hT : FiniteMinimalSufficient E T) :
    LikelihoodFiberCriterion (fun x theta ↦ E.pmf theta x) T := by
  intro x y
  constructor
  · intro hxy
    exact sufficient_fiber_implies_proportional E T hall hT.1 hxy
  · intro hxy
    have hCanonicalSufficient : FiniteSufficient E
        (canonicalMinimalSufficient (fun x theta ↦ E.pmf theta x)) :=
      likelihoodFiberCriterion_implies_finiteSufficient E _
        (canonicalMinimalSufficient_isLikelihoodMinimalSufficient
          (fun x theta ↦ E.pmf theta x))
    rcases hT.2 (canonicalMinimalSufficient
        (fun x theta ↦ E.pmf theta x)) hCanonicalSufficient with ⟨f, hf⟩
    rw [hf x, hf y]
    congr 1
    exact (canonicalMinimalSufficient_eq_iff
      (fun x theta ↦ E.pmf theta x) x y).mpr hxy

/-- In finite effective-support models, genuine minimal sufficiency is
equivalent to the likelihood-fiber criterion.  The effective-support
qualification is essential; no unrestricted density-version claim is made. -/
theorem finite_minimal_sufficiency_iff_likelihoodFiberCriterion
    {Theta : Type u} {X Y : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E) :
    FiniteMinimalSufficient E T ↔
      LikelihoodFiberCriterion (fun x theta ↦ E.pmf theta x) T := by
  exact ⟨finiteMinimalSufficient_implies_likelihoodFiberCriterion E T hall,
    likelihoodFiberCriterion_implies_finiteMinimalSufficient E T hall⟩

/-- The canonical likelihood-class statistic is genuinely finite minimal
sufficient on an effective sample space. -/
theorem canonicalMinimalSufficient_isFiniteMinimalSufficient
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (hall : ∀ x, x ∈ effectiveSupport E) :
    FiniteMinimalSufficient E
      (canonicalMinimalSufficient (fun x theta ↦ E.pmf theta x)) := by
  apply (finite_minimal_sufficiency_iff_likelihoodFiberCriterion E _ hall).mpr
  exact canonicalMinimalSufficient_isLikelihoodMinimalSufficient _

/-- Every injective relabelling of the canonical likelihood-class statistic
is genuinely finite minimal sufficient on an effective sample space. -/
theorem injective_relabel_canonicalMinimalSufficient_isFiniteMinimalSufficient
    {Theta : Type u} {X : Type v} {A : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (hall : ∀ x, x ∈ effectiveSupport E)
    (relabel : Quotient (likelihoodProportionalitySetoid
      (fun x theta ↦ E.pmf theta x)) → A)
    (hrelabel : Function.Injective relabel) :
    FiniteMinimalSufficient E
      (relabel ∘ canonicalMinimalSufficient
        (fun x theta ↦ E.pmf theta x)) := by
  apply (finite_minimal_sufficiency_iff_likelihoodFiberCriterion E _ hall).mpr
  exact injective_relabel_canonicalMinimalSufficient _ relabel hrelabel

/-! ## Exact finite pair definitions used by the paper -/

/-- Exact finite, heterogeneous version of the paper's sufficiency relation.
Two effective inference bases are related when they admit genuinely finite
minimal sufficient statistics whose induced mass functions agree through a bijection,
and the two observed statistic values correspond through that bijection. -/
def finiteSufficiencyPair
    {Θ : Type u} {X₁ : Type v} {X₂ : Type w}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X₁] [Nonempty X₁] [Fintype X₂] [Nonempty X₂]
    (E₁ : FiniteModel Θ X₁) (x₁ : InferenceBase E₁)
    (E₂ : FiniteModel Θ X₂) (x₂ : InferenceBase E₂) : Prop :=
  ∃ (Y₁ : Type z) (Y₂ : Type z) (T₁ : X₁ → Y₁) (T₂ : X₂ → Y₂)
      (h : Y₂ ≃ Y₁),
    FiniteMinimalSufficient E₁ T₁ ∧
      FiniteMinimalSufficient E₂ T₂ ∧
      Function.Surjective T₁ ∧ Function.Surjective T₂ ∧
      (∀ θ y, inducedPMF E₁ T₁ θ (h y) = inducedPMF E₂ T₂ θ y) ∧
      T₁ x₁.1 = h (T₂ x₂.1)

/-- A type-correct directional instance of the paper's conditioning clause.
The map `embed` preserves the stored injective outcome code in the ordinary
case, or it parametrizes the observed fiber of a nontrivial surjective
ancillary selector; in either case its image is exactly that fiber. -/
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

/-- Exact symmetric finite version of the paper's conditionality relation:
one base is the ancillary conditional model of the other, with the observed
values matched by the ordinary or selector-tag identification. -/
def finiteConditionalityPair
    {Θ : Type u} {X₁ X₂ : Type v}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X₁] [Nonempty X₁] [Fintype X₂] [Nonempty X₂]
    (E₁ : FiniteModel Θ X₁) (code₁ : X₁ → Nat) (x₁ : InferenceBase E₁)
    (E₂ : FiniteModel Θ X₂) (code₂ : X₂ → Nat) (x₂ : InferenceBase E₂) : Prop :=
  finiteDirectionalConditionalityPair.{u, v} E₁ code₁ x₁ E₂ code₂ x₂ ∨
    finiteDirectionalConditionalityPair.{u, v} E₂ code₂ x₂ E₁ code₁ x₁

/-- Ancillarity makes the conditioning-event probability parameter-free;
positivity then turns the conditional-model identity into the paper's common
positive likelihood factor. -/
theorem finiteDirectionalConditionalityPair_implies_proportional
    {Theta : Type u} {X₁ X₂ : Type v}
    [Fintype Theta] [Nonempty Theta]
    [Fintype X₁] [Nonempty X₁] [Fintype X₂] [Nonempty X₂]
    {E₁ : FiniteModel Theta X₁} {x₁ : InferenceBase E₁}
    {E₂ : FiniteModel Theta X₂} {x₂ : InferenceBase E₂}
    {code₁ : X₁ → Nat} {code₂ : X₂ → Nat}
    (hC : finiteDirectionalConditionalityPair.{u, v}
      E₁ code₁ x₁ E₂ code₂ x₂) :
    Proportional (fun theta ↦ E₁.pmf theta x₁.1)
      (fun theta ↦ E₂.pmf theta x₂.1) := by
  rcases hC with ⟨A₀, A, embed, hancillary, hpositive, _hinjective,
    _hidentification, _hfiber, hobserved, hconditional⟩
  let theta₀ : Theta := Classical.choice inferInstance
  let q := inducedPMF E₁ A theta₀ (A x₁.1)
  have hq : 0 < q := hpositive theta₀
  refine ⟨q, hq, ?_⟩
  intro theta
  change E₁.pmf theta x₁.1 = q * E₂.pmf theta x₂.1
  have hden : inducedPMF E₁ A theta (A x₁.1) = q :=
    hancillary theta theta₀ (A x₁.1)
  rw [hconditional theta x₂.1, hden]
  rw [← hobserved]
  field_simp [ne_of_gt hq]

/-- When the two finite models use the same injective outcome code, a
directional conditionality step can match only the same observed value.  The
ordinary branch preserves that code; in the selector branch, an injective
self-map covers the whole finite sample space, contradicting a nontrivial
surjective selector unless its observed fiber is the whole space. -/
theorem finiteDirectionalConditionalityPair_same_code_observation_eq
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    {E₁ E₂ : FiniteModel Theta X}
    {code : X → Nat} (hcode : Function.Injective code)
    {x₁ : InferenceBase E₁} {x₂ : InferenceBase E₂}
    (hC : finiteDirectionalConditionalityPair
      E₁ code x₁ E₂ code x₂) :
    x₁.1 = x₂.1 := by
  rcases hC with ⟨A₀, A, embed, _hancillary, _hpositive, hinjective,
    hidentification, hfiber, hobserved, _hconditional⟩
  rcases hidentification with hordinary | hselector
  · apply hcode
    rw [← hordinary x₂.1, hobserved]
  · rcases hselector with ⟨hnontrivial, hsurjectiveA⟩
    letI : Nontrivial A₀ := hnontrivial
    have hsurjectiveEmbed : Function.Surjective embed :=
      (Finite.injective_iff_surjective).mp hinjective
    obtain ⟨a, ha⟩ := exists_ne (A x₁.1)
    obtain ⟨y, hy⟩ := hsurjectiveA a
    obtain ⟨z, hz⟩ := hsurjectiveEmbed y
    have hAy : A y = A x₁.1 := (hfiber y).2 ⟨z, hz⟩
    exact False.elim (ha (hy ▸ hAy))

/-! ## One heterogeneous universe of finite inference bases -/

/-- A type-correct package for a finite inference base whose sample type may
vary while the finite parameter type remains fixed.  The injective natural
code retains literal outcome identity across effective-support subtypes. This
supplies the single universe on which the paper's global relations `L`, `S`,
and `C` live. -/
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

/-- The observed likelihood carried by a packed inference base. -/
def PackedFiniteInferenceBase.likelihood
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase Theta) : Theta → ℝ :=
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  fun theta ↦ I.model.pmf theta I.outcome

/-- The complete likelihood family carried by a packed experiment. -/
def PackedFiniteInferenceBase.likelihoodFamily
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase Theta) : I.Sample → Theta → ℝ :=
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  fun x theta ↦ I.model.pmf theta x

/-- Forget the package while retaining the certified effective outcome. -/
def PackedFiniteInferenceBase.asInferenceBase
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase Theta) :
    letI : Fintype I.Sample := I.sampleFintype
    letI : Nonempty I.Sample := I.sampleNonempty
    InferenceBase I.model := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  exact ⟨I.outcome, I.outcome_effective⟩

/-- A finite statistic on one packed experiment, including the finite
nonempty codomain needed for its induced experiment. -/
structure PackedFiniteStatistic
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase.{u, v} Theta) where
  Codomain : Type v
  codomainFintype : Fintype Codomain
  codomainNonempty : Nonempty Codomain
  statistic : I.Sample → Codomain
  statistic_surjective : Function.Surjective statistic

/-- The canonical likelihood-class statistic, bundled with its exact finite
image as codomain. -/
noncomputable def packedCanonicalMinimalSufficientStatistic
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase.{u, v} Theta) : PackedFiniteStatistic I where
  Codomain := Quotient (likelihoodProportionalitySetoid I.likelihoodFamily)
  codomainFintype := by
    letI : Fintype I.Sample := I.sampleFintype
    classical
    exact Fintype.ofSurjective
      (canonicalMinimalSufficient I.likelihoodFamily) Quotient.mk_surjective
  codomainNonempty :=
    ⟨canonicalMinimalSufficient I.likelihoodFamily
      (Classical.choice I.sampleNonempty)⟩
  statistic := canonicalMinimalSufficient I.likelihoodFamily
  statistic_surjective := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    exact ⟨x, rfl⟩

/-- The experiment induced by a packed finite statistic. -/
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

/-- The lower-tail LR p-value on the experiment induced by `T`. -/
noncomputable def PackedFiniteStatistic.reducedPValue
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    {I : PackedFiniteInferenceBase.{u, v} Theta}
    (T : PackedFiniteStatistic I) (P : ParameterPartition Theta) : ℝ := by
  letI : Fintype T.Codomain := T.codomainFintype
  letI : Nonempty T.Codomain := T.codomainNonempty
  exact lowerTailLRPValue T.inducedModel P (T.statistic I.outcome)

/-- The paper's lower-tail LR p-value evaluated on a packed inference base. -/
noncomputable def packedLowerTailLRPValue
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (P : ParameterPartition Theta)
    (I : PackedFiniteInferenceBase.{u, v} Theta) : ℝ := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  exact lowerTailLRPValue I.model P I.outcome

/-- The packed LR p-value has the paper's exact codomain `[0,1]`. -/
theorem packedLowerTailLRPValue_mem_Icc
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (P : ParameterPartition Theta)
    (I : PackedFiniteInferenceBase.{u, v} Theta) :
    packedLowerTailLRPValue P I ∈ Set.Icc (0 : ℝ) 1 := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  exact lowerTailLRPValue_mem_Icc I.model P I.outcome

/-- The LR p-value bundled with its certified unit-interval range. -/
noncomputable def packedLowerTailLRPValueInUnitInterval
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (P : ParameterPartition Theta)
    (I : PackedFiniteInferenceBase.{u, v} Theta) : Set.Icc (0 : ℝ) 1 :=
  ⟨packedLowerTailLRPValue P I, packedLowerTailLRPValue_mem_Icc P I⟩

/-- One global relation-valued LR p-value procedure over heterogeneous finite
experiments with a common parameter space and null partition. -/
noncomputable def packedLowerTailLRPValueProcedure
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (P : ParameterPartition Theta) :
    Procedure (PackedFiniteInferenceBase.{u, v} Theta) (Set.Icc (0 : ℝ) 1) :=
  graphProcedure (packedLowerTailLRPValueInUnitInterval P)

/-- Exact global likelihood relation on packed finite inference bases. -/
def packedFiniteLikelihoodRelation
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    StatisticalRelation (PackedFiniteInferenceBase.{u, v} Theta) :=
  likelihoodRelation PackedFiniteInferenceBase.likelihood

/-! ## Procedures on the common inference-base universe -/

/-- Posterior probability with exactly the paper's `[0,1]` codomain and
positive-normalizer hypothesis, allowing the sample space to vary. -/
noncomputable def packedPosteriorProbability
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (prior : Theta → ℝ) (hprior : ∀ theta, 0 ≤ prior theta)
    (hden : ∀ I : PackedFiniteInferenceBase.{u, v} Theta,
      0 < posteriorNormalizer I.likelihood prior)
    (H : Finset Theta) (I : PackedFiniteInferenceBase.{u, v} Theta) :
    Set.Icc (0 : ℝ) 1 := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  exact ⟨posteriorProbability I.likelihood prior H,
    posteriorProbability_mem_Icc_of_nonnegative_prior
      I.model prior hprior I.outcome (hden I) H⟩

@[simp] theorem packedPosteriorProbability_val
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (prior : Theta → ℝ) (hprior : ∀ theta, 0 ≤ prior theta)
    (hden : ∀ I : PackedFiniteInferenceBase.{u, v} Theta,
      0 < posteriorNormalizer I.likelihood prior)
    (H : Finset Theta) (I : PackedFiniteInferenceBase.{u, v} Theta) :
    (packedPosteriorProbability prior hprior hden H I).val =
      posteriorProbability I.likelihood prior H := rfl

/-- The posterior function, viewed as a relation on the common universe. -/
noncomputable def packedPosteriorProcedure
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (prior : Theta → ℝ) (hprior : ∀ theta, 0 ≤ prior theta)
    (hden : ∀ I : PackedFiniteInferenceBase.{u, v} Theta,
      0 < posteriorNormalizer I.likelihood prior) (H : Finset Theta) :
    Procedure (PackedFiniteInferenceBase.{u, v} Theta) (Set.Icc (0 : ℝ) 1) :=
  graphProcedure (packedPosteriorProbability prior hprior hden H)

theorem packedPosteriorProcedure_preserves_likelihood
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (prior : Theta → ℝ) (hprior : ∀ theta, 0 ≤ prior theta)
    (hden : ∀ I : PackedFiniteInferenceBase.{u, v} Theta,
      0 < posteriorNormalizer I.likelihood prior) (H : Finset Theta) :
    Preserves (packedPosteriorProcedure prior hprior hden H)
      packedFiniteLikelihoodRelation := by
  intro I J hIJ
  simp only [packedPosteriorProcedure, output_graphProcedure]
  congr 1
  apply Subtype.ext
  exact posteriorProbability_eq_of_proportional H hIJ (ne_of_gt (hden J))

theorem packedPosteriorProcedure_output_nonempty
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (prior : Theta → ℝ) (hprior : ∀ theta, 0 ≤ prior theta)
    (hden : ∀ I : PackedFiniteInferenceBase.{u, v} Theta,
      0 < posteriorNormalizer I.likelihood prior)
    (H : Finset Theta) (I : PackedFiniteInferenceBase.{u, v} Theta) :
    (output (packedPosteriorProcedure prior hprior hden H) I).Nonempty := by
  simp [packedPosteriorProcedure]

/-- A strictly positive prior supplies the denominator hypothesis for every
effective packed inference base, as asserted in the paper. -/
theorem packedPosteriorNormalizer_pos_of_positive_prior
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (prior : Theta → ℝ) (hprior : ∀ theta, 0 < prior theta)
    (I : PackedFiniteInferenceBase.{u, v} Theta) :
    0 < posteriorNormalizer I.likelihood prior := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  exact posteriorNormalizer_pos_of_positive_prior
    I.model prior hprior I.outcome_effective

/-- All realized UMVUE estimates, with each rule defined on the sample space
of its own experiment.  No existence of an unbiased estimator is assumed. -/
noncomputable def packedUMVUEOutput
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (parameter : Theta → ℝ) (I : PackedFiniteInferenceBase.{u, v} Theta) :
    Set ℝ := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  exact umvueOutput I.model parameter I.outcome

@[simp] theorem mem_packedUMVUEOutput_iff
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (parameter : Theta → ℝ) (I : PackedFiniteInferenceBase.{u, v} Theta) (r : ℝ) :
    r ∈ packedUMVUEOutput parameter I ↔
      (letI : Fintype I.Sample := I.sampleFintype
       letI : Nonempty I.Sample := I.sampleNonempty
       ∃ h : I.Sample → ℝ, IsUMVUE I.model parameter h ∧ r = h I.outcome) :=
  Iff.rfl

/-- Exactly the confidence relation in the paper, on heterogeneous packed
inference bases rather than on a single ambient sample type. -/
noncomputable def packedConfidenceProcedure
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] (alpha : ℝ) :
    Procedure (PackedFiniteInferenceBase.{u, v} Theta) (Set Theta) :=
  {p | letI : Fintype p.1.Sample := p.1.sampleFintype
       letI : Nonempty p.1.Sample := p.1.sampleNonempty
       ∃ CR : p.1.Sample → Set Theta,
         HasCoverage p.1.model alpha CR ∧ p.2 = CR p.1.outcome}

@[simp] theorem mem_output_packedConfidenceProcedure_iff
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (alpha : ℝ) (I : PackedFiniteInferenceBase.{u, v} Theta) (R : Set Theta) :
    R ∈ output (packedConfidenceProcedure alpha) I ↔
      (letI : Fintype I.Sample := I.sampleFintype
       letI : Nonempty I.Sample := I.sampleNonempty
       ∃ CR : I.Sample → Set Theta,
         HasCoverage I.model alpha CR ∧ R = CR I.outcome) := Iff.rfl

theorem packedConfidenceProcedure_output_nonempty
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (I : PackedFiniteInferenceBase.{u, v} Theta) :
    (output (packedConfidenceProcedure alpha) I).Nonempty := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  refine ⟨Set.univ, ?_⟩
  exact ⟨fun _ ↦ Set.univ, fullConfidenceRegion_hasCoverage I.model halpha, rfl⟩

/-- Exact global sufficiency relation on packed finite inference bases.  Its
existential data are precisely the two minimal statistics, the bijection, the
relabeled equality of induced experiments, and the observed-value equality
in the manuscript definition. -/
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

/-- Exact global symmetric conditionality relation on packed finite inference
bases, obtained from the ancillary conditional-model clause above in either
direction. -/
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

/-- The exact packed sufficiency relation is symmetric: invert the displayed
bijection and reverse the equality of the two induced experiments. -/
theorem packedFiniteSufficiencyRelation_symmetric
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Symmetric (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) := by
  intro I J hS
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype J.Sample := J.sampleFintype
  letI : Nonempty J.Sample := J.sampleNonempty
  rcases hS with ⟨T₁, T₂, h, hmin₁, hmin₂, hmass, hobserved⟩
  refine ⟨T₂, T₁, h.symm, hmin₂, hmin₁, ?_, ?_⟩
  · intro theta y
    letI : Fintype T₁.Codomain := T₁.codomainFintype
    letI : Nonempty T₁.Codomain := T₁.codomainNonempty
    letI : Fintype T₂.Codomain := T₂.codomainFintype
    letI : Nonempty T₂.Codomain := T₂.codomainNonempty
    simpa using (hmass theta (h.symm y)).symm
  · have hobs := congrArg h.symm hobserved
    simpa using hobs.symm

/-- Choosing the canonical statistic on both sides supplies every identity
pair of the exact packed sufficiency relation. -/
theorem packedFiniteSufficiencyRelation_reflexive
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Reflexive (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) := by
  intro I
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  let T := packedCanonicalMinimalSufficientStatistic I
  refine ⟨T, T, Equiv.refl _, ?_, ?_, ?_, rfl⟩
  · exact canonicalMinimalSufficient_isFiniteMinimalSufficient
      I.model I.all_outcomes_effective
  · exact canonicalMinimalSufficient_isFiniteMinimalSufficient
      I.model I.all_outcomes_effective
  · intro theta y
    rfl

/-- The unique relabelling between two surjective statistics with identical
fibers.  This is the finite set-theoretic step behind transitivity of `S`. -/
noncomputable def relabelSameFibers
    {X : Type u} {A : Type v} {B : Type w}
    (T : X → A) (U : X → B)
    (hT : Function.Surjective T) (hU : Function.Surjective U)
    (hfib : ∀ x y, T x = T y ↔ U x = U y) : B ≃ A := by
  let f : B → A := fun b ↦ T (Classical.choose (hU b))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro b c hbc
    have hb : U (Classical.choose (hU b)) = b := Classical.choose_spec (hU b)
    have hc : U (Classical.choose (hU c)) = c := Classical.choose_spec (hU c)
    have hchosen :
        U (Classical.choose (hU b)) = U (Classical.choose (hU c)) :=
      (hfib _ _).mp hbc
    exact hb.symm.trans (hchosen.trans hc)
  · intro a
    rcases hT a with ⟨x, rfl⟩
    refine ⟨U x, ?_⟩
    exact (hfib _ _).mpr (Classical.choose_spec (hU (U x)))

/-- The fiber relabelling takes each value of the second statistic to the
corresponding value of the first. -/
theorem relabelSameFibers_apply
    {X : Type u} {A : Type v} {B : Type w}
    (T : X → A) (U : X → B)
    (hT : Function.Surjective T) (hU : Function.Surjective U)
    (hfib : ∀ x y, T x = T y ↔ U x = U y) (x : X) :
    relabelSameFibers T U hT hU hfib (U x) = T x := by
  change T (Classical.choose (hU (U x))) = T x
  exact (hfib _ _).mpr (Classical.choose_spec (hU (U x)))

/-- Relabelling two statistics with the same fibers also relabels their
induced mass functions exactly. -/
theorem inducedPMF_relabelSameFibers
    {Theta : Type u} {X : Type v} {A : Type w} {B : Type z}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → A) (U : X → B)
    (hT : Function.Surjective T) (hU : Function.Surjective U)
    (hfib : ∀ x y, T x = T y ↔ U x = U y)
    (theta : Theta) (b : B) :
    inducedPMF E T theta (relabelSameFibers T U hT hU hfib b) =
      inducedPMF E U theta b := by
  classical
  unfold inducedPMF
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      apply (relabelSameFibers T U hT hU hfib).injective
      rw [relabelSameFibers_apply]
      exact hx
    · intro hx
      subst b
      exact (relabelSameFibers_apply T U hT hU hfib x).symm
  · intro _ _
    rfl

/-- The exact packed sufficiency relation is transitive.  The middle pair of
minimal statistics is joined by its unique fiber relabelling, and the three
induced-model bijections compose. -/
theorem packedFiniteSufficiencyRelation_transitive
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Transitive (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) := by
  intro I J K hIJ hJK
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype J.Sample := J.sampleFintype
  letI : Nonempty J.Sample := J.sampleNonempty
  letI : Fintype K.Sample := K.sampleFintype
  letI : Nonempty K.Sample := K.sampleNonempty
  rcases hIJ with ⟨Tᵢ, Tⱼ, hIJ, hminᵢ, hminⱼ, hmassIJ, hobsIJ⟩
  rcases hJK with ⟨Uⱼ, Uₖ, hJK, hminUⱼ, hminₖ, hmassJK, hobsJK⟩
  have hfib : ∀ x y, Tⱼ.statistic x = Tⱼ.statistic y ↔
      Uⱼ.statistic x = Uⱼ.statistic y := by
    intro x y
    have hcriterionT :=
      finiteMinimalSufficient_implies_likelihoodFiberCriterion
        J.model Tⱼ.statistic J.all_outcomes_effective hminⱼ
    have hcriterionU :=
      finiteMinimalSufficient_implies_likelihoodFiberCriterion
        J.model Uⱼ.statistic J.all_outcomes_effective hminUⱼ
    exact (hcriterionT x y).trans (hcriterionU x y).symm
  let g : Uⱼ.Codomain ≃ Tⱼ.Codomain :=
    relabelSameFibers Tⱼ.statistic Uⱼ.statistic
      Tⱼ.statistic_surjective Uⱼ.statistic_surjective hfib
  let h : Uₖ.Codomain ≃ Tᵢ.Codomain := hJK.trans (g.trans hIJ)
  refine ⟨Tᵢ, Uₖ, h, hminᵢ, hminₖ, ?_, ?_⟩
  · intro theta y
    letI : Fintype Tᵢ.Codomain := Tᵢ.codomainFintype
    letI : Nonempty Tᵢ.Codomain := Tᵢ.codomainNonempty
    letI : Fintype Tⱼ.Codomain := Tⱼ.codomainFintype
    letI : Nonempty Tⱼ.Codomain := Tⱼ.codomainNonempty
    letI : Fintype Uⱼ.Codomain := Uⱼ.codomainFintype
    letI : Nonempty Uⱼ.Codomain := Uⱼ.codomainNonempty
    letI : Fintype Uₖ.Codomain := Uₖ.codomainFintype
    letI : Nonempty Uₖ.Codomain := Uₖ.codomainNonempty
    letI : Fintype J.Sample := J.sampleFintype
    letI : Nonempty J.Sample := J.sampleNonempty
    calc
      Tᵢ.inducedModel.pmf theta (h y) =
          Tⱼ.inducedModel.pmf theta (g (hJK y)) := by
            simpa [h] using hmassIJ theta (g (hJK y))
      _ = Uⱼ.inducedModel.pmf theta (hJK y) := by
        exact inducedPMF_relabelSameFibers J.model
          Tⱼ.statistic Uⱼ.statistic Tⱼ.statistic_surjective
          Uⱼ.statistic_surjective hfib theta (hJK y)
      _ = Uₖ.inducedModel.pmf theta y := hmassJK theta y
  · dsimp [h]
    rw [← hobsJK]
    rw [relabelSameFibers_apply]
    exact hobsIJ

/-- The paper's exact packed sufficiency relation is therefore an
equivalence relation. -/
theorem packedFiniteSufficiencyRelation_isEquivalence
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Equivalence (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact packedFiniteSufficiencyRelation_reflexive i
  · intro i j hij
    exact packedFiniteSufficiencyRelation_symmetric hij
  · intro i j k hij hjk
    exact packedFiniteSufficiencyRelation_transitive hij hjk

/-- The exact packed conditionality relation is symmetric because its
definition includes the conditioning clause in either direction. -/
theorem packedFiniteConditionalityRelation_symmetric
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Symmetric (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) := by
  intro I J h
  simpa [packedFiniteConditionalityRelation, finiteConditionalityPair, Or.comm]
    using h

/-- Conditioning on a constant ancillary gives every identity pair, so the
exact packed conditionality relation is reflexive. -/
theorem packedFiniteConditionalityRelation_reflexive
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Reflexive (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) := by
  intro I
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  apply Or.inl
  let a₀ : ULift.{v} Unit := ⟨()⟩
  refine ⟨ULift.{v} Unit, (fun _ ↦ a₀), id, ancillary_const I.model a₀, ?_,
    Function.injective_id, Or.inl (fun _ ↦ rfl), ?_, rfl, ?_⟩
  · intro theta
    rw [inducedPMF_const_eq I.model a₀ a₀ theta rfl]
    norm_num
  · intro y
    simp
  · intro theta y
    simp [inducedPMF_const_eq I.model a₀ a₀ theta rfl]

/-- For the exact packed definitions, every conditionality pair is a
likelihood pair.  This derives the inclusion from ancillarity, event
positivity, and the conditional-mass equation rather than postulating it. -/
theorem packedFiniteConditionalityRelation_le_likelihoodRelation
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    packedFiniteConditionalityRelation.{u, v} (Theta := Theta) ≤
      packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) := by
  intro I J hC
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype J.Sample := J.sampleFintype
  letI : Nonempty J.Sample := J.sampleNonempty
  change Proportional I.likelihood J.likelihood
  rcases hC with hforward | hreverse
  · exact finiteDirectionalConditionalityPair_implies_proportional hforward
  · exact proportional_symm
      (finiteDirectionalConditionalityPair_implies_proportional hreverse)

/-! ## Evans's finite closure construction -/

namespace Evans2013Construction

inductive Two : Type v
  | zero
  | one
  deriving DecidableEq, Fintype, Inhabited

def two0 : Two.{v} := Two.zero
def two1 : Two.{v} := Two.one

noncomputable def finiteNatCode (X : Type v) [Fintype X] : X → Nat :=
  fun x ↦ (Fintype.equivFin X x).val

theorem finiteNatCode_injective (X : Type v) [Fintype X] :
    Function.Injective (finiteNatCode X) :=
  Fin.val_injective.comp (Fintype.equivFin X).injective

theorem sum_two {M : Type u} [AddCommMonoid M] (f : Two.{v} → M) :
    ∑ b, f b = f Two.zero + f Two.one := by
  classical
  rw [show (Finset.univ : Finset Two.{v}) = {Two.zero, Two.one} by
    ext b
    cases b <;> simp]
  simp

theorem FiniteModel.pmf_le_one
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (theta : Theta) (x : X) :
    E.pmf theta x ≤ 1 := by
  classical
  rw [← E.pmf_sum_one theta]
  exact Finset.single_le_sum (fun y _ ↦ E.pmf_nonneg theta y)
    (Finset.mem_univ x)

noncomputable def starPMF
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (observed : X) (alpha : ℝ)
    (theta : Theta) : X ⊕ Two.{v} → ℝ
  | Sum.inl x => (alpha / 2) * E.pmf theta x
  | Sum.inr b => if b = two0 then (1 - alpha * E.pmf theta observed) / 2
      else (1 - alpha + alpha * E.pmf theta observed) / 2

noncomputable def starModel
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (observed : X) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    FiniteModel Theta (X ⊕ Two.{v}) where
  pmf := starPMF E observed alpha
  pmf_nonneg := by
    intro theta z
    cases z with
    | inl x =>
        exact mul_nonneg (le_of_lt (half_pos halpha0)) (E.pmf_nonneg theta x)
    | inr b =>
        by_cases hb : b = two0
        · simp only [starPMF, hb, if_true]
          have hm := FiniteModel.pmf_le_one E theta observed
          have hm0 := E.pmf_nonneg theta observed
          have ham : alpha * E.pmf theta observed ≤ 1 := by
            calc
              alpha * E.pmf theta observed ≤ 1 * E.pmf theta observed :=
                mul_le_mul_of_nonneg_right (le_of_lt halpha1) hm0
              _ = E.pmf theta observed := one_mul _
              _ ≤ 1 := hm
          positivity
        · simp only [starPMF, hb, if_false]
          have hm0 := E.pmf_nonneg theta observed
          positivity
  pmf_sum_one := by
    intro theta
    classical
    rw [Fintype.sum_sum_type]
    simp only [starPMF]
    rw [← Finset.mul_sum]
    rw [E.pmf_sum_one]
    rw [sum_two]
    simp [two0]
    ring

def starBranch {X : Type v} : X ⊕ Two.{v} → Two.{v}
  | Sum.inl _ => Two.zero
  | Sum.inr _ => Two.one

noncomputable def starFork {X : Type v} (observed : X) (z : X ⊕ Two.{v}) : Two.{v} := by
  classical
  exact match z with
    | Sum.inl x => if x = observed then Two.zero else Two.one
    | Sum.inr b => if b = Two.zero then Two.zero else Two.one

def mainEmbed {X : Type v} : X → X ⊕ Two.{v} := Sum.inl

def forkEmbed {X : Type v} (observed : X) : Two.{v} → X ⊕ Two.{v}
  | Two.zero => Sum.inl observed
  | Two.one => Sum.inr Two.zero

theorem inducedPMF_starBranch_zero
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (observed : X) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) (theta : Theta) :
    inducedPMF (starModel E observed alpha halpha0 halpha1) starBranch theta Two.zero =
      alpha / 2 := by
  classical
  unfold inducedPMF
  rw [Finset.sum_filter]
  rw [Fintype.sum_sum_type]
  simp [starModel, starBranch, starPMF]
  rw [← Finset.mul_sum, E.pmf_sum_one]
  ring

theorem inducedPMF_starFork_zero
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (observed : X) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) (theta : Theta) :
    inducedPMF (starModel E observed alpha halpha0 halpha1) (starFork observed)
      theta Two.zero = 1 / 2 := by
  classical
  unfold inducedPMF
  rw [Finset.sum_filter]
  rw [Fintype.sum_sum_type]
  simp [starModel, starFork, starPMF, two0]
  ring

theorem inducedPMF_starBranch_one
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (observed : X) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) (theta : Theta) :
    inducedPMF (starModel E observed alpha halpha0 halpha1) starBranch theta Two.one =
      1 - alpha / 2 := by
  have hsum := inducedPMF_sum_one
    (starModel E observed alpha halpha0 halpha1) starBranch theta
  rw [sum_two, inducedPMF_starBranch_zero] at hsum
  linarith

theorem inducedPMF_starFork_one
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (observed : X) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) (theta : Theta) :
    inducedPMF (starModel E observed alpha halpha0 halpha1) (starFork observed)
      theta Two.one = 1 / 2 := by
  have hsum := inducedPMF_sum_one
    (starModel E observed alpha halpha0 halpha1) (starFork observed) theta
  rw [sum_two, inducedPMF_starFork_zero] at hsum
  linarith

theorem ancillary_starBranch
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (observed : X) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    Ancillary (starModel E observed alpha halpha0 halpha1) starBranch := by
  intro theta psi b
  cases b with
  | zero => rw [inducedPMF_starBranch_zero, inducedPMF_starBranch_zero]
  | one => rw [inducedPMF_starBranch_one, inducedPMF_starBranch_one]

theorem ancillary_starFork
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (observed : X) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    Ancillary (starModel E observed alpha halpha0 halpha1) (starFork observed) := by
  intro theta psi b
  cases b with
  | zero => rw [inducedPMF_starFork_zero, inducedPMF_starFork_zero]
  | one => rw [inducedPMF_starFork_one, inducedPMF_starFork_one]

theorem starModel_all_effective
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (observed : X) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hE : ∀ x, x ∈ effectiveSupport E) :
    ∀ z, z ∈ effectiveSupport (starModel E observed alpha halpha0 halpha1) := by
  intro z
  cases z with
  | inl x =>
      rcases hE x with ⟨theta, htheta⟩
      refine ⟨theta, ?_⟩
      change 0 < (alpha / 2) * E.pmf theta x
      positivity
  | inr b =>
      let theta : Theta := Classical.choice inferInstance
      refine ⟨theta, ?_⟩
      cases b with
      | zero =>
          change 0 < (1 - alpha * E.pmf theta observed) / 2
          have hm := FiniteModel.pmf_le_one E theta observed
          have hm0 := E.pmf_nonneg theta observed
          have ham : alpha * E.pmf theta observed < 1 := by
            calc
              alpha * E.pmf theta observed ≤ alpha * 1 :=
                mul_le_mul_of_nonneg_left hm (le_of_lt halpha0)
              _ = alpha := mul_one _
              _ < 1 := halpha1
          positivity
      | one =>
          change 0 < (1 - alpha + alpha * E.pmf theta observed) / 2
          have hm0 := E.pmf_nonneg theta observed
          have haNonneg : 0 ≤ alpha * E.pmf theta observed :=
            mul_nonneg (le_of_lt halpha0) hm0
          linarith

noncomputable def bridgePMF
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (observed : X) (alpha : ℝ)
    (theta : Theta) : Two.{v} → ℝ
  | Two.zero => alpha * E.pmf theta observed
  | Two.one => 1 - alpha * E.pmf theta observed

noncomputable def bridgeModel
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (observed : X) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    FiniteModel Theta Two.{v} where
  pmf := bridgePMF E observed alpha
  pmf_nonneg := by
    intro theta b
    cases b with
    | zero => exact mul_nonneg (le_of_lt halpha0) (E.pmf_nonneg theta observed)
    | one =>
        have hm := FiniteModel.pmf_le_one E theta observed
        have hm0 := E.pmf_nonneg theta observed
        have ham : alpha * E.pmf theta observed ≤ 1 := by
          calc
            alpha * E.pmf theta observed ≤ 1 * E.pmf theta observed :=
              mul_le_mul_of_nonneg_right (le_of_lt halpha1) hm0
            _ = E.pmf theta observed := one_mul _
            _ ≤ 1 := hm
        exact sub_nonneg.mpr ham
  pmf_sum_one := by
    intro theta
    rw [sum_two]
    simp [bridgePMF]

theorem bridgeModel_all_effective
    {Theta : Type u} {X : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (observed : X) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hObserved : observed ∈ effectiveSupport E) :
    ∀ b, b ∈ effectiveSupport (bridgeModel E observed alpha halpha0 halpha1) := by
  intro b
  cases b with
  | zero =>
      rcases hObserved with ⟨theta, htheta⟩
      refine ⟨theta, ?_⟩
      change 0 < alpha * E.pmf theta observed
      positivity
  | one =>
      let theta : Theta := Classical.choice inferInstance
      refine ⟨theta, ?_⟩
      change 0 < 1 - alpha * E.pmf theta observed
      have hm := FiniteModel.pmf_le_one E theta observed
      have hm0 := E.pmf_nonneg theta observed
      have ham : alpha * E.pmf theta observed < 1 := by
        calc
          alpha * E.pmf theta observed ≤ alpha * 1 :=
            mul_le_mul_of_nonneg_left hm (le_of_lt halpha0)
          _ = alpha := mul_one _
          _ < 1 := halpha1
      linarith

noncomputable def starPacked
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase.{u, v} Theta) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    PackedFiniteInferenceBase.{u, v} Theta := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  let E := starModel I.model I.outcome alpha halpha0 halpha1
  have hall : ∀ z, z ∈ effectiveSupport E :=
    starModel_all_effective I.model I.outcome alpha halpha0 halpha1
      I.all_outcomes_effective
  exact
    { Sample := I.Sample ⊕ Two.{v}
      sampleFintype := inferInstance
      sampleNonempty := inferInstance
      outcomeCode := finiteNatCode (I.Sample ⊕ Two.{v})
      outcomeCode_injective := finiteNatCode_injective (I.Sample ⊕ Two.{v})
      model := E
      outcome := Sum.inl I.outcome
      outcome_effective := hall (Sum.inl I.outcome)
      all_outcomes_effective := hall }

noncomputable def bridgePacked
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase.{u, v} Theta) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    PackedFiniteInferenceBase.{u, v} Theta := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  let E := bridgeModel I.model I.outcome alpha halpha0 halpha1
  have hall : ∀ b, b ∈ effectiveSupport E :=
    bridgeModel_all_effective I.model I.outcome alpha halpha0 halpha1
      I.outcome_effective
  exact
    { Sample := Two.{v}
      sampleFintype := inferInstance
      sampleNonempty := inferInstance
      outcomeCode := finiteNatCode Two.{v}
      outcomeCode_injective := finiteNatCode_injective Two.{v}
      model := E
      outcome := Two.zero
      outcome_effective := hall Two.zero
      all_outcomes_effective := hall }

theorem starBranch_surjective {X : Type v} [Nonempty X] :
    Function.Surjective (starBranch : X ⊕ Two.{v} → Two.{v}) := by
  intro b
  cases b with
  | zero => exact ⟨Sum.inl (Classical.choice inferInstance), rfl⟩
  | one => exact ⟨Sum.inr Two.zero, rfl⟩

theorem starFork_surjective {X : Type v} (observed : X) :
    Function.Surjective (starFork observed : X ⊕ Two.{v} → Two.{v}) := by
  intro b
  cases b with
  | zero => exact ⟨Sum.inl observed, by simp [starFork]⟩
  | one => exact ⟨Sum.inr Two.one, by simp [starFork]⟩

theorem mainEmbed_injective {X : Type v} :
    Function.Injective (mainEmbed : X → X ⊕ Two.{v}) := by
  intro x y h
  exact Sum.inl.inj h

theorem forkEmbed_injective {X : Type v} (observed : X) :
    Function.Injective (forkEmbed observed : Two.{v} → X ⊕ Two.{v}) := by
  intro b c h
  cases b <;> cases c <;> simp [forkEmbed] at h ⊢

theorem starBranch_observed_fiber {X : Type v} (observed : X)
    (z : X ⊕ Two.{v}) :
    starBranch z = starBranch (Sum.inl observed) ↔
      ∃ x, mainEmbed x = z := by
  cases z with
  | inl x => exact ⟨fun _ ↦ ⟨x, rfl⟩, fun _ ↦ rfl⟩
  | inr b => simp [starBranch, mainEmbed]

theorem starFork_observed_fiber {X : Type v} (observed : X)
    (z : X ⊕ Two.{v}) :
    starFork observed z = starFork observed (Sum.inl observed) ↔
      ∃ b, forkEmbed observed b = z := by
  classical
  cases z with
  | inl x =>
      constructor
      · intro h
        simp [starFork] at h
        subst x
        exact ⟨Two.zero, rfl⟩
      · rintro ⟨b, hb⟩
        cases b with
        | zero => simpa [forkEmbed, starFork] using hb.symm
        | one => simp [forkEmbed] at hb
  | inr b =>
      constructor
      · intro h
        simp [starFork] at h
        subst b
        exact ⟨Two.one, rfl⟩
      · rintro ⟨c, hc⟩
        cases c with
        | zero => simp [forkEmbed] at hc
        | one =>
            simp [forkEmbed] at hc
            subst b
            simp [starFork]

theorem starPacked_conditions_to_original
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase.{u, v} Theta) (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    packedFiniteConditionalityRelation (starPacked I alpha halpha0 halpha1) I := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  apply Or.inl
  refine ⟨Two.{v}, starBranch, mainEmbed,
    ?_, ?_, mainEmbed_injective, Or.inr ?_, ?_, rfl, ?_⟩
  · change Ancillary (starModel I.model I.outcome alpha halpha0 halpha1) starBranch
    exact ancillary_starBranch I.model I.outcome alpha halpha0 halpha1
  · intro theta
    change 0 < inducedPMF (starModel I.model I.outcome alpha halpha0 halpha1)
      starBranch theta Two.zero
    rw [inducedPMF_starBranch_zero]
    exact half_pos halpha0
  · exact ⟨⟨Two.zero, Two.one, by simp⟩, starBranch_surjective⟩
  · intro z
    change starBranch z = starBranch (Sum.inl I.outcome) ↔
      ∃ y, mainEmbed y = z
    exact starBranch_observed_fiber I.outcome z
  · intro theta y
    change I.model.pmf theta y =
      (starModel I.model I.outcome alpha halpha0 halpha1).pmf theta (Sum.inl y) /
        inducedPMF (starModel I.model I.outcome alpha halpha0 halpha1)
          starBranch theta Two.zero
    rw [inducedPMF_starBranch_zero]
    change I.model.pmf theta y =
      ((alpha / 2) * I.model.pmf theta y) / (alpha / 2)
    field_simp [ne_of_gt halpha0]

theorem starPacked_conditions_to_bridge_of_scaled_eq
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I J : PackedFiniteInferenceBase.{u, v} Theta)
    (alphaI alphaJ : ℝ)
    (hI0 : 0 < alphaI) (hI1 : alphaI < 1)
    (hJ0 : 0 < alphaJ) (hJ1 : alphaJ < 1)
    (hscaled : ∀ theta,
      alphaI * I.likelihood theta = alphaJ * J.likelihood theta) :
    packedFiniteConditionalityRelation
      (starPacked J alphaJ hJ0 hJ1) (bridgePacked I alphaI hI0 hI1) := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype J.Sample := J.sampleFintype
  letI : Nonempty J.Sample := J.sampleNonempty
  apply Or.inl
  refine ⟨Two.{v}, starFork J.outcome, forkEmbed J.outcome,
    ?_, ?_, forkEmbed_injective J.outcome, Or.inr ?_, ?_, rfl, ?_⟩
  · change Ancillary (starModel J.model J.outcome alphaJ hJ0 hJ1)
      (starFork J.outcome)
    exact ancillary_starFork J.model J.outcome alphaJ hJ0 hJ1
  · intro theta
    dsimp [starPacked, PackedFiniteInferenceBase.asInferenceBase]
    simp only [starFork]
    change 0 < inducedPMF (starModel J.model J.outcome alphaJ hJ0 hJ1)
      (starFork J.outcome) theta Two.zero
    rw [inducedPMF_starFork_zero]
    norm_num
  · exact ⟨⟨Two.zero, Two.one, by simp⟩, starFork_surjective J.outcome⟩
  · intro z
    change starFork J.outcome z = starFork J.outcome (Sum.inl J.outcome) ↔
      ∃ b, forkEmbed J.outcome b = z
    exact starFork_observed_fiber J.outcome z
  · intro theta b
    dsimp [starPacked, bridgePacked, PackedFiniteInferenceBase.asInferenceBase]
    simp only [starFork]
    change (bridgeModel I.model I.outcome alphaI hI0 hI1).pmf theta b =
      (starModel J.model J.outcome alphaJ hJ0 hJ1).pmf theta
          (forkEmbed J.outcome b) /
        inducedPMF (starModel J.model J.outcome alphaJ hJ0 hJ1)
          (starFork J.outcome) theta Two.zero
    rw [inducedPMF_starFork_zero]
    have hs := hscaled theta
    change alphaI * I.model.pmf theta I.outcome =
      alphaJ * J.model.pmf theta J.outcome at hs
    cases b with
    | zero =>
        change alphaI * I.model.pmf theta I.outcome =
          ((alphaJ / 2) * J.model.pmf theta J.outcome) / (1 / 2)
        rw [hs]
        ring
    | one =>
        change 1 - alphaI * I.model.pmf theta I.outcome =
          ((1 - alphaJ * J.model.pmf theta J.outcome) / 2) / (1 / 2)
        rw [hs]
        ring

end Evans2013Construction

open Evans2013Construction

/-- Evans (2013), Theorem 7: on the global universe of packed finite inference
bases, the equivalence closure of the conditionality relation is exactly the
likelihood relation.  This is the closure identity `C̄ = L`, not the false raw
identity `C = L`. -/
theorem packedFiniteConditionalityClosure_eq_likelihoodRelation
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    equivalenceClosure
        (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) =
      packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) := by
  apply le_antisymm
  · exact equivalenceClosure_minimal
      (likelihoodRelation_isEquivalence PackedFiniteInferenceBase.likelihood)
      packedFiniteConditionalityRelation_le_likelihoodRelation
  · intro I J hL
    rcases hL with ⟨k, hk, hlik⟩
    let alphaI : ℝ := 1 / (1 + k)
    let alphaJ : ℝ := k / (1 + k)
    have hdenom : 0 < 1 + k := by linarith
    have hI0 : 0 < alphaI := by
      dsimp [alphaI]
      positivity
    have hI1 : alphaI < 1 := by
      dsimp [alphaI]
      apply (div_lt_one hdenom).2
      linarith
    have hJ0 : 0 < alphaJ := by
      dsimp [alphaJ]
      positivity
    have hJ1 : alphaJ < 1 := by
      dsimp [alphaJ]
      apply (div_lt_one hdenom).2
      linarith
    have hscaled : ∀ theta,
        alphaI * I.likelihood theta = alphaJ * J.likelihood theta := by
      intro theta
      dsimp [alphaI, alphaJ]
      rw [hlik theta]
      field_simp [ne_of_gt hdenom]
    let SI := starPacked I alphaI hI0 hI1
    let SJ := starPacked J alphaJ hJ0 hJ1
    let B := bridgePacked I alphaI hI0 hI1
    have hSI : packedFiniteConditionalityRelation SI I := by
      exact starPacked_conditions_to_original I alphaI hI0 hI1
    have hSJ : packedFiniteConditionalityRelation SJ J := by
      exact starPacked_conditions_to_original J alphaJ hJ0 hJ1
    have hSIB : packedFiniteConditionalityRelation SI B := by
      exact starPacked_conditions_to_bridge_of_scaled_eq I I alphaI alphaI
        hI0 hI1 hI0 hI1 (fun _ ↦ rfl)
    have hSJB : packedFiniteConditionalityRelation SJ B := by
      exact starPacked_conditions_to_bridge_of_scaled_eq I J alphaI alphaJ
        hI0 hI1 hJ0 hJ1 hscaled
    have hI_SI : equivalenceClosure packedFiniteConditionalityRelation I SI :=
      Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hSI)
    have hSI_B : equivalenceClosure packedFiniteConditionalityRelation SI B :=
      Relation.EqvGen.rel _ _ hSIB
    have hB_SJ : equivalenceClosure packedFiniteConditionalityRelation B SJ :=
      Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hSJB)
    have hSJ_J : equivalenceClosure packedFiniteConditionalityRelation SJ J :=
      Relation.EqvGen.rel _ _ hSJ
    exact Relation.EqvGen.trans _ _ _ hI_SI
      (Relation.EqvGen.trans _ _ _ hSI_B
        (Relation.EqvGen.trans _ _ _ hB_SJ hSJ_J))

namespace Evans2013Construction

theorem observed_likelihood_proportional_induced_of_likelihoodFiberCriterion
    {Theta : Type u} {X Y : Type v}
    [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (T : X → Y)
    (hmin : IsLikelihoodMinimalSufficient (fun x theta ↦ E.pmf theta x) T)
    (x : X) :
    Proportional (fun theta ↦ E.pmf theta x)
      (fun theta ↦ inducedPMF E T theta (T x)) := by
  classical
  let Fiber := {y : X // T y = T x}
  letI : Nonempty Fiber := ⟨⟨x, rfl⟩⟩
  have hp : ∀ y : Fiber,
      Proportional (fun theta ↦ E.pmf theta y.1)
        (fun theta ↦ E.pmf theta x) := by
    intro y
    exact (hmin y.1 x).mp y.2
  choose k hk hEq using hp
  let K : ℝ := ∑ y : Fiber, k y
  have hK : 0 < K := by
    dsimp [K]
    exact Finset.sum_pos (fun y _ ↦ hk y) Finset.univ_nonempty
  have hinduced : ∀ theta,
      inducedPMF E T theta (T x) = K * E.pmf theta x := by
    intro theta
    unfold inducedPMF
    rw [Finset.sum_subtype (p := fun y ↦ T y = T x)
      (Finset.univ.filter (fun y ↦ T y = T x))
      (by intro y; simp) (E.pmf theta)]
    simp_rw [hEq]
    rw [← Finset.sum_mul]
  refine ⟨K⁻¹, inv_pos.mpr hK, ?_⟩
  intro theta
  change E.pmf theta x = K⁻¹ * inducedPMF E T theta (T x)
  rw [hinduced]
  field_simp [ne_of_gt hK]

end Evans2013Construction

/-! ## Finite likelihood-ratio reduction through sufficient statistics -/

/-- Multiplication by a positive constant commutes with a maximum over a
nonempty finite parameter set. -/
theorem finiteMaximum_mul_pos
    {A : Type u} [Fintype A]
    (s : Finset A) (hs : s.Nonempty) (f : A → ℝ)
    (k : ℝ) (hk : 0 < k) :
    finiteMaximum s hs (fun a ↦ k * f a) = k * finiteMaximum s hs f := by
  apply le_antisymm
  · apply finiteMaximum_le
    intro a ha
    exact mul_le_mul_of_nonneg_left (le_finiteMaximum s hs f ha) hk.le
  · obtain ⟨a, ha, hmax⟩ := exists_eq_finiteMaximum s hs f
    rw [← hmax]
    exact le_finiteMaximum s hs (fun a ↦ k * f a) ha

/-- Positive proportionality scales both restricted likelihood maxima by
the same constant. -/
theorem maxLikelihoodOn_eq_mul_of_proportional
    {Θ : Type u} {X : Type v} {Y : Type w}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (E : FiniteModel Θ X) (F : FiniteModel Θ Y)
    (x : X) (y : Y) {k : ℝ} (hk : 0 < k)
    (hmass : ∀ theta, E.pmf theta x = k * F.pmf theta y)
    (H : Finset Θ) (hH : H.Nonempty) :
    maxLikelihoodOn E H hH x = k * maxLikelihoodOn F H hH y := by
  unfold maxLikelihoodOn
  simp_rw [hmass]
  exact finiteMaximum_mul_pos H hH (fun theta ↦ F.pmf theta y) k hk

/-- Positive proportionality preserves the extended likelihood ratio,
including its `0 / 0 = 0` and positive-over-zero `=∞` cases. -/
theorem extendedLikelihoodRatio_eq_of_proportional
    {Θ : Type u} {X : Type v} {Y : Type w}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (E : FiniteModel Θ X) (F : FiniteModel Θ Y)
    (P : ParameterPartition Θ) (x : X) (y : Y)
    (h : Proportional (fun theta ↦ E.pmf theta x)
      (fun theta ↦ F.pmf theta y)) :
    extendedLikelihoodRatio E P x = extendedLikelihoodRatio F P y := by
  rcases h with ⟨k, hk, hmass⟩
  unfold extendedLikelihoodRatio
  rw [maxLikelihoodOn_eq_mul_of_proportional E F x y hk hmass
        P.nullPart P.null_nonempty,
      maxLikelihoodOn_eq_mul_of_proportional E F x y hk hmass
        P.alternativePart P.alternative_nonempty,
      ENNReal.ofReal_mul hk.le, ENNReal.ofReal_mul hk.le]
  exact ENNReal.mul_div_mul_left _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr hk))
    ENNReal.ofReal_ne_top

/-- The original and induced experiments have the same LR score at
corresponding values whenever the statistic has exact likelihood fibers. -/
theorem extendedLikelihoodRatio_induced_of_likelihoodFiberCriterion
    {Θ : Type u} {X Y : Type v}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (E : FiniteModel Θ X) (T : X → Y)
    (hcriterion : LikelihoodFiberCriterion
      (fun x theta ↦ E.pmf theta x) T)
    (P : ParameterPartition Θ) (x : X) :
    extendedLikelihoodRatio E P x =
      extendedLikelihoodRatio (inducedModel E T) P (T x) := by
  apply extendedLikelihoodRatio_eq_of_proportional
  exact Evans2013Construction.observed_likelihood_proportional_induced_of_likelihoodFiberCriterion
    E T hcriterion x

/-- Finite sufficiency makes each observed likelihood a strictly positive
multiple of its induced likelihood on an effective sample space. -/
theorem observed_likelihood_proportional_induced_of_finiteSufficient
    {Θ : Type u} {X Y : Type v}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X] [Nonempty X]
    (E : FiniteModel Θ X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E)
    (hS : FiniteSufficient E T) (x : X) :
    Proportional (fun theta ↦ E.pmf theta x)
      (fun theta ↦ inducedPMF E T theta (T x)) := by
  rcases hS with ⟨q, hq⟩
  have hqpos : 0 < q x := by
    rcases hall x with ⟨theta, htheta⟩
    rw [hq theta x] at htheta
    have hinduced : 0 ≤ inducedPMF E T theta (T x) :=
      inducedPMF_nonneg E T theta (T x)
    nlinarith
  refine ⟨q x, hqpos, ?_⟩
  intro theta
  simpa [mul_comm] using hq theta x

/-- Every genuinely sufficient finite statistic preserves the LR score at
corresponding original and induced observations. -/
theorem extendedLikelihoodRatio_induced_of_finiteSufficient
    {Θ : Type u} {X Y : Type v}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (E : FiniteModel Θ X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E)
    (hS : FiniteSufficient E T)
    (P : ParameterPartition Θ) (x : X) :
    extendedLikelihoodRatio E P x =
      extendedLikelihoodRatio (inducedModel E T) P (T x) := by
  apply extendedLikelihoodRatio_eq_of_proportional
  exact observed_likelihood_proportional_induced_of_finiteSufficient
    E T hall hS x

/-- If an LR score factors through a statistic, summing by statistic fibers
gives the same parameterwise lower-tail probability in the induced model. -/
theorem lowerTailProbability_induced_of_score
    {Θ : Type u} {X Y : Type v}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (E : FiniteModel Θ X) (T : X → Y)
    (P : ParameterPartition Θ) (x : X) (theta : Θ)
    (hscore : ∀ z, extendedLikelihoodRatio E P z =
      extendedLikelihoodRatio (inducedModel E T) P (T z)) :
    lowerTailProbability E P x theta =
      lowerTailProbability (inducedModel E T) P (T x) theta := by
  classical
  unfold lowerTailProbability
  calc
    (∑ z ∈ lowerTailRegion E P x, E.pmf theta z) =
        ∑ y ∈ lowerTailRegion (inducedModel E T) P (T x),
          ∑ z ∈ lowerTailRegion E P x with T z = y,
            E.pmf theta z := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro z hz
      rw [mem_lowerTailRegion_iff] at hz ⊢
      simpa only [hscore z, hscore x] using hz
    _ = ∑ y ∈ lowerTailRegion (inducedModel E T) P (T x),
          inducedPMF E T theta y := by
      apply Finset.sum_congr rfl
      intro y hy
      unfold inducedPMF
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun hz ↦ hz.2
      · intro hzT
        refine ⟨?_, hzT⟩
        rw [mem_lowerTailRegion_iff] at hy ⊢
        simpa only [hscore z, hscore x, hzT] using hy

/-- Exact likelihood fibers give equality of every parameterwise LR
lower-tail probability before and after reduction. -/
theorem lowerTailProbability_induced_of_likelihoodFiberCriterion
    {Θ : Type u} {X Y : Type v}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (E : FiniteModel Θ X) (T : X → Y)
    (hcriterion : LikelihoodFiberCriterion
      (fun x theta ↦ E.pmf theta x) T)
    (P : ParameterPartition Θ) (x : X) (theta : Θ) :
    lowerTailProbability E P x theta =
      lowerTailProbability (inducedModel E T) P (T x) theta := by
  apply lowerTailProbability_induced_of_score
  intro z
  exact extendedLikelihoodRatio_induced_of_likelihoodFiberCriterion
    E T hcriterion P z

/-- Finite sufficiency alone gives equality of every parameterwise LR
lower-tail probability before and after reduction. -/
theorem lowerTailProbability_induced_of_finiteSufficient
    {Θ : Type u} {X Y : Type v}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (E : FiniteModel Θ X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E)
    (hS : FiniteSufficient E T)
    (P : ParameterPartition Θ) (x : X) (theta : Θ) :
    lowerTailProbability E P x theta =
      lowerTailProbability (inducedModel E T) P (T x) theta := by
  apply lowerTailProbability_induced_of_score
  intro z
  exact extendedLikelihoodRatio_induced_of_finiteSufficient
    E T hall hS P z

/-- Exact likelihood fibers give the complete finite lower-tail LR p-value
reduction. -/
theorem lowerTailLRPValue_induced_of_likelihoodFiberCriterion
    {Θ : Type u} {X Y : Type v}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (E : FiniteModel Θ X) (T : X → Y)
    (hcriterion : LikelihoodFiberCriterion
      (fun x theta ↦ E.pmf theta x) T)
    (P : ParameterPartition Θ) (x : X) :
    lowerTailLRPValue E P x =
      lowerTailLRPValue (inducedModel E T) P (T x) := by
  unfold lowerTailLRPValue
  congr 1
  funext theta
  exact lowerTailProbability_induced_of_likelihoodFiberCriterion
    E T hcriterion P x theta

/-- Every genuinely sufficient finite statistic gives the complete
lower-tail LR p-value reduction. -/
theorem lowerTailLRPValue_induced_of_finiteSufficient
    {Θ : Type u} {X Y : Type v}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (E : FiniteModel Θ X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E)
    (hS : FiniteSufficient E T)
    (P : ParameterPartition Θ) (x : X) :
    lowerTailLRPValue E P x =
      lowerTailLRPValue (inducedModel E T) P (T x) := by
  unfold lowerTailLRPValue
  congr 1
  funext theta
  exact lowerTailProbability_induced_of_finiteSufficient
    E T hall hS P x theta

/-- Genuine finite minimal sufficiency gives equality of each
parameter-indexed LR lower-tail probability. -/
theorem lowerTailProbability_induced_of_finiteMinimalSufficient
    {Θ : Type u} {X Y : Type v}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (E : FiniteModel Θ X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E)
    (hmin : FiniteMinimalSufficient E T)
    (P : ParameterPartition Θ) (x : X) (theta : Θ) :
    lowerTailProbability E P x theta =
      lowerTailProbability (inducedModel E T) P (T x) theta := by
  exact lowerTailProbability_induced_of_finiteSufficient
    E T hall hmin.1 P x theta

/-- Genuine finite minimal sufficiency yields the LR p-value reduction, with
no factorization or reduction equality supplied as a hypothesis. -/
theorem lowerTailLRPValue_induced_of_finiteMinimalSufficient
    {Θ : Type u} {X Y : Type v}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (E : FiniteModel Θ X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E)
    (hmin : FiniteMinimalSufficient E T)
    (P : ParameterPartition Θ) (x : X) :
    lowerTailLRPValue E P x =
      lowerTailLRPValue (inducedModel E T) P (T x) := by
  exact lowerTailLRPValue_induced_of_finiteSufficient
    E T hall hmin.1 P x

/-- Evans (2013), Lemma 5: the packed finite sufficiency relation is contained
in the likelihood relation. -/
theorem packedFiniteSufficiencyRelation_le_likelihoodRelation
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    packedFiniteSufficiencyRelation.{u, v} (Theta := Theta) ≤
      packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) := by
  intro I J hS
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype J.Sample := J.sampleFintype
  letI : Nonempty J.Sample := J.sampleNonempty
  rcases hS with ⟨T₁, T₂, h, hmin₁, hmin₂, hmass, hobserved⟩
  letI : Fintype T₁.Codomain := T₁.codomainFintype
  letI : Nonempty T₁.Codomain := T₁.codomainNonempty
  letI : Fintype T₂.Codomain := T₂.codomainFintype
  letI : Nonempty T₂.Codomain := T₂.codomainNonempty
  have hcriterion₁ :=
    finiteMinimalSufficient_implies_likelihoodFiberCriterion
      I.model T₁.statistic I.all_outcomes_effective hmin₁
  have hcriterion₂ :=
    finiteMinimalSufficient_implies_likelihoodFiberCriterion
      J.model T₂.statistic J.all_outcomes_effective hmin₂
  have hI := observed_likelihood_proportional_induced_of_likelihoodFiberCriterion
    I.model T₁.statistic hcriterion₁ I.outcome
  have hJ := observed_likelihood_proportional_induced_of_likelihoodFiberCriterion
    J.model T₂.statistic hcriterion₂ J.outcome
  have hmiddle : Proportional
      (fun theta ↦ T₁.inducedModel.pmf theta (T₁.statistic I.outcome))
      (fun theta ↦ T₂.inducedModel.pmf theta (T₂.statistic J.outcome)) := by
    refine ⟨1, by norm_num, ?_⟩
    intro theta
    change T₁.inducedModel.pmf theta (T₁.statistic I.outcome) =
      1 * T₂.inducedModel.pmf theta (T₂.statistic J.outcome)
    rw [hobserved, hmass]
    ring
  change Proportional I.likelihood J.likelihood
  exact proportional_trans hI (proportional_trans hmiddle (proportional_symm hJ))

/-- Evans (2013), Theorem 9: the equivalence closure of the union of packed
conditionality and sufficiency is exactly the likelihood relation.  This is
`overline (C ∪ S) = L`; the raw union is in general a proper subrelation. -/
theorem packedFiniteJointClosure_eq_likelihoodRelation
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    equivalenceClosure
        (relationUnion
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta))
          (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta))) =
      packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) := by
  apply le_antisymm
  · apply equivalenceClosure_minimal
      (likelihoodRelation_isEquivalence PackedFiniteInferenceBase.likelihood)
    intro I J h
    rcases h with hC | hS
    · exact packedFiniteConditionalityRelation_le_likelihoodRelation I J hC
    · exact packedFiniteSufficiencyRelation_le_likelihoodRelation I J hS
  · rw [← packedFiniteConditionalityClosure_eq_likelihoodRelation]
    apply equivalenceClosure_minimal
      (equivalenceClosure_isEquivalence (relationUnion
        packedFiniteConditionalityRelation packedFiniteSufficiencyRelation))
    intro I J hC
    exact Relation.EqvGen.rel _ _ (Or.inl hC)

/-! ## Directional and symmetric conditionality -/

/-- A directional conditionality specification records which base is the
unconditioned model and which base is obtained by conditioning.  Its
statistical content is supplied by hypotheses on the relation. -/
abbrev DirectionalConditionality (ι : Type u) := StatisticalRelation ι

/-- The paper's explicitly reflexive and symmetric conditionality relation:
identity pairs, forward conditioning steps, and reversed conditioning steps. -/
def conditionalityRelation {ι : Type u} (C₀ : DirectionalConditionality ι) :
    StatisticalRelation ι :=
  fun i j ↦ i = j ∨ C₀ i j ∨ C₀ j i

/-- Every directional conditioning step is a conditionality pair. -/
theorem directionalConditionality_le_conditionalityRelation
    {ι : Type u} (C₀ : DirectionalConditionality ι) :
    C₀ ≤ conditionalityRelation C₀ := by
  intro i j hij
  exact Or.inr (Or.inl hij)

/-- The explicit conditionality relation contains every identity pair. -/
theorem conditionalityRelation_reflexive {ι : Type u}
    (C₀ : DirectionalConditionality ι) :
    Reflexive (conditionalityRelation C₀) := by
  intro i
  exact Or.inl rfl

/-- Adding reverse steps makes the explicit conditionality relation symmetric. -/
theorem conditionalityRelation_symmetric {ι : Type u}
    (C₀ : DirectionalConditionality ι) :
    Symmetric (conditionalityRelation C₀) := by
  intro i j hij
  rcases hij with hij | hij | hji
  · exact Or.inl hij.symm
  · exact Or.inr (Or.inr hij)
  · exact Or.inr (Or.inl hji)

/-- Minimal hypotheses for the reflexive symmetric closure of a directional
relation to stay inside another relation. -/
theorem conditionalityRelation_le_of_reflexive_symmetric
    {ι : Type u} {C₀ L : StatisticalRelation ι}
    (hLrefl : Reflexive L) (hLsymm : Symmetric L) (hC₀L : C₀ ≤ L) :
    conditionalityRelation C₀ ≤ L := by
  intro i j hij
  rcases hij with hij | hij | hji
  · simpa [hij] using hLrefl j
  · exact hC₀L i j hij
  · exact hLsymm (hC₀L j i hji)

/-- If every directional conditioning step has a positive,
parameter-independent factor, then the explicitly symmetrized conditionality
relation is a subrelation of the likelihood relation. -/
theorem conditionalityRelation_le_likelihoodRelation
    {ι : Type u} {Θ : Type v} (likelihood : ι → Θ → ℝ)
    (C₀ : DirectionalConditionality ι)
    (hfactor : ∀ ⦃i j⦄, C₀ i j →
      ∃ q : ℝ, 0 < q ∧ ∀ θ, likelihood i θ = q * likelihood j θ) :
    conditionalityRelation C₀ ≤ likelihoodRelation likelihood := by
  apply conditionalityRelation_le_of_reflexive_symmetric
  · exact (likelihoodRelation_isEquivalence likelihood).1
  · intro i j hij
    exact proportional_symm hij
  · intro i j hij
    exact hfactor hij

/-- Symmetrizing and adjoining identity pairs before taking equivalence
closure does not change the generated equivalence relation. -/
theorem equivalenceClosure_conditionalityRelation {ι : Type u}
    (C₀ : DirectionalConditionality ι) :
    equivalenceClosure (conditionalityRelation C₀) = equivalenceClosure C₀ := by
  apply le_antisymm
  · apply equivalenceClosure_minimal (equivalenceClosure_isEquivalence C₀)
    intro i j hij
    rcases hij with hij | hij | hij
    · subst j
      exact (equivalenceClosure_isEquivalence C₀).refl i
    · exact relation_le_equivalenceClosure C₀ i j hij
    · exact (equivalenceClosure_isEquivalence C₀).symm
        (relation_le_equivalenceClosure C₀ j i hij)
  · apply equivalenceClosure_minimal
      (equivalenceClosure_isEquivalence (conditionalityRelation C₀))
    intro i j hij
    exact relation_le_equivalenceClosure (conditionalityRelation C₀) i j
      (directionalConditionality_le_conditionalityRelation C₀ i j hij)

/-! ## Witness criteria for nontransitivity and incomparability -/

/-- Two composable related pairs with an unrelated pair of endpoints witness
failure of transitivity. -/
theorem not_transitive_of_witness {ι : Type u} {R : StatisticalRelation ι}
    {i j k : ι} (hij : R i j) (hjk : R j k) (hik : ¬ R i k) :
    ¬ Transitive R := by
  intro htrans
  exact hik (htrans hij hjk)

/-- A fork of directional conditioning steps witnesses nontransitivity of the
symmetric conditionality relation whenever its endpoints have no direct step
in either direction. -/
theorem conditionalityRelation_not_transitive_of_fork
    {ι : Type u} {C₀ : DirectionalConditionality ι} {i j k : ι}
    (hij : C₀ i j) (hkj : C₀ k j) (hik_ne : i ≠ k)
    (hik : ¬ C₀ i k) (hki : ¬ C₀ k i) :
    ¬ Transitive (conditionalityRelation C₀) := by
  apply not_transitive_of_witness
      (R := conditionalityRelation C₀)
      (Or.inr (Or.inl hij)) (Or.inr (Or.inr hkj))
  simpa [conditionalityRelation, hik_ne, hik, hki]

/-- Two relations are incomparable when neither is included in the other. -/
def RelationsIncomparable {ι : Type u}
    (R S : StatisticalRelation ι) : Prop :=
  ¬ R ≤ S ∧ ¬ S ≤ R

/-- One witness in each set difference proves incomparability. -/
theorem relationsIncomparable_of_witnesses
    {ι : Type u} {R S : StatisticalRelation ι}
    {r₁ r₂ s₁ s₂ : ι}
    (hr : R r₁ r₂ ∧ ¬ S r₁ r₂)
    (hs : S s₁ s₂ ∧ ¬ R s₁ s₂) :
    RelationsIncomparable R S := by
  constructor
  · intro hRS
    exact hr.2 (hRS r₁ r₂ hr.1)
  · intro hSR
    exact hs.2 (hSR s₁ s₂ hs.1)

/-- Named specialization of the generic witness criterion to the paper's
sufficiency and conditionality relations. -/
theorem sufficiency_conditionality_incomparable_of_witnesses
    {ι : Type u} {S C : StatisticalRelation ι}
    {s₁ s₂ c₁ c₂ : ι}
    (hSnotC : S s₁ s₂ ∧ ¬ C s₁ s₂)
    (hCnotS : C c₁ c₂ ∧ ¬ S c₁ c₂) :
    RelationsIncomparable S C :=
  relationsIncomparable_of_witnesses hSnotC hCnotS

/-- Reflexive sufficiency and conditionality relations share every identity
pair, even when they are incomparable. -/
theorem reflexive_relations_share_identity
    {ι : Type u} {S C : StatisticalRelation ι}
    (hS : Reflexive S) (hC : Reflexive C) (i : ι) :
    S i i ∧ C i i :=
  ⟨hS i, hC i⟩

/-! ## Equivalence closure and unions -/

/-- Taking equivalence closure does nothing to an equivalence relation. -/
theorem equivalenceClosure_eq_self_of_equivalence
    {ι : Type u} {R : StatisticalRelation ι} (hR : Equivalence R) :
    equivalenceClosure R = R :=
  hR.eqvGen_eq

/-- A union is contained in `L` exactly from the two constituent inclusions. -/
theorem relationUnion_le_of_le
    {ι : Type u} {C S L : StatisticalRelation ι}
    (hCL : C ≤ L) (hSL : S ≤ L) :
    relationUnion C S ≤ L := by
  intro i j hij
  exact hij.elim (hCL i j) (hSL i j)

/-- A point of `L` outside both constituents makes their union a strict
subrelation of `L`. -/
theorem relationUnion_lt_of_witness
    {ι : Type u} {C S L : StatisticalRelation ι}
    (hCL : C ≤ L) (hSL : S ≤ L)
    {i j : ι} (hLij : L i j) (hCij : ¬ C i j) (hSij : ¬ S i j) :
    relationUnion C S < L := by
  rw [lt_iff_le_and_ne]
  refine ⟨relationUnion_le_of_le hCL hSL, ?_⟩
  intro hEq
  have : relationUnion C S i j := by
    rw [hEq]
    exact hLij
  exact this.elim hCij hSij

/-- Equivalence closure is monotone. -/
theorem equivalenceClosure_mono
    {ι : Type u} {R S : StatisticalRelation ι} (hRS : R ≤ S) :
    equivalenceClosure R ≤ equivalenceClosure S := by
  apply equivalenceClosure_minimal
  · exact equivalenceClosure_isEquivalence S
  · exact fun i j hij ↦ Relation.EqvGen.rel i j (hRS i j hij)

/-- If both constituents lie in an equivalence relation, so does the
equivalence closure of their union. -/
theorem equivalenceClosure_relationUnion_le
    {ι : Type u} {C S L : StatisticalRelation ι}
    (hL : Equivalence L) (hCL : C ≤ L) (hSL : S ≤ L) :
    equivalenceClosure (relationUnion C S) ≤ L := by
  exact equivalenceClosure_minimal hL (relationUnion_le_of_le hCL hSL)

/-- If `C` already generates `L`, adjoining any subrelation of `L` does not
change that equivalence closure. -/
theorem equivalenceClosure_relationUnion_eq_of_left
    {ι : Type u} {C S L : StatisticalRelation ι}
    (hL : Equivalence L) (hC : equivalenceClosure C = L)
    (hSL : S ≤ L) :
    equivalenceClosure (relationUnion C S) = L := by
  apply le_antisymm
  · apply equivalenceClosure_relationUnion_le hL
    · intro i j hij
      rw [← hC]
      exact Relation.EqvGen.rel i j hij
    · exact hSL
  · rw [← hC]
    apply equivalenceClosure_mono
    intro i j hij
    exact Or.inl hij

/-! ## Finite lower-tail mass transport -/

/-- The lower score tail determined by an observed reduced-data point. -/
def lowerTail {X : Type u} {Score : Type z} [Preorder Score]
    (score : X → Score) (observed : X) : Set X :=
  {x | score x ≤ score observed}

/-- The probability mass of a lower score tail in a finite induced model. -/
noncomputable def lowerTailMass {X : Type u} {Score : Type z}
    [Fintype X] [Preorder Score] [DecidableLE Score]
    (mass : X → ℝ) (score : X → Score) (observed : X) : ℝ :=
  ∑ x, if score x ≤ score observed then mass x else 0

/-- The finite null-parameter maximum of the lower-tail masses.  This is the
abstract likelihood-ratio p-value used in the transport theorem below. -/
noncomputable def finiteLowerTailPValue {X : Type u} {Θ : Type v}
    {Score : Type z} [Fintype X] [Preorder Score] [DecidableLE Score]
    (null : Finset Θ) (hnull : null.Nonempty)
    (mass : Θ → X → ℝ) (score : X → Score) (observed : X) : ℝ :=
  null.sup' hnull (fun θ ↦ lowerTailMass (mass θ) score observed)

/-- A score-preserving bijection carries the lower-tail region at the second
observed point exactly onto the lower-tail region at the first. -/
theorem lowerTail_image_equiv
    {X₁ : Type u} {X₂ : Type v} {Score : Type z} [Preorder Score]
    (h : X₂ ≃ X₁) (score₁ : X₁ → Score) (score₂ : X₂ → Score)
    (hscore : ∀ x, score₁ (h x) = score₂ x) (observed₂ : X₂) :
    h '' lowerTail score₂ observed₂ = lowerTail score₁ (h observed₂) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change score₁ (h y) ≤ score₁ (h observed₂)
    change score₂ y ≤ score₂ observed₂ at hy
    rw [hscore y, hscore observed₂]
    exact hy
  · intro hx
    refine ⟨h.symm x, ?_, h.apply_symm_apply x⟩
    change score₂ (h.symm x) ≤ score₂ observed₂
    rw [← hscore (h.symm x), h.apply_symm_apply, ← hscore observed₂]
    exact hx

/-- Change of variables for a finite lower-tail sum.  Both the score and the
induced mass are transported along the bijection. -/
theorem lowerTailMass_equiv
    {X₁ : Type u} {X₂ : Type v} {Score : Type z}
    [Fintype X₁] [Fintype X₂] [Preorder Score] [DecidableLE Score]
    (h : X₂ ≃ X₁) (score₁ : X₁ → Score) (score₂ : X₂ → Score)
    (mass₁ : X₁ → ℝ) (mass₂ : X₂ → ℝ)
    (hscore : ∀ x, score₁ (h x) = score₂ x)
    (hmass : ∀ x, mass₁ (h x) = mass₂ x) (observed₂ : X₂) :
    lowerTailMass mass₁ score₁ (h observed₂) =
      lowerTailMass mass₂ score₂ observed₂ := by
  unfold lowerTailMass
  calc
    (∑ x : X₁, if score₁ x ≤ score₁ (h observed₂) then mass₁ x else 0) =
        ∑ y : X₂,
          if score₁ (h y) ≤ score₁ (h observed₂) then mass₁ (h y) else 0 :=
      (h.sum_comp _).symm
    _ = ∑ y : X₂,
          if score₂ y ≤ score₂ observed₂ then mass₂ y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [hscore y, hscore observed₂, hmass y]

/-- Parameterwise equality of lower-tail masses is preserved by taking the
finite maximum over a nonempty null parameter set. -/
theorem finiteLowerTailPValue_equiv
    {X₁ : Type u} {X₂ : Type v} {Θ : Type w} {Score : Type z}
    [Fintype X₁] [Fintype X₂] [Preorder Score] [DecidableLE Score]
    (h : X₂ ≃ X₁) (score₁ : X₁ → Score) (score₂ : X₂ → Score)
    (mass₁ : Θ → X₁ → ℝ) (mass₂ : Θ → X₂ → ℝ)
    (hscore : ∀ x, score₁ (h x) = score₂ x)
    (hmass : ∀ θ x, mass₁ θ (h x) = mass₂ θ x)
    (null : Finset Θ) (hnull : null.Nonempty) (observed₂ : X₂) :
    finiteLowerTailPValue null hnull mass₁ score₁ (h observed₂) =
      finiteLowerTailPValue null hnull mass₂ score₂ observed₂ := by
  unfold finiteLowerTailPValue
  apply Finset.sup'_congr hnull rfl
  intro θ _
  exact lowerTailMass_equiv h score₁ score₂ (mass₁ θ) (mass₂ θ)
    hscore (hmass θ) observed₂

/-- The complete finite-bijection transport statement behind the manuscript's
lower-tail calculation: the tail regions correspond, all parameter-indexed
tail masses agree, and hence the resulting p-values agree. -/
theorem finite_bijection_lowerTail_score_mass_transport
    {X₁ : Type u} {X₂ : Type v} {Θ : Type w} {Score : Type z}
    [Fintype X₁] [Fintype X₂] [Preorder Score] [DecidableLE Score]
    (h : X₂ ≃ X₁) (score₁ : X₁ → Score) (score₂ : X₂ → Score)
    (mass₁ : Θ → X₁ → ℝ) (mass₂ : Θ → X₂ → ℝ)
    (hscore : ∀ x, score₁ (h x) = score₂ x)
    (hmass : ∀ θ x, mass₁ θ (h x) = mass₂ θ x)
    (null : Finset Θ) (hnull : null.Nonempty)
    (observed₁ : X₁) (observed₂ : X₂) (hobserved : observed₁ = h observed₂) :
    h '' lowerTail score₂ observed₂ = lowerTail score₁ observed₁ ∧
      (∀ θ, lowerTailMass (mass₁ θ) score₁ observed₁ =
        lowerTailMass (mass₂ θ) score₂ observed₂) ∧
      finiteLowerTailPValue null hnull mass₁ score₁ observed₁ =
        finiteLowerTailPValue null hnull mass₂ score₂ observed₂ := by
  subst observed₁
  refine ⟨lowerTail_image_equiv h score₁ score₂ hscore observed₂, ?_,
    finiteLowerTailPValue_equiv h score₁ score₂ mass₁ mass₂ hscore hmass
      null hnull observed₂⟩
  intro θ
  exact lowerTailMass_equiv h score₁ score₂ (mass₁ θ) (mass₂ θ)
    hscore (hmass θ) observed₂

/-! ## Exact extended-likelihood-ratio transport -/

/-- Relabelling outcomes without changing any parameter-indexed mass leaves
each finite restricted likelihood maximum unchanged. -/
theorem maxLikelihoodOn_equiv
    {Θ : Type u} {X₁ : Type v} {X₂ : Type w}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X₁] [Nonempty X₁] [Fintype X₂] [Nonempty X₂]
    (E₁ : FiniteModel Θ X₁) (E₂ : FiniteModel Θ X₂) (h : X₂ ≃ X₁)
    (hmass : ∀ θ x, E₁.pmf θ (h x) = E₂.pmf θ x)
    (H : Finset Θ) (hH : H.Nonempty) (x : X₂) :
    maxLikelihoodOn E₁ H hH (h x) = maxLikelihoodOn E₂ H hH x := by
  unfold maxLikelihoodOn
  congr 2
  funext θ
  exact hmass θ x

/-- The paper's extended likelihood ratio, including its `0/0` and positive
over zero cases, is invariant under an exact relabelling of experiments. -/
theorem extendedLikelihoodRatio_equiv
    {Θ : Type u} {X₁ : Type v} {X₂ : Type w}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X₁] [Nonempty X₁] [Fintype X₂] [Nonempty X₂]
    (E₁ : FiniteModel Θ X₁) (E₂ : FiniteModel Θ X₂) (h : X₂ ≃ X₁)
    (hmass : ∀ θ x, E₁.pmf θ (h x) = E₂.pmf θ x)
    (P : ParameterPartition Θ) (x : X₂) :
    extendedLikelihoodRatio E₁ P (h x) = extendedLikelihoodRatio E₂ P x := by
  unfold extendedLikelihoodRatio
  rw [maxLikelihoodOn_equiv E₁ E₂ h hmass P.nullPart P.null_nonempty x]
  rw [maxLikelihoodOn_equiv E₁ E₂ h hmass P.alternativePart
    P.alternative_nonempty x]

/-- The concrete lower-tail probability from S04 is the generic lower-tail
mass from this module, now instantiated with an `ENNReal` score. -/
theorem lowerTailProbability_eq_lowerTailMass
    {Θ : Type u} {X : Type v} [Fintype Θ] [Nonempty Θ]
    [Fintype X] [Nonempty X]
    (E : FiniteModel Θ X) (P : ParameterPartition Θ) (x : X) (θ : Θ) :
    lowerTailProbability E P x θ =
      lowerTailMass (E.pmf θ) (extendedLikelihoodRatio E P) x := by
  classical
  unfold lowerTailProbability lowerTailRegion lowerTailMass
  rw [Finset.sum_filter]

/-- An exact bijection of finite experiments transports the paper's complete
extended-LR lower-tail p-value, with no finiteness assumption on the ratio. -/
theorem lowerTailLRPValue_equiv
    {Θ : Type u} {X₁ : Type v} {X₂ : Type w}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X₁] [Nonempty X₁] [Fintype X₂] [Nonempty X₂]
    (E₁ : FiniteModel Θ X₁) (E₂ : FiniteModel Θ X₂) (h : X₂ ≃ X₁)
    (hmass : ∀ θ x, E₁.pmf θ (h x) = E₂.pmf θ x)
    (P : ParameterPartition Θ) (observed₂ : X₂) :
    lowerTailLRPValue E₁ P (h observed₂) =
      lowerTailLRPValue E₂ P observed₂ := by
  unfold lowerTailLRPValue
  congr 1
  funext θ
  rw [lowerTailProbability_eq_lowerTailMass,
    lowerTailProbability_eq_lowerTailMass]
  exact lowerTailMass_equiv h
    (extendedLikelihoodRatio E₁ P) (extendedLikelihoodRatio E₂ P)
    (E₁.pmf θ) (E₂.pmf θ)
    (extendedLikelihoodRatio_equiv E₁ E₂ h hmass P) (hmass θ) observed₂

/-- Formula-explicit assembly of the LR-region and p-value transport used in
the manuscript's proof that the LR p-value respects sufficiency relabellings. -/
theorem extended_lr_region_and_pvalue_transport
    {Θ : Type u} {X₁ : Type v} {X₂ : Type w}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X₁] [Nonempty X₁] [Fintype X₂] [Nonempty X₂]
    (E₁ : FiniteModel Θ X₁) (E₂ : FiniteModel Θ X₂) (h : X₂ ≃ X₁)
    (hmass : ∀ θ x, E₁.pmf θ (h x) = E₂.pmf θ x)
    (P : ParameterPartition Θ) (observed₂ : X₂) :
    h '' lowerTail (extendedLikelihoodRatio E₂ P) observed₂ =
        lowerTail (extendedLikelihoodRatio E₁ P) (h observed₂) ∧
      lowerTailLRPValue E₁ P (h observed₂) =
        lowerTailLRPValue E₂ P observed₂ := by
  exact ⟨lowerTail_image_equiv h
      (extendedLikelihoodRatio E₁ P) (extendedLikelihoodRatio E₂ P)
      (extendedLikelihoodRatio_equiv E₁ E₂ h hmass P) observed₂,
    lowerTailLRPValue_equiv E₁ E₂ h hmass P observed₂⟩

/-- A generic assembly lemma: two already-established reduction equalities
and an exact relabelling of the reduced experiments imply equality of the
original LR p-values, including infinite extended likelihood ratios.  The
finite reduction equalities themselves are proved above. -/
theorem lowerTailLRPValue_eq_of_sufficiency_relabelling
    {Θ : Type u} {X₁ : Type v} {X₂ : Type w}
    {Y₁ : Type v} {Y₂ : Type w}
    [Fintype Θ] [Nonempty Θ]
    [Fintype X₁] [Nonempty X₁] [Fintype X₂] [Nonempty X₂]
    [Fintype Y₁] [Nonempty Y₁] [Fintype Y₂] [Nonempty Y₂]
    (E₁ : FiniteModel Θ X₁) (E₂ : FiniteModel Θ X₂)
    (E_T₁ : FiniteModel Θ Y₁) (E_T₂ : FiniteModel Θ Y₂)
    (T₁ : X₁ → Y₁) (T₂ : X₂ → Y₂) (h : Y₂ ≃ Y₁)
    (P : ParameterPartition Θ) (x₁ : X₁) (x₂ : X₂)
    (hobservation : T₁ x₁ = h (T₂ x₂))
    (hrelabel : ∀ θ y, E_T₁.pmf θ (h y) = E_T₂.pmf θ y)
    (hreduction₁ : lowerTailLRPValue E₁ P x₁ =
      lowerTailLRPValue E_T₁ P (T₁ x₁))
    (hreduction₂ : lowerTailLRPValue E₂ P x₂ =
      lowerTailLRPValue E_T₂ P (T₂ x₂)) :
    lowerTailLRPValue E₁ P x₁ = lowerTailLRPValue E₂ P x₂ := by
  calc
    lowerTailLRPValue E₁ P x₁ =
        lowerTailLRPValue E_T₁ P (T₁ x₁) := hreduction₁
    _ = lowerTailLRPValue E_T₁ P (h (T₂ x₂)) := by rw [hobservation]
    _ = lowerTailLRPValue E_T₂ P (T₂ x₂) :=
      lowerTailLRPValue_equiv E_T₁ E_T₂ h hrelabel P (T₂ x₂)
    _ = lowerTailLRPValue E₂ P x₂ := hreduction₂.symm

/-! ## Global LR p-value preservation on the exact packed relation -/

/-- The packed lower-tail LR p-value reduces through every genuinely finite
minimal sufficient statistic.  No factorization premise is exposed: it is a
consequence of the preceding result. -/
theorem packedLowerTailLRPValue_eq_reduced
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (P : ParameterPartition Theta)
    (I : PackedFiniteInferenceBase.{u, v} Theta)
    (T : PackedFiniteStatistic I)
    (hmin :
      letI : Fintype I.Sample := I.sampleFintype
      letI : Nonempty I.Sample := I.sampleNonempty
      FiniteMinimalSufficient I.model T.statistic) :
    packedLowerTailLRPValue P I = T.reducedPValue P := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype T.Codomain := T.codomainFintype
  letI : Nonempty T.Codomain := T.codomainNonempty
  exact lowerTailLRPValue_induced_of_finiteMinimalSufficient
    I.model T.statistic I.all_outcomes_effective hmin P I.outcome

/-- The named global LR p-value procedure preserves the exact, heterogeneous
finite sufficiency relation, with the factorization and LR reductions proved
internally. -/
theorem packedLowerTailLRPValueProcedure_preserves_sufficiency
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (P : ParameterPartition Theta) :
    Preserves (packedLowerTailLRPValueProcedure.{u, v} P)
      (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) := by
  intro I J hS
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype J.Sample := J.sampleFintype
  letI : Nonempty J.Sample := J.sampleNonempty
  simp only [packedLowerTailLRPValueProcedure, output_graphProcedure]
  apply Set.singleton_eq_singleton_iff.mpr
  apply Subtype.ext
  rcases hS with ⟨T₁, T₂, h, hmin₁, hmin₂, hmass, hobserved⟩
  letI : Fintype T₁.Codomain := T₁.codomainFintype
  letI : Nonempty T₁.Codomain := T₁.codomainNonempty
  letI : Fintype T₂.Codomain := T₂.codomainFintype
  letI : Nonempty T₂.Codomain := T₂.codomainNonempty
  calc
    packedLowerTailLRPValue P I = T₁.reducedPValue P :=
      packedLowerTailLRPValue_eq_reduced P I T₁ hmin₁
    _ = lowerTailLRPValue T₁.inducedModel P (h (T₂.statistic J.outcome)) := by
      rw [← hobserved]
      rfl
    _ = T₂.reducedPValue P := by
      exact lowerTailLRPValue_equiv T₁.inducedModel T₂.inducedModel h hmass P
        (T₂.statistic J.outcome)
    _ = packedLowerTailLRPValue P J :=
      (packedLowerTailLRPValue_eq_reduced P J T₂ hmin₂).symm

end VennDiagrams


/-! ## Reduced-first finite stable conditionality

The laminal construction in this section is applied to the minimal-sufficient
reduced experiment, not to all ancillaries of the unreduced experiment.
Only this explicitly qualified relation is called `SC_red` in the manuscript.
-/

open Finset Classical
open scoped BigOperators

namespace VennDiagrams
namespace ReducedStable

universe u v

variable {Theta : Type u} {X : Type v}
variable [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]

noncomputable def eventMass (E : FiniteModel Theta X) (theta : Theta)
    (s : Finset X) : ℝ := ∑ x ∈ s, E.pmf theta x

def AncillaryEvent (E : FiniteModel Theta X) (s : Finset X) : Prop :=
  ∀ theta psi, eventMass E theta s = eventMass E psi s

def CentralEvent (E : FiniteModel Theta X) (s : Finset X) : Prop :=
  AncillaryEvent E s ∧ ∀ t, AncillaryEvent E t → AncillaryEvent E (s ∩ t)

noncomputable def laminalCell (E : FiniteModel Theta X) (x : X) : Finset X := by
  classical
  exact univ.filter fun y ↦
    ∀ s : Finset X, CentralEvent E s → (x ∈ s ↔ y ∈ s)

noncomputable def laminalConditionalPMF (E : FiniteModel Theta X) (x : X)
    (theta : Theta) (y : X) : ℝ := by
  classical
  exact if y ∈ laminalCell E x then
    E.pmf theta y / eventMass E theta (laminalCell E x) else 0

@[simp] theorem eventMass_univ (E : FiniteModel Theta X) (theta : Theta) :
    eventMass E theta univ = 1 := E.pmf_sum_one theta

theorem eventMass_nonneg (E : FiniteModel Theta X) (theta : Theta) (s : Finset X) :
    0 ≤ eventMass E theta s :=
  Finset.sum_nonneg fun x _ ↦ E.pmf_nonneg theta x

theorem eventMass_mono (E : FiniteModel Theta X) (theta : Theta)
    {s t : Finset X} (hst : s ⊆ t) : eventMass E theta s ≤ eventMass E theta t := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hst
  intro x _ _
  exact E.pmf_nonneg theta x

theorem eventMass_inter_add_sdiff (E : FiniteModel Theta X) (theta : Theta)
    (s t : Finset X) :
    eventMass E theta (s ∩ t) + eventMass E theta (s \ t) = eventMass E theta s := by
  classical
  exact Finset.sum_inter_add_sum_sdiff s t (E.pmf theta)

theorem ancillaryEvent_univ (E : FiniteModel Theta X) : AncillaryEvent E univ := by
  intro theta psi
  simp

theorem ancillaryEvent_sdiff (E : FiniteModel Theta X) (s t : Finset X)
    (hs : AncillaryEvent E s) (hst : AncillaryEvent E (s ∩ t)) :
    AncillaryEvent E (s \ t) := by
  intro theta psi
  have ht := eventMass_inter_add_sdiff E theta s t
  have hp := eventMass_inter_add_sdiff E psi s t
  rw [hs theta psi, hst theta psi] at ht
  linarith

theorem ancillaryEvent_compl (E : FiniteModel Theta X) (s : Finset X)
    (hs : AncillaryEvent E s) : AncillaryEvent E sᶜ := by
  classical
  simpa only [Finset.compl_eq_univ_sdiff] using
    ancillaryEvent_sdiff E univ s (ancillaryEvent_univ E) (by simpa using hs)

theorem centralEvent_univ (E : FiniteModel Theta X) : CentralEvent E univ := by
  refine ⟨ancillaryEvent_univ E, ?_⟩
  intro t ht
  simpa using ht

theorem centralEvent_compl (E : FiniteModel Theta X) (s : Finset X)
    (hs : CentralEvent E s) : CentralEvent E sᶜ := by
  classical
  refine ⟨ancillaryEvent_compl E s hs.1, ?_⟩
  intro t ht
  have hinter : AncillaryEvent E (t ∩ s) := by
    simpa [Finset.inter_comm] using hs.2 t ht
  simpa [Finset.sdiff_eq_inter_compl, Finset.inter_comm] using
    ancillaryEvent_sdiff E t s ht hinter

theorem centralEvent_inter (E : FiniteModel Theta X) (s t : Finset X)
    (hs : CentralEvent E s) (ht : CentralEvent E t) : CentralEvent E (s ∩ t) := by
  classical
  refine ⟨hs.2 t ht.1, ?_⟩
  intro a ha
  simpa [Finset.inter_assoc] using hs.2 (t ∩ a) (ht.2 a ha)

theorem centralEvent_finiteIntersection (E : FiniteModel Theta X)
    (F : Finset (Finset X)) (hF : ∀ s ∈ F, CentralEvent E s) :
    CentralEvent E (univ.filter fun y ↦ ∀ s ∈ F, y ∈ s) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using centralEvent_univ E
  | @insert s F hs ih =>
    have heq : (univ.filter fun y ↦ ∀ t ∈ insert s F, y ∈ t) =
        s ∩ (univ.filter fun y ↦ ∀ t ∈ F, y ∈ t) := by
      ext y
      simp
    rw [heq]
    exact centralEvent_inter E s _ (hF s (mem_insert_self s F))
      (ih fun t ht ↦ hF t (mem_insert_of_mem ht))

@[simp] theorem mem_laminalCell_iff (E : FiniteModel Theta X) (x y : X) :
    y ∈ laminalCell E x ↔
      ∀ s : Finset X, CentralEvent E s → (x ∈ s ↔ y ∈ s) := by
  classical
  simp [laminalCell]

theorem laminalCell_eq_intersection (E : FiniteModel Theta X) (x : X) :
    laminalCell E x =
      univ.filter (fun y ↦ ∀ s ∈ (univ.filter fun s : Finset X ↦
        CentralEvent E s ∧ x ∈ s), y ∈ s) := by
  classical
  ext y
  simp only [mem_laminalCell_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hy s hs
    exact (hy s hs.1).mp hs.2
  · intro hy s hs
    constructor
    · intro hx
      exact hy s ⟨hs, hx⟩
    · intro hys
      by_contra hx
      have hyc := hy sᶜ ⟨centralEvent_compl E s hs, by simpa using hx⟩
      exact (Finset.mem_compl.mp hyc) hys

theorem laminalCell_central (E : FiniteModel Theta X) (x : X) :
    CentralEvent E (laminalCell E x) := by
  classical
  rw [laminalCell_eq_intersection]
  apply centralEvent_finiteIntersection
  intro s hs
  exact (mem_filter.mp hs).2.1

theorem laminalCell_ancillary (E : FiniteModel Theta X) (x : X) :
    AncillaryEvent E (laminalCell E x) := (laminalCell_central E x).1

theorem laminalCell_subset_central (E : FiniteModel Theta X) (x : X)
    (s : Finset X) (hs : CentralEvent E s) (hxs : x ∈ s) : laminalCell E x ⊆ s := by
  intro y hy
  exact ((mem_laminalCell_iff E x y).mp hy s hs).mp hxs

@[simp] theorem mem_laminalCell_self (E : FiniteModel Theta X) (x : X) :
    x ∈ laminalCell E x := by
  rw [mem_laminalCell_iff]
  intro s hs
  rfl

theorem mem_laminalCell_symm (E : FiniteModel Theta X) {x y : X}
    (h : y ∈ laminalCell E x) : x ∈ laminalCell E y := by
  rw [mem_laminalCell_iff] at h ⊢
  intro s hs
  exact (h s hs).symm

theorem mem_laminalCell_trans (E : FiniteModel Theta X) {x y z : X}
    (hxy : y ∈ laminalCell E x) (hyz : z ∈ laminalCell E y) :
    z ∈ laminalCell E x := by
  rw [mem_laminalCell_iff] at hxy hyz ⊢
  intro s hs
  exact (hxy s hs).trans (hyz s hs)

theorem laminalCell_eq_of_mem (E : FiniteModel Theta X) {x y : X}
    (hxy : y ∈ laminalCell E x) : laminalCell E x = laminalCell E y := by
  ext z
  constructor
  · exact mem_laminalCell_trans E (mem_laminalCell_symm E hxy)
  · exact mem_laminalCell_trans E hxy

theorem laminalCell_eq_iff (E : FiniteModel Theta X) (x y : X) :
    laminalCell E x = laminalCell E y ↔ y ∈ laminalCell E x := by
  constructor
  · intro h
    rw [h]
    exact mem_laminalCell_self E y
  · exact laminalCell_eq_of_mem E

theorem laminalCell_fiber (E : FiniteModel Theta X) (x : X) :
    (univ.filter fun y ↦ laminalCell E y = laminalCell E x) = laminalCell E x := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact eq_comm.trans (laminalCell_eq_iff E x y)

/-- The center atoms define an actual ancillary statistic, not merely a
collection of events of parameter-independent probability. -/
theorem laminalStatistic_ancillary (E : FiniteModel Theta X) :
    Ancillary E (laminalCell E) := by
  intro theta psi a
  by_cases ha : ∃ x, laminalCell E x = a
  · obtain ⟨x, rfl⟩ := ha
    have hsum (tau : Theta) : inducedPMF E (laminalCell E) tau (laminalCell E x) =
        eventMass E tau (laminalCell E x) := by
      unfold inducedPMF eventMass
      apply Finset.sum_congr
      · ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact eq_comm.trans (laminalCell_eq_iff E x y)
      · intro y hy
        rfl
    rw [hsum theta, hsum psi]
    exact laminalCell_ancillary E x theta psi
  · have hn : ∀ x, laminalCell E x ≠ a := fun x hx ↦ ha ⟨x, hx⟩
    simp [inducedPMF, hn]

/-- Maximality in fiber form: a statistic with central fibers cannot
distinguish observations in the same laminal cell. -/
theorem statistic_eq_of_laminalCell_eq (E : FiniteModel Theta X)
    {Y : Type*} (A : X → Y)
    (hA : ∀ a, CentralEvent E (univ.filter fun z ↦ A z = a))
    {x y : X} (hxy : laminalCell E x = laminalCell E y) : A x = A y := by
  have hy : y ∈ laminalCell E x := (laminalCell_eq_iff E x y).mp hxy
  have hys := laminalCell_subset_central E x
    (univ.filter fun z ↦ A z = A x) (hA (A x)) (by simp) hy
  exact (mem_filter.mp hys).2.symm

theorem laminalCell_mass_pos (E : FiniteModel Theta X)
    (hall : ∀ x, x ∈ effectiveSupport E) (x : X) (theta : Theta) :
    0 < eventMass E theta (laminalCell E x) := by
  obtain ⟨psi, hpsi⟩ := hall x
  have hle : E.pmf psi x ≤ eventMass E psi (laminalCell E x) :=
    Finset.single_le_sum (fun y _ ↦ E.pmf_nonneg psi y) (mem_laminalCell_self E x)
  rw [laminalCell_ancillary E x theta psi]
  exact hpsi.trans_le hle

theorem laminalConditionalPMF_nonneg (E : FiniteModel Theta X) (x : X)
    (theta : Theta) (y : X) : 0 ≤ laminalConditionalPMF E x theta y := by
  classical
  unfold laminalConditionalPMF
  split_ifs
  · exact div_nonneg (E.pmf_nonneg theta y) (eventMass_nonneg E theta _)
  · exact le_rfl

theorem laminalConditionalPMF_sum_one (E : FiniteModel Theta X)
    (hall : ∀ x, x ∈ effectiveSupport E) (x : X) (theta : Theta) :
    ∑ y, laminalConditionalPMF E x theta y = 1 := by
  classical
  simp only [laminalConditionalPMF]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (laminalCell_mass_pos E hall x theta))

noncomputable def laminalConditionalModel (E : FiniteModel Theta X)
    (hall : ∀ x, x ∈ effectiveSupport E) (x : X) : FiniteModel Theta X where
  pmf := laminalConditionalPMF E x
  pmf_nonneg := laminalConditionalPMF_nonneg E x
  pmf_sum_one := laminalConditionalPMF_sum_one E hall x

end ReducedStable
end VennDiagrams

open Finset
open scoped BigOperators Classical

namespace VennDiagrams
namespace ReducedStable

universe u v w

variable {Theta : Type u} {X : Type v}
variable [Fintype Theta] [Nonempty Theta] [Fintype X] [Nonempty X]

/-- A conforming event remains ancillary after conditioning on any ancillary
event. The equality also covers zero-mass events using real division by zero;
the probability interpretation uses positive conditioning mass. -/
theorem centralEvent_conditional_invariance
    (E : FiniteModel Theta X) {s t : Finset X}
    (hs : CentralEvent E s) (ht : AncillaryEvent E t)
    (theta psi : Theta) :
    eventMass E theta (s ∩ t) / eventMass E theta t =
      eventMass E psi (s ∩ t) / eventMass E psi t := by
  rw [hs.2 t ht theta psi, ht theta psi]

/-- Conformity is exactly preservation of ancillarity under all ancillary
event conditionings. Zero-probability events have zero intersection mass,
so this characterization does not hide a positivity assumption. -/
theorem centralEvent_iff_conditional_invariance
    (E : FiniteModel Theta X) (s : Finset X) :
    CentralEvent E s ↔ AncillaryEvent E s ∧
      ∀ t, AncillaryEvent E t → ∀ theta psi,
        eventMass E theta (s ∩ t) / eventMass E theta t =
          eventMass E psi (s ∩ t) / eventMass E psi t := by
  constructor
  · intro hs
    exact ⟨hs.1, fun t ht theta psi ↦
      centralEvent_conditional_invariance E hs ht theta psi⟩
  · rintro ⟨hs, hcond⟩
    refine ⟨hs, ?_⟩
    intro t ht theta psi
    by_cases hz : eventMass E theta t = 0
    · have hpz : eventMass E psi t = 0 := (ht theta psi).symm.trans hz
      have hzero : ∀ alpha, eventMass E alpha t = 0 →
          eventMass E alpha (s ∩ t) = 0 := by
        intro alpha halpha
        apply le_antisymm
        · exact (eventMass_mono E alpha Finset.inter_subset_right).trans (le_of_eq halpha)
        · exact eventMass_nonneg E alpha (s ∩ t)
      rw [hzero theta hz, hzero psi hpz]
    · have hc := hcond t ht theta psi
      rw [← ht theta psi] at hc
      exact (div_left_inj' hz).mp hc

/-- Every fiber of an ancillary statistic is an ancillary event. -/
theorem ancillaryEvent_fiber
    (E : FiniteModel Theta X) {Y : Type w} (A : X → Y)
    (hA : Ancillary E A) (a : Y) :
    AncillaryEvent E (Finset.univ.filter (fun x ↦ A x = a)) := by
  classical
  intro theta psi
  simpa [eventMass, inducedPMF] using hA theta psi a

/-- Exact finite reweighting of the conditional component models indexed by
an ancillary statistic. A probability interpretation requires nonnegative
weights summing to one and zero weights for impossible components. -/
noncomputable def reweightedEventMass
    (E : FiniteModel Theta X) {Y : Type w} [Fintype Y]
    (A : X → Y) (weights : Y → ℝ) (theta : Theta) (s : Finset X) : ℝ := by
  classical
  exact ∑ a, weights a *
    (eventMass E theta (s ∩ Finset.univ.filter (fun x ↦ A x = a)) /
      eventMass E theta (Finset.univ.filter (fun x ↦ A x = a)))

/-- Stability under every finite reweighting of any ancillary statistic.
The stronger equality for arbitrary real weights includes all supported
probability weights and does not assume stability as a hypothesis. -/
theorem centralEvent_reweighting_invariant
    (E : FiniteModel Theta X) {Y : Type w} [Fintype Y]
    (A : X → Y) (hA : Ancillary E A) (weights : Y → ℝ)
    {s : Finset X} (hs : CentralEvent E s) (theta psi : Theta) :
    reweightedEventMass E A weights theta s =
      reweightedEventMass E A weights psi s := by
  classical
  unfold reweightedEventMass
  apply Finset.sum_congr rfl
  intro a _
  rw [centralEvent_conditional_invariance E hs
    (ancillaryEvent_fiber E A hA a) theta psi]

end ReducedStable
end VennDiagrams

open scoped BigOperators

namespace VennDiagrams
namespace ReducedStable

universe u v w
variable {Theta : Type u} {X : Type v} {Y : Type w}
variable [Fintype Theta] [Nonempty Theta]
variable [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]

/-- Relabelling an event preserves its probability under the matched models. -/
theorem eventMass_map_equiv
    (E1 : FiniteModel Theta X) (E2 : FiniteModel Theta Y)
    (e : Y ≃ X)
    (hmass : ∀ theta y, E1.pmf theta (e y) = E2.pmf theta y)
    (theta : Theta) (s : Finset Y) :
    eventMass E1 theta (s.map e.toEmbedding) = eventMass E2 theta s := by
  classical
  simp only [eventMass, Finset.sum_map, Equiv.coe_toEmbedding, hmass]

theorem AncillaryEvent_map_equiv_iff
    (E1 : FiniteModel Theta X) (E2 : FiniteModel Theta Y)
    (e : Y ≃ X)
    (hmass : ∀ theta y, E1.pmf theta (e y) = E2.pmf theta y)
    (s : Finset Y) :
    AncillaryEvent E1 (s.map e.toEmbedding) ↔ AncillaryEvent E2 s := by
  simp only [AncillaryEvent, eventMass_map_equiv E1 E2 e hmass]

/-- The stable-event structure is equivariant under an exact model relabelling. -/
theorem CentralEvent_map_equiv_iff
    (E1 : FiniteModel Theta X) (E2 : FiniteModel Theta Y)
    (e : Y ≃ X)
    (hmass : ∀ theta y, E1.pmf theta (e y) = E2.pmf theta y)
    (s : Finset Y) :
    CentralEvent E1 (s.map e.toEmbedding) ↔ CentralEvent E2 s := by
  classical
  constructor
  · rintro ⟨hs, hcentral⟩
    refine ⟨(AncillaryEvent_map_equiv_iff E1 E2 e hmass s).mp hs, ?_⟩
    intro t ht
    apply (AncillaryEvent_map_equiv_iff E1 E2 e hmass (s ∩ t)).mp
    rw [Finset.map_inter]
    exact hcentral (t.map e.toEmbedding)
      ((AncillaryEvent_map_equiv_iff E1 E2 e hmass t).mpr ht)
  · rintro ⟨hs, hcentral⟩
    refine ⟨(AncillaryEvent_map_equiv_iff E1 E2 e hmass s).mpr hs, ?_⟩
    intro t ht
    have hback : ∀ theta x, E2.pmf theta (e.symm x) = E1.pmf theta x := by
      intro theta x
      simpa only [e.apply_symm_apply] using (hmass theta (e.symm x)).symm
    have hanc : AncillaryEvent E2 (t.map e.symm.toEmbedding) :=
      (AncillaryEvent_map_equiv_iff E2 E1 e.symm hback t).mpr ht
    have hjoint := (AncillaryEvent_map_equiv_iff E1 E2 e hmass
      (s ∩ t.map e.symm.toEmbedding)).mpr
        (hcentral (t.map e.symm.toEmbedding) hanc)
    have hsets : (s ∩ t.map e.symm.toEmbedding).map e.toEmbedding =
        s.map e.toEmbedding ∩ t := by
      ext x
      simp
    exact hsets ▸ hjoint

/-- Laminal-cell membership is unaffected by relabelling the reduced experiment. -/
theorem mem_laminalCell_equiv
    (E1 : FiniteModel Theta X) (E2 : FiniteModel Theta Y)
    (e : Y ≃ X)
    (hmass : ∀ theta y, E1.pmf theta (e y) = E2.pmf theta y)
    (x y : Y) :
    e y ∈ laminalCell E1 (e x) ↔ y ∈ laminalCell E2 x := by
  classical
  simp only [laminalCell, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h s hs
    have hx := h (s.map e.toEmbedding)
      ((CentralEvent_map_equiv_iff E1 E2 e hmass s).mpr hs)
    simpa using hx
  · intro h s hs
    have hback : ∀ theta x, E2.pmf theta (e.symm x) = E1.pmf theta x := by
      intro theta x
      simpa only [e.apply_symm_apply] using (hmass theta (e.symm x)).symm
    have hx := h (s.map e.symm.toEmbedding)
      ((CentralEvent_map_equiv_iff E2 E1 e.symm hback s).mpr hs)
    simpa using hx

theorem laminalCell_equiv
    (E1 : FiniteModel Theta X) (E2 : FiniteModel Theta Y)
    (e : Y ≃ X)
    (hmass : ∀ theta y, E1.pmf theta (e y) = E2.pmf theta y)
    (x : Y) :
    laminalCell E1 (e x) = (laminalCell E2 x).map e.toEmbedding := by
  classical
  ext z
  obtain ⟨y, rfl⟩ := e.surjective z
  simpa using mem_laminalCell_equiv E1 E2 e hmass x y

theorem eventMass_laminalCell_equiv
    (E1 : FiniteModel Theta X) (E2 : FiniteModel Theta Y)
    (e : Y ≃ X)
    (hmass : ∀ theta y, E1.pmf theta (e y) = E2.pmf theta y)
    (x : Y) (theta : Theta) :
    eventMass E1 theta (laminalCell E1 (e x)) =
      eventMass E2 theta (laminalCell E2 x) := by
  rw [laminalCell_equiv E1 E2 e hmass x]
  exact eventMass_map_equiv E1 E2 e hmass theta (laminalCell E2 x)

/-- The laminal conditional PMFs transform by the same exact sample bijection. -/
theorem laminalConditionalPMF_equiv
    (E1 : FiniteModel Theta X) (E2 : FiniteModel Theta Y)
    (e : Y ≃ X)
    (hmass : ∀ theta y, E1.pmf theta (e y) = E2.pmf theta y)
    (x y : Y) (theta : Theta) :
    laminalConditionalPMF E1 (e x) theta (e y) =
      laminalConditionalPMF E2 x theta y := by
  classical
  simp only [laminalConditionalPMF, mem_laminalCell_equiv E1 E2 e hmass x y,
    hmass, eventMass_laminalCell_equiv E1 E2 e hmass x theta]

end ReducedStable
end VennDiagrams

namespace VennDiagrams

universe u v

/-- Surjectivity onto the statistic range preserves effectiveness of every
outcome of the induced model. -/
theorem PackedFiniteStatistic.inducedModel_all_effective
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    {I : PackedFiniteInferenceBase.{u, v} Theta} (T : PackedFiniteStatistic I) :
    letI : Fintype T.Codomain := T.codomainFintype
    letI : Nonempty T.Codomain := T.codomainNonempty
    ∀ y, y ∈ effectiveSupport T.inducedModel := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype T.Codomain := T.codomainFintype
  letI : Nonempty T.Codomain := T.codomainNonempty
  classical
  intro y
  obtain ⟨x, rfl⟩ := T.statistic_surjective y
  obtain ⟨theta, htheta⟩ := I.all_outcomes_effective x
  refine ⟨theta, htheta.trans_le ?_⟩
  change I.model.pmf theta x ≤ inducedPMF I.model T.statistic theta (T.statistic x)
  unfold inducedPMF
  exact Finset.single_le_sum (fun z _ ↦ I.model.pmf_nonneg theta z)
    (by simp)

/-- Reduced-first stable conditionality on the paper's packed finite universe.
Both models are first reduced by genuinely minimal sufficient statistics.
Their laminal conditional PMFs then agree through a bijection of the complete
minimal-statistic ranges, with the observed statistic values corresponding.
The conditional PMFs are zero outside their observed laminal cells. -/
def packedFiniteReducedStableConditionalityRelation
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
          ReducedStable.laminalConditionalPMF T₁.inducedModel
              (T₁.statistic I.outcome) theta (h y) =
            ReducedStable.laminalConditionalPMF T₂.inducedModel
              (T₂.statistic J.outcome) theta y) ∧
        T₁.statistic I.outcome = h (T₂.statistic J.outcome)

/-- Sufficiency is included in reduced-first stable conditionality because
laminal conditioning is invariant under the same parameterwise relabelling. -/
theorem packedFiniteSufficiencyRelation_le_reducedStableConditionality
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    packedFiniteSufficiencyRelation.{u, v} (Theta := Theta) ≤
      packedFiniteReducedStableConditionalityRelation.{u, v} (Theta := Theta) := by
  intro I J hS
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype J.Sample := J.sampleFintype
  letI : Nonempty J.Sample := J.sampleNonempty
  rcases hS with ⟨T₁, T₂, h, hmin₁, hmin₂, hmass, hobserved⟩
  letI : Fintype T₁.Codomain := T₁.codomainFintype
  letI : Nonempty T₁.Codomain := T₁.codomainNonempty
  letI : Fintype T₂.Codomain := T₂.codomainFintype
  letI : Nonempty T₂.Codomain := T₂.codomainNonempty
  refine ⟨T₁, T₂, h, hmin₁, hmin₂, ?_, hobserved⟩
  intro theta y
  rw [hobserved]
  exact ReducedStable.laminalConditionalPMF_equiv
    T₁.inducedModel T₂.inducedModel h hmass (T₂.statistic J.outcome) y theta

theorem packedFiniteReducedStableConditionalityRelation_reflexive
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Reflexive
      (packedFiniteReducedStableConditionalityRelation.{u, v} (Theta := Theta)) := by
  intro I
  exact packedFiniteSufficiencyRelation_le_reducedStableConditionality I I
    (packedFiniteSufficiencyRelation_reflexive I)

theorem packedFiniteReducedStableConditionalityRelation_symmetric
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Symmetric
      (packedFiniteReducedStableConditionalityRelation.{u, v} (Theta := Theta)) := by
  intro I J hSC
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype J.Sample := J.sampleFintype
  letI : Nonempty J.Sample := J.sampleNonempty
  rcases hSC with ⟨T₁, T₂, h, hmin₁, hmin₂, hmass, hobserved⟩
  refine ⟨T₂, T₁, h.symm, hmin₂, hmin₁, ?_, ?_⟩
  · intro theta y
    letI : Fintype T₁.Codomain := T₁.codomainFintype
    letI : Nonempty T₁.Codomain := T₁.codomainNonempty
    letI : Fintype T₂.Codomain := T₂.codomainFintype
    letI : Nonempty T₂.Codomain := T₂.codomainNonempty
    simpa using (hmass theta (h.symm y)).symm
  · have hobs := congrArg h.symm hobserved
    simpa using hobs.symm

/-! ## Singleton parameters and a parameter-free separation from direct C -/

theorem proportional_of_subsingleton_parameter
    {Theta : Type u} [Nonempty Theta] [Subsingleton Theta]
    {f g : Theta → ℝ} (hf : ∃ theta, 0 < f theta)
    (hg : ∃ theta, 0 < g theta) : Proportional f g := by
  obtain ⟨theta₀, hf⟩ := hf
  obtain ⟨theta₁, hg⟩ := hg
  have heq : theta₁ = theta₀ := Subsingleton.elim _ _
  subst theta₁
  refine ⟨f theta₀ / g theta₀, div_pos hf hg, ?_⟩
  intro theta
  have heq : theta = theta₀ := Subsingleton.elim _ _
  subst theta
  field_simp

theorem packed_likelihood_universal_of_subsingleton_parameter
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] [Subsingleton Theta]
    (I J : PackedFiniteInferenceBase.{u, v} Theta) :
    packedFiniteLikelihoodRelation I J := by
  exact proportional_of_subsingleton_parameter I.outcome_effective J.outcome_effective

def packedConstantStatistic
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase.{u, v} Theta) : PackedFiniteStatistic I where
  Codomain := PUnit.{v+1}
  codomainFintype := inferInstance
  codomainNonempty := inferInstance
  statistic := fun _ ↦ PUnit.unit
  statistic_surjective := by
    intro y
    exact ⟨I.outcome, Subsingleton.elim _ _⟩

theorem packed_constant_minimal_of_subsingleton_parameter
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] [Subsingleton Theta]
    (I : PackedFiniteInferenceBase.{u, v} Theta) :
    letI : Fintype I.Sample := I.sampleFintype
    letI : Nonempty I.Sample := I.sampleNonempty
    FiniteMinimalSufficient I.model (packedConstantStatistic I).statistic := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  apply likelihoodFiberCriterion_implies_finiteMinimalSufficient
      I.model (packedConstantStatistic I).statistic I.all_outcomes_effective
  intro x y
  exact ⟨fun _ ↦ proportional_of_subsingleton_parameter
    (I.all_outcomes_effective x) (I.all_outcomes_effective y),
    fun _ ↦ rfl⟩

theorem packed_sufficiency_universal_of_subsingleton_parameter
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] [Subsingleton Theta]
    (I J : PackedFiniteInferenceBase.{u, v} Theta) :
    packedFiniteSufficiencyRelation I J := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype J.Sample := J.sampleFintype
  letI : Nonempty J.Sample := J.sampleNonempty
  refine ⟨packedConstantStatistic I, packedConstantStatistic J, Equiv.refl _,
    packed_constant_minimal_of_subsingleton_parameter I,
    packed_constant_minimal_of_subsingleton_parameter J, ?_, rfl⟩
  intro theta y
  change inducedPMF I.model (fun _ ↦ PUnit.unit) theta y =
    inducedPMF J.model (fun _ ↦ PUnit.unit) theta y
  rw [inducedPMF_const_eq _ _ _ _ (Subsingleton.elim _ _),
    inducedPMF_const_eq _ _ _ _ (Subsingleton.elim _ _)]

theorem packed_sufficiency_eq_likelihood_of_subsingleton_parameter
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] [Subsingleton Theta] :
    packedFiniteSufficiencyRelation.{u, v} (Theta := Theta) =
      packedFiniteLikelihoodRelation := by
  funext I J
  exact propext ⟨fun _ ↦ packed_likelihood_universal_of_subsingleton_parameter I J,
    fun _ ↦ packed_sufficiency_universal_of_subsingleton_parameter I J⟩

theorem packed_BT1_strictness_false_of_subsingleton_parameter
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] [Subsingleton Theta]
    (A : Type w) :
    ¬ preservingClass A (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) ⊂
      preservingClass A (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) := by
  rw [packed_sufficiency_eq_likelihood_of_subsingleton_parameter]
  simp

theorem no_partition_of_subsingleton_parameter
    {Theta : Type u} [Fintype Theta] [Subsingleton Theta] :
    IsEmpty (ParameterPartition Theta) := by
  refine ⟨fun P ↦ ?_⟩
  obtain ⟨x, hx⟩ := P.null_nonempty
  obtain ⟨y, hy⟩ := P.alternative_nonempty
  have heq : x = y := Subsingleton.elim _ _
  exact P.disjoint hx (heq ▸ hy)

noncomputable def parameterFreeCoinModel
    (Theta : Type u) [Fintype Theta] [Nonempty Theta] :
    FiniteModel Theta (ULift.{v} (Fin 2)) where
  pmf := fun _ _ ↦ 1 / 2
  pmf_nonneg := by intros; norm_num
  pmf_sum_one := by intros; norm_num

noncomputable def packedParameterFreeCoin
    (Theta : Type u) [Fintype Theta] [Nonempty Theta]
    (x : Fin 2) : PackedFiniteInferenceBase.{u, v} Theta where
  Sample := ULift.{v} (Fin 2)
  sampleFintype := inferInstance
  sampleNonempty := inferInstance
  outcomeCode := fun y ↦ y.down.val
  outcomeCode_injective := by
    intro x y h
    exact ULift.ext _ _ (Fin.val_injective h)
  model := parameterFreeCoinModel Theta
  outcome := ULift.up x
  outcome_effective := by
    refine ⟨Classical.choice inferInstance, ?_⟩
    norm_num [parameterFreeCoinModel]
  all_outcomes_effective := by
    intro y
    refine ⟨Classical.choice inferInstance, ?_⟩
    norm_num [parameterFreeCoinModel]

theorem parameterFreeCoin_minimal
    (Theta : Type u) [Fintype Theta] [Nonempty Theta] :
    FiniteMinimalSufficient (parameterFreeCoinModel.{u, v} Theta)
      (fun _ ↦ (PUnit.unit : PUnit.{v+1})) := by
  apply likelihoodFiberCriterion_implies_finiteMinimalSufficient
    (parameterFreeCoinModel Theta) _
    (packedParameterFreeCoin Theta 0).all_outcomes_effective
  intro x y
  exact ⟨fun _ ↦ proportional_refl _, fun _ ↦ rfl⟩

theorem parameterFreeCoin_in_sufficiency_not_conditionality
    (Theta : Type u) [Fintype Theta] [Nonempty Theta] :
    packedFiniteSufficiencyRelation
        (packedParameterFreeCoin.{u, v} Theta 0) (packedParameterFreeCoin Theta 1) ∧
      ¬ packedFiniteConditionalityRelation.{u, v}
        (packedParameterFreeCoin Theta 0) (packedParameterFreeCoin Theta 1) := by
  constructor
  · refine ⟨packedConstantStatistic _, packedConstantStatistic _, Equiv.refl _,
      parameterFreeCoin_minimal Theta, parameterFreeCoin_minimal Theta, ?_, rfl⟩
    intro theta y
    rfl
  · intro h
    have hcode : Function.Injective
        (fun y : ULift.{v} (Fin 2) ↦ y.down.val) := by
      intro x y h
      exact ULift.ext _ _ (Fin.val_injective h)
    rcases h with hforward | hreverse
    · have heq := finiteDirectionalConditionalityPair_same_code_observation_eq
        hcode hforward
      exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down heq)
    · have heq := finiteDirectionalConditionalityPair_same_code_observation_eq
        hcode hreverse
      exact (by decide : (1 : Fin 2) ≠ 0) (congrArg ULift.down heq)

theorem packed_sufficiency_not_le_conditionality_all_parameters
    (Theta : Type u) [Fintype Theta] [Nonempty Theta] :
    ¬ packedFiniteSufficiencyRelation.{u, v} (Theta := Theta) ≤
      packedFiniteConditionalityRelation := by
  intro h
  obtain ⟨hS, hC⟩ := parameterFreeCoin_in_sufficiency_not_conditionality Theta
  exact hC (h _ _ hS)

theorem packed_reduced_stable_not_le_conditionality_all_parameters
    (Theta : Type u) [Fintype Theta] [Nonempty Theta] :
    ¬ packedFiniteReducedStableConditionalityRelation.{u, v} (Theta := Theta) ≤
      packedFiniteConditionalityRelation := by
  intro h
  exact packed_sufficiency_not_le_conditionality_all_parameters Theta
    (le_trans packedFiniteSufficiencyRelation_le_reducedStableConditionality h)

theorem packed_conditionality_le_sufficiency_of_subsingleton_parameter
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] [Subsingleton Theta] :
    packedFiniteConditionalityRelation.{u, v} (Theta := Theta) ≤
      packedFiniteSufficiencyRelation := by
  intro I J _
  exact packed_sufficiency_universal_of_subsingleton_parameter I J

theorem packed_conditionality_not_transitive_all_parameters
    (Theta : Type u) [Fintype Theta] [Nonempty Theta] :
    ¬ Transitive (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) := by
  intro htrans
  have hEq : Equivalence
      (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) :=
    ⟨packedFiniteConditionalityRelation_reflexive,
      fun h ↦ packedFiniteConditionalityRelation_symmetric h,
      fun h₁ h₂ ↦ htrans h₁ h₂⟩
  have hL : packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) ≤
      packedFiniteConditionalityRelation := by
    rw [← packedFiniteConditionalityClosure_eq_likelihoodRelation]
    exact equivalenceClosure_minimal hEq le_rfl
  exact packed_sufficiency_not_le_conditionality_all_parameters Theta
    (le_trans packedFiniteSufficiencyRelation_le_likelihoodRelation hL)

theorem packed_reduced_stable_universal_of_subsingleton_parameter
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] [Subsingleton Theta]
    (I J : PackedFiniteInferenceBase.{u, v} Theta) :
    packedFiniteReducedStableConditionalityRelation I J :=
  packedFiniteSufficiencyRelation_le_reducedStableConditionality I J
    (packed_sufficiency_universal_of_subsingleton_parameter I J)


end VennDiagrams
