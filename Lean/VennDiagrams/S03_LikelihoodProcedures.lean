import VennDiagrams.S01_Relations
import Mathlib

/-!
# S03 — Likelihood-proportional procedures

The paper's likelihood relation depends only on positive proportionality of
the two observed likelihood functions.  This module proves that relation is
an equivalence relation and certifies the MLE, posterior, and Bayesian-ray
invariance statements at their natural level of generality.
-/

open Set Finset
open scoped BigOperators

namespace VennDiagrams

universe u v

/-- Positive proportionality of two real-valued likelihood functions. -/
def Proportional {Θ : Type u} (f g : Θ → ℝ) : Prop :=
  ∃ k : ℝ, 0 < k ∧ ∀ θ, f θ = k * g θ

theorem proportional_refl {Θ : Type u} (f : Θ → ℝ) : Proportional f f := by
  refine ⟨1, by norm_num, ?_⟩
  intro θ
  ring

theorem proportional_symm {Θ : Type u} {f g : Θ → ℝ}
    (h : Proportional f g) : Proportional g f := by
  rcases h with ⟨k, hk, hfg⟩
  refine ⟨k⁻¹, inv_pos.mpr hk, ?_⟩
  intro θ
  rw [hfg θ]
  field_simp [ne_of_gt hk]

theorem proportional_trans {Θ : Type u} {f g h : Θ → ℝ}
    (hfg : Proportional f g) (hgh : Proportional g h) : Proportional f h := by
  rcases hfg with ⟨k, hk, hfg⟩
  rcases hgh with ⟨c, hc, hgh⟩
  refine ⟨k * c, mul_pos hk hc, ?_⟩
  intro θ
  rw [hfg θ, hgh θ]
  ring

/-- The likelihood relation on any collection of inference bases carrying an
observed likelihood function. -/
def likelihoodRelation {ι : Type u} {Θ : Type v} (likelihood : ι → Θ → ℝ) :
    StatisticalRelation ι :=
  fun i j ↦ Proportional (likelihood i) (likelihood j)

theorem likelihoodRelation_isEquivalence {ι : Type u} {Θ : Type v}
    (likelihood : ι → Θ → ℝ) : Equivalence (likelihoodRelation likelihood) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact proportional_refl _
  · intro i j hij
    exact proportional_symm hij
  · intro i j k hij hjk
    exact proportional_trans hij hjk

/-- The maximum-likelihood set (argmax set), with no uniqueness assumption. -/
def maximizerSet {Θ : Type u} (f : Θ → ℝ) : Set Θ :=
  {θ | ∀ ψ, f ψ ≤ f θ}

theorem maximizerSet_eq_of_proportional {Θ : Type u} {f g : Θ → ℝ}
    (h : Proportional f g) : maximizerSet f = maximizerSet g := by
  rcases h with ⟨k, hk, hfg⟩
  ext θ
  constructor
  · intro hmax ψ
    exact (mul_le_mul_iff_of_pos_left hk).mp (by simpa [hfg] using hmax ψ)
  · intro hmax ψ
    have := (mul_le_mul_iff_of_pos_left hk).mpr (hmax ψ)
    simpa [hfg] using this

/-- The graph relation of the manuscript's maximum-likelihood set estimator. -/
def maximumLikelihoodProcedure {ι : Type u} {Θ : Type v}
    (likelihood : ι → Θ → ℝ) : Procedure ι (Set Θ) :=
  graphProcedure fun i ↦ maximizerSet (likelihood i)

/-- Maximum-likelihood set estimates preserve the likelihood relation. -/
theorem maximumLikelihoodProcedure_preserves_likelihood
    {ι : Type u} {Θ : Type v} (likelihood : ι → Θ → ℝ) :
    Preserves (maximumLikelihoodProcedure likelihood) (likelihoodRelation likelihood) := by
  intro i j hij
  simp only [maximumLikelihoodProcedure, output_graphProcedure]
  rw [maximizerSet_eq_of_proportional hij]

/-- A finite likelihood/prior normalizing constant. -/
def posteriorNormalizer {Θ : Type u} [Fintype Θ]
    (likelihood prior : Θ → ℝ) : ℝ :=
  ∑ θ, likelihood θ * prior θ

/-- Posterior mass at one parameter value. -/
noncomputable def posteriorMass {Θ : Type u} [Fintype Θ]
    (likelihood prior : Θ → ℝ) (θ : Θ) : ℝ :=
  likelihood θ * prior θ / posteriorNormalizer likelihood prior

/-- Posterior probability of a finite parameter event. -/
noncomputable def posteriorProbability {Θ : Type u} [Fintype Θ]
    (likelihood prior : Θ → ℝ) (H : Finset Θ) : ℝ :=
  ∑ θ ∈ H, posteriorMass likelihood prior θ

theorem posteriorNormalizer_eq_of_proportional {Θ : Type u} [Fintype Θ]
    {f g prior : Θ → ℝ} {k : ℝ} (h : ∀ θ, f θ = k * g θ) :
    posteriorNormalizer f prior = k * posteriorNormalizer g prior := by
  simp only [posteriorNormalizer, h]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ _
  ring

/-- A positive common likelihood factor cancels from the posterior. -/
theorem posteriorMass_eq_of_proportional {Θ : Type u} [Fintype Θ]
    {f g prior : Θ → ℝ} (hfg : Proportional f g)
    (hden : posteriorNormalizer g prior ≠ 0) (θ : Θ) :
    posteriorMass f prior θ = posteriorMass g prior θ := by
  rcases hfg with ⟨k, hk, hfg⟩
  have hnorm := posteriorNormalizer_eq_of_proportional (prior := prior) hfg
  simp only [posteriorMass, hfg, hnorm]
  field_simp [ne_of_gt hk, hden]

theorem posteriorProbability_eq_of_proportional {Θ : Type u} [Fintype Θ]
    {f g prior : Θ → ℝ} (H : Finset Θ) (hfg : Proportional f g)
    (hden : posteriorNormalizer g prior ≠ 0) :
    posteriorProbability f prior H = posteriorProbability g prior H := by
  simp only [posteriorProbability]
  apply Finset.sum_congr rfl
  intro θ _
  exact posteriorMass_eq_of_proportional hfg hden θ

/-- The graph relation of posterior probabilities for a fixed prior and event. -/
noncomputable def posteriorProcedure {ι : Type u} {Θ : Type v} [Fintype Θ]
    (likelihood : ι → Θ → ℝ) (prior : Θ → ℝ) (H : Finset Θ) : Procedure ι ℝ :=
  graphProcedure fun i ↦ posteriorProbability (likelihood i) prior H

/-- Posterior probabilities preserve `L`, provided their denominators exist. -/
theorem posteriorProcedure_preserves_likelihood
    {ι : Type u} {Θ : Type v} [Fintype Θ]
    (likelihood : ι → Θ → ℝ) (prior : Θ → ℝ) (H : Finset Θ)
    (hden : ∀ i, posteriorNormalizer (likelihood i) prior ≠ 0) :
    Preserves (posteriorProcedure likelihood prior H) (likelihoodRelation likelihood) := by
  intro i j hij
  simp only [posteriorProcedure, output_graphProcedure]
  rw [posteriorProbability_eq_of_proportional H hij (hden j)]

/-- The positive ray generated by a likelihood function. -/
def positiveRay {Θ : Type u} (f : Θ → ℝ) : Set (Θ → ℝ) :=
  {g | ∃ c : ℝ, 0 < c ∧ ∀ θ, g θ = c * f θ}

theorem positiveRay_eq_of_proportional {Θ : Type u} {f g : Θ → ℝ}
    (hfg : Proportional f g) : positiveRay f = positiveRay g := by
  rcases hfg with ⟨k, hk, hfg⟩
  ext q
  constructor
  · rintro ⟨c, hc, hq⟩
    refine ⟨c * k, mul_pos hc hk, ?_⟩
    intro θ
    rw [hq θ, hfg θ]
    ring
  · rintro ⟨c, hc, hq⟩
    refine ⟨c * k⁻¹, mul_pos hc (inv_pos.mpr hk), ?_⟩
    intro θ
    rw [hq θ, hfg θ]
    field_simp [ne_of_gt hk]

/-- Evans-style Bayesian information: every positive likelihood multiple,
paired with every prior object. -/
def bayesianInformationProcedure {ι : Type u} {Θ : Type v} {PriorType : Type*}
    (likelihood : ι → Θ → ℝ) : Procedure ι ((Θ → ℝ) × PriorType) :=
  {p | p.2.1 ∈ positiveRay (likelihood p.1)}

/-- The Bayesian information relation preserves proportional likelihoods. -/
theorem bayesianInformationProcedure_preserves_likelihood
    {ι : Type u} {Θ : Type v} {PriorType : Type*} (likelihood : ι → Θ → ℝ) :
    Preserves (bayesianInformationProcedure (PriorType := PriorType) likelihood)
      (likelihoodRelation likelihood) := by
  intro i j hij
  have hray := positiveRay_eq_of_proportional hij
  ext out
  exact Set.ext_iff.1 hray out.1

/-- A generic ancillary-conditioning factorization immediately gives an `L`
pair.  The positivity condition is essential. -/
theorem conditional_factorization_implies_likelihood
    {Θ : Type u} {fJoint fConditional : Θ → ℝ} {eventProbability : ℝ}
    (hpos : 0 < eventProbability)
    (hfactor : ∀ θ, fJoint θ = eventProbability * fConditional θ) :
    Proportional fJoint fConditional :=
  ⟨eventProbability, hpos, hfactor⟩

end VennDiagrams
