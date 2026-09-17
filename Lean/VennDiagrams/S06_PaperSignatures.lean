import VennDiagrams.S01_Relations
import VennDiagrams.S02_FiniteExamples
import VennDiagrams.S03_LikelihoodProcedures
import VennDiagrams.S04_StatisticalPrimitives
import VennDiagrams.S05_SufficiencyConditionality

/-!
# S06 — Exact paper-facing signatures

This module links the paper's results to exact Lean declarations.
Theorem 3.1 and Corollaries 3.1–3.2 specialize the procedure framework
to finite inference bases, deriving the required relation identities
from the companion's proofs. Internal IDs in declaration names are mapped
to the paper's numbered results in `PAPER_COVERAGE.md`. The reusable
`EvansPremises` structure records hypotheses for abstract variants.
-/

open Set
open scoped BigOperators

namespace VennDiagrams
namespace Certification
namespace PaperSignature

universe u v w

/-- The reusable relation-level interface used by the main procedure theorem.
The packed instance is constructed below from proved Evans certificates. -/
structure EvansPremises {ι : Type u}
    (C S L : StatisticalRelation ι) : Prop where
  sufficiency_equivalence : Equivalence S
  sufficiency_le_likelihood : S ≤ L
  sufficiency_strict_witness : ∃ i j, L i j ∧ ¬ S i j
  conditionality_closure : equivalenceClosure C = L
  joint_closure : equivalenceClosure (relationUnion C S) = L

/-- A separate reusable relation-level witness for `C ∪ S ⊊ L`; it is not a
premise of the procedure-class theorem, whose proof does not use it. -/
structure EvansJointStrictPremise {ι : Type u}
    (C S L : StatisticalRelation ι) : Prop where
  witness : ∃ i j, L i j ∧ ¬ C i j ∧ ¬ S i j

/-- The conditionality-closure field entails `C ⊆ L`. -/
theorem EvansPremises.conditionality_le_likelihood
    {ι : Type u} {C S L : StatisticalRelation ι} (h : EvansPremises C S L) :
    C ≤ L := by
  rw [← h.conditionality_closure]
  exact relation_le_equivalenceClosure C

/-- An explicit witness outside both local relations certifies the paper's
strict inclusion `C ∪ S ⊊ L`. -/
theorem EvansPremises.joint_strict_inclusion
    {ι : Type u} {C S L : StatisticalRelation ι} (h : EvansPremises C S L)
    (hstrict : EvansJointStrictPremise C S L) :
    relationUnion C S < L := by
  rcases hstrict.witness with ⟨i, j, hL, hC, hS⟩
  exact relationUnion_lt_of_witness h.conditionality_le_likelihood
    h.sufficiency_le_likelihood hL hC hS

-- manuscript-id: procedure
theorem definition_procedure_output {ι : Type u} {A : Type v}
    (Ev : Procedure ι A) (i : ι) :
    output Ev i = {a | (i, a) ∈ Ev} :=
  rfl

-- manuscript-id: preserving
theorem definition_preserves_relation {ι : Type u} {A : Type v}
    (Ev : Procedure ι A) (D : StatisticalRelation ι) :
    Preserves Ev D ↔ ∀ ⦃i j⦄, D i j → output Ev i = output Ev j :=
  Iff.rfl

-- manuscript-id: joint-preserving
theorem definition_joint_preservation {ι : Type u} {A : Type v}
    (Ev : Procedure ι A) (D₁ D₂ : StatisticalRelation ι) :
    (Ev ∈ preservingClass A D₁ ∩ preservingClass A D₂ ↔
      Preserves Ev D₁ ∧ Preserves Ev D₂) ∧
    (Ev ∈ preservingClass A D₁ ∩ preservingClass A D₂ ↔
      Ev ∈ preservingClass A (relationUnion D₁ D₂)) := by
  exact ⟨Iff.rfl, (preserves_union_iff Ev D₁ D₂).symm⟩

-- manuscript-id: bl:1
theorem lemma_bl1_equivalence_closure {ι : Type u}
    (D : StatisticalRelation ι) :
    equivalenceClosure D = Relation.ReflTransGen (Relation.SymmGen D) :=
  equivalenceClosure_eq_zigzagClosure D

-- manuscript-id: bl:3
theorem lemma_bl3_disjoint_classes {ι : Type u}
    (D : StatisticalRelation ι) (i j : ι) :
    ¬ equivalenceClosure D i j ↔
      Disjoint (relationClass (equivalenceClosure D) i)
        (relationClass (equivalenceClosure D) j) :=
  not_related_iff_disjoint_relationClasses
    (equivalenceClosure_isEquivalence D) i j

-- manuscript-id: lemma-a
theorem lemma_a_preserving_classes {ι : Type u} {A : Type v}
    (D₁ D₂ : StatisticalRelation ι) :
    (D₁ ≤ D₂ → preservingClass A D₂ ⊆ preservingClass A D₁) ∧
      preservingClass A (relationUnion D₁ D₂) =
        preservingClass A D₁ ∩ preservingClass A D₂ ∧
      (preservingClass A D₁).Nonempty := by
  exact ⟨fun h ↦ preservingClass_antitone h,
    preservingClass_union D₁ D₂, preservingClass_nonempty D₁⟩

-- manuscript-id: lemma-b
theorem lemma_b_strict_antitone {ι : Type u} {A : Type v} [Nonempty A]
    {R₁ R₂ : StatisticalRelation ι}
    (hR₁ : Equivalence R₁) (hsub : R₁ ≤ R₂)
    (hstrict : ∃ i j, R₂ i j ∧ ¬ R₁ i j) :
    preservingClass A R₂ ⊂ preservingClass A R₁ :=
  preservingClass_strict_antitone hR₁ hsub hstrict

-- manuscript-id: FT
theorem lemma_FT_preservation_closure {ι : Type u} {A : Type v}
    (D : StatisticalRelation ι) :
    preservingClass A D = preservingClass A (equivalenceClosure D) :=
  preservingClass_equivalenceClosure D

theorem theorem_BT1_procedure_classes_of_premises
    {ι : Type u} {A : Type v} [Nonempty A]
    {C S L : StatisticalRelation ι} (h : EvansPremises C S L) :
    preservingClass A L = preservingClass A C ∧
      preservingClass A L ⊂ preservingClass A S ∧
      preservingClass A L = preservingClass A C ∩ preservingClass A S :=
  VennDiagrams.theorem_BT1 h.conditionality_closure
    h.sufficiency_equivalence h.sufficiency_le_likelihood
    h.sufficiency_strict_witness h.joint_closure

theorem corollary_BT2_conditional_pairs_of_premises
    {ι : Type u} {A : Type v}
    {C S L : StatisticalRelation ι} (h : EvansPremises C S L)
    {Ev : Procedure ι A} (hEv : Preserves Ev C) {i j : ι}
    (hij : L i j ∧ ¬ C i j) : output Ev i = output Ev j :=
  VennDiagrams.corollary_BT2 h.conditionality_closure hEv hij

theorem corollary_BT3_joint_pairs_of_premises
    {ι : Type u} {A : Type v}
    {C S L : StatisticalRelation ι} (h : EvansPremises C S L)
    {Ev : Procedure ι A} (hEvS : Preserves Ev S) (hEvC : Preserves Ev C)
    {i j : ι} (hij : L i j ∧ ¬ relationUnion S C i j) :
    output Ev i = output Ev j :=
  VennDiagrams.corollary_BT3 h.joint_closure hEvS hEvC hij

/-- Single-statement assembly of the paper's procedure-level separation:
once a procedure preserves `S`, one `L`-related pair with unequal outputs
certifies membership in `G_S \ G_L`.  For the LR p-value, S05 supplies the
proved finite factorization and sufficiency-transport equality, while S02
supplies the exact proportional-likelihood counterexample. -/
theorem pvalue_sufficiency_not_likelihood_assembly
    {ι : Type u} {A : Type v} {S L : StatisticalRelation ι}
    {Ev : Procedure ι A} (hS : Preserves Ev S) {i j : ι}
    (hL : L i j) (hne : output Ev i ≠ output Ev j) :
    Ev ∈ preservingClass A S \ preservingClass A L := by
  refine ⟨hS, ?_⟩
  intro hpresL
  exact hne (hpresL hL)

/-- One promoted bundle for the exact heterogeneous finite definitions of
`L`, `S`, and `C`: `L` and `S` are equivalence relations, `C` is reflexive
and symmetric, and the ancillary conditional-model equation entails
`C ⊆ L`. -/
theorem packed_relation_structure_certificate
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Equivalence
        (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) ∧
      Equivalence
        (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) ∧
      Reflexive
        (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧
      Symmetric
        (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧
      packedFiniteConditionalityRelation.{u, v} (Theta := Theta) ≤
        packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) := by
  exact ⟨likelihoodRelation_isEquivalence PackedFiniteInferenceBase.likelihood,
    packedFiniteSufficiencyRelation_isEquivalence,
    packedFiniteConditionalityRelation_reflexive,
    packedFiniteConditionalityRelation_symmetric,
    packedFiniteConditionalityRelation_le_likelihoodRelation⟩

namespace Finite

open FiniteExamples

/-- A compact promoted conjunction of the finite-example conclusions.  The
assertion ledger additionally points to each full table theorem in S02. -/
structure ExactCertificate : Prop where
  e0_normalized : ∀ theta, ∑ x, e0 theta x = 1
  eT_normalized : ∀ theta, ∑ t, eT theta t = 1
  induced_minimal_models_coincide : ∀ theta m, eM theta m = eMT theta m
  statistic_M_has_likelihood_fibers : ∀ x y,
    mStatistic x = mStatistic y ↔ likelihoodProportional e0 x y
  statistic_MT_has_likelihood_fibers : ∀ x y,
    mTStatistic x = mTStatistic y ↔ likelihoodProportional eT x y
  mle_models_coincide : ∀ theta eta,
    inducedMass (e0 theta) e0MLE eta = inducedMass (eT theta) eTMLE eta
  U_ancillary : IsAncillary e0 firstCoordinate
  V_ancillary : IsAncillary e0 secondCoordinate
  conditionality_not_transitive :
    ¬ (∀ ⦃i j k⦄, concreteConditionality i j →
      concreteConditionality j k → concreteConditionality i k)
  hierarchical_normalized : ∀ theta,
    (∑ x, e3 theta x) = 1 ∧ (∑ x, e4 theta x) = 1 ∧
      (∑ x, eStar theta x) = 1
  selector_ancillary : IsAncillary eStar selector
  selector_zero_is_E3 : ∀ theta x,
    eStar theta (embedE3 x) / inducedMass (eStar theta) selector .b0 = e3 theta x
  selector_one_is_E4 : ∀ theta x,
    eStar theta (embedE4 x) / inducedMass (eStar theta) selector .b1 = e4 theta x
  hierarchical_MLE_laws_differ :
    inducedMass (eStar .one) eStarMLE .one ≠ inducedMass (e3 .one) e3MLE .one
  pA_same_minimal_class : mStatistic .x00 = mStatistic .x11
  pB_positive_scaling : PositivelyProportional eStar e3 .s01 .d1
  pB_no_minimal_partition_bijection :
    ¬ Nonempty (EStarMinimalClass ≃ E3MinimalClass)
  pvalue_counterexample : pValue5 .x = 1 / 10 ∧ pValue6 .u = 1 / 5 ∧
    pValue5 .x ≠ pValue6 .u

end Finite

open FiniteExamples

instance paperParameterNonempty : Nonempty Parameter := ⟨.one⟩

/-! ## Exact packed witnesses for `S`/`C` incomparability -/

namespace PackedRelationExample

local instance : Nonempty E0Outcome := ⟨.x00⟩
local instance : Nonempty EStarOutcome := ⟨.s01⟩
local instance : Nonempty E3Outcome := ⟨.d1⟩
local instance : Nonempty E4Outcome := ⟨.c0⟩
local instance : Nonempty TOutcome := ⟨.t0⟩

def e0OutcomeCode : E0Outcome → Nat
  | .x00 => 0
  | .x01 => 1
  | .x10 => 2
  | .x11 => 3

theorem e0OutcomeCode_injective : Function.Injective e0OutcomeCode := by
  intro x y h
  cases x <;> cases y <;> simp_all [e0OutcomeCode]

def eStarOutcomeCode : EStarOutcome → Nat
  | .s01 => 0
  | .s02 => 1
  | .s03 => 2
  | .s10 => 3
  | .s11 => 4

theorem eStarOutcomeCode_injective : Function.Injective eStarOutcomeCode := by
  intro x y h
  cases x <;> cases y <;> simp_all [eStarOutcomeCode]

def e3OutcomeCode : E3Outcome → Nat
  | .d1 => 0
  | .d2 => 1
  | .d3 => 2

theorem e3OutcomeCode_injective : Function.Injective e3OutcomeCode := by
  intro x y h
  cases x <;> cases y <;> simp_all [e3OutcomeCode]

/- The rational tables in S02, viewed in the real-valued finite-model API. -/
def e0RealPmf (theta : Parameter) (x : E0Outcome) : ℝ := e0 theta x
def eTRealPmf (theta : Parameter) (t : TOutcome) : ℝ := eT theta t
def eStarRealPmf (theta : Parameter) (x : EStarOutcome) : ℝ := eStar theta x
def e3RealPmf (theta : Parameter) (x : E3Outcome) : ℝ := e3 theta x

def e0FiniteModel : FiniteModel Parameter E0Outcome where
  pmf := e0RealPmf
  pmf_nonneg := by
    intro theta x
    cases theta <;> cases x <;> norm_num [e0RealPmf, e0]
  pmf_sum_one := by
    intro theta
    cases theta <;> norm_num [e0RealPmf, e0]

def eTFiniteModel : FiniteModel Parameter TOutcome where
  pmf := eTRealPmf
  pmf_nonneg := by
    intro theta t
    cases theta <;> cases t <;>
      simp [eTRealPmf, eT, inducedMass, totalStatistic, e0] <;> norm_num
  pmf_sum_one := by
    intro theta
    cases theta <;>
      simp [eTRealPmf, eT, inducedMass, totalStatistic, e0] <;> norm_num

def eStarFiniteModel : FiniteModel Parameter EStarOutcome where
  pmf := eStarRealPmf
  pmf_nonneg := by
    intro theta x
    cases theta <;> cases x <;> norm_num [eStarRealPmf, eStar, e3, e4]
  pmf_sum_one := by
    intro theta
    cases theta <;> norm_num [eStarRealPmf, eStar, e3, e4]

def e3FiniteModel : FiniteModel Parameter E3Outcome where
  pmf := e3RealPmf
  pmf_nonneg := by
    intro theta x
    cases theta <;> cases x <;> norm_num [e3RealPmf, e3]
  pmf_sum_one := by
    intro theta
    cases theta <;> norm_num [e3RealPmf, e3]

/- On the two-parameter family, positive proportionality is the familiar
cross-product equality whenever the first coordinates are positive. -/
theorem proportional_iff_cross (f g : Parameter → ℝ)
    (hf : 0 < f .one) (hg : 0 < g .one) :
    Proportional f g ↔ f .one * g .two = f .two * g .one := by
  constructor
  · rintro ⟨k, _hk, h⟩
    rw [h .one, h .two]
    ring
  · intro h
    refine ⟨f .one / g .one, div_pos hf hg, ?_⟩
    intro theta
    cases theta
    · field_simp
    · field_simp
      exact h.symm

theorem e0Real_minimal (x y : E0Outcome) :
    e0MinimalClass x = e0MinimalClass y ↔
      Proportional (fun theta ↦ e0RealPmf theta x)
        (fun theta ↦ e0RealPmf theta y) := by
  rw [proportional_iff_cross]
  · cases x <;> cases y <;>
      norm_num [e0MinimalClass, e0RealPmf, e0] <;> decide
  · cases x <;> norm_num [e0RealPmf, e0]
  · cases y <;> norm_num [e0RealPmf, e0]

/-- The paper's displayed statistic `M` has exactly the likelihood fibers in
the real-valued finite model. -/
theorem mStatistic_likelihoodFiberCriterion :
    LikelihoodFiberCriterion
      (fun x theta ↦ e0FiniteModel.pmf theta x) mStatistic := by
  intro x y
  rw [proportional_iff_cross]
  · cases x <;> cases y <;>
      norm_num [mStatistic, e0FiniteModel, e0RealPmf, e0] <;> decide
  · cases x <;> norm_num [e0FiniteModel, e0RealPmf, e0]
  · cases y <;> norm_num [e0FiniteModel, e0RealPmf, e0]

/-- The paper's displayed statistic `M_T` has exactly the likelihood fibers
in the induced real-valued finite model. -/
theorem mTStatistic_likelihoodFiberCriterion :
    LikelihoodFiberCriterion
      (fun t theta ↦ eTFiniteModel.pmf theta t) mTStatistic := by
  intro x y
  rw [proportional_iff_cross]
  · cases x <;> cases y <;>
      simp [mTStatistic, eTFiniteModel, eTRealPmf, eT, inducedMass,
        totalStatistic, e0] <;> norm_num
  · cases x <;>
      simp [eTFiniteModel, eTRealPmf, eT, inducedMass,
        totalStatistic, e0] <;> norm_num
  · cases y <;>
      simp [eTFiniteModel, eTRealPmf, eT, inducedMass,
        totalStatistic, e0] <;> norm_num

theorem e0FiniteModel_all_outcomes_effective :
    ∀ x, x ∈ effectiveSupport e0FiniteModel := by
  intro x
  exact ⟨Parameter.one, by
    cases x <;> norm_num [e0FiniteModel, e0RealPmf, e0]⟩

theorem eTFiniteModel_all_outcomes_effective :
    ∀ t, t ∈ effectiveSupport eTFiniteModel := by
  intro t
  exact ⟨Parameter.one, by
    cases t <;>
      simp [eTFiniteModel, eTRealPmf, eT, inducedMass,
        totalStatistic, e0] <;> norm_num⟩

/-- The displayed statistic `M` is genuinely finite minimal sufficient, not
merely a partition satisfying a named criterion. -/
theorem mStatistic_isFiniteMinimalSufficient :
    FiniteMinimalSufficient e0FiniteModel mStatistic :=
  likelihoodFiberCriterion_implies_finiteMinimalSufficient
    e0FiniteModel mStatistic e0FiniteModel_all_outcomes_effective
      mStatistic_likelihoodFiberCriterion

/-- The displayed statistic `M_T` is genuinely finite minimal sufficient in
the induced experiment. -/
theorem mTStatistic_isFiniteMinimalSufficient :
    FiniteMinimalSufficient eTFiniteModel mTStatistic :=
  likelihoodFiberCriterion_implies_finiteMinimalSufficient
    eTFiniteModel mTStatistic eTFiniteModel_all_outcomes_effective
      mTStatistic_likelihoodFiberCriterion

theorem eStarReal_minimal (x y : EStarOutcome) :
    eStarMinimalClass x = eStarMinimalClass y ↔
      Proportional (fun theta ↦ eStarRealPmf theta x)
        (fun theta ↦ eStarRealPmf theta y) := by
  rw [proportional_iff_cross]
  · cases x <;> cases y <;>
      norm_num [eStarMinimalClass, eStarRealPmf, eStar, e3, e4] <;> decide
  · cases x <;> norm_num [eStarRealPmf, eStar, e3, e4]
  · cases y <;> norm_num [eStarRealPmf, eStar, e3, e4]

theorem e3Real_minimal (x y : E3Outcome) :
    e3MinimalClass x = e3MinimalClass y ↔
      Proportional (fun theta ↦ e3RealPmf theta x)
        (fun theta ↦ e3RealPmf theta y) := by
  rw [proportional_iff_cross]
  · cases x <;> cases y <;>
      norm_num [e3MinimalClass, e3RealPmf, e3] <;> decide
  · cases x <;> norm_num [e3RealPmf, e3]
  · cases y <;> norm_num [e3RealPmf, e3]

/- The four inference bases underlying the paper's pairs `p_A` and `p_B`. -/
def packedE0X00 : PackedFiniteInferenceBase Parameter where
  Sample := E0Outcome
  sampleFintype := inferInstance
  sampleNonempty := inferInstance
  outcomeCode := e0OutcomeCode
  outcomeCode_injective := e0OutcomeCode_injective
  model := e0FiniteModel
  outcome := .x00
  outcome_effective := ⟨.one, by norm_num [e0FiniteModel, e0RealPmf, e0]⟩
  all_outcomes_effective := by
    intro x
    exact ⟨.one, by cases x <;> norm_num [e0FiniteModel, e0RealPmf, e0]⟩

def packedE0X11 : PackedFiniteInferenceBase Parameter where
  Sample := E0Outcome
  sampleFintype := inferInstance
  sampleNonempty := inferInstance
  outcomeCode := e0OutcomeCode
  outcomeCode_injective := e0OutcomeCode_injective
  model := e0FiniteModel
  outcome := .x11
  outcome_effective := ⟨.one, by norm_num [e0FiniteModel, e0RealPmf, e0]⟩
  all_outcomes_effective := by
    intro x
    exact ⟨.one, by cases x <;> norm_num [e0FiniteModel, e0RealPmf, e0]⟩

def packedEStarS01 : PackedFiniteInferenceBase Parameter where
  Sample := EStarOutcome
  sampleFintype := inferInstance
  sampleNonempty := inferInstance
  outcomeCode := eStarOutcomeCode
  outcomeCode_injective := eStarOutcomeCode_injective
  model := eStarFiniteModel
  outcome := .s01
  outcome_effective :=
    ⟨.one, by norm_num [eStarFiniteModel, eStarRealPmf, eStar, e3, e4]⟩
  all_outcomes_effective := by
    intro x
    exact ⟨.one, by cases x <;>
      norm_num [eStarFiniteModel, eStarRealPmf, eStar, e3, e4]⟩

def packedE3D1 : PackedFiniteInferenceBase Parameter where
  Sample := E3Outcome
  sampleFintype := inferInstance
  sampleNonempty := inferInstance
  outcomeCode := e3OutcomeCode
  outcomeCode_injective := e3OutcomeCode_injective
  model := e3FiniteModel
  outcome := .d1
  outcome_effective := ⟨.one, by norm_num [e3FiniteModel, e3RealPmf, e3]⟩
  all_outcomes_effective := by
    intro x
    exact ⟨.one, by cases x <;> norm_num [e3FiniteModel, e3RealPmf, e3]⟩

def e0StatisticX00 : PackedFiniteStatistic packedE0X00 where
  Codomain := E0MinimalClass
  codomainFintype := inferInstance
  codomainNonempty := ⟨.diagonal⟩
  statistic := e0MinimalClass
  statistic_surjective := by
    intro c
    cases c
    · exact ⟨.x00, rfl⟩
    · exact ⟨.x01, rfl⟩

def e0StatisticX11 : PackedFiniteStatistic packedE0X11 where
  Codomain := E0MinimalClass
  codomainFintype := inferInstance
  codomainNonempty := ⟨.diagonal⟩
  statistic := e0MinimalClass
  statistic_surjective := by
    intro c
    cases c
    · exact ⟨.x00, rfl⟩
    · exact ⟨.x01, rfl⟩

/- The first manuscript witness lies in packed `S`: the two observations
have the same minimal-sufficient class and the induced models are identical. -/
theorem pA_in_packedS :
    packedFiniteSufficiencyRelation packedE0X00 packedE0X11 := by
  refine ⟨e0StatisticX00, e0StatisticX11, Equiv.refl _, ?_, ?_, ?_, rfl⟩
  · exact likelihoodFiberCriterion_implies_finiteMinimalSufficient
      e0FiniteModel e0MinimalClass packedE0X00.all_outcomes_effective
      e0Real_minimal
  · exact likelihoodFiberCriterion_implies_finiteMinimalSufficient
      e0FiniteModel e0MinimalClass packedE0X11.all_outcomes_effective
      e0Real_minimal
  · intro theta code
    rfl

/- It is not in packed `C`, because an exact same-sample conditioning pair
must retain the observed sample value. -/
theorem pA_not_in_packedC :
    ¬ packedFiniteConditionalityRelation packedE0X00 packedE0X11 := by
  intro h
  rcases h with hforward | hreverse
  · have heq :=
      finiteDirectionalConditionalityPair_same_code_observation_eq
        e0OutcomeCode_injective hforward
    exact (by decide : E0Outcome.x00 ≠ .x11) heq
  · have heq :=
      finiteDirectionalConditionalityPair_same_code_observation_eq
        e0OutcomeCode_injective hreverse
    exact (by decide : E0Outcome.x11 ≠ .x00) heq

/- The six initial sufficiency pairs on the same packed universe as the
main theorems, using the displayed statistics `M` and `M_T`. -/
def packedE0 (x : E0Outcome) : PackedFiniteInferenceBase Parameter :=
  { packedE0X00 with
    outcome := x
    outcome_effective := e0FiniteModel_all_outcomes_effective x }

def eTOutcomeCode : TOutcome → Nat
  | .t0 => 0
  | .t1 => 1
  | .t2 => 2

theorem eTOutcomeCode_injective : Function.Injective eTOutcomeCode := by
  intro x y h
  cases x <;> cases y <;> simp_all [eTOutcomeCode]

def packedET (t : TOutcome) : PackedFiniteInferenceBase Parameter where
  Sample := TOutcome
  sampleFintype := inferInstance
  sampleNonempty := inferInstance
  outcomeCode := eTOutcomeCode
  outcomeCode_injective := eTOutcomeCode_injective
  model := eTFiniteModel
  outcome := t
  outcome_effective := eTFiniteModel_all_outcomes_effective t
  all_outcomes_effective := eTFiniteModel_all_outcomes_effective

def packedMStatistic (x : E0Outcome) : PackedFiniteStatistic (packedE0 x) where
  Codomain := BitValue
  codomainFintype := inferInstance
  codomainNonempty := ⟨.b0⟩
  statistic := mStatistic
  statistic_surjective := by
    intro m
    cases m
    · exact ⟨.x00, rfl⟩
    · exact ⟨.x01, rfl⟩

def packedMTStatistic (t : TOutcome) : PackedFiniteStatistic (packedET t) where
  Codomain := BitValue
  codomainFintype := inferInstance
  codomainNonempty := ⟨.b0⟩
  statistic := mTStatistic
  statistic_surjective := by
    intro m
    cases m
    · exact ⟨.t0, rfl⟩
    · exact ⟨.t1, rfl⟩

theorem m_and_mT_inducedPMF_coincide (theta : Parameter) (m : BitValue) :
    inducedPMF e0FiniteModel mStatistic theta m =
      inducedPMF eTFiniteModel mTStatistic theta m := by
  classical
  unfold inducedPMF
  rw [Finset.sum_filter, Finset.sum_filter]
  cases theta <;> cases m <;>
    simp [e0FiniteModel, eTFiniteModel, e0RealPmf, eTRealPmf,
      mStatistic, mTStatistic, eT, inducedMass, totalStatistic, e0]

theorem packedE0_packedET_sufficiency_of_m_eq
    {x : E0Outcome} {t : TOutcome} (h : mStatistic x = mTStatistic t) :
    packedFiniteSufficiencyRelation (packedE0 x) (packedET t) := by
  refine ⟨packedMStatistic x, packedMTStatistic t, Equiv.refl _,
    mStatistic_isFiniteMinimalSufficient,
    mTStatistic_isFiniteMinimalSufficient, ?_, h⟩
  exact m_and_mT_inducedPMF_coincide

theorem packedE0_sufficiency_of_m_eq
    {x y : E0Outcome} (h : mStatistic x = mStatistic y) :
    packedFiniteSufficiencyRelation (packedE0 x) (packedE0 y) := by
  exact ⟨packedMStatistic x, packedMStatistic y, Equiv.refl _,
    mStatistic_isFiniteMinimalSufficient,
    mStatistic_isFiniteMinimalSufficient, fun _ _ ↦ rfl, h⟩

/-- All six pairs listed in the initial sufficiency example satisfy the
actual packed sufficiency relation, with genuine minimal sufficient statistics. -/
theorem six_listed_initial_packedS_memberships :
    packedFiniteSufficiencyRelation (packedE0 .x00) (packedET .t0) ∧
    packedFiniteSufficiencyRelation (packedE0 .x11) (packedET .t2) ∧
    packedFiniteSufficiencyRelation (packedE0 .x01) (packedET .t1) ∧
    packedFiniteSufficiencyRelation (packedE0 .x10) (packedET .t1) ∧
    packedFiniteSufficiencyRelation (packedE0 .x00) (packedE0 .x11) ∧
    packedFiniteSufficiencyRelation (packedE0 .x01) (packedE0 .x10) :=
  ⟨packedE0_packedET_sufficiency_of_m_eq rfl,
    packedE0_packedET_sufficiency_of_m_eq rfl,
    packedE0_packedET_sufficiency_of_m_eq rfl,
    packedE0_packedET_sufficiency_of_m_eq rfl,
    packedE0_sufficiency_of_m_eq rfl,
    packedE0_sufficiency_of_m_eq rfl⟩

theorem selectorReal_mass (theta : Parameter) (a : BitValue) :
    inducedPMF eStarFiniteModel selector theta a = 1 / 2 := by
  classical
  unfold inducedPMF
  cases a
  · rw [Finset.sum_filter]
    cases theta <;>
      simp [eStarFiniteModel, eStarRealPmf, selector, eStar, e3, e4] <;>
      norm_num
  · rw [Finset.sum_filter]
    cases theta <;>
      simp [eStarFiniteModel, eStarRealPmf, selector, eStar, e3, e4] <;>
      norm_num

theorem selectorReal_ancillary : Ancillary eStarFiniteModel selector := by
  intro theta psi a
  rw [selectorReal_mass theta a, selectorReal_mass psi a]

theorem selectorReal_mass_pos (theta : Parameter) :
    0 < inducedPMF eStarFiniteModel selector theta .b0 := by
  rw [selectorReal_mass]
  norm_num

theorem embedE3_injective : Function.Injective embedE3 := by
  intro x y h
  cases x <;> cases y <;> simp [embedE3] at h ⊢

theorem selector_surjective : Function.Surjective selector := by
  intro a
  cases a
  · exact ⟨.s01, rfl⟩
  · exact ⟨.s10, rfl⟩

theorem selector_b0_fiber (y1 : EStarOutcome) :
    selector y1 = selector EStarOutcome.s01 ↔
      ∃ y2, embedE3 y2 = y1 := by
  cases y1
  · exact ⟨fun _ ↦ ⟨.d1, rfl⟩, fun _ ↦ rfl⟩
  · exact ⟨fun _ ↦ ⟨.d2, rfl⟩, fun _ ↦ rfl⟩
  · exact ⟨fun _ ↦ ⟨.d3, rfl⟩, fun _ ↦ rfl⟩
  · constructor
    · intro h
      contradiction
    · rintro ⟨y2, h⟩
      cases y2 <;> contradiction
  · constructor
    · intro h
      contradiction
    · rintro ⟨y2, h⟩
      cases y2 <;> contradiction

theorem eStar_condition_to_e3_real (theta : Parameter) (y : E3Outcome) :
    e3FiniteModel.pmf theta y =
      eStarFiniteModel.pmf theta (embedE3 y) /
        inducedPMF eStarFiniteModel selector theta
          (selector EStarOutcome.s01) := by
  rw [selectorReal_mass]
  cases theta <;> cases y <;>
    norm_num [e3FiniteModel, e3RealPmf,
      eStarFiniteModel, eStarRealPmf, selector, embedE3, eStar, e3, e4]

/- The second manuscript witness lies in packed `C`: conditioning the fair
selector mixture on selector value zero gives `E3` exactly. -/
theorem pB_in_packedC :
    packedFiniteConditionalityRelation packedEStarS01 packedE3D1 := by
  apply Or.inl
  refine ⟨BitValue, selector, embedE3, selectorReal_ancillary,
    selectorReal_mass_pos, embedE3_injective, Or.inr ?_, selector_b0_fiber,
    rfl, eStar_condition_to_e3_real⟩
  exact ⟨⟨.b0, .b1, by decide⟩, selector_surjective⟩

/-- The same hierarchical mixture at any of its five observations. -/
def packedEStar (x : EStarOutcome) : PackedFiniteInferenceBase Parameter :=
  { packedEStarS01 with
    outcome := x
    outcome_effective := packedEStarS01.all_outcomes_effective x }

/-- The die component at any of its three observations. -/
def packedE3 (x : E3Outcome) : PackedFiniteInferenceBase Parameter :=
  { packedE3D1 with
    outcome := x
    outcome_effective := packedE3D1.all_outcomes_effective x }

def e4RealPmf (theta : Parameter) (x : E4Outcome) : ℝ := e4 theta x

/-- The coin component with exactly the rational masses already certified. -/
def e4FiniteModel : FiniteModel Parameter E4Outcome where
  pmf := e4RealPmf
  pmf_nonneg := by
    intro theta x
    change 0 ≤ (e4 theta x : ℝ)
    exact_mod_cast le_of_lt (hierarchical_models_strictly_positive.2.1 theta x)
  pmf_sum_one := by
    intro theta
    change (∑ x, (e4 theta x : ℝ)) = 1
    have h := (hierarchical_models_normalized theta).2.1
    exact_mod_cast h

def e4OutcomeCode : E4Outcome → Nat
  | .c0 => 0
  | .c1 => 1

theorem e4OutcomeCode_injective : Function.Injective e4OutcomeCode := by
  intro x y h
  cases x <;> cases y <;> simp_all [e4OutcomeCode]

/-- The coin component at either observation. -/
def packedE4 (x : E4Outcome) : PackedFiniteInferenceBase Parameter where
  Sample := E4Outcome
  sampleFintype := inferInstance
  sampleNonempty := inferInstance
  outcomeCode := e4OutcomeCode
  outcomeCode_injective := e4OutcomeCode_injective
  model := e4FiniteModel
  outcome := x
  outcome_effective := ⟨.one, by
    change 0 < (e4 .one x : ℝ)
    exact_mod_cast hierarchical_models_strictly_positive.2.1 .one x⟩
  all_outcomes_effective := by
    intro y
    exact ⟨.one, by
      change 0 < (e4 .one y : ℝ)
      exact_mod_cast hierarchical_models_strictly_positive.2.1 .one y⟩

theorem embedE4_injective : Function.Injective embedE4 := by
  intro x y h
  cases x <;> cases y <;> simp_all [embedE4]

theorem selector_b1_fiber (y1 : EStarOutcome) :
    selector y1 = BitValue.b1 ↔ ∃ y2, embedE4 y2 = y1 := by
  cases y1 <;> decide

theorem eStar_condition_to_e4_real (theta : Parameter) (y : E4Outcome) :
    e4FiniteModel.pmf theta y =
      eStarFiniteModel.pmf theta (embedE4 y) /
        inducedPMF eStarFiniteModel selector theta .b1 := by
  rw [selectorReal_mass]
  have h := (condition_on_selector_one_is_e4 theta y).symm
  rw [selector_mass_table] at h
  change (e4 theta y : ℝ) = (eStar theta (embedE4 y) : ℝ) / (1 / 2)
  have hcast := congrArg (fun q : ℚ ↦ (q : ℝ)) h
  push_cast at hcast
  exact hcast

/-- Every die observation is related to its tagged mixture observation by C. -/
theorem packedEStar_packedE3_conditionality (x : E3Outcome) :
    packedFiniteConditionalityRelation (packedEStar (embedE3 x)) (packedE3 x) := by
  cases x <;>
    apply Or.inl <;>
    refine ⟨BitValue, selector, embedE3, selectorReal_ancillary,
      selectorReal_mass_pos, embedE3_injective, Or.inr ?_, selector_b0_fiber,
      rfl, eStar_condition_to_e3_real⟩ <;>
    exact ⟨⟨.b0, .b1, by decide⟩, selector_surjective⟩

/-- Every coin observation is related to its tagged mixture observation by C. -/
theorem packedEStar_packedE4_conditionality (x : E4Outcome) :
    packedFiniteConditionalityRelation (packedEStar (embedE4 x)) (packedE4 x) := by
  have hmass : ∀ theta, 0 < inducedPMF eStarFiniteModel selector theta .b1 := by
    intro theta
    rw [selectorReal_mass]
    norm_num
  cases x <;>
    apply Or.inl <;>
    refine ⟨BitValue, selector, embedE4, selectorReal_ancillary,
      hmass, embedE4_injective, Or.inr ?_, selector_b1_fiber,
      rfl, eStar_condition_to_e4_real⟩ <;>
    exact ⟨⟨.b0, .b1, by decide⟩, selector_surjective⟩

/-- All five pairs displayed in the hierarchical example use the actual C. -/
theorem five_listed_hierarchical_packedC_memberships :
    packedFiniteConditionalityRelation (packedEStar .s01) (packedE3 .d1) ∧
      packedFiniteConditionalityRelation (packedEStar .s02) (packedE3 .d2) ∧
      packedFiniteConditionalityRelation (packedEStar .s03) (packedE3 .d3) ∧
      packedFiniteConditionalityRelation (packedEStar .s10) (packedE4 .c0) ∧
      packedFiniteConditionalityRelation (packedEStar .s11) (packedE4 .c1) :=
  ⟨packedEStar_packedE3_conditionality .d1,
    packedEStar_packedE3_conditionality .d2,
    packedEStar_packedE3_conditionality .d3,
    packedEStar_packedE4_conditionality .c0,
    packedEStar_packedE4_conditionality .c1⟩

theorem eStarMinimalClass_surjective :
    Function.Surjective eStarMinimalClass := by
  intro c
  cases c
  · exact ⟨.s01, rfl⟩
  · exact ⟨.s02, rfl⟩
  · exact ⟨.s10, rfl⟩
  · exact ⟨.s11, rfl⟩

theorem e3MinimalClass_surjective :
    Function.Surjective e3MinimalClass := by
  intro c
  cases c
  · exact ⟨.d1, rfl⟩
  · exact ⟨.d2, rfl⟩

/- No packed sufficiency witness can relate `EStar` and `E3`: every
surjective minimal statistic has respectively four and two fibers. -/
theorem pB_not_in_packedS :
    ¬ packedFiniteSufficiencyRelation packedEStarS01 packedE3D1 := by
  letI : Fintype packedEStarS01.Sample := packedEStarS01.sampleFintype
  letI : Nonempty packedEStarS01.Sample := packedEStarS01.sampleNonempty
  letI : Fintype packedE3D1.Sample := packedE3D1.sampleFintype
  letI : Nonempty packedE3D1.Sample := packedE3D1.sampleNonempty
  rintro ⟨TStar, T3, h, hminStar, hmin3, _hmass, _hobserved⟩
  letI : Fintype TStar.Codomain := TStar.codomainFintype
  letI : Nonempty TStar.Codomain := TStar.codomainNonempty
  letI : Fintype T3.Codomain := T3.codomainFintype
  letI : Nonempty T3.Codomain := T3.codomainNonempty
  have hcriterionStar :=
    finiteMinimalSufficient_implies_likelihoodFiberCriterion
      packedEStarS01.model TStar.statistic
      packedEStarS01.all_outcomes_effective hminStar
  have hcriterion3 :=
    finiteMinimalSufficient_implies_likelihoodFiberCriterion
      packedE3D1.model T3.statistic packedE3D1.all_outcomes_effective hmin3
  have hfibStar : ∀ x y,
      TStar.statistic x = TStar.statistic y ↔
        eStarMinimalClass x = eStarMinimalClass y := by
    intro x y
    exact (hcriterionStar x y).trans (eStarReal_minimal x y).symm
  have hfib3 : ∀ x y,
      T3.statistic x = T3.statistic y ↔
        e3MinimalClass x = e3MinimalClass y := by
    intro x y
    exact (hcriterion3 x y).trans (e3Real_minimal x y).symm
  let hStar : EStarMinimalClass ≃ TStar.Codomain :=
    relabelSameFibers TStar.statistic eStarMinimalClass
      TStar.statistic_surjective eStarMinimalClass_surjective hfibStar
  let h3 : E3MinimalClass ≃ T3.Codomain :=
    relabelSameFibers T3.statistic e3MinimalClass
      T3.statistic_surjective e3MinimalClass_surjective hfib3
  have hcStar := Fintype.card_congr hStar
  have hc3 := Fintype.card_congr h3
  have hc := Fintype.card_congr h
  have hStarKnown : Fintype.card EStarMinimalClass = 4 := by decide
  have h3Known : Fintype.card E3MinimalClass = 2 := by decide
  omega

/-! ## The packed E0 conditionality non-transitivity witness -/

noncomputable section

/- These are the effective supports of `E0 | U=0` and `E0 | V=0`.
Their stored codes retain the corresponding ambient `E0` outcome labels. -/
inductive E0GivenU0Outcome where
  | x00
  | x01
  deriving DecidableEq, Fintype, Repr

inductive E0GivenV0Outcome where
  | x00
  | x10
  deriving DecidableEq, Fintype, Repr

local instance : Nonempty E0GivenU0Outcome := ⟨.x00⟩
local instance : Nonempty E0GivenV0Outcome := ⟨.x00⟩

@[simp] theorem sum_E0GivenU0Outcome {R : Type*} [AddCommMonoid R]
    (f : E0GivenU0Outcome → R) : (∑ x, f x) = f .x00 + f .x01 := by
  rw [show (Finset.univ : Finset E0GivenU0Outcome) = {.x00, .x01} by decide]
  simp

@[simp] theorem sum_E0GivenV0Outcome {R : Type*} [AddCommMonoid R]
    (f : E0GivenV0Outcome → R) : (∑ x, f x) = f .x00 + f .x10 := by
  rw [show (Finset.univ : Finset E0GivenV0Outcome) = {.x00, .x10} by decide]
  simp

def e0GivenU0RealPmf : Parameter → E0GivenU0Outcome → ℝ
  | .one, .x00 => 1 / 5
  | .one, .x01 => 4 / 5
  | .two, .x00 => 3 / 5
  | .two, .x01 => 2 / 5

def e0GivenV0RealPmf : Parameter → E0GivenV0Outcome → ℝ
  | .one, .x00 => 1 / 5
  | .one, .x10 => 4 / 5
  | .two, .x00 => 3 / 5
  | .two, .x10 => 2 / 5

theorem e0GivenU0RealPmf_eq_ratCast (theta : Parameter)
    (x : E0GivenU0Outcome) :
    e0GivenU0RealPmf theta x =
      (e0GivenU0 theta (match x with | .x00 => .x00 | .x01 => .x01) : ℝ) := by
  cases theta <;> cases x <;>
    simp [e0GivenU0RealPmf, e0GivenU0, e1, inducedMass,
      firstCoordinate, e0] <;> norm_num

theorem e0GivenV0RealPmf_eq_ratCast (theta : Parameter)
    (x : E0GivenV0Outcome) :
    e0GivenV0RealPmf theta x =
      (e0GivenV0 theta (match x with | .x00 => .x00 | .x10 => .x10) : ℝ) := by
  cases theta <;> cases x <;>
    simp [e0GivenV0RealPmf, e0GivenV0, e2, inducedMass,
      secondCoordinate, e0] <;> norm_num

def e0GivenU0FiniteModel : FiniteModel Parameter E0GivenU0Outcome where
  pmf := e0GivenU0RealPmf
  pmf_nonneg := by
    intro theta x
    cases theta <;> cases x <;> norm_num [e0GivenU0RealPmf]
  pmf_sum_one := by
    intro theta
    cases theta <;> norm_num [e0GivenU0RealPmf]

def e0GivenV0FiniteModel : FiniteModel Parameter E0GivenV0Outcome where
  pmf := e0GivenV0RealPmf
  pmf_nonneg := by
    intro theta x
    cases theta <;> cases x <;> norm_num [e0GivenV0RealPmf]
  pmf_sum_one := by
    intro theta
    cases theta <;> norm_num [e0GivenV0RealPmf]

def e0GivenU0OutcomeCode : E0GivenU0Outcome → Nat
  | .x00 => 0
  | .x01 => 1

def e0GivenV0OutcomeCode : E0GivenV0Outcome → Nat
  | .x00 => 0
  | .x10 => 2

theorem e0GivenU0OutcomeCode_injective :
    Function.Injective e0GivenU0OutcomeCode := by
  intro x y h
  cases x <;> cases y <;> simp [e0GivenU0OutcomeCode] at h ⊢

theorem e0GivenV0OutcomeCode_injective :
    Function.Injective e0GivenV0OutcomeCode := by
  intro x y h
  cases x <;> cases y <;> simp [e0GivenV0OutcomeCode] at h ⊢

def embedE0GivenU0 : E0GivenU0Outcome → E0Outcome
  | .x00 => .x00
  | .x01 => .x01

def embedE0GivenV0 : E0GivenV0Outcome → E0Outcome
  | .x00 => .x00
  | .x10 => .x10

theorem embedE0GivenU0_injective : Function.Injective embedE0GivenU0 := by
  intro x y h
  cases x <;> cases y <;> simp [embedE0GivenU0] at h ⊢

theorem embedE0GivenV0_injective : Function.Injective embedE0GivenV0 := by
  intro x y h
  cases x <;> cases y <;> simp [embedE0GivenV0] at h ⊢

theorem e0FirstCoordinateReal_mass (theta : Parameter) (u : BitValue) :
    inducedPMF e0FiniteModel firstCoordinate theta u = 1 / 2 := by
  classical
  unfold inducedPMF
  rw [Finset.sum_filter]
  cases theta <;> cases u <;>
    simp [e0FiniteModel, e0RealPmf, firstCoordinate, e0] <;> norm_num

theorem e0SecondCoordinateReal_mass (theta : Parameter) (v : BitValue) :
    inducedPMF e0FiniteModel secondCoordinate theta v = 1 / 2 := by
  classical
  unfold inducedPMF
  rw [Finset.sum_filter]
  cases theta <;> cases v <;>
    simp [e0FiniteModel, e0RealPmf, secondCoordinate, e0] <;> norm_num

theorem e0FirstCoordinateReal_ancillary :
    Ancillary e0FiniteModel firstCoordinate := by
  intro theta psi u
  rw [e0FirstCoordinateReal_mass theta u, e0FirstCoordinateReal_mass psi u]

theorem e0SecondCoordinateReal_ancillary :
    Ancillary e0FiniteModel secondCoordinate := by
  intro theta psi v
  rw [e0SecondCoordinateReal_mass theta v, e0SecondCoordinateReal_mass psi v]

theorem firstCoordinate_surjective : Function.Surjective firstCoordinate := by
  intro u
  cases u
  · exact ⟨.x00, rfl⟩
  · exact ⟨.x10, rfl⟩

theorem secondCoordinate_surjective : Function.Surjective secondCoordinate := by
  intro v
  cases v
  · exact ⟨.x00, rfl⟩
  · exact ⟨.x01, rfl⟩

theorem firstCoordinate_observed_fiber (x : E0Outcome) :
    firstCoordinate x = firstCoordinate E0Outcome.x00 ↔
      ∃ y, embedE0GivenU0 y = x := by
  cases x
  · exact ⟨fun _ ↦ ⟨.x00, rfl⟩, fun _ ↦ rfl⟩
  · exact ⟨fun _ ↦ ⟨.x01, rfl⟩, fun _ ↦ rfl⟩
  · constructor
    · intro h
      contradiction
    · rintro ⟨y, h⟩
      cases y <;> contradiction
  · constructor
    · intro h
      contradiction
    · rintro ⟨y, h⟩
      cases y <;> contradiction

theorem secondCoordinate_observed_fiber (x : E0Outcome) :
    secondCoordinate x = secondCoordinate E0Outcome.x00 ↔
      ∃ y, embedE0GivenV0 y = x := by
  cases x
  · exact ⟨fun _ ↦ ⟨.x00, rfl⟩, fun _ ↦ rfl⟩
  · constructor
    · intro h
      contradiction
    · rintro ⟨y, h⟩
      cases y <;> contradiction
  · exact ⟨fun _ ↦ ⟨.x10, rfl⟩, fun _ ↦ rfl⟩
  · constructor
    · intro h
      contradiction
    · rintro ⟨y, h⟩
      cases y <;> contradiction

theorem e0_conditions_to_u0_real (theta : Parameter)
    (y : E0GivenU0Outcome) :
    e0GivenU0FiniteModel.pmf theta y =
      e0FiniteModel.pmf theta (embedE0GivenU0 y) /
        inducedPMF e0FiniteModel firstCoordinate theta
          (firstCoordinate E0Outcome.x00) := by
  rw [e0FirstCoordinateReal_mass]
  cases theta <;> cases y <;>
    norm_num [e0GivenU0FiniteModel, e0GivenU0RealPmf, e0FiniteModel,
      e0RealPmf, embedE0GivenU0, e0]

theorem e0_conditions_to_v0_real (theta : Parameter)
    (y : E0GivenV0Outcome) :
    e0GivenV0FiniteModel.pmf theta y =
      e0FiniteModel.pmf theta (embedE0GivenV0 y) /
        inducedPMF e0FiniteModel secondCoordinate theta
          (secondCoordinate E0Outcome.x00) := by
  rw [e0SecondCoordinateReal_mass]
  cases theta <;> cases y <;>
    norm_num [e0GivenV0FiniteModel, e0GivenV0RealPmf, e0FiniteModel,
      e0RealPmf, embedE0GivenV0, e0]

def packedE0GivenU0X00 : PackedFiniteInferenceBase Parameter where
  Sample := E0GivenU0Outcome
  sampleFintype := inferInstance
  sampleNonempty := inferInstance
  outcomeCode := e0GivenU0OutcomeCode
  outcomeCode_injective := e0GivenU0OutcomeCode_injective
  model := e0GivenU0FiniteModel
  outcome := .x00
  outcome_effective := ⟨.one, by
    norm_num [e0GivenU0FiniteModel, e0GivenU0RealPmf]⟩
  all_outcomes_effective := by
    intro x
    exact ⟨.one, by
      cases x <;> norm_num [e0GivenU0FiniteModel, e0GivenU0RealPmf]⟩

def packedE0GivenV0X00 : PackedFiniteInferenceBase Parameter where
  Sample := E0GivenV0Outcome
  sampleFintype := inferInstance
  sampleNonempty := inferInstance
  outcomeCode := e0GivenV0OutcomeCode
  outcomeCode_injective := e0GivenV0OutcomeCode_injective
  model := e0GivenV0FiniteModel
  outcome := .x00
  outcome_effective := ⟨.one, by
    norm_num [e0GivenV0FiniteModel, e0GivenV0RealPmf]⟩
  all_outcomes_effective := by
    intro x
    exact ⟨.one, by
      cases x <;> norm_num [e0GivenV0FiniteModel, e0GivenV0RealPmf]⟩

theorem packedE0_conditions_to_u0 :
    finiteDirectionalConditionalityPair e0FiniteModel e0OutcomeCode
      packedE0X00.asInferenceBase e0GivenU0FiniteModel
      e0GivenU0OutcomeCode packedE0GivenU0X00.asInferenceBase := by
  refine ⟨BitValue, firstCoordinate, embedE0GivenU0,
    e0FirstCoordinateReal_ancillary, ?_, embedE0GivenU0_injective, Or.inr ?_,
    firstCoordinate_observed_fiber, rfl, e0_conditions_to_u0_real⟩
  · intro theta
    rw [e0FirstCoordinateReal_mass]
    norm_num
  · exact ⟨⟨.b0, .b1, by decide⟩, firstCoordinate_surjective⟩

theorem packedE0_conditions_to_v0 :
    finiteDirectionalConditionalityPair e0FiniteModel e0OutcomeCode
      packedE0X00.asInferenceBase e0GivenV0FiniteModel
      e0GivenV0OutcomeCode packedE0GivenV0X00.asInferenceBase := by
  refine ⟨BitValue, secondCoordinate, embedE0GivenV0,
    e0SecondCoordinateReal_ancillary, ?_, embedE0GivenV0_injective, Or.inr ?_,
    secondCoordinate_observed_fiber, rfl, e0_conditions_to_v0_real⟩
  · intro theta
    rw [e0SecondCoordinateReal_mass]
    norm_num
  · exact ⟨⟨.b0, .b1, by decide⟩, secondCoordinate_surjective⟩

theorem e0GivenU0_ancillary_constant {A₀ : Type} (A : E0GivenU0Outcome → A₀)
    (hA : Ancillary e0GivenU0FiniteModel A) : ∀ x, A x = A .x00 := by
  classical
  have hmass := hA Parameter.one Parameter.two (A .x00)
  unfold inducedPMF at hmass
  rw [Finset.sum_filter, Finset.sum_filter,
    sum_E0GivenU0Outcome, sum_E0GivenU0Outcome] at hmass
  have hsame : A .x01 = A .x00 := by
    by_contra hne
    simp [hne, e0GivenU0FiniteModel, e0GivenU0RealPmf] at hmass
    norm_num at hmass
  intro x
  cases x
  · rfl
  · exact hsame

theorem e0GivenV0_ancillary_constant {A₀ : Type} (A : E0GivenV0Outcome → A₀)
    (hA : Ancillary e0GivenV0FiniteModel A) : ∀ x, A x = A .x00 := by
  classical
  have hmass := hA Parameter.one Parameter.two (A .x00)
  unfold inducedPMF at hmass
  rw [Finset.sum_filter, Finset.sum_filter,
    sum_E0GivenV0Outcome, sum_E0GivenV0Outcome] at hmass
  have hsame : A .x10 = A .x00 := by
    by_contra hne
    simp [hne, e0GivenV0FiniteModel, e0GivenV0RealPmf] at hmass
    norm_num at hmass
  intro x
  cases x
  · rfl
  · exact hsame

theorem nontrivial_surjective_not_constant
    {X A₀ : Type} [Nonempty X] (A : X → A₀)
    (hconstant : ∀ x y, A x = A y)
    (hnontrivial : Nontrivial A₀) (hsurjective : Function.Surjective A) : False := by
  letI : Nontrivial A₀ := hnontrivial
  rcases exists_pair_ne A₀ with ⟨a, b, hab⟩
  rcases hsurjective a with ⟨x, rfl⟩
  rcases hsurjective b with ⟨y, rfl⟩
  exact hab (hconstant x y)

theorem no_direction_u0_to_v0 :
    ¬ finiteDirectionalConditionalityPair e0GivenU0FiniteModel
      e0GivenU0OutcomeCode packedE0GivenU0X00.asInferenceBase
      e0GivenV0FiniteModel e0GivenV0OutcomeCode
      packedE0GivenV0X00.asInferenceBase := by
  rintro ⟨A₀, A, embed, hancillary, _hpositive, _hinjective,
    hcode | hselector, _hfiber, _hobserved, _hconditional⟩
  · have hmissing := hcode E0GivenV0Outcome.x10
    cases h : embed .x10 <;> rw [h] at hmissing <;>
      norm_num [e0GivenU0OutcomeCode, e0GivenV0OutcomeCode] at hmissing
  · exact nontrivial_surjective_not_constant A
      (fun x y ↦ (e0GivenU0_ancillary_constant A hancillary x).trans
        (e0GivenU0_ancillary_constant A hancillary y).symm)
      hselector.1 hselector.2

theorem no_direction_v0_to_u0 :
    ¬ finiteDirectionalConditionalityPair e0GivenV0FiniteModel
      e0GivenV0OutcomeCode packedE0GivenV0X00.asInferenceBase
      e0GivenU0FiniteModel e0GivenU0OutcomeCode
      packedE0GivenU0X00.asInferenceBase := by
  rintro ⟨A₀, A, embed, hancillary, _hpositive, _hinjective,
    hcode | hselector, _hfiber, _hobserved, _hconditional⟩
  · have hmissing := hcode E0GivenU0Outcome.x01
    cases h : embed .x01 <;> rw [h] at hmissing <;>
      norm_num [e0GivenU0OutcomeCode, e0GivenV0OutcomeCode] at hmissing
  · exact nontrivial_surjective_not_constant A
      (fun x y ↦ (e0GivenV0_ancillary_constant A hancillary x).trans
        (e0GivenV0_ancillary_constant A hancillary y).symm)
      hselector.1 hselector.2

theorem packed_e0_conditionality_nontransitivity_witness :
    packedFiniteConditionalityRelation packedE0GivenU0X00 packedE0X00 ∧
      packedFiniteConditionalityRelation packedE0X00 packedE0GivenV0X00 ∧
      ¬ packedFiniteConditionalityRelation packedE0GivenU0X00
        packedE0GivenV0X00 := by
  exact ⟨Or.inr packedE0_conditions_to_u0,
    Or.inl packedE0_conditions_to_v0,
    fun h ↦ h.elim no_direction_u0_to_v0 no_direction_v0_to_u0⟩

theorem packedConditionality_not_transitive :
    ¬ Transitive
      (packedFiniteConditionalityRelation.{0, 0} (Theta := Parameter)) := by
  intro htrans
  exact packed_e0_conditionality_nontransitivity_witness.2.2
    (htrans packed_e0_conditionality_nontransitivity_witness.1
      packed_e0_conditionality_nontransitivity_witness.2.1)

end

end PackedRelationExample

/- Direct conditionality is nontransitive even for a singleton parameter
space: the parameter-free coin gives an S-pair outside C. -/
theorem packedFiniteConditionalityRelation_not_transitive
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    ¬ Transitive
      (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) :=
  packed_conditionality_not_transitive_all_parameters Theta

/- The two exact S02 pairs certify incomparability of the actual global
packed sufficiency and conditionality relations. -/
theorem packed_sufficiency_conditionality_incomparable_twoPoint :
    RelationsIncomparable
      (packedFiniteSufficiencyRelation.{0, 0} (Theta := Parameter))
      (packedFiniteConditionalityRelation.{0, 0} (Theta := Parameter)) := by
  exact relationsIncomparable_of_witnesses
    ⟨PackedRelationExample.pA_in_packedS,
      PackedRelationExample.pA_not_in_packedC⟩
    ⟨PackedRelationExample.pB_in_packedC,
      PackedRelationExample.pB_not_in_packedS⟩

/-- The parameter-free coin prevents any relation containing sufficiency
from being contained in direct conditionality, for every nonempty finite
parameter space. -/
theorem packed_sufficiency_extension_not_le_conditionality
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (R : StatisticalRelation (PackedFiniteInferenceBase.{u, v} Theta))
    (hS : packedFiniteSufficiencyRelation ≤ R) :
    ¬ R ≤ packedFiniteConditionalityRelation := by
  intro hC
  exact packed_sufficiency_not_le_conditionality_all_parameters Theta
    (le_trans hS hC)

/-- Qualified finite form of the sufficiency inclusion: stability and the
laminal partition are computed in each minimal-sufficient reduced model. -/
theorem reduced_stable_sufficiency
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    packedFiniteSufficiencyRelation.{u, v} (Theta := Theta) ≤
      packedFiniteReducedStableConditionalityRelation.{u, v} (Theta := Theta) :=
  packedFiniteSufficiencyRelation_le_reducedStableConditionality

/-- The manuscript's same-observation-class pair belongs to reduced-first
stable conditionality but not to its literal, direct conditionality relation. -/
theorem reduced_stable_counterexample :
    packedFiniteReducedStableConditionalityRelation
        PackedRelationExample.packedE0X00 PackedRelationExample.packedE0X11 ∧
      ¬ packedFiniteConditionalityRelation
        PackedRelationExample.packedE0X00 PackedRelationExample.packedE0X11 := by
  exact ⟨reduced_stable_sufficiency _ _ PackedRelationExample.pA_in_packedS,
    PackedRelationExample.pA_not_in_packedC⟩

/-- Non-inclusion in direct C for every nonempty finite parameter space.
This says nothing about an unqualified original-model stable-conditionality
relation. -/
theorem reduced_stable_not_le_conditionality
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    ¬ packedFiniteReducedStableConditionalityRelation.{u, v} (Theta := Theta) ≤
      packedFiniteConditionalityRelation :=
  packed_sufficiency_extension_not_le_conditionality _ reduced_stable_sufficiency

/-! ## The packed E5/E6 LR p-value counterexample -/

namespace PackedPValueExample

noncomputable section

instance e5OutcomeNonempty : Nonempty E5Outcome := ⟨.x⟩
instance e6OutcomeNonempty : Nonempty E6Outcome := ⟨.u⟩

def e5OutcomeCode : E5Outcome → Nat
  | .x => 0
  | .y => 1

theorem e5OutcomeCode_injective : Function.Injective e5OutcomeCode := by
  intro x y h
  cases x <;> cases y <;> simp_all [e5OutcomeCode]

def e6OutcomeCode : E6Outcome → Nat
  | .u => 0
  | .v => 1

theorem e6OutcomeCode_injective : Function.Injective e6OutcomeCode := by
  intro x y h
  cases x <;> cases y <;> simp_all [e6OutcomeCode]

/-- The paper's `E5` table, now in the real-valued `FiniteModel` API. -/
def e5RealPmf : Parameter → E5Outcome → ℝ
  | .one, .x => 1 / 10
  | .one, .y => 9 / 10
  | .two, .x => 1 / 5
  | .two, .y => 4 / 5

/-- The paper's `E6` table, now in the real-valued `FiniteModel` API. -/
def e6RealPmf : Parameter → E6Outcome → ℝ
  | .one, .u => 1 / 5
  | .one, .v => 4 / 5
  | .two, .u => 2 / 5
  | .two, .v => 3 / 5

/-- The real `E5` table is exactly the cast of the rational table certified
in S02. -/
theorem e5RealPmf_eq_ratCast (theta : Parameter) (z : E5Outcome) :
    e5RealPmf theta z = (e5 theta z : ℝ) := by
  cases theta <;> cases z <;> norm_num [e5RealPmf, e5]

/-- The real `E6` table is exactly the cast of the rational table certified
in S02. -/
theorem e6RealPmf_eq_ratCast (theta : Parameter) (z : E6Outcome) :
    e6RealPmf theta z = (e6 theta z : ℝ) := by
  cases theta <;> cases z <;> norm_num [e6RealPmf, e6]

def e5FiniteModel : FiniteModel Parameter E5Outcome where
  pmf := e5RealPmf
  pmf_nonneg := by
    intro theta z
    cases theta <;> cases z <;> norm_num [e5RealPmf]
  pmf_sum_one := by
    intro theta
    cases theta <;> norm_num [e5RealPmf]

def e6FiniteModel : FiniteModel Parameter E6Outcome where
  pmf := e6RealPmf
  pmf_nonneg := by
    intro theta z
    cases theta <;> cases z <;> norm_num [e6RealPmf]
  pmf_sum_one := by
    intro theta
    cases theta <;> norm_num [e6RealPmf]

/-- The singleton null `{theta1}` versus alternative `{theta2}` used for the
paper's E5/E6 likelihood-ratio tests. -/
def singletonNullPartition : ParameterPartition Parameter where
  nullPart := {.one}
  alternativePart := {.two}
  null_nonempty := by simp
  alternative_nonempty := by simp
  disjoint := by simp
  exhaustive := by
    intro theta
    cases theta <;> simp

theorem finiteMaximum_singleton {A : Type*} [Fintype A]
    (a : A) (f : A → ℝ) :
    finiteMaximum {a} (by simp) f = f a := by
  classical
  simp [finiteMaximum]

theorem e5_extendedLikelihoodRatio_x :
    extendedLikelihoodRatio e5FiniteModel singletonNullPartition .x =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [extendedLikelihoodRatio_of_denominator_pos]
  · congr 1
    norm_num [maxLikelihoodOn, singletonNullPartition, finiteMaximum,
      e5FiniteModel, e5RealPmf]
  · norm_num [maxLikelihoodOn, singletonNullPartition, finiteMaximum,
      e5FiniteModel, e5RealPmf]

theorem e5_extendedLikelihoodRatio_y :
    extendedLikelihoodRatio e5FiniteModel singletonNullPartition .y =
      ENNReal.ofReal (9 / 8 : ℝ) := by
  rw [extendedLikelihoodRatio_of_denominator_pos]
  · congr 1
    norm_num [maxLikelihoodOn, singletonNullPartition, finiteMaximum,
      e5FiniteModel, e5RealPmf]
  · norm_num [maxLikelihoodOn, singletonNullPartition, finiteMaximum,
      e5FiniteModel, e5RealPmf]

theorem e6_extendedLikelihoodRatio_u :
    extendedLikelihoodRatio e6FiniteModel singletonNullPartition .u =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [extendedLikelihoodRatio_of_denominator_pos]
  · congr 1
    norm_num [maxLikelihoodOn, singletonNullPartition, finiteMaximum,
      e6FiniteModel, e6RealPmf]
  · norm_num [maxLikelihoodOn, singletonNullPartition, finiteMaximum,
      e6FiniteModel, e6RealPmf]

theorem e6_extendedLikelihoodRatio_v :
    extendedLikelihoodRatio e6FiniteModel singletonNullPartition .v =
      ENNReal.ofReal (4 / 3 : ℝ) := by
  rw [extendedLikelihoodRatio_of_denominator_pos]
  · congr 1
    norm_num [maxLikelihoodOn, singletonNullPartition, finiteMaximum,
      e6FiniteModel, e6RealPmf]
  · norm_num [maxLikelihoodOn, singletonNullPartition, finiteMaximum,
      e6FiniteModel, e6RealPmf]

theorem e5_lowerTailRegion_x :
    lowerTailRegion e5FiniteModel singletonNullPartition .x = {.x} := by
  ext z
  cases z
  · simp
  · simp only [mem_lowerTailRegion_iff, Finset.mem_singleton]
    rw [e5_extendedLikelihoodRatio_y, e5_extendedLikelihoodRatio_x]
    norm_num
    decide

theorem e6_lowerTailRegion_u :
    lowerTailRegion e6FiniteModel singletonNullPartition .u = {.u} := by
  ext z
  cases z
  · simp
  · simp only [mem_lowerTailRegion_iff, Finset.mem_singleton]
    rw [e6_extendedLikelihoodRatio_v, e6_extendedLikelihoodRatio_u]
    norm_num
    decide

theorem e5_lowerTailLRPValue_x :
    lowerTailLRPValue e5FiniteModel singletonNullPartition .x = 1 / 10 := by
  classical
  unfold lowerTailLRPValue
  change finiteMaximum ({.one} : Finset Parameter) _
    (lowerTailProbability e5FiniteModel singletonNullPartition .x) = 1 / 10
  rw [finiteMaximum_singleton]
  unfold lowerTailProbability
  rw [e5_lowerTailRegion_x]
  norm_num [e5FiniteModel, e5RealPmf]

theorem e6_lowerTailLRPValue_u :
    lowerTailLRPValue e6FiniteModel singletonNullPartition .u = 1 / 5 := by
  classical
  unfold lowerTailLRPValue
  change finiteMaximum ({.one} : Finset Parameter) _
    (lowerTailProbability e6FiniteModel singletonNullPartition .u) = 1 / 5
  rw [finiteMaximum_singleton]
  unfold lowerTailProbability
  rw [e6_lowerTailRegion_u]
  norm_num [e6FiniteModel, e6RealPmf]

/-- The packed inference base `(E5,x)`. -/
def packedE5X : PackedFiniteInferenceBase Parameter where
  Sample := E5Outcome
  sampleFintype := inferInstance
  sampleNonempty := inferInstance
  outcomeCode := e5OutcomeCode
  outcomeCode_injective := e5OutcomeCode_injective
  model := e5FiniteModel
  outcome := .x
  outcome_effective := by
    exact ⟨.one, by norm_num [e5FiniteModel, e5RealPmf]⟩
  all_outcomes_effective := by
    intro z
    exact ⟨.one, by cases z <;> norm_num [e5FiniteModel, e5RealPmf]⟩

/-- The packed inference base `(E6,u)`. -/
def packedE6U : PackedFiniteInferenceBase Parameter where
  Sample := E6Outcome
  sampleFintype := inferInstance
  sampleNonempty := inferInstance
  outcomeCode := e6OutcomeCode
  outcomeCode_injective := e6OutcomeCode_injective
  model := e6FiniteModel
  outcome := .u
  outcome_effective := by
    exact ⟨.one, by norm_num [e6FiniteModel, e6RealPmf]⟩
  all_outcomes_effective := by
    intro z
    exact ⟨.one, by cases z <;> norm_num [e6FiniteModel, e6RealPmf]⟩

theorem packedE5X_pValue :
    packedLowerTailLRPValue singletonNullPartition packedE5X = 1 / 10 := by
  exact e5_lowerTailLRPValue_x

theorem packedE6U_pValue :
    packedLowerTailLRPValue singletonNullPartition packedE6U = 1 / 5 := by
  exact e6_lowerTailLRPValue_u

/-- The observed likelihood of `(E5,x)` is one half of that of `(E6,u)`, so
the two packed inference bases are related by the global likelihood relation. -/
theorem packedE5X_packedE6U_likelihood_related :
    packedFiniteLikelihoodRelation.{0, 0} packedE5X packedE6U := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro theta
  change e5RealPmf theta .x = 1 / 2 * e6RealPmf theta .u
  cases theta <;> norm_num [e5RealPmf, e6RealPmf]

/- The likelihood-proportionality classes within each of the two experiments
are singletons. -/
theorem e5_likelihood_class_singleton (z w : E5Outcome) :
    z = w ↔
      Proportional (fun theta ↦ e5FiniteModel.pmf theta z)
        (fun theta ↦ e5FiniteModel.pmf theta w) := by
  rw [PackedRelationExample.proportional_iff_cross]
  · cases z <;> cases w <;>
      norm_num [e5FiniteModel, e5RealPmf] <;> decide
  · cases z <;> norm_num [e5FiniteModel, e5RealPmf]
  · cases w <;> norm_num [e5FiniteModel, e5RealPmf]

theorem e6_likelihood_class_singleton (z w : E6Outcome) :
    z = w ↔
      Proportional (fun theta ↦ e6FiniteModel.pmf theta z)
        (fun theta ↦ e6FiniteModel.pmf theta w) := by
  rw [PackedRelationExample.proportional_iff_cross]
  · cases z <;> cases w <;>
      norm_num [e6FiniteModel, e6RealPmf] <;> decide
  · cases z <;> norm_num [e6FiniteModel, e6RealPmf]
  · cases w <;> norm_num [e6FiniteModel, e6RealPmf]

/- Each displayed two-point experiment has only the trivial ancillary: a
nonconstant fiber has different mass at the two parameter values. -/
theorem e5_ancillary_constant {A₀ : Type} (A : E5Outcome → A₀)
    (hA : Ancillary e5FiniteModel A) : ∀ z, A z = A .x := by
  classical
  have hmass := hA Parameter.one Parameter.two (A .x)
  unfold inducedPMF at hmass
  rw [Finset.sum_filter, Finset.sum_filter,
    sum_E5Outcome, sum_E5Outcome] at hmass
  have hy : A .y = A .x := by
    by_contra hne
    simpa [hne, e5FiniteModel, e5RealPmf] using hmass
  intro z
  cases z
  · rfl
  · exact hy

theorem e6_ancillary_constant {A₀ : Type} (A : E6Outcome → A₀)
    (hA : Ancillary e6FiniteModel A) : ∀ z, A z = A .u := by
  classical
  have hmass := hA Parameter.one Parameter.two (A .u)
  unfold inducedPMF at hmass
  rw [Finset.sum_filter, Finset.sum_filter,
    sum_E6Outcome, sum_E6Outcome] at hmass
  have hv : A .v = A .u := by
    by_contra hne
    simp [hne, e6FiniteModel, e6RealPmf] at hmass
    norm_num at hmass
  intro z
  cases z
  · rfl
  · exact hv

theorem e5_not_directional_to_e6 :
    ¬ finiteDirectionalConditionalityPair e5FiniteModel e5OutcomeCode
      packedE5X.asInferenceBase e6FiniteModel e6OutcomeCode
      packedE6U.asInferenceBase := by
  rintro ⟨A₀, A, embed, hancillary, _hpositive, _hinjective,
    _hidentification, _hfiber, hobserved, hconditional⟩
  have hconstant := e5_ancillary_constant A hancillary
  have hden : inducedPMF e5FiniteModel A Parameter.one (A .x) = 1 := by
    rw [show A = (fun _ ↦ A .x) from funext hconstant]
    exact inducedPMF_const_eq e5FiniteModel (A .x) (A .x) .one rfl
  have hm := hconditional Parameter.one E6Outcome.u
  change embed E6Outcome.u = E5Outcome.x at hobserved
  rw [hobserved] at hm
  change e6FiniteModel.pmf .one .u = e5FiniteModel.pmf .one .x /
    inducedPMF e5FiniteModel A .one (A .x) at hm
  rw [hden] at hm
  norm_num [e5FiniteModel, e5RealPmf, e6FiniteModel, e6RealPmf] at hm

theorem e6_not_directional_to_e5 :
    ¬ finiteDirectionalConditionalityPair e6FiniteModel e6OutcomeCode
      packedE6U.asInferenceBase e5FiniteModel e5OutcomeCode
      packedE5X.asInferenceBase := by
  rintro ⟨A₀, A, embed, hancillary, _hpositive, _hinjective,
    _hidentification, _hfiber, hobserved, hconditional⟩
  have hconstant := e6_ancillary_constant A hancillary
  have hden : inducedPMF e6FiniteModel A Parameter.one (A .u) = 1 := by
    rw [show A = (fun _ ↦ A .u) from funext hconstant]
    exact inducedPMF_const_eq e6FiniteModel (A .u) (A .u) .one rfl
  have hm := hconditional Parameter.one E5Outcome.x
  change embed E5Outcome.x = E6Outcome.u at hobserved
  rw [hobserved] at hm
  change e5FiniteModel.pmf .one .x = e6FiniteModel.pmf .one .u /
    inducedPMF e6FiniteModel A .one (A .u) at hm
  rw [hden] at hm
  norm_num [e5FiniteModel, e5RealPmf, e6FiniteModel, e6RealPmf] at hm

/- The E5/E6 likelihood pair is not a direct conditionality pair in either
direction, because both experiments have only trivial ancillaries while
their observed masses differ. -/
theorem packedE5X_packedE6U_not_conditionality :
    ¬ packedFiniteConditionalityRelation packedE5X packedE6U := by
  intro hC
  exact hC.elim e5_not_directional_to_e6 e6_not_directional_to_e5

/- Nor is the pair sufficient: minimal sufficiency forces singleton fibers,
so equality of the induced observed masses would assert `1/10 = 1/5`. -/
theorem packedE5X_packedE6U_not_sufficiency :
    ¬ packedFiniteSufficiencyRelation packedE5X packedE6U := by
  letI : Fintype packedE5X.Sample := packedE5X.sampleFintype
  letI : Nonempty packedE5X.Sample := packedE5X.sampleNonempty
  letI : Fintype packedE6U.Sample := packedE6U.sampleFintype
  letI : Nonempty packedE6U.Sample := packedE6U.sampleNonempty
  rintro ⟨T₅, T₆, h, hmin₅, hmin₆, hmass, hobserved⟩
  letI : Fintype T₅.Codomain := T₅.codomainFintype
  letI : Nonempty T₅.Codomain := T₅.codomainNonempty
  letI : Fintype T₆.Codomain := T₆.codomainFintype
  letI : Nonempty T₆.Codomain := T₆.codomainNonempty
  have hcriterion₅ :=
    finiteMinimalSufficient_implies_likelihoodFiberCriterion
      packedE5X.model T₅.statistic packedE5X.all_outcomes_effective hmin₅
  have hcriterion₆ :=
    finiteMinimalSufficient_implies_likelihoodFiberCriterion
      packedE6U.model T₆.statistic packedE6U.all_outcomes_effective hmin₆
  have hinjective₅ : Function.Injective T₅.statistic := by
    intro z w hzw
    exact (e5_likelihood_class_singleton z w).2 ((hcriterion₅ z w).1 hzw)
  have hinjective₆ : Function.Injective T₆.statistic := by
    intro z w hzw
    exact (e6_likelihood_class_singleton z w).2 ((hcriterion₆ z w).1 hzw)
  have hm := hmass Parameter.one (T₆.statistic .u)
  change T₅.statistic E5Outcome.x = h (T₆.statistic E6Outcome.u) at hobserved
  rw [← hobserved] at hm
  change inducedPMF e5FiniteModel T₅.statistic .one (T₅.statistic .x) =
    inducedPMF e6FiniteModel T₆.statistic .one (T₆.statistic .u) at hm
  unfold inducedPMF at hm
  rw [Finset.sum_filter, Finset.sum_filter,
    sum_E5Outcome, sum_E6Outcome] at hm
  simp [hinjective₅.eq_iff, hinjective₆.eq_iff,
    e5FiniteModel, e5RealPmf, e6FiniteModel, e6RealPmf] at hm

theorem packedE5X_packedE6U_joint_strict_witness :
    packedFiniteLikelihoodRelation packedE5X packedE6U ∧
      ¬ packedFiniteConditionalityRelation packedE5X packedE6U ∧
      ¬ packedFiniteSufficiencyRelation packedE5X packedE6U :=
  ⟨packedE5X_packedE6U_likelihood_related,
    packedE5X_packedE6U_not_conditionality,
    packedE5X_packedE6U_not_sufficiency⟩

theorem packedLowerTailLRPValueProcedure_not_preserves_likelihood :
    ¬ Preserves (packedLowerTailLRPValueProcedure.{0, 0} singletonNullPartition)
        (packedFiniteLikelihoodRelation.{0, 0} (Theta := Parameter)) := by
  intro hpres
  have hout := hpres packedE5X_packedE6U_likelihood_related
  simp only [packedLowerTailLRPValueProcedure, output_graphProcedure] at hout
  have hpSubtype := Set.singleton_eq_singleton_iff.mp hout
  have hp := congrArg Subtype.val hpSubtype
  simp only [packedLowerTailLRPValueInUnitInterval] at hp
  rw [packedE5X_pValue, packedE6U_pValue] at hp
  norm_num at hp

/-- The named global LR p-value procedure belongs to `G_S` but not to `G_L`;
the finite factorization and reduction steps are proved internally. -/
theorem packedLowerTailLRPValueProcedure_in_sufficiency_not_likelihood :
    packedLowerTailLRPValueProcedure.{0, 0} singletonNullPartition ∈
      preservingClass (Set.Icc (0 : ℝ) 1)
          (packedFiniteSufficiencyRelation.{0, 0} (Theta := Parameter)) \
        preservingClass (Set.Icc (0 : ℝ) 1)
          (packedFiniteLikelihoodRelation.{0, 0} (Theta := Parameter)) := by
  exact ⟨packedLowerTailLRPValueProcedure_preserves_sufficiency
      singletonNullPartition,
    packedLowerTailLRPValueProcedure_not_preserves_likelihood⟩

end

end PackedPValueExample

/-! ## Transport from two parameter rows to arbitrary finite parameter spaces -/

namespace FiniteParameterTransfer

universe z

variable {Alpha : Type u} {Beta : Type w}
variable [Fintype Alpha] [Nonempty Alpha] [Fintype Beta] [Nonempty Beta]

def reparameterizeModel {X : Type v} [Fintype X] [Nonempty X]
    (f : Beta → Alpha) (E : FiniteModel Alpha X) : FiniteModel Beta X where
  pmf := fun theta x ↦ E.pmf (f theta) x
  pmf_nonneg := fun theta x ↦ E.pmf_nonneg (f theta) x
  pmf_sum_one := fun theta ↦ E.pmf_sum_one (f theta)

theorem sufficient_iff {X : Type v} {Y : Type z} [Fintype X] [Nonempty X]
    (f : Beta → Alpha) (hf : Function.Surjective f)
    (E : FiniteModel Alpha X) (T : X → Y) :
    FiniteSufficient (reparameterizeModel f E) T ↔ FiniteSufficient E T := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    intro theta x
    rcases hf theta with ⟨psi, rfl⟩
    exact hq psi x
  · rintro ⟨q, hq⟩
    exact ⟨q, fun theta x ↦ hq (f theta) x⟩

theorem minimalSufficient_iff {X : Type v} {Y : Type z}
    [Fintype X] [Nonempty X]
    (f : Beta → Alpha) (hf : Function.Surjective f)
    (E : FiniteModel Alpha X) (T : X → Y) :
    FiniteMinimalSufficient (reparameterizeModel f E) T ↔
      FiniteMinimalSufficient E T := by
  constructor
  · rintro ⟨hT, hmin⟩
    refine ⟨(sufficient_iff f hf E T).mp hT, ?_⟩
    intro Z S hS
    exact hmin S ((sufficient_iff f hf E S).mpr hS)
  · rintro ⟨hT, hmin⟩
    refine ⟨(sufficient_iff f hf E T).mpr hT, ?_⟩
    intro Z S hS
    exact hmin S ((sufficient_iff f hf E S).mp hS)

def reparameterize (f : Beta → Alpha) (hf : Function.Surjective f)
    (I : PackedFiniteInferenceBase.{u, v} Alpha) :
    PackedFiniteInferenceBase.{w, v} Beta where
  Sample := I.Sample
  sampleFintype := I.sampleFintype
  sampleNonempty := I.sampleNonempty
  outcomeCode := I.outcomeCode
  outcomeCode_injective := I.outcomeCode_injective
  model := @reparameterizeModel _ _ _ _ _ _ _ I.sampleFintype I.sampleNonempty f I.model
  outcome := I.outcome
  outcome_effective := by
    rcases I.outcome_effective with ⟨theta, htheta⟩
    rcases hf theta with ⟨psi, rfl⟩
    exact ⟨psi, htheta⟩
  all_outcomes_effective := by
    intro x
    rcases I.all_outcomes_effective x with ⟨theta, htheta⟩
    rcases hf theta with ⟨psi, rfl⟩
    exact ⟨psi, htheta⟩

def statisticForward (f : Beta → Alpha) (hf : Function.Surjective f)
    {I : PackedFiniteInferenceBase.{u, v} Alpha} (T : PackedFiniteStatistic I) :
    PackedFiniteStatistic (reparameterize f hf I) where
  Codomain := T.Codomain
  codomainFintype := T.codomainFintype
  codomainNonempty := T.codomainNonempty
  statistic := T.statistic
  statistic_surjective := T.statistic_surjective

def statisticBackward (f : Beta → Alpha) (hf : Function.Surjective f)
    {I : PackedFiniteInferenceBase.{u, v} Alpha}
    (T : PackedFiniteStatistic (reparameterize f hf I)) : PackedFiniteStatistic I where
  Codomain := T.Codomain
  codomainFintype := T.codomainFintype
  codomainNonempty := T.codomainNonempty
  statistic := T.statistic
  statistic_surjective := T.statistic_surjective

theorem sufficiency_iff (f : Beta → Alpha) (hf : Function.Surjective f)
    (I J : PackedFiniteInferenceBase.{u, v} Alpha) :
    packedFiniteSufficiencyRelation (reparameterize f hf I) (reparameterize f hf J) ↔
      packedFiniteSufficiencyRelation I J := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype J.Sample := J.sampleFintype
  letI : Nonempty J.Sample := J.sampleNonempty
  constructor
  · rintro ⟨T₁, T₂, h, hmin₁, hmin₂, hmass, hobs⟩
    refine ⟨statisticBackward f hf T₁, statisticBackward f hf T₂, h,
      (minimalSufficient_iff f hf I.model T₁.statistic).mp hmin₁,
      (minimalSufficient_iff f hf J.model T₂.statistic).mp hmin₂, ?_, hobs⟩
    intro theta y
    rcases hf theta with ⟨psi, rfl⟩
    exact hmass psi y
  · rintro ⟨T₁, T₂, h, hmin₁, hmin₂, hmass, hobs⟩
    exact ⟨statisticForward f hf T₁, statisticForward f hf T₂, h,
      (minimalSufficient_iff f hf I.model T₁.statistic).mpr hmin₁,
      (minimalSufficient_iff f hf J.model T₂.statistic).mpr hmin₂,
      fun theta y ↦ hmass (f theta) y, hobs⟩

theorem conditionality_iff (f : Beta → Alpha) (hf : Function.Surjective f)
    (I J : PackedFiniteInferenceBase.{u, v} Alpha) :
    packedFiniteConditionalityRelation (reparameterize f hf I) (reparameterize f hf J) ↔
      packedFiniteConditionalityRelation I J := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype J.Sample := J.sampleFintype
  letI : Nonempty J.Sample := J.sampleNonempty
  have directional (K M : PackedFiniteInferenceBase.{u, v} Alpha) :
      (letI : Fintype K.Sample := K.sampleFintype
       letI : Nonempty K.Sample := K.sampleNonempty
       letI : Fintype M.Sample := M.sampleFintype
       letI : Nonempty M.Sample := M.sampleNonempty
       letI : Fintype (reparameterize f hf K).Sample := K.sampleFintype
       letI : Nonempty (reparameterize f hf K).Sample := K.sampleNonempty
       letI : Fintype (reparameterize f hf M).Sample := M.sampleFintype
       letI : Nonempty (reparameterize f hf M).Sample := M.sampleNonempty
       finiteDirectionalConditionalityPair (reparameterize f hf K).model K.outcomeCode
         (reparameterize f hf K).asInferenceBase (reparameterize f hf M).model M.outcomeCode
         (reparameterize f hf M).asInferenceBase ↔
       finiteDirectionalConditionalityPair K.model K.outcomeCode K.asInferenceBase
         M.model M.outcomeCode M.asInferenceBase) := by
    letI : Fintype K.Sample := K.sampleFintype
    letI : Nonempty K.Sample := K.sampleNonempty
    letI : Fintype M.Sample := M.sampleFintype
    letI : Nonempty M.Sample := M.sampleNonempty
    constructor
    · rintro ⟨A₀, A, embed, hanc, hpos, hinj, hcode, hfiber, hobs, hmass⟩
      refine ⟨A₀, A, embed, ?_, ?_, hinj, hcode, hfiber, hobs, ?_⟩
      · intro theta psi a
        rcases hf theta with ⟨theta', rfl⟩
        rcases hf psi with ⟨psi', rfl⟩
        exact hanc theta' psi' a
      · intro theta
        rcases hf theta with ⟨psi, rfl⟩
        exact hpos psi
      · intro theta y
        rcases hf theta with ⟨psi, rfl⟩
        exact hmass psi y
    · rintro ⟨A₀, A, embed, hanc, hpos, hinj, hcode, hfiber, hobs, hmass⟩
      exact ⟨A₀, A, embed, fun theta psi a ↦ hanc (f theta) (f psi) a,
        fun theta ↦ hpos (f theta), hinj, hcode, hfiber, hobs,
        fun theta y ↦ hmass (f theta) y⟩
  exact or_congr (directional I J) (directional J I)

theorem likelihood_iff (f : Beta → Alpha) (hf : Function.Surjective f)
    (I J : PackedFiniteInferenceBase.{u, v} Alpha) :
    packedFiniteLikelihoodRelation (reparameterize f hf I) (reparameterize f hf J) ↔
      packedFiniteLikelihoodRelation I J := by
  constructor
  · rintro ⟨c, hc, hmass⟩
    refine ⟨c, hc, ?_⟩
    intro theta
    rcases hf theta with ⟨psi, rfl⟩
    exact hmass psi
  · rintro ⟨c, hc, hmass⟩
    exact ⟨c, hc, fun theta ↦ hmass (f theta)⟩

/-- Every parameter space with at least two points can repeat the two
parameter rows of the manuscript's concrete examples. -/
theorem exists_surjection_parameter (Theta : Type u) [Nontrivial Theta] :
    ∃ f : Theta → FiniteExamples.Parameter, Function.Surjective f := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne Theta
  refine ⟨fun theta ↦ if theta = a then .one else .two, ?_⟩
  intro p
  cases p
  · exact ⟨a, if_pos rfl⟩
  · exact ⟨b, if_neg hab.symm⟩

theorem sufficiency_not_conditionality_witness
    (Theta : Type u) [Fintype Theta] [Nontrivial Theta] :
    ∃ I J : PackedFiniteInferenceBase.{u, 0} Theta,
      packedFiniteSufficiencyRelation I J ∧ ¬ packedFiniteConditionalityRelation I J := by
  obtain ⟨f, hf⟩ := exists_surjection_parameter Theta
  refine ⟨reparameterize f hf PackedRelationExample.packedE0X00,
    reparameterize f hf PackedRelationExample.packedE0X11, ?_, ?_⟩
  · exact (sufficiency_iff f hf _ _).mpr PackedRelationExample.pA_in_packedS
  · exact fun h ↦ PackedRelationExample.pA_not_in_packedC
      ((conditionality_iff f hf _ _).mp h)

theorem conditionality_not_sufficiency_witness
    (Theta : Type u) [Fintype Theta] [Nontrivial Theta] :
    ∃ I J : PackedFiniteInferenceBase.{u, 0} Theta,
      packedFiniteConditionalityRelation I J ∧ ¬ packedFiniteSufficiencyRelation I J := by
  obtain ⟨f, hf⟩ := exists_surjection_parameter Theta
  refine ⟨reparameterize f hf PackedRelationExample.packedEStarS01,
    reparameterize f hf PackedRelationExample.packedE3D1, ?_, ?_⟩
  · exact (conditionality_iff f hf _ _).mpr PackedRelationExample.pB_in_packedC
  · exact fun h ↦ PackedRelationExample.pB_not_in_packedS
      ((sufficiency_iff f hf _ _).mp h)

theorem joint_strict_witness
    (Theta : Type u) [Fintype Theta] [Nontrivial Theta] :
    ∃ I J : PackedFiniteInferenceBase.{u, 0} Theta,
      packedFiniteLikelihoodRelation I J ∧
        ¬ packedFiniteConditionalityRelation I J ∧ ¬ packedFiniteSufficiencyRelation I J := by
  obtain ⟨f, hf⟩ := exists_surjection_parameter Theta
  refine ⟨reparameterize f hf PackedPValueExample.packedE5X,
    reparameterize f hf PackedPValueExample.packedE6U, ?_, ?_, ?_⟩
  · exact (likelihood_iff f hf _ _).mpr
      PackedPValueExample.packedE5X_packedE6U_likelihood_related
  · exact fun h ↦ PackedPValueExample.packedE5X_packedE6U_not_conditionality
      ((conditionality_iff f hf _ _).mp h)
  · exact fun h ↦ PackedPValueExample.packedE5X_packedE6U_not_sufficiency
      ((sufficiency_iff f hf _ _).mp h)

theorem conditionality_nontransitivity_witness
    (Theta : Type u) [Fintype Theta] [Nontrivial Theta] :
    ∃ I J K : PackedFiniteInferenceBase.{u, 0} Theta,
      packedFiniteConditionalityRelation I J ∧
        packedFiniteConditionalityRelation J K ∧ ¬ packedFiniteConditionalityRelation I K := by
  obtain ⟨f, hf⟩ := exists_surjection_parameter Theta
  refine ⟨reparameterize f hf PackedRelationExample.packedE0GivenU0X00,
    reparameterize f hf PackedRelationExample.packedE0X00,
    reparameterize f hf PackedRelationExample.packedE0GivenV0X00, ?_, ?_, ?_⟩
  · exact (conditionality_iff f hf _ _).mpr
      PackedRelationExample.packed_e0_conditionality_nontransitivity_witness.1
  · exact (conditionality_iff f hf _ _).mpr
      PackedRelationExample.packed_e0_conditionality_nontransitivity_witness.2.1
  · exact fun h ↦ PackedRelationExample.packed_e0_conditionality_nontransitivity_witness.2.2
      ((conditionality_iff f hf _ _).mp h)

end FiniteParameterTransfer

/-! The same witnesses inhabit every sample universe; lifting does not
change their finite PMFs or their observation codes. -/
namespace SampleUniverseLift

variable {Theta : Type u} [Fintype Theta] [Nonempty Theta]

noncomputable def liftModel {X : Type} [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) : FiniteModel Theta (ULift.{v} X) where
  pmf := fun theta x ↦ E.pmf theta x.down
  pmf_nonneg := fun theta x ↦ E.pmf_nonneg theta x.down
  pmf_sum_one := by
    intro theta
    simpa using (Fintype.sum_equiv (Equiv.ulift : ULift.{v} X ≃ X)
      (fun x ↦ E.pmf theta x.down) (E.pmf theta) (fun _ ↦ rfl)).trans
      (E.pmf_sum_one theta)

noncomputable abbrev lift (I : PackedFiniteInferenceBase.{u, 0} Theta) :
    PackedFiniteInferenceBase.{u, v} Theta where
  Sample := ULift.{v} I.Sample
  sampleFintype := by
    letI : Fintype I.Sample := I.sampleFintype
    infer_instance
  sampleNonempty := by
    letI : Nonempty I.Sample := I.sampleNonempty
    infer_instance
  outcomeCode := fun x ↦ I.outcomeCode x.down
  outcomeCode_injective := by
    intro x y h
    exact ULift.ext _ _ (I.outcomeCode_injective h)
  model := @liftModel _ _ _ _ I.sampleFintype I.sampleNonempty I.model
  outcome := ⟨I.outcome⟩
  outcome_effective := I.outcome_effective
  all_outcomes_effective := fun x ↦ I.all_outcomes_effective x.down

theorem induced_liftModel {X : Type} {Y : Type w}
    [Fintype X] [Nonempty X] (E : FiniteModel Theta X)
    (T : ULift.{v} X → Y) (theta : Theta) (y : Y) :
    inducedPMF (liftModel E) T theta y =
      inducedPMF E (fun x ↦ T ⟨x⟩) theta y := by
  classical
  unfold inducedPMF
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Fintype.sum_equiv (Equiv.ulift : ULift.{v} X ≃ X) _ _ (fun _ ↦ rfl)

theorem induced_lifted_statistic {X A : Type}
    [Fintype X] [Nonempty X] (E : FiniteModel Theta X)
    (T : X → A) (theta : Theta) (y : A) :
    inducedPMF (liftModel.{u, v} E) (fun x ↦ (⟨T x.down⟩ : ULift.{v} A)) theta ⟨y⟩ =
      inducedPMF E T theta y := by
  classical
  rw [induced_liftModel]
  simp [inducedPMF]

theorem likelihood (I J : PackedFiniteInferenceBase.{u, 0} Theta)
    (h : packedFiniteLikelihoodRelation I J) :
    packedFiniteLikelihoodRelation (lift.{u, v} I) (lift.{u, v} J) := h

theorem conditionality (I J : PackedFiniteInferenceBase.{u, 0} Theta)
    (h : packedFiniteConditionalityRelation I J) :
    packedFiniteConditionalityRelation (lift.{u, v} I) (lift.{u, v} J) := by
  have directional (K M : PackedFiniteInferenceBase.{u, 0} Theta) :
      (letI : Fintype K.Sample := K.sampleFintype
       letI : Nonempty K.Sample := K.sampleNonempty
       letI : Fintype M.Sample := M.sampleFintype
       letI : Nonempty M.Sample := M.sampleNonempty
       letI : Fintype (lift.{u, v} K).Sample := (lift K).sampleFintype
       letI : Nonempty (lift.{u, v} K).Sample := (lift K).sampleNonempty
       letI : Fintype (lift.{u, v} M).Sample := (lift M).sampleFintype
       letI : Nonempty (lift.{u, v} M).Sample := (lift M).sampleNonempty
       finiteDirectionalConditionalityPair K.model K.outcomeCode K.asInferenceBase
         M.model M.outcomeCode M.asInferenceBase →
       finiteDirectionalConditionalityPair (lift K).model (lift K).outcomeCode
         (lift K).asInferenceBase (lift M).model (lift M).outcomeCode
         (lift M).asInferenceBase) := by
    letI : Fintype K.Sample := K.sampleFintype
    letI : Nonempty K.Sample := K.sampleNonempty
    letI : Fintype M.Sample := M.sampleFintype
    letI : Nonempty M.Sample := M.sampleNonempty
    rintro ⟨A₀, A, embed, hanc, hpos, hinj, hcode, hfiber, hobs, hmass⟩
    refine ⟨ULift.{v} A₀, fun x ↦ ⟨A x.down⟩,
      fun y ↦ ⟨embed y.down⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro theta psi a
      rcases a with ⟨a⟩
      change inducedPMF (liftModel K.model) _ theta _ = inducedPMF (liftModel K.model) _ psi _
      rw [induced_lifted_statistic, induced_lifted_statistic]
      exact hanc theta psi a
    · intro theta
      change 0 < inducedPMF (liftModel K.model) _ theta _
      rw [induced_lifted_statistic]
      exact hpos theta
    · intro x y hxy
      exact ULift.ext _ _ (hinj (congrArg ULift.down hxy))
    · rcases hcode with hcode | ⟨hnt, hsurj⟩
      · exact Or.inl (fun y ↦ hcode y.down)
      · letI : Nontrivial A₀ := hnt
        refine Or.inr ⟨inferInstance, ?_⟩
        intro a
        rcases hsurj a.down with ⟨x, hx⟩
        exact ⟨⟨x⟩, ULift.ext _ _ hx⟩
    · intro x
      constructor
      · intro hx
        rcases (hfiber x.down).mp (congrArg ULift.down hx) with ⟨y, hy⟩
        exact ⟨⟨y⟩, ULift.ext _ _ hy⟩
      · rintro ⟨y, hy⟩
        exact ULift.ext _ _ ((hfiber x.down).mpr ⟨y.down, congrArg ULift.down hy⟩)
    · exact ULift.ext _ _ hobs
    · intro theta y
      change M.model.pmf theta y.down = K.model.pmf theta (embed y.down) /
        inducedPMF (liftModel K.model) _ theta _
      rw [induced_lifted_statistic]
      exact hmass theta y.down
  exact h.elim (fun h ↦ Or.inl (directional I J h))
    (fun h ↦ Or.inr (directional J I h))

open FiniteExamples PackedRelationExample PackedPValueExample

theorem pB_not_sufficiency :
    ¬ packedFiniteSufficiencyRelation (lift.{0, v} packedEStarS01)
      (lift.{0, v} packedE3D1) := by
  let I := lift.{0, v} packedEStarS01
  let J := lift.{0, v} packedE3D1
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype J.Sample := J.sampleFintype
  letI : Nonempty J.Sample := J.sampleNonempty
  rintro ⟨TStar, T3, h, hminStar, hmin3, _hmass, _hobserved⟩
  letI : Fintype TStar.Codomain := TStar.codomainFintype
  letI : Fintype T3.Codomain := T3.codomainFintype
  have hcriterionStar := finiteMinimalSufficient_implies_likelihoodFiberCriterion
    I.model TStar.statistic I.all_outcomes_effective hminStar
  have hcriterion3 := finiteMinimalSufficient_implies_likelihoodFiberCriterion
    J.model T3.statistic J.all_outcomes_effective hmin3
  have hfibStar : ∀ x y,
      TStar.statistic ⟨x⟩ = TStar.statistic ⟨y⟩ ↔
        eStarMinimalClass x = eStarMinimalClass y := by
    intro x y
    exact (hcriterionStar ⟨x⟩ ⟨y⟩).trans (eStarReal_minimal x y).symm
  have hfib3 : ∀ x y,
      T3.statistic ⟨x⟩ = T3.statistic ⟨y⟩ ↔
        e3MinimalClass x = e3MinimalClass y := by
    intro x y
    exact (hcriterion3 ⟨x⟩ ⟨y⟩).trans (e3Real_minimal x y).symm
  have hsurjStar : Function.Surjective (fun x ↦ TStar.statistic ⟨x⟩) := by
    intro y
    rcases TStar.statistic_surjective y with ⟨x, hx⟩
    exact ⟨x.down, hx⟩
  have hsurj3 : Function.Surjective (fun x ↦ T3.statistic ⟨x⟩) := by
    intro y
    rcases T3.statistic_surjective y with ⟨x, hx⟩
    exact ⟨x.down, hx⟩
  let hStar : EStarMinimalClass ≃ TStar.Codomain :=
    relabelSameFibers _ eStarMinimalClass hsurjStar eStarMinimalClass_surjective hfibStar
  let h3 : E3MinimalClass ≃ T3.Codomain :=
    relabelSameFibers _ e3MinimalClass hsurj3 e3MinimalClass_surjective hfib3
  have hcStar := Fintype.card_congr hStar
  have hc3 := Fintype.card_congr h3
  have hc := Fintype.card_congr h
  have hStarKnown : Fintype.card EStarMinimalClass = 4 := by decide
  have h3Known : Fintype.card E3MinimalClass = 2 := by decide
  omega

theorem e5_ancillary_constant_general {A₀ : Type v} (A : E5Outcome → A₀)
    (hA : Ancillary e5FiniteModel A) : ∀ z, A z = A .x := by
  classical
  have hmass := hA Parameter.one Parameter.two (A .x)
  unfold inducedPMF at hmass
  rw [Finset.sum_filter, Finset.sum_filter,
    sum_E5Outcome, sum_E5Outcome] at hmass
  have hy : A .y = A .x := by
    by_contra hne
    simp [hne, e5FiniteModel, e5RealPmf] at hmass
  intro z
  cases z
  · rfl
  · exact hy

theorem e6_ancillary_constant_general {A₀ : Type v} (A : E6Outcome → A₀)
    (hA : Ancillary e6FiniteModel A) : ∀ z, A z = A .u := by
  classical
  have hmass := hA Parameter.one Parameter.two (A .u)
  unfold inducedPMF at hmass
  rw [Finset.sum_filter, Finset.sum_filter,
    sum_E6Outcome, sum_E6Outcome] at hmass
  have hv : A .v = A .u := by
    by_contra hne
    simp [hne, e6FiniteModel, e6RealPmf] at hmass
    norm_num at hmass
  intro z
  cases z
  · rfl
  · exact hv

theorem joint_not_conditionality :
    ¬ packedFiniteConditionalityRelation (lift.{0, v} packedE5X)
      (lift.{0, v} packedE6U) := by
  let I := lift.{0, v} packedE5X
  let J := lift.{0, v} packedE6U
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype J.Sample := J.sampleFintype
  letI : Nonempty J.Sample := J.sampleNonempty
  intro hC
  rcases hC with hC | hC
  · rcases hC with ⟨A₀, A, embed, hanc, _, _, _, _, hobs, hcond⟩
    have hanc' : Ancillary e5FiniteModel (fun z ↦ A ⟨z⟩) := by
      intro theta psi a
      have hh := hanc theta psi a
      change inducedPMF (liftModel e5FiniteModel) A theta a =
        inducedPMF (liftModel e5FiniteModel) A psi a at hh
      exact (induced_liftModel e5FiniteModel A theta a).symm.trans
        (hh.trans (induced_liftModel e5FiniteModel A psi a))
    have hconstant := e5_ancillary_constant_general _ hanc'
    have hden : inducedPMF I.model A .one (A I.outcome) = 1 := by
      change inducedPMF (liftModel e5FiniteModel) A .one (A ⟨E5Outcome.x⟩) = 1
      rw [induced_liftModel]
      rw [show (fun z ↦ A (⟨z⟩ : ULift.{v} E5Outcome)) =
        (fun _ ↦ A ⟨E5Outcome.x⟩) from funext hconstant]
      exact inducedPMF_const_eq e5FiniteModel _ _ .one rfl
    have hm := hcond Parameter.one J.outcome
    change embed J.outcome = I.outcome at hobs
    change J.model.pmf .one J.outcome = I.model.pmf .one (embed J.outcome) /
      inducedPMF I.model A .one (A I.outcome) at hm
    rw [hobs, hden] at hm
    norm_num [I, J, lift, liftModel, packedE5X, packedE6U,
      e5FiniteModel, e6FiniteModel, e5RealPmf, e6RealPmf] at hm
    change (1 / 5 : ℝ) = 1 / 10 at hm
    norm_num at hm
  · rcases hC with ⟨A₀, A, embed, hanc, _, _, _, _, hobs, hcond⟩
    have hanc' : Ancillary e6FiniteModel (fun x ↦ A ⟨x⟩) := by
      intro theta psi a
      have hh := hanc theta psi a
      change inducedPMF (liftModel e6FiniteModel) A theta a =
        inducedPMF (liftModel e6FiniteModel) A psi a at hh
      exact (induced_liftModel e6FiniteModel A theta a).symm.trans
        (hh.trans (induced_liftModel e6FiniteModel A psi a))
    have hconstant := e6_ancillary_constant_general _ hanc'
    have hden : inducedPMF J.model A .one (A J.outcome) = 1 := by
      change inducedPMF (liftModel e6FiniteModel) A .one (A ⟨E6Outcome.u⟩) = 1
      rw [induced_liftModel]
      rw [show (fun x ↦ A (⟨x⟩ : ULift.{v} E6Outcome)) =
        (fun _ ↦ A ⟨E6Outcome.u⟩) from funext hconstant]
      exact inducedPMF_const_eq e6FiniteModel _ _ .one rfl
    have hm := hcond Parameter.one I.outcome
    change embed I.outcome = J.outcome at hobs
    change I.model.pmf .one I.outcome = J.model.pmf .one (embed I.outcome) /
      inducedPMF J.model A .one (A J.outcome) at hm
    rw [hobs, hden] at hm
    norm_num [I, J, lift, liftModel, packedE5X, packedE6U,
      e5FiniteModel, e6FiniteModel, e5RealPmf, e6RealPmf] at hm
    change (1 / 10 : ℝ) = 1 / 5 at hm
    norm_num at hm

theorem joint_not_sufficiency :
    ¬ packedFiniteSufficiencyRelation (lift.{0, v} packedE5X)
      (lift.{0, v} packedE6U) := by
  classical
  let I := lift.{0, v} packedE5X
  let J := lift.{0, v} packedE6U
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  letI : Fintype J.Sample := J.sampleFintype
  letI : Nonempty J.Sample := J.sampleNonempty
  rintro ⟨T₅, T₆, h, hmin₅, hmin₆, hmass, hobserved⟩
  letI : Fintype T₅.Codomain := T₅.codomainFintype
  letI : Nonempty T₅.Codomain := T₅.codomainNonempty
  letI : Fintype T₆.Codomain := T₆.codomainFintype
  letI : Nonempty T₆.Codomain := T₆.codomainNonempty
  have hcriterion₅ := finiteMinimalSufficient_implies_likelihoodFiberCriterion
    I.model T₅.statistic I.all_outcomes_effective hmin₅
  have hcriterion₆ := finiteMinimalSufficient_implies_likelihoodFiberCriterion
    J.model T₆.statistic J.all_outcomes_effective hmin₆
  have hinjective₅ : Function.Injective (fun z ↦ T₅.statistic ⟨z⟩) := by
    intro z w hzw
    exact (e5_likelihood_class_singleton z w).2 ((hcriterion₅ ⟨z⟩ ⟨w⟩).1 hzw)
  have hinjective₆ : Function.Injective (fun x ↦ T₆.statistic ⟨x⟩) := by
    intro z w hzw
    exact (e6_likelihood_class_singleton z w).2 ((hcriterion₆ ⟨z⟩ ⟨w⟩).1 hzw)
  have hm := hmass Parameter.one (T₆.statistic J.outcome)
  rw [← hobserved] at hm
  change inducedPMF (liftModel e5FiniteModel) T₅.statistic .one (T₅.statistic ⟨E5Outcome.x⟩) =
    inducedPMF (liftModel e6FiniteModel) T₆.statistic .one (T₆.statistic ⟨E6Outcome.u⟩) at hm
  rw [induced_liftModel, induced_liftModel] at hm
  unfold inducedPMF at hm
  rw [Finset.sum_filter, Finset.sum_filter,
    sum_E5Outcome, sum_E6Outcome] at hm
  have hne₅ : T₅.statistic ⟨E5Outcome.y⟩ ≠ T₅.statistic ⟨E5Outcome.x⟩ := by
    intro heq
    have := hinjective₅ heq
    contradiction
  have hne₆ : T₆.statistic ⟨E6Outcome.v⟩ ≠ T₆.statistic ⟨E6Outcome.u⟩ := by
    intro heq
    have := hinjective₆ heq
    contradiction
  norm_num [hne₅, hne₆, e5FiniteModel, e5RealPmf, e6FiniteModel, e6RealPmf] at hm
  change ((if T₅.statistic ⟨E5Outcome.x⟩ = T₅.statistic ⟨E5Outcome.x⟩ then (1 / 10 : ℝ) else 0) +
      if T₅.statistic ⟨E5Outcome.y⟩ = T₅.statistic ⟨E5Outcome.x⟩ then 9 / 10 else 0) =
    ((if T₆.statistic ⟨E6Outcome.u⟩ = T₆.statistic ⟨E6Outcome.u⟩ then (1 / 5 : ℝ) else 0) +
      if T₆.statistic ⟨E6Outcome.v⟩ = T₆.statistic ⟨E6Outcome.u⟩ then 4 / 5 else 0) at hm
  rw [if_pos rfl, if_neg hne₅, if_pos rfl, if_neg hne₆] at hm
  norm_num at hm

theorem joint_strict_witness (Theta : Type u) [Fintype Theta] [Nontrivial Theta] :
    ∃ I J : PackedFiniteInferenceBase.{u, v} Theta,
      packedFiniteLikelihoodRelation I J ∧
        ¬ packedFiniteConditionalityRelation I J ∧ ¬ packedFiniteSufficiencyRelation I J := by
  obtain ⟨f, hf⟩ := FiniteParameterTransfer.exists_surjection_parameter Theta
  refine ⟨FiniteParameterTransfer.reparameterize f hf (lift.{0, v} packedE5X),
    FiniteParameterTransfer.reparameterize f hf (lift.{0, v} packedE6U), ?_, ?_, ?_⟩
  · exact (FiniteParameterTransfer.likelihood_iff f hf _ _).mpr
      (likelihood _ _ packedE5X_packedE6U_likelihood_related)
  · exact fun h ↦ joint_not_conditionality
      ((FiniteParameterTransfer.conditionality_iff f hf _ _).mp h)
  · exact fun h ↦ joint_not_sufficiency
      ((FiniteParameterTransfer.sufficiency_iff f hf _ _).mp h)

theorem conditionality_not_sufficiency_witness
    (Theta : Type u) [Fintype Theta] [Nontrivial Theta] :
    ∃ I J : PackedFiniteInferenceBase.{u, v} Theta,
      packedFiniteConditionalityRelation I J ∧ ¬ packedFiniteSufficiencyRelation I J := by
  obtain ⟨f, hf⟩ := FiniteParameterTransfer.exists_surjection_parameter Theta
  refine ⟨FiniteParameterTransfer.reparameterize f hf (lift.{0, v} packedEStarS01),
    FiniteParameterTransfer.reparameterize f hf (lift.{0, v} packedE3D1), ?_, ?_⟩
  · exact (FiniteParameterTransfer.conditionality_iff f hf _ _).mpr
      (conditionality _ _ pB_in_packedC)
  · exact fun h ↦ pB_not_sufficiency
      ((FiniteParameterTransfer.sufficiency_iff f hf _ _).mp h)

end SampleUniverseLift

/-! ## LR separation for every finite null/alternative parameter partition -/
namespace FinitePValueTransfer

open FiniteExamples PackedPValueExample FiniteParameterTransfer

variable {Theta : Type u} [Fintype Theta] [Nonempty Theta]

noncomputable def partitionMap (P : ParameterPartition Theta) : Theta → Parameter := by
  classical
  exact fun theta ↦ if theta ∈ P.nullPart then .one else .two

omit [Nonempty Theta] in
theorem partitionMap_null (P : ParameterPartition Theta) {theta : Theta}
    (h : theta ∈ P.nullPart) : partitionMap P theta = .one := by
  classical
  simp [partitionMap, h]

omit [Nonempty Theta] in
theorem partitionMap_alternative (P : ParameterPartition Theta) {theta : Theta}
    (h : theta ∈ P.alternativePart) : partitionMap P theta = .two := by
  classical
  have hn : theta ∉ P.nullPart := fun hn ↦ P.disjoint hn h
  simp [partitionMap, hn]

omit [Nonempty Theta] in
theorem partitionMap_surjective (P : ParameterPartition Theta) :
    Function.Surjective (partitionMap P) := by
  intro p
  cases p
  · obtain ⟨theta, ht⟩ := P.null_nonempty
    exact ⟨theta, partitionMap_null P ht⟩
  · obtain ⟨theta, ht⟩ := P.alternative_nonempty
    exact ⟨theta, partitionMap_alternative P ht⟩

theorem finiteMaximum_of_constant_on {A : Type w} [Fintype A]
    (s : Finset A) (hs : s.Nonempty) (f : A → ℝ) (c : ℝ)
    (h : ∀ a ∈ s, f a = c) : finiteMaximum s hs f = c := by
  apply le_antisymm
  · exact finiteMaximum_le s hs f (fun a ha ↦ (h a ha).le)
  · obtain ⟨a, ha⟩ := hs
    rw [← h a ha]
    exact le_finiteMaximum s ⟨a, ha⟩ f ha

theorem max_null {X : Type v} [Fintype X] [Nonempty X]
    (E : FiniteModel Parameter X) (P : ParameterPartition Theta) (x : X) :
    maxLikelihoodOn (reparameterizeModel (partitionMap P) E)
      P.nullPart P.null_nonempty x = E.pmf .one x := by
  apply finiteMaximum_of_constant_on
  intro theta htheta
  change E.pmf (partitionMap P theta) x = _
  rw [partitionMap_null P htheta]

theorem max_alternative {X : Type v} [Fintype X] [Nonempty X]
    (E : FiniteModel Parameter X) (P : ParameterPartition Theta) (x : X) :
    maxLikelihoodOn (reparameterizeModel (partitionMap P) E)
      P.alternativePart P.alternative_nonempty x = E.pmf .two x := by
  apply finiteMaximum_of_constant_on
  intro theta htheta
  change E.pmf (partitionMap P theta) x = _
  rw [partitionMap_alternative P htheta]

theorem likelihoodRatio_reparameterize {X : Type v} [Fintype X] [Nonempty X]
    (E : FiniteModel Parameter X) (P : ParameterPartition Theta) (x : X) :
    extendedLikelihoodRatio (reparameterizeModel (partitionMap P) E) P x =
      extendedLikelihoodRatio E singletonNullPartition x := by
  unfold extendedLikelihoodRatio
  rw [max_null, max_alternative]
  simp [maxLikelihoodOn, singletonNullPartition, finiteMaximum_singleton]

theorem lowerTailRegion_reparameterize {X : Type v} [Fintype X] [Nonempty X]
    (E : FiniteModel Parameter X) (P : ParameterPartition Theta) (x : X) :
    lowerTailRegion (reparameterizeModel (partitionMap P) E) P x =
      lowerTailRegion E singletonNullPartition x := by
  ext y
  simp only [mem_lowerTailRegion_iff, likelihoodRatio_reparameterize]

theorem lowerTailProbability_reparameterize {X : Type v} [Fintype X] [Nonempty X]
    (E : FiniteModel Parameter X) (P : ParameterPartition Theta) (x : X)
    (theta : Theta) :
    lowerTailProbability (reparameterizeModel (partitionMap P) E) P x theta =
      lowerTailProbability E singletonNullPartition x (partitionMap P theta) := by
  unfold lowerTailProbability
  rw [lowerTailRegion_reparameterize]
  rfl

theorem pvalue_reparameterize {X : Type v} [Fintype X] [Nonempty X]
    (E : FiniteModel Parameter X) (P : ParameterPartition Theta) (x : X) :
    lowerTailLRPValue (reparameterizeModel (partitionMap P) E) P x =
      lowerTailLRPValue E singletonNullPartition x := by
  unfold lowerTailLRPValue
  have hc : ∀ theta ∈ P.nullPart,
      lowerTailProbability (reparameterizeModel (partitionMap P) E) P x theta =
        lowerTailProbability E singletonNullPartition x .one := by
    intro theta htheta
    rw [lowerTailProbability_reparameterize, partitionMap_null P htheta]
  rw [finiteMaximum_of_constant_on _ _ _ _ hc]
  simp [singletonNullPartition, finiteMaximum_singleton]

theorem pvalue_lift_model {X : Type} [Fintype X] [Nonempty X]
    (E : FiniteModel Theta X) (P : ParameterPartition Theta) (x : X) :
    lowerTailLRPValue (SampleUniverseLift.liftModel.{u, v} E) P ⟨x⟩ =
      lowerTailLRPValue E P x := by
  classical
  have hprob : lowerTailProbability (SampleUniverseLift.liftModel.{u, v} E) P ⟨x⟩ =
      lowerTailProbability E P x := by
    funext theta
    unfold lowerTailProbability lowerTailRegion
    rw [Finset.sum_filter, Finset.sum_filter]
    exact Fintype.sum_equiv (Equiv.ulift : ULift.{v} X ≃ X) _ _ (fun _ ↦ rfl)
  unfold lowerTailLRPValue
  rw [hprob]

noncomputable def e5Base (P : ParameterPartition Theta) :
    PackedFiniteInferenceBase.{u, v} Theta :=
  reparameterize (partitionMap P) (partitionMap_surjective P)
    (SampleUniverseLift.lift.{0, v} packedE5X)

noncomputable def e6Base (P : ParameterPartition Theta) :
    PackedFiniteInferenceBase.{u, v} Theta :=
  reparameterize (partitionMap P) (partitionMap_surjective P)
    (SampleUniverseLift.lift.{0, v} packedE6U)

theorem e5_pvalue (P : ParameterPartition Theta) :
    packedLowerTailLRPValue P (e5Base.{u, v} P) = 1 / 10 := by
  change lowerTailLRPValue
    (reparameterizeModel (partitionMap P) (SampleUniverseLift.liftModel e5FiniteModel))
      P ⟨E5Outcome.x⟩ = _
  rw [pvalue_reparameterize, pvalue_lift_model, e5_lowerTailLRPValue_x]

theorem e6_pvalue (P : ParameterPartition Theta) :
    packedLowerTailLRPValue P (e6Base.{u, v} P) = 1 / 5 := by
  change lowerTailLRPValue
    (reparameterizeModel (partitionMap P) (SampleUniverseLift.liftModel e6FiniteModel))
      P ⟨E6Outcome.u⟩ = _
  rw [pvalue_reparameterize, pvalue_lift_model, e6_lowerTailLRPValue_u]

theorem likelihood_related (P : ParameterPartition Theta) :
    packedFiniteLikelihoodRelation (e5Base.{u, v} P) (e6Base P) := by
  apply (likelihood_iff (partitionMap P) (partitionMap_surjective P) _ _).mpr
  exact SampleUniverseLift.likelihood _ _ packedE5X_packedE6U_likelihood_related

theorem not_preserves_likelihood (P : ParameterPartition Theta) :
    ¬ Preserves (packedLowerTailLRPValueProcedure.{u, v} P)
      (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) := by
  intro hpres
  have hout := hpres (likelihood_related.{u, v} P)
  simp only [packedLowerTailLRPValueProcedure, output_graphProcedure] at hout
  have hpSubtype := Set.singleton_eq_singleton_iff.mp hout
  have hp := congrArg Subtype.val hpSubtype
  simp only [packedLowerTailLRPValueInUnitInterval] at hp
  rw [e5_pvalue, e6_pvalue] at hp
  norm_num at hp

theorem procedure_in_sufficiency_not_likelihood (P : ParameterPartition Theta) :
    packedLowerTailLRPValueProcedure.{u, v} P ∈
      preservingClass (Set.Icc (0 : ℝ) 1)
        (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) \
      preservingClass (Set.Icc (0 : ℝ) 1)
        (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) :=
  ⟨packedLowerTailLRPValueProcedure_preserves_sufficiency P, not_preserves_likelihood P⟩

end FinitePValueTransfer

/-- For every genuine finite null/alternative partition, the global LR
p-value procedure preserves S but not L; the transported E5/E6 pair retains
its exact p-values. -/
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
  exact ⟨FinitePValueTransfer.procedure_in_sufficiency_not_likelihood P,
    FinitePValueTransfer.e5Base P, FinitePValueTransfer.e6Base P,
    FinitePValueTransfer.likelihood_related P,
    FinitePValueTransfer.e5_pvalue P, FinitePValueTransfer.e6_pvalue P⟩

/-- Incomparability for every finite parameter space with at least two points. -/
theorem packed_sufficiency_conditionality_incomparable
    {Theta : Type u} [Fintype Theta] [Nontrivial Theta] :
    RelationsIncomparable
      (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta))
      (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) := by
  obtain ⟨I, J, hC, hS⟩ :=
    SampleUniverseLift.conditionality_not_sufficiency_witness.{u, v} Theta
  exact relationsIncomparable_of_witnesses
    (parameterFreeCoin_in_sufficiency_not_conditionality.{u, v} Theta) ⟨hC, hS⟩

/-- Direct C is strictly below its likelihood closure for every nonempty
finite parameter space, including a singleton. -/
theorem evans2013_theorem7_packed
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    packedFiniteConditionalityRelation.{u, v} (Theta := Theta) <
        equivalenceClosure
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧
      equivalenceClosure
          (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) =
        packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) := by
  refine ⟨?_, packedFiniteConditionalityClosure_eq_likelihoodRelation⟩
  rw [lt_iff_le_and_ne]
  refine ⟨relation_le_equivalenceClosure _, ?_⟩
  intro heq
  apply packedFiniteConditionalityRelation_not_transitive (Theta := Theta)
  rw [heq]
  intro I J K hIJ hJK
  exact (equivalenceClosure_isEquivalence _).trans hIJ hJK

/-- The two-row union-separation witness extends to every finite parameter
space with at least two points. The closure identity itself needs no such
size restriction. -/
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
  refine ⟨?_, packedFiniteJointClosure_eq_likelihoodRelation⟩
  obtain ⟨I, J, hL, hC, hS⟩ :=
    SampleUniverseLift.joint_strict_witness.{u, v} Theta
  exact relationUnion_lt_of_witness
    packedFiniteConditionalityRelation_le_likelihoodRelation
    packedFiniteSufficiencyRelation_le_likelihoodRelation hL hC hS

/-- Sufficiency is strictly below likelihood whenever there are at least
two parameter values. -/
theorem packedFiniteSufficiencyRelation_lt_likelihoodRelation
    {Theta : Type u} [Fintype Theta] [Nontrivial Theta] :
    packedFiniteSufficiencyRelation.{u, v} (Theta := Theta) <
      packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) := by
  rw [lt_iff_le_and_ne]
  refine ⟨packedFiniteSufficiencyRelation_le_likelihoodRelation, ?_⟩
  obtain ⟨I, J, hL, _, hS⟩ :=
    SampleUniverseLift.joint_strict_witness.{u, v} Theta
  intro heq
  exact hS (heq ▸ hL)

theorem packed_evans2013_premises
    {Theta : Type u} [Fintype Theta] [Nontrivial Theta] :
    EvansPremises
      (packedFiniteConditionalityRelation.{u, v} (Theta := Theta))
      (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta))
      (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) where
  sufficiency_equivalence := packedFiniteSufficiencyRelation_isEquivalence
  sufficiency_le_likelihood := packedFiniteSufficiencyRelation_le_likelihoodRelation
  sufficiency_strict_witness := by
    obtain ⟨I, J, hL, _, hS⟩ := SampleUniverseLift.joint_strict_witness.{u, v} Theta
    exact ⟨I, J, hL, hS⟩
  conditionality_closure := packedFiniteConditionalityClosure_eq_likelihoodRelation
  joint_closure := packedFiniteJointClosure_eq_likelihoodRelation

/-- When the output type is empty, the empty relation is the only procedure. -/
theorem procedure_eq_empty_of_isEmpty_output
    {ι : Type u} {A : Type v} [IsEmpty A] (Ev : Procedure ι A) :
    Ev = ∅ := by
  ext p
  exact isEmptyElim p.2

theorem preservingClass_eq_of_isEmpty_output
    {ι : Type u} {A : Type v} [IsEmpty A]
    (D E : StatisticalRelation ι) :
    preservingClass A D = preservingClass A E := by
  have h (R : StatisticalRelation ι) : preservingClass A R = Set.univ := by
    apply Set.eq_univ_of_forall
    intro Ev i j _
    ext a
    exact isEmptyElim a
  rw [h D, h E]

/-- Exact strictness criterion, including singleton parameters and empty outputs. -/
theorem packed_procedure_class_strict_iff
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] {A : Type w} :
    preservingClass A
        (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) ⊂
      preservingClass A
        (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) ↔
      Nontrivial Theta ∧ Nonempty A := by
  classical
  constructor
  · intro h
    constructor
    · by_contra hn
      letI : Subsingleton Theta := not_nontrivial_iff_subsingleton.mp hn
      exact packed_BT1_strictness_false_of_subsingleton_parameter A h
    · by_contra hn
      letI : IsEmpty A := ⟨fun a ↦ hn ⟨a⟩⟩
      have heq := preservingClass_eq_of_isEmpty_output (A := A)
        (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta))
        (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta))
      rw [heq] at h
      exact (lt_irrefl _ h)
  · rintro ⟨hTheta, hA⟩
    letI : Nontrivial Theta := hTheta
    letI : Nonempty A := hA
    exact (theorem_BT1_procedure_classes_of_premises
      (A := A) (packed_evans2013_premises (Theta := Theta))).2.1

/-- All three procedure statements on every nonempty finite parameter space. -/
-- manuscript-id: BT1
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
  refine ⟨?_, ⟨preservingClass_antitone
    packedFiniteSufficiencyRelation_le_likelihoodRelation,
    packed_procedure_class_strict_iff⟩, ?_⟩
  · rw [preservingClass_equivalenceClosure
      (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)),
      packedFiniteConditionalityClosure_eq_likelihoodRelation]
  · rw [← preservingClass_union,
      preservingClass_equivalenceClosure (relationUnion
        (packedFiniteConditionalityRelation.{u, v} (Theta := Theta))
        (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta))),
      packedFiniteJointClosure_eq_likelihoodRelation]

theorem singleton_parameter_procedure_classes
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] [Subsingleton Theta]
    {A : Type w} :
    packedFiniteSufficiencyRelation.{u, v} (Theta := Theta) =
      packedFiniteLikelihoodRelation ∧
    preservingClass A
        (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) =
      preservingClass A
        (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) ∧
    preservingClass A
        (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) =
      preservingClass A
        (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) := by
  refine ⟨packed_sufficiency_eq_likelihood_of_subsingleton_parameter, ?_, ?_⟩
  · rw [packed_sufficiency_eq_likelihood_of_subsingleton_parameter]
  · rw [preservingClass_equivalenceClosure,
      packedFiniteConditionalityClosure_eq_likelihoodRelation]

/- Corollary 3.1: a C-preserving procedure gives equal outputs on pairs
in L \ C. The proof uses the certified conditionality-closure identity
and holds for every nonempty finite parameter space.
The manuscript ID below is a stable key used by the verification index. -/
-- manuscript-id: BT2
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
    output Ev i = output Ev j :=
  VennDiagrams.corollary_BT2
    packedFiniteConditionalityClosure_eq_likelihoodRelation hEv hij

/- Corollary 3.2: joint preservation of S and C gives equal outputs on
pairs in L \ (S ∪ C). The proof uses the certified joint-closure identity
and holds for every nonempty finite parameter space. -/
-- manuscript-id: BT3
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
    output Ev i = output Ev j :=
  VennDiagrams.corollary_BT3
    packedFiniteJointClosure_eq_likelihoodRelation hEv.1 hEv.2 hij

theorem packed_evans2013_joint_strict_premise
    {Theta : Type u} [Fintype Theta] [Nontrivial Theta] :
    EvansJointStrictPremise
      (packedFiniteConditionalityRelation.{u, v} (Theta := Theta))
      (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta))
      (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) :=
  ⟨SampleUniverseLift.joint_strict_witness Theta⟩

/-- A single promoted certificate for the paper's concrete E5/E6 LR p-value
separation, including the two exact values, the `L`-pair, and the resulting
strict procedure-class witness. -/
theorem packed_e5_e6_lr_pvalue_separation
    : packedLowerTailLRPValue PackedPValueExample.singletonNullPartition
        PackedPValueExample.packedE5X = 1 / 10 ∧
      packedLowerTailLRPValue PackedPValueExample.singletonNullPartition
        PackedPValueExample.packedE6U = 1 / 5 ∧
      packedFiniteLikelihoodRelation.{0, 0}
        PackedPValueExample.packedE5X PackedPValueExample.packedE6U ∧
      packedLowerTailLRPValueProcedure.{0, 0}
          PackedPValueExample.singletonNullPartition ∈
        preservingClass (Set.Icc (0 : ℝ) 1)
            (packedFiniteSufficiencyRelation.{0, 0} (Theta := Parameter)) \
          preservingClass (Set.Icc (0 : ℝ) 1)
            (packedFiniteLikelihoodRelation.{0, 0} (Theta := Parameter)) := by
  exact ⟨PackedPValueExample.packedE5X_pValue,
    PackedPValueExample.packedE6U_pValue,
    PackedPValueExample.packedE5X_packedE6U_likelihood_related,
    PackedPValueExample.packedLowerTailLRPValueProcedure_in_sufficiency_not_likelihood⟩

/-- One promoted, assumption-free certificate for the finite sufficiency
foundations used by the paper: Neyman--Fisher factorization, the genuine
minimal-sufficiency criterion, the canonical statistic and its injective
relabellings, and lower-tail LR reduction. -/
theorem finite_sufficiency_and_lr_certificate
    {Theta : Type u} {X Y : Type v}
    [Fintype Theta] [Nonempty Theta]
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (E : FiniteModel Theta X) (T : X → Y)
    (hall : ∀ x, x ∈ effectiveSupport E)
    (P : ParameterPartition Theta) (observed : X) :
    (FiniteSufficient E T ↔ StrictFiniteFactorization E T) ∧
      (FiniteMinimalSufficient E T ↔
        LikelihoodFiberCriterion (fun x theta ↦ E.pmf theta x) T) ∧
      FiniteMinimalSufficient E
        (canonicalMinimalSufficient (fun x theta ↦ E.pmf theta x)) ∧
      (∀ (relabel : Quotient (likelihoodProportionalitySetoid
          (fun x theta ↦ E.pmf theta x)) → Y),
        Function.Injective relabel →
          FiniteMinimalSufficient E
            (relabel ∘ canonicalMinimalSufficient
              (fun x theta ↦ E.pmf theta x))) ∧
      (FiniteSufficient E T →
        lowerTailLRPValue E P observed =
          lowerTailLRPValue (inducedModel E T) P (T observed)) := by
  exact ⟨finite_neyman_fisher_factorization E T hall,
    finite_minimal_sufficiency_iff_likelihoodFiberCriterion E T hall,
    canonicalMinimalSufficient_isFiniteMinimalSufficient E hall,
    fun relabel hinjective ↦
      injective_relabel_canonicalMinimalSufficient_isFiniteMinimalSufficient
        E hall relabel hinjective,
    fun hS ↦ lowerTailLRPValue_induced_of_finiteSufficient
      E T hall hS P observed⟩

/-- The paper's two explicit pairs assemble into an exact incomparability
certificate for the instantiated sufficiency and conditionality relations. -/
theorem concrete_sufficiency_conditionality_incomparable :
    RelationsIncomparable comparisonSufficiency comparisonConditionality :=
  relationsIncomparable_of_witnesses pA_in_S_diff_C pB_in_C_diff_S

theorem finite_examples_exact_certificate : Finite.ExactCertificate := by
  exact
    { e0_normalized := e0_normalized
      eT_normalized := eT_normalized
      induced_minimal_models_coincide := induced_m_models_coincide
      statistic_M_has_likelihood_fibers :=
        mStatistic_minimal_sufficient_criterion
      statistic_MT_has_likelihood_fibers :=
        mTStatistic_minimal_sufficient_criterion
      mle_models_coincide := e0_eT_mle_laws_coincide
      U_ancillary := firstCoordinate_ancillary
      V_ancillary := secondCoordinate_ancillary
      conditionality_not_transitive := concreteConditionality_not_transitive
      hierarchical_normalized := hierarchical_models_normalized
      selector_ancillary := selector_ancillary
      selector_zero_is_E3 := condition_on_selector_zero_is_e3
      selector_one_is_E4 := condition_on_selector_one_is_e4
      hierarchical_MLE_laws_differ := hierarchical_mle_laws_differ
      pA_same_minimal_class := pA_statistic_values_equal
      pB_positive_scaling := pB_positive_proportionality
      pB_no_minimal_partition_bijection := no_bijection_between_pB_minimal_partitions
      pvalue_counterexample := ⟨exact_lr_p_values.1, exact_lr_p_values.2,
        proportional_likelihoods_but_different_p_values.2⟩ }

theorem procedure_examples_certificate
    {ι : Type u} {Theta : Type v} [Fintype Theta]
    {PriorType : Type*} (observedLikelihood : ι → Theta → ℝ)
    (prior : Theta → ℝ) (H : Finset Theta)
    (hden : ∀ i, posteriorNormalizer (observedLikelihood i) prior ≠ 0) :
    Preserves (maximumLikelihoodProcedure observedLikelihood)
        (likelihoodRelation observedLikelihood) ∧
      Preserves (posteriorProcedure observedLikelihood prior H)
        (likelihoodRelation observedLikelihood) ∧
      Preserves
        (bayesianInformationProcedure (PriorType := PriorType) observedLikelihood)
        (likelihoodRelation observedLikelihood) := by
  exact ⟨maximumLikelihoodProcedure_preserves_likelihood observedLikelihood,
    posteriorProcedure_preserves_likelihood observedLikelihood prior H hden,
    bayesianInformationProcedure_preserves_likelihood observedLikelihood⟩

end PaperSignature
end Certification
end VennDiagrams

/-! ## Complete numbered Evans (2013) result map

These signatures certify Lemmas 1–6, Theorems 7–9 and Corollary 10 using
the definitions above. The existing Theorem 7 and Theorem 9 certificates
are reused. No relation-level Evans conclusion is an input hypothesis.
The two generic closure lemmas hold for arbitrary relations; statistical
statements use the paper's finite, effective, coded inference bases.
-/

namespace VennDiagrams
namespace Certification
namespace PaperSignature

universe u v

/-- Evans (2013), Lemma 1: equivalence closure is finite zigzag connectivity.
Allowing a zero-step chain removes the need to assume reflexivity of `R`. -/
theorem evans2013_lemma1 {ι : Type u} (R : StatisticalRelation ι) :
    equivalenceClosure R = Relation.ReflTransGen (Relation.SymmGen R) :=
  equivalenceClosure_eq_zigzagClosure R

/-- Evans (2013), Lemma 2: closing either component before taking the union
does not change the equivalence closure of that union. -/
theorem evans2013_lemma2 {ι : Type u} (R₁ R₂ : StatisticalRelation ι) :
    equivalenceClosure
        (relationUnion (equivalenceClosure R₁) (equivalenceClosure R₂)) =
      equivalenceClosure (relationUnion R₁ R₂) := by
  apply le_antisymm
  · apply equivalenceClosure_minimal (equivalenceClosure_isEquivalence _)
    have h₁ : equivalenceClosure R₁ ≤
        equivalenceClosure (relationUnion R₁ R₂) :=
      equivalenceClosure_minimal (equivalenceClosure_isEquivalence _)
        (fun i j hij ↦ Relation.EqvGen.rel i j (Or.inl hij))
    have h₂ : equivalenceClosure R₂ ≤
        equivalenceClosure (relationUnion R₁ R₂) :=
      equivalenceClosure_minimal (equivalenceClosure_isEquivalence _)
        (fun i j hij ↦ Relation.EqvGen.rel i j (Or.inr hij))
    intro i j hij
    exact hij.elim (h₁ i j) (h₂ i j)
  · apply equivalenceClosure_minimal (equivalenceClosure_isEquivalence _)
    intro i j hij
    apply Relation.EqvGen.rel
    exact hij.elim
      (fun h ↦ Or.inl (Relation.EqvGen.rel i j h))
      (fun h ↦ Or.inr (Relation.EqvGen.rel i j h))

/-- Evans (2013), Lemma 3: the likelihood relation is an equivalence. -/
theorem evans2013_lemma3_packed
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Equivalence (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) :=
  likelihoodRelation_isEquivalence PackedFiniteInferenceBase.likelihood

/-- Evans (2013), Lemma 4: likelihood classes give a genuinely sufficient
and minimal sufficient statistic in every packed finite experiment. -/
theorem evans2013_lemma4_packed
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I : PackedFiniteInferenceBase.{u, v} Theta) :
    letI : Fintype I.Sample := I.sampleFintype
    letI : Nonempty I.Sample := I.sampleNonempty
    FiniteMinimalSufficient I.model (canonicalMinimalSufficient I.likelihoodFamily) := by
  letI : Fintype I.Sample := I.sampleFintype
  letI : Nonempty I.Sample := I.sampleNonempty
  exact canonicalMinimalSufficient_isFiniteMinimalSufficient
    I.model I.all_outcomes_effective

/-- Evans (2013), Lemma 5: genuine sufficiency is an equivalence relation
contained in likelihood. -/
theorem evans2013_lemma5_packed
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Equivalence (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) ∧
      packedFiniteSufficiencyRelation.{u, v} (Theta := Theta) ≤
        packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) :=
  ⟨packedFiniteSufficiencyRelation_isEquivalence,
    packedFiniteSufficiencyRelation_le_likelihoodRelation⟩

/-- Evans (2013), Lemma 6: direct conditionality is reflexive, symmetric,
nontransitive and contained in likelihood, including singleton parameters. -/
theorem evans2013_lemma6_packed
    {Theta : Type u} [Fintype Theta] [Nonempty Theta] :
    Reflexive (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧
      Symmetric (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧
      ¬ Transitive (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧
      packedFiniteConditionalityRelation.{u, v} (Theta := Theta) ≤
        packedFiniteLikelihoodRelation.{u, v} (Theta := Theta) :=
  ⟨packedFiniteConditionalityRelation_reflexive,
    packedFiniteConditionalityRelation_symmetric,
    packedFiniteConditionalityRelation_not_transitive,
    packedFiniteConditionalityRelation_le_likelihoodRelation⟩

/-- Evans (2013), Theorem 8: both inclusions in the joint closure argument
are derived for the actual finite statistical relations. -/
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
  refine ⟨relationUnion_le_of_le
    packedFiniteConditionalityRelation_le_likelihoodRelation
    packedFiniteSufficiencyRelation_le_likelihoodRelation, ?_⟩
  rw [packedFiniteJointClosure_eq_likelihoodRelation]

/-- Evans (2013), Corollary 10: both the local union and sufficiency alone
are strictly below the conditionality closure when there are two parameters. -/
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
  rw [packedFiniteConditionalityClosure_eq_likelihoodRelation]
  exact ⟨evans2013_theorem9_packed.1, rfl,
    packedFiniteSufficiencyRelation_lt_likelihoodRelation⟩

/-- The appendix's four-step claim, with three intermediate inference
bases in the same universe and four applications of the exact direct `C`. -/
theorem evans2013_four_step_chain_packed
    {Theta : Type u} [Fintype Theta] [Nonempty Theta]
    (I J : PackedFiniteInferenceBase.{u, v} Theta)
    (hL : packedFiniteLikelihoodRelation I J) :
    ∃ M₁ H M₂ : PackedFiniteInferenceBase.{u, v} Theta,
      packedFiniteConditionalityRelation I M₁ ∧
      packedFiniteConditionalityRelation M₁ H ∧
      packedFiniteConditionalityRelation H M₂ ∧
      packedFiniteConditionalityRelation M₂ J := by
  rcases hL with ⟨k, hk, hlik⟩
  let a : ℝ := 1 / (1 + k)
  let b : ℝ := k / (1 + k)
  have hden : 0 < 1 + k := by linarith
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by
    dsimp [a]
    apply (div_lt_one hden).2
    linarith
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hb1 : b < 1 := by
    dsimp [b]
    apply (div_lt_one hden).2
    linarith
  have hscaled : ∀ theta, a * I.likelihood theta = b * J.likelihood theta := by
    intro theta
    dsimp [a, b]
    rw [hlik theta]
    field_simp [ne_of_gt hden]
  refine ⟨Evans2013Construction.starPacked I a ha0 ha1,
    Evans2013Construction.bridgePacked I a ha0 ha1,
    Evans2013Construction.starPacked J b hb0 hb1, ?_, ?_, ?_, ?_⟩
  · exact packedFiniteConditionalityRelation_symmetric
      (Evans2013Construction.starPacked_conditions_to_original I a ha0 ha1)
  · exact Evans2013Construction.starPacked_conditions_to_bridge_of_scaled_eq
      I I a a ha0 ha1 ha0 ha1 (fun _ ↦ rfl)
  · exact packedFiniteConditionalityRelation_symmetric
      (Evans2013Construction.starPacked_conditions_to_bridge_of_scaled_eq
        I J a b ha0 ha1 hb0 hb1 hscaled)
  · exact Evans2013Construction.starPacked_conditions_to_original J b hb0 hb1

/-- A single proved conjunction of all ten numbered Evans (2013) results.
The only restrictions are the finite-model domain and the parameter-size
requirement needed for the strict statements in Theorem 9 and Corollary 10.
The individual certificates retain their stronger singleton-parameter scope. -/
theorem evans2013_full_certificate_packed
    {Theta : Type u} [Fintype Theta] [Nontrivial Theta] :
    let C := packedFiniteConditionalityRelation.{u, v} (Theta := Theta)
    let S := packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)
    let L := packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)
    (∀ R : StatisticalRelation (PackedFiniteInferenceBase.{u, v} Theta),
      equivalenceClosure R = Relation.ReflTransGen (Relation.SymmGen R)) ∧
    (∀ R₁ R₂ : StatisticalRelation (PackedFiniteInferenceBase.{u, v} Theta),
      equivalenceClosure
          (relationUnion (equivalenceClosure R₁) (equivalenceClosure R₂)) =
        equivalenceClosure (relationUnion R₁ R₂)) ∧
    Equivalence L ∧
    (∀ I : PackedFiniteInferenceBase.{u, v} Theta,
      letI : Fintype I.Sample := I.sampleFintype
      letI : Nonempty I.Sample := I.sampleNonempty
      FiniteMinimalSufficient I.model (canonicalMinimalSufficient I.likelihoodFamily)) ∧
    (Equivalence S ∧ S ≤ L) ∧
    (Reflexive C ∧ Symmetric C ∧ ¬ Transitive C ∧ C ≤ L) ∧
    (C < equivalenceClosure C ∧ equivalenceClosure C = L) ∧
    (relationUnion C S ≤ L ∧ L ≤ equivalenceClosure (relationUnion C S)) ∧
    (relationUnion C S < L ∧ equivalenceClosure (relationUnion C S) = L) ∧
    (relationUnion C S < equivalenceClosure C ∧ equivalenceClosure C = L ∧
      S < equivalenceClosure C) := by
  exact ⟨evans2013_lemma1, evans2013_lemma2, evans2013_lemma3_packed,
    evans2013_lemma4_packed, evans2013_lemma5_packed, evans2013_lemma6_packed,
    evans2013_theorem7_packed, evans2013_theorem8_packed,
    evans2013_theorem9_packed, evans2013_corollary10_packed⟩

end PaperSignature
end Certification
end VennDiagrams
