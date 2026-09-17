import VennDiagrams.S01_Relations
import Mathlib.Tactic

/-!
# S02 — Exact certification of the finite examples

This module checks, over `ℚ`, every numerical table used in the manuscript's
finite examples.  All displayed decimal probabilities are represented by the
corresponding exact fractions.  In particular, marginals, conditional laws,
induced laws, MLE laws, likelihood-ratio regions, and p-values are computed
from the probability mass functions below.
-/

open scoped BigOperators

namespace VennDiagrams
namespace FiniteExamples

/-! ## Common finite-probability definitions -/

/-- The two parameter values denoted `1` and `2` in the manuscript. -/
inductive Parameter where
  | one
  | two
  deriving DecidableEq, Fintype, Repr

/-- A two-valued observable.  The constructors represent `0` and `1`. -/
inductive BitValue where
  | b0
  | b1
  deriving DecidableEq, Fintype, Repr

/-- The mass induced by a statistic on a finite sample space. -/
def inducedMass {X A : Type*} [Fintype X] [DecidableEq A]
    (p : X → ℚ) (T : X → A) (a : A) : ℚ :=
  ∑ x, if T x = a then p x else 0

/-- For the two-point parameter space, the manuscript's MLE condition. -/
def IsMLE {X : Type*} (p : Parameter → X → ℚ) (x : X)
    (theta : Parameter) : Prop :=
  p .one x ≤ p theta x ∧ p .two x ≤ p theta x

/-- Equality of the cross-products of two two-coordinate likelihood vectors.
For the strictly positive examples below this is exactly proportionality by a
positive constant. -/
def likelihoodProportional {X : Type*} (p : Parameter → X → ℚ)
    (x y : X) : Prop :=
  p .one x * p .two y = p .two x * p .one y

/-- Cross-experiment form of likelihood proportionality. -/
def crossLikelihoodProportional {X Y : Type*}
    (p : Parameter → X → ℚ) (q : Parameter → Y → ℚ)
    (x : X) (y : Y) : Prop :=
  p .one x * q .two y = p .two x * q .one y

/-- The paper's literal positive-scaling definition of proportional
likelihoods, allowing the two likelihoods to come from different models. -/
def PositivelyProportional {X Y : Type*}
    (p : Parameter → X → ℚ) (q : Parameter → Y → ℚ)
    (x : X) (y : Y) : Prop :=
  ∃ k : ℚ, 0 < k ∧ ∀ theta, p theta x = k * q theta y

/-- On positive likelihoods the cross-product test is equivalent to the
paper's existence of a positive proportionality constant. -/
theorem crossLikelihoodProportional_iff_positiveScale {X Y : Type*}
    (p : Parameter → X → ℚ) (q : Parameter → Y → ℚ) (x : X) (y : Y)
    (hp : 0 < p .one x) (hq : 0 < q .one y) :
    crossLikelihoodProportional p q x y ↔ PositivelyProportional p q x y := by
  constructor
  · intro h
    refine ⟨p .one x / q .one y, div_pos hp hq, ?_⟩
    intro theta
    cases theta
    · field_simp
    · dsimp [crossLikelihoodProportional] at h
      field_simp
      exact h.symm
  · rintro ⟨k, _hk, h⟩
    dsimp [crossLikelihoodProportional]
    rw [h .one, h .two]
    ring

/-- A finite statistic is ancillary when its induced mass is parameter-free. -/
def IsAncillary {X A : Type*} [Fintype X] [DecidableEq A]
    (p : Parameter → X → ℚ) (T : X → A) : Prop :=
  ∀ a, inducedMass (p .one) T a = inducedMass (p .two) T a

/-! ## The experiments E0, E1, E2, and ET -/

/-- The four outcomes `(0,0)`, `(0,1)`, `(1,0)`, and `(1,1)` of `E0`. -/
inductive E0Outcome where
  | x00
  | x01
  | x10
  | x11
  deriving DecidableEq, Fintype, Repr

@[simp] theorem sum_E0Outcome {R : Type*} [AddCommMonoid R]
    (f : E0Outcome → R) :
    (∑ x, f x) = f .x00 + f .x01 + f .x10 + f .x11 := by
  rw [show (Finset.univ : Finset E0Outcome) = {.x00, .x01, .x10, .x11} by decide]
  simp [add_assoc]

/-- The exact joint probability table for `E0`. -/
def e0 : Parameter → E0Outcome → ℚ
  | .one, .x00 => 1 / 10
  | .one, .x01 => 2 / 5
  | .one, .x10 => 2 / 5
  | .one, .x11 => 1 / 10
  | .two, .x00 => 3 / 10
  | .two, .x01 => 1 / 5
  | .two, .x10 => 1 / 5
  | .two, .x11 => 3 / 10

/-- The first coordinate `U=X1`. -/
def firstCoordinate : E0Outcome → BitValue
  | .x00 | .x01 => .b0
  | .x10 | .x11 => .b1

/-- The second coordinate `V=X2`. -/
def secondCoordinate : E0Outcome → BitValue
  | .x00 | .x10 => .b0
  | .x01 | .x11 => .b1

/-- The marginal model `E1`. -/
def e1 (theta : Parameter) (x : BitValue) : ℚ :=
  inducedMass (e0 theta) firstCoordinate x

/-- The marginal model `E2`. -/
def e2 (theta : Parameter) (x : BitValue) : ℚ :=
  inducedMass (e0 theta) secondCoordinate x

/-- The three possible values of `T=X1+X2`. -/
inductive TOutcome where
  | t0
  | t1
  | t2
  deriving DecidableEq, Fintype, Repr

@[simp] theorem sum_TOutcome {R : Type*} [AddCommMonoid R]
    (f : TOutcome → R) :
    (∑ t, f t) = f .t0 + f .t1 + f .t2 := by
  rw [show (Finset.univ : Finset TOutcome) = {.t0, .t1, .t2} by decide]
  simp [add_assoc]

/-- The statistic `T=X1+X2`. -/
def totalStatistic : E0Outcome → TOutcome
  | .x00 => .t0
  | .x01 | .x10 => .t1
  | .x11 => .t2

/-- The model `ET` induced from `E0` by `T`. -/
def eT (theta : Parameter) (t : TOutcome) : ℚ :=
  inducedMass (e0 theta) totalStatistic t

/-- The statistic `M=1_{T=1}` on `E0`. -/
def mStatistic : E0Outcome → BitValue
  | .x00 | .x11 => .b0
  | .x01 | .x10 => .b1

/-- The corresponding statistic `MT=1_{t=1}` on `ET`. -/
def mTStatistic : TOutcome → BitValue
  | .t0 | .t2 => .b0
  | .t1 => .b1

/-- The model induced by `M` from `E0`. -/
def eM (theta : Parameter) (m : BitValue) : ℚ :=
  inducedMass (e0 theta) mStatistic m

/-- The model induced by `MT` from `ET`. -/
def eMT (theta : Parameter) (m : BitValue) : ℚ :=
  inducedMass (eT theta) mTStatistic m

theorem e0_probability_table :
    e0 .one .x00 = 1 / 10 ∧ e0 .two .x00 = 3 / 10 ∧
    e0 .one .x01 = 2 / 5 ∧ e0 .two .x01 = 1 / 5 ∧
    e0 .one .x10 = 2 / 5 ∧ e0 .two .x10 = 1 / 5 ∧
    e0 .one .x11 = 1 / 10 ∧ e0 .two .x11 = 3 / 10 := by
  norm_num [e0]

theorem e0_normalized (theta : Parameter) : ∑ x, e0 theta x = 1 := by
  cases theta <;> norm_num [e0]

theorem e0_strictly_positive (theta : Parameter) (x : E0Outcome) :
    0 < e0 theta x := by
  cases theta <;> cases x <;> norm_num [e0]

theorem e1_probability_table :
    e1 .one .b0 = 1 / 2 ∧ e1 .two .b0 = 1 / 2 ∧
    e1 .one .b1 = 1 / 2 ∧ e1 .two .b1 = 1 / 2 := by
  (simp [e1, inducedMass, firstCoordinate, e0]; norm_num)

theorem e2_probability_table :
    e2 .one .b0 = 1 / 2 ∧ e2 .two .b0 = 1 / 2 ∧
    e2 .one .b1 = 1 / 2 ∧ e2 .two .b1 = 1 / 2 := by
  (simp [e2, inducedMass, secondCoordinate, e0]; norm_num)

theorem e1_e2_uniform (theta : Parameter) (x : BitValue) :
    e1 theta x = 1 / 2 ∧ e2 theta x = 1 / 2 := by
  cases theta <;> cases x <;>
    simp [e1, e2, inducedMass, firstCoordinate, secondCoordinate, e0] <;> norm_num

theorem marginal_models_normalized (theta : Parameter) :
    e1 theta .b0 + e1 theta .b1 = 1 ∧
      e2 theta .b0 + e2 theta .b1 = 1 := by
  cases theta <;>
    simp [e1, e2, inducedMass, firstCoordinate, secondCoordinate, e0] <;> norm_num

theorem eT_probability_table :
    eT .one .t0 = 1 / 10 ∧ eT .two .t0 = 3 / 10 ∧
    eT .one .t1 = 4 / 5 ∧ eT .two .t1 = 2 / 5 ∧
    eT .one .t2 = 1 / 10 ∧ eT .two .t2 = 3 / 10 := by
  (simp [eT, inducedMass, totalStatistic, e0]; norm_num)

theorem eT_normalized (theta : Parameter) : ∑ t, eT theta t = 1 := by
  cases theta <;> simp [eT, inducedMass, totalStatistic, e0] <;> norm_num

theorem induced_m_models_table :
    eM .one .b0 = 1 / 5 ∧ eM .two .b0 = 3 / 5 ∧
    eM .one .b1 = 4 / 5 ∧ eM .two .b1 = 2 / 5 ∧
    eMT .one .b0 = 1 / 5 ∧ eMT .two .b0 = 3 / 5 ∧
    eMT .one .b1 = 4 / 5 ∧ eMT .two .b1 = 2 / 5 := by
  (simp [eM, eMT, eT, inducedMass, mStatistic, mTStatistic,
    totalStatistic, e0]; norm_num)

theorem induced_m_models_coincide (theta : Parameter) (m : BitValue) :
    eM theta m = eMT theta m := by
  cases theta <;> cases m <;>
    simp [eM, eMT, eT, inducedMass, mStatistic, mTStatistic,
      totalStatistic, e0]

theorem induced_m_models_normalized (theta : Parameter) :
    eM theta .b0 + eM theta .b1 = 1 ∧
      eMT theta .b0 + eMT theta .b1 = 1 := by
  cases theta <;>
    simp [eM, eMT, eT, inducedMass, mStatistic, mTStatistic,
      totalStatistic, e0] <;> norm_num

theorem mStatistic_minimal_sufficient_criterion (x y : E0Outcome) :
    mStatistic x = mStatistic y ↔ likelihoodProportional e0 x y := by
  cases x <;> cases y <;>
    simp [mStatistic, likelihoodProportional, e0] <;> norm_num

theorem mTStatistic_minimal_sufficient_criterion (x y : TOutcome) :
    mTStatistic x = mTStatistic y ↔ likelihoodProportional eT x y := by
  cases x <;> cases y <;>
    simp [mTStatistic, likelihoodProportional, eT, inducedMass,
      totalStatistic, e0] <;> norm_num

/-- The unique MLE in `E0`. -/
def e0MLE : E0Outcome → Parameter
  | .x00 | .x11 => .two
  | .x01 | .x10 => .one

/-- The unique MLE in `ET`. -/
def eTMLE : TOutcome → Parameter
  | .t0 | .t2 => .two
  | .t1 => .one

theorem e0_mle_characterization (x : E0Outcome) (theta : Parameter) :
    IsMLE e0 x theta ↔ theta = e0MLE x := by
  cases x <;> cases theta <;> simp [IsMLE, e0, e0MLE] <;> norm_num

theorem eT_mle_characterization (t : TOutcome) (theta : Parameter) :
    IsMLE eT t theta ↔ theta = eTMLE t := by
  cases t <;> cases theta <;>
    simp [IsMLE, eT, inducedMass, totalStatistic, e0, eTMLE] <;> norm_num

/-- Both parameter values maximize the flat marginal likelihoods. -/
theorem e1_all_parameters_are_mles (x : BitValue) (theta : Parameter) :
    IsMLE e1 x theta := by
  cases x <;> cases theta <;>
    simp [IsMLE, e1, inducedMass, firstCoordinate, e0] <;> norm_num

/-- Both parameter values maximize the flat marginal likelihoods. -/
theorem e2_all_parameters_are_mles (x : BitValue) (theta : Parameter) :
    IsMLE e2 x theta := by
  cases x <;> cases theta <;>
    simp [IsMLE, e2, inducedMass, secondCoordinate, e0] <;> norm_num

theorem displayed_e0_and_eT_mle_values :
    e0MLE .x00 = .two ∧ e0MLE .x01 = .one ∧
    e0MLE .x10 = .one ∧ e0MLE .x11 = .two ∧
    eTMLE .t0 = .two ∧ eTMLE .t1 = .one ∧ eTMLE .t2 = .two := by
  decide

theorem e0_mle_induced_table :
    inducedMass (e0 .one) e0MLE .one = 4 / 5 ∧
    inducedMass (e0 .two) e0MLE .one = 2 / 5 ∧
    inducedMass (e0 .one) e0MLE .two = 1 / 5 ∧
    inducedMass (e0 .two) e0MLE .two = 3 / 5 := by
  (simp [inducedMass, e0MLE, e0]; norm_num)

theorem eT_mle_induced_table :
    inducedMass (eT .one) eTMLE .one = 4 / 5 ∧
    inducedMass (eT .two) eTMLE .one = 2 / 5 ∧
    inducedMass (eT .one) eTMLE .two = 1 / 5 ∧
    inducedMass (eT .two) eTMLE .two = 3 / 5 := by
  (simp [inducedMass, eTMLE, eT, totalStatistic, e0]; norm_num)

theorem e0_eT_mle_laws_coincide (theta eta : Parameter) :
    inducedMass (e0 theta) e0MLE eta = inducedMass (eT theta) eTMLE eta := by
  cases theta <;> cases eta <;>
    simp [inducedMass, e0MLE, eTMLE, eT, totalStatistic, e0]

/-! ## Ancillarity and the conditional E0 tables -/

/-- `E0` conditioned on `U=0`, with zero mass off the conditional support. -/
def e0GivenU0 (theta : Parameter) (x : E0Outcome) : ℚ :=
  if firstCoordinate x = .b0 then e0 theta x / e1 theta .b0 else 0

/-- `E0` conditioned on `V=0`, with zero mass off the conditional support. -/
def e0GivenV0 (theta : Parameter) (x : E0Outcome) : ℚ :=
  if secondCoordinate x = .b0 then e0 theta x / e2 theta .b0 else 0

/-- `E0` conditioned on `V=1`, with zero mass off the conditional support. -/
def e0GivenV1 (theta : Parameter) (x : E0Outcome) : ℚ :=
  if secondCoordinate x = .b1 then e0 theta x / e2 theta .b1 else 0

theorem firstCoordinate_ancillary : IsAncillary e0 firstCoordinate := by
  intro x
  cases x <;> simp [inducedMass, firstCoordinate, e0] <;> norm_num

theorem secondCoordinate_ancillary : IsAncillary e0 secondCoordinate := by
  intro x
  cases x <;> simp [inducedMass, secondCoordinate, e0] <;> norm_num

theorem coordinate_masses_are_half (theta : Parameter) (x : BitValue) :
    inducedMass (e0 theta) firstCoordinate x = 1 / 2 ∧
    inducedMass (e0 theta) secondCoordinate x = 1 / 2 := by
  cases theta <;> cases x <;>
    simp [inducedMass, firstCoordinate, secondCoordinate, e0] <;> norm_num

theorem conditional_v_table :
    e0GivenV0 .one .x00 = 1 / 5 ∧ e0GivenV0 .two .x00 = 3 / 5 ∧
    e0GivenV0 .one .x01 = 0 ∧ e0GivenV0 .two .x01 = 0 ∧
    e0GivenV0 .one .x10 = 4 / 5 ∧ e0GivenV0 .two .x10 = 2 / 5 ∧
    e0GivenV0 .one .x11 = 0 ∧ e0GivenV0 .two .x11 = 0 ∧
    e0GivenV1 .one .x00 = 0 ∧ e0GivenV1 .two .x00 = 0 ∧
    e0GivenV1 .one .x01 = 4 / 5 ∧ e0GivenV1 .two .x01 = 2 / 5 ∧
    e0GivenV1 .one .x10 = 0 ∧ e0GivenV1 .two .x10 = 0 ∧
    e0GivenV1 .one .x11 = 1 / 5 ∧ e0GivenV1 .two .x11 = 3 / 5 := by
  (simp [e0GivenV0, e0GivenV1, e2, inducedMass,
    secondCoordinate, e0]; norm_num)

theorem conditional_u0_v0_table :
    e0GivenU0 .one .x00 = 1 / 5 ∧ e0GivenU0 .two .x00 = 3 / 5 ∧
    e0GivenU0 .one .x01 = 4 / 5 ∧ e0GivenU0 .two .x01 = 2 / 5 ∧
    e0GivenU0 .one .x10 = 0 ∧ e0GivenU0 .two .x10 = 0 ∧
    e0GivenU0 .one .x11 = 0 ∧ e0GivenU0 .two .x11 = 0 ∧
    e0GivenV0 .one .x00 = 1 / 5 ∧ e0GivenV0 .two .x00 = 3 / 5 ∧
    e0GivenV0 .one .x01 = 0 ∧ e0GivenV0 .two .x01 = 0 ∧
    e0GivenV0 .one .x10 = 4 / 5 ∧ e0GivenV0 .two .x10 = 2 / 5 ∧
    e0GivenV0 .one .x11 = 0 ∧ e0GivenV0 .two .x11 = 0 := by
  (simp [e0GivenU0, e0GivenV0, e1, e2, inducedMass,
    firstCoordinate, secondCoordinate, e0]; norm_num)

theorem conditional_models_normalized (theta : Parameter) :
    (∑ x, e0GivenU0 theta x) = 1 ∧
    (∑ x, e0GivenV0 theta x) = 1 ∧
    (∑ x, e0GivenV1 theta x) = 1 := by
  cases theta <;>
    simp [e0GivenU0, e0GivenV0, e0GivenV1, e1, e2, inducedMass,
      firstCoordinate, secondCoordinate, e0] <;> norm_num

theorem conditional_u0_observed_mle :
    IsMLE e0GivenU0 .x00 .two ∧ IsMLE e0GivenU0 .x01 .one := by
  (simp [IsMLE, e0GivenU0, e1, inducedMass, firstCoordinate, e0]; norm_num)

theorem conditional_u0_mle_induced_table :
    inducedMass (e0GivenU0 .one) e0MLE .one = 4 / 5 ∧
    inducedMass (e0GivenU0 .two) e0MLE .one = 2 / 5 ∧
    inducedMass (e0GivenU0 .one) e0MLE .two = 1 / 5 ∧
    inducedMass (e0GivenU0 .two) e0MLE .two = 3 / 5 := by
  (simp [inducedMass, e0MLE, e0GivenU0, e1, firstCoordinate, e0]; norm_num)

theorem e0_conditional_u0_mle_laws_coincide (theta eta : Parameter) :
    inducedMass (e0 theta) e0MLE eta =
      inducedMass (e0GivenU0 theta) e0MLE eta := by
  cases theta <;> cases eta <;>
    simp [inducedMass, e0MLE, e0GivenU0, e1, firstCoordinate, e0] <;> norm_num

theorem conditional_u0_v0_observed_likelihoods_equal (theta : Parameter) :
    e0GivenU0 theta .x00 = e0GivenV0 theta .x00 := by
  cases theta <;>
    simp [e0GivenU0, e0GivenV0, e1, e2, inducedMass,
      firstCoordinate, secondCoordinate, e0]

/-- Conditioning a finite family on one fiber of a statistic.  The positivity
side condition needed for a statistical conditional law is kept in
`DirectConditioning` below. -/
def conditionedModel {X A : Type*} [Fintype X] [DecidableEq A]
    (p : Parameter → X → ℚ) (T : X → A) (a : A) :
    Parameter → X → ℚ :=
  fun theta x =>
    if T x = a then p theta x / inducedMass (p theta) T a else 0

/-- Every ancillary statistic on the effective two-point support of
`E0 | U=0` is constant.  The codomain is arbitrary (and need not itself be
enumerated); values off the effective support are immaterial. -/
theorem ancillary_e0GivenU0_constant_on_effective_support
    {A : Type*} [DecidableEq A] (T : E0Outcome → A)
    (hT : IsAncillary e0GivenU0 T) : T .x00 = T .x01 := by
  by_contra hne
  have hne' : T .x01 ≠ T .x00 := Ne.symm hne
  have hmass := hT (T .x00)
  simp [inducedMass, e0GivenU0, e1, firstCoordinate, e0, hne'] at hmass
  norm_num at hmass

/-- Every ancillary statistic on the effective two-point support of
`E0 | V=0` is constant. -/
theorem ancillary_e0GivenV0_constant_on_effective_support
    {A : Type*} [DecidableEq A] (T : E0Outcome → A)
    (hT : IsAncillary e0GivenV0 T) : T .x00 = T .x10 := by
  by_contra hne
  have hne' : T .x10 ≠ T .x00 := Ne.symm hne
  have hmass := hT (T .x00)
  simp [inducedMass, e0GivenV0, e2, secondCoordinate, e0, hne'] at hmass
  norm_num at hmass

/-- Precise partition characterization of ancillarity for `E0 | U=0`. -/
theorem ancillary_e0GivenU0_iff_constant_on_effective_support
    {A : Type*} [DecidableEq A] (T : E0Outcome → A) :
    IsAncillary e0GivenU0 T ↔ T .x00 = T .x01 := by
  constructor
  · exact ancillary_e0GivenU0_constant_on_effective_support T
  · intro hsame a
    simp [inducedMass, e0GivenU0, e1, firstCoordinate, e0, hsame]
    by_cases ha : T .x01 = a
    · simp [ha]
      norm_num
    · simp [ha]

/-- Precise partition characterization of ancillarity for `E0 | V=0`. -/
theorem ancillary_e0GivenV0_iff_constant_on_effective_support
    {A : Type*} [DecidableEq A] (T : E0Outcome → A) :
    IsAncillary e0GivenV0 T ↔ T .x00 = T .x10 := by
  constructor
  · exact ancillary_e0GivenV0_constant_on_effective_support T
  · intro hsame a
    simp [inducedMass, e0GivenV0, e2, secondCoordinate, e0, hsame]
    by_cases ha : T .x10 = a
    · simp [ha]
      norm_num
    · simp [ha]

/-- A direct ordinary conditioning step, expressed using a binary indicator
of the conditioning event.  Every single conditioning event admits such an
indicator, so this is the relevant finite-partition formulation here. -/
def DirectConditioning {X : Type*} [Fintype X]
    (p q : Parameter → X → ℚ) : Prop :=
  ∃ T : X → BitValue, IsAncillary p T ∧
    ∃ a : BitValue, (∀ theta, 0 < inducedMass (p theta) T a) ∧
      ∀ theta x, q theta x = conditionedModel p T a theta x

theorem joint_directly_conditions_to_u0 : DirectConditioning e0 e0GivenU0 := by
  refine ⟨firstCoordinate, firstCoordinate_ancillary, .b0, ?_, ?_⟩
  · intro theta
    rw [coordinate_masses_are_half theta .b0 |>.1]
    norm_num
  · intro theta x
    rfl

theorem joint_directly_conditions_to_v0 : DirectConditioning e0 e0GivenV0 := by
  refine ⟨secondCoordinate, secondCoordinate_ancillary, .b0, ?_, ?_⟩
  · intro theta
    rw [coordinate_masses_are_half theta .b0 |>.2]
    norm_num
  · intro theta x
    rfl

/-- Conditioning cannot create the point `x10`, which has zero mass in the
source `E0 | U=0` but positive mass in `E0 | V=0`. -/
theorem no_direct_conditioning_u0_to_v0 :
    ¬ DirectConditioning e0GivenU0 e0GivenV0 := by
  rintro ⟨T, _hAncillary, a, _hpositive, hmodel⟩
  have h := hmodel .one .x10
  simp [conditionedModel, inducedMass, e0GivenU0, e0GivenV0,
    e1, e2, firstCoordinate, secondCoordinate, e0] at h
  norm_num at h

/-- The reverse conditioning cannot create `x01`. -/
theorem no_direct_conditioning_v0_to_u0 :
    ¬ DirectConditioning e0GivenV0 e0GivenU0 := by
  rintro ⟨T, _hAncillary, a, _hpositive, hmodel⟩
  have h := hmodel .one .x01
  simp [conditionedModel, inducedMass, e0GivenU0, e0GivenV0,
    e1, e2, firstCoordinate, secondCoordinate, e0] at h
  norm_num at h

/-- The three model labels in the manuscript's non-transitivity chain.  All
three associated inference bases use the common observed point `x00`. -/
inductive ConditionalModelLabel where
  | givenU0
  | joint
  | givenV0
  deriving DecidableEq, Fintype, Repr

def conditionalFamily : ConditionalModelLabel → Parameter → E0Outcome → ℚ
  | .givenU0 => e0GivenU0
  | .joint => e0
  | .givenV0 => e0GivenV0

/-- Symmetric direct conditionality among the three concrete models. -/
def concreteConditionality : StatisticalRelation ConditionalModelLabel :=
  fun i j => DirectConditioning (conditionalFamily i) (conditionalFamily j) ∨
    DirectConditioning (conditionalFamily j) (conditionalFamily i)

theorem conditionality_nontransitivity_witness :
    concreteConditionality .givenU0 .joint ∧
    concreteConditionality .joint .givenV0 ∧
    ¬ concreteConditionality .givenU0 .givenV0 := by
  constructor
  · exact Or.inr joint_directly_conditions_to_u0
  constructor
  · exact Or.inl joint_directly_conditions_to_v0
  · intro h
    rcases h with h | h
    · exact no_direct_conditioning_u0_to_v0 h
    · exact no_direct_conditioning_v0_to_u0 h

theorem concreteConditionality_not_transitive :
    ¬ (∀ ⦃i j k⦄, concreteConditionality i j →
      concreteConditionality j k → concreteConditionality i k) := by
  intro htrans
  exact conditionality_nontransitivity_witness.2.2
    (htrans conditionality_nontransitivity_witness.1
      conditionality_nontransitivity_witness.2.1)

/-! ## The hierarchical experiments E3, E4, and EStar -/

inductive E3Outcome where
  | d1
  | d2
  | d3
  deriving DecidableEq, Fintype, Repr

@[simp] theorem sum_E3Outcome {R : Type*} [AddCommMonoid R]
    (f : E3Outcome → R) :
    (∑ x, f x) = f .d1 + f .d2 + f .d3 := by
  rw [show (Finset.univ : Finset E3Outcome) = {.d1, .d2, .d3} by decide]
  simp [add_assoc]

inductive E4Outcome where
  | c0
  | c1
  deriving DecidableEq, Fintype, Repr

@[simp] theorem sum_E4Outcome {R : Type*} [AddCommMonoid R]
    (f : E4Outcome → R) :
    (∑ x, f x) = f .c0 + f .c1 := by
  rw [show (Finset.univ : Finset E4Outcome) = {.c0, .c1} by decide]
  simp

inductive EStarOutcome where
  | s01
  | s02
  | s03
  | s10
  | s11
  deriving DecidableEq, Fintype, Repr

@[simp] theorem sum_EStarOutcome {R : Type*} [AddCommMonoid R]
    (f : EStarOutcome → R) :
    (∑ x, f x) = f .s01 + f .s02 + f .s03 + f .s10 + f .s11 := by
  rw [show (Finset.univ : Finset EStarOutcome) =
    {.s01, .s02, .s03, .s10, .s11} by decide]
  simp [add_assoc]

def e3 : Parameter → E3Outcome → ℚ
  | .one, .d1 => 1 / 3
  | .one, .d2 => 1 / 3
  | .one, .d3 => 1 / 3
  | .two, .d1 => 5 / 12
  | .two, .d2 => 2 / 12
  | .two, .d3 => 5 / 12

def e4 : Parameter → E4Outcome → ℚ
  | .one, .c0 => 1 / 2
  | .one, .c1 => 1 / 2
  | .two, .c0 => 7 / 10
  | .two, .c1 => 3 / 10

/-- The fair-selector mixture `EStar`. -/
def eStar : Parameter → EStarOutcome → ℚ
  | theta, .s01 => (1 / 2) * e3 theta .d1
  | theta, .s02 => (1 / 2) * e3 theta .d2
  | theta, .s03 => (1 / 2) * e3 theta .d3
  | theta, .s10 => (1 / 2) * e4 theta .c0
  | theta, .s11 => (1 / 2) * e4 theta .c1

def selector : EStarOutcome → BitValue
  | .s01 | .s02 | .s03 => .b0
  | .s10 | .s11 => .b1

def embedE3 : E3Outcome → EStarOutcome
  | .d1 => .s01
  | .d2 => .s02
  | .d3 => .s03

def embedE4 : E4Outcome → EStarOutcome
  | .c0 => .s10
  | .c1 => .s11

theorem e3_probability_table :
    e3 .one .d1 = 1 / 3 ∧ e3 .two .d1 = 5 / 12 ∧
    e3 .one .d2 = 1 / 3 ∧ e3 .two .d2 = 2 / 12 ∧
    e3 .one .d3 = 1 / 3 ∧ e3 .two .d3 = 5 / 12 := by
  norm_num [e3]

theorem e4_probability_table :
    e4 .one .c0 = 1 / 2 ∧ e4 .two .c0 = 7 / 10 ∧
    e4 .one .c1 = 1 / 2 ∧ e4 .two .c1 = 3 / 10 := by
  norm_num [e4]

theorem eStar_probability_table :
    eStar .one .s01 = 1 / 6 ∧ eStar .two .s01 = 5 / 24 ∧
    eStar .one .s02 = 1 / 6 ∧ eStar .two .s02 = 1 / 12 ∧
    eStar .one .s03 = 1 / 6 ∧ eStar .two .s03 = 5 / 24 ∧
    eStar .one .s10 = 1 / 4 ∧ eStar .two .s10 = 7 / 20 ∧
    eStar .one .s11 = 1 / 4 ∧ eStar .two .s11 = 3 / 20 := by
  norm_num [eStar, e3, e4]

theorem hierarchical_models_normalized (theta : Parameter) :
    (∑ x, e3 theta x) = 1 ∧ (∑ x, e4 theta x) = 1 ∧
      (∑ x, eStar theta x) = 1 := by
  cases theta <;> simp [e3, e4, eStar] <;> norm_num

theorem hierarchical_models_strictly_positive :
    (∀ theta x, 0 < e3 theta x) ∧ (∀ theta x, 0 < e4 theta x) ∧
      (∀ theta x, 0 < eStar theta x) := by
  constructor
  · intro theta x
    cases theta <;> cases x <;> norm_num [e3]
  constructor
  · intro theta x
    cases theta <;> cases x <;> norm_num [e4]
  · intro theta x
    cases theta <;> cases x <;> norm_num [eStar, e3, e4]

theorem selector_mass_table (theta : Parameter) (u : BitValue) :
    inducedMass (eStar theta) selector u = 1 / 2 := by
  cases theta <;> cases u <;>
    simp [inducedMass, selector, eStar, e3, e4] <;> norm_num

theorem selector_ancillary : IsAncillary eStar selector := by
  intro u
  rw [selector_mass_table .one u, selector_mass_table .two u]

/-- Conditioning the mixture on selector value zero recovers `E3`. -/
theorem condition_on_selector_zero_is_e3 (theta : Parameter) (x : E3Outcome) :
    eStar theta (embedE3 x) / inducedMass (eStar theta) selector .b0 = e3 theta x := by
  cases theta <;> cases x <;>
    simp [eStar, embedE3, inducedMass, selector, e3, e4] <;> norm_num

/-- Conditioning the mixture on selector value one recovers `E4`. -/
theorem condition_on_selector_one_is_e4 (theta : Parameter) (x : E4Outcome) :
    eStar theta (embedE4 x) / inducedMass (eStar theta) selector .b1 = e4 theta x := by
  cases theta <;> cases x <;>
    simp [eStar, embedE4, inducedMass, selector, e3, e4] <;> norm_num

def e3MLE : E3Outcome → Parameter
  | .d1 | .d3 => .two
  | .d2 => .one

def e4MLE : E4Outcome → Parameter
  | .c0 => .two
  | .c1 => .one

def eStarMLE : EStarOutcome → Parameter
  | .s01 | .s03 | .s10 => .two
  | .s02 | .s11 => .one

theorem e3_mle_characterization (x : E3Outcome) (theta : Parameter) :
    IsMLE e3 x theta ↔ theta = e3MLE x := by
  cases x <;> cases theta <;> simp [IsMLE, e3, e3MLE] <;> norm_num

theorem e4_mle_characterization (x : E4Outcome) (theta : Parameter) :
    IsMLE e4 x theta ↔ theta = e4MLE x := by
  cases x <;> cases theta <;> simp [IsMLE, e4, e4MLE] <;> norm_num

theorem eStar_mle_characterization (x : EStarOutcome) (theta : Parameter) :
    IsMLE eStar x theta ↔ theta = eStarMLE x := by
  cases x <;> cases theta <;>
    simp [IsMLE, eStar, e3, e4, eStarMLE] <;> norm_num

theorem hierarchical_observed_mles :
    eStarMLE .s01 = .two ∧ e3MLE .d1 = .two := by
  decide

theorem e3_mle_induced_table :
    inducedMass (e3 .one) e3MLE .one = 1 / 3 ∧
    inducedMass (e3 .two) e3MLE .one = 2 / 12 ∧
    inducedMass (e3 .one) e3MLE .two = 2 / 3 ∧
    inducedMass (e3 .two) e3MLE .two = 10 / 12 := by
  (simp [inducedMass, e3MLE, e3]; norm_num)

theorem e4_mle_induced_table :
    inducedMass (e4 .one) e4MLE .one = 1 / 2 ∧
    inducedMass (e4 .two) e4MLE .one = 3 / 10 ∧
    inducedMass (e4 .one) e4MLE .two = 1 / 2 ∧
    inducedMass (e4 .two) e4MLE .two = 7 / 10 := by
  simp [inducedMass, e4MLE, e4]

theorem eStar_mle_induced_table :
    inducedMass (eStar .one) eStarMLE .one = 10 / 24 ∧
    inducedMass (eStar .two) eStarMLE .one = 7 / 30 ∧
    inducedMass (eStar .one) eStarMLE .two = 14 / 24 ∧
    inducedMass (eStar .two) eStarMLE .two = 23 / 30 := by
  (simp [inducedMass, eStarMLE, eStar, e3, e4]; norm_num)

theorem hierarchical_mle_laws_differ :
    inducedMass (eStar .one) eStarMLE .one ≠
      inducedMass (e3 .one) e3MLE .one := by
  (simp [inducedMass, eStarMLE, e3MLE, eStar, e3, e4]; norm_num)

/-! ## Likelihood-proportionality partitions for pA and pB -/

inductive E0MinimalClass where
  | diagonal
  | offDiagonal
  deriving DecidableEq, Fintype, Repr

def e0MinimalClass : E0Outcome → E0MinimalClass
  | .x00 | .x11 => .diagonal
  | .x01 | .x10 => .offDiagonal

theorem e0_proportional_iff_same_minimal_class (x y : E0Outcome) :
    likelihoodProportional e0 x y ↔ e0MinimalClass x = e0MinimalClass y := by
  cases x <;> cases y <;>
    norm_num [likelihoodProportional, e0MinimalClass, e0] <;> decide

theorem e0_positive_scale_iff_same_minimal_class (x y : E0Outcome) :
    PositivelyProportional e0 e0 x y ↔ e0MinimalClass x = e0MinimalClass y := by
  rw [← crossLikelihoodProportional_iff_positiveScale e0 e0 x y
    (e0_strictly_positive .one x) (e0_strictly_positive .one y)]
  exact e0_proportional_iff_same_minimal_class x y

theorem pA_likelihoods_proportional : likelihoodProportional e0 .x00 .x11 := by
  norm_num [likelihoodProportional, e0]

theorem pA_statistic_values_equal : mStatistic .x00 = mStatistic .x11 := by
  rfl

theorem e0_minimal_partition_has_two_classes :
    (Finset.univ.image e0MinimalClass).card = 2 := by
  decide

theorem e0_minimal_partition_fibers :
    (Finset.univ.filter fun x => e0MinimalClass x = .diagonal) = {.x00, .x11} ∧
    (Finset.univ.filter fun x => e0MinimalClass x = .offDiagonal) = {.x01, .x10} := by
  decide

inductive E3MinimalClass where
  | outer
  | middle
  deriving DecidableEq, Fintype, Repr

def e3MinimalClass : E3Outcome → E3MinimalClass
  | .d1 | .d3 => .outer
  | .d2 => .middle

inductive EStarMinimalClass where
  | dieOuter
  | dieMiddle
  | coinZero
  | coinOne
  deriving DecidableEq, Fintype, Repr

def eStarMinimalClass : EStarOutcome → EStarMinimalClass
  | .s01 | .s03 => .dieOuter
  | .s02 => .dieMiddle
  | .s10 => .coinZero
  | .s11 => .coinOne

theorem e3_proportional_iff_same_minimal_class (x y : E3Outcome) :
    likelihoodProportional e3 x y ↔ e3MinimalClass x = e3MinimalClass y := by
  cases x <;> cases y <;>
    norm_num [likelihoodProportional, e3MinimalClass, e3] <;> decide

theorem eStar_proportional_iff_same_minimal_class (x y : EStarOutcome) :
    likelihoodProportional eStar x y ↔ eStarMinimalClass x = eStarMinimalClass y := by
  cases x <;> cases y <;>
    norm_num [likelihoodProportional, eStarMinimalClass, eStar, e3, e4] <;> decide

theorem e3_positive_scale_iff_same_minimal_class (x y : E3Outcome) :
    PositivelyProportional e3 e3 x y ↔ e3MinimalClass x = e3MinimalClass y := by
  rw [← crossLikelihoodProportional_iff_positiveScale e3 e3 x y
    (hierarchical_models_strictly_positive.1 .one x)
    (hierarchical_models_strictly_positive.1 .one y)]
  exact e3_proportional_iff_same_minimal_class x y

theorem eStar_positive_scale_iff_same_minimal_class (x y : EStarOutcome) :
    PositivelyProportional eStar eStar x y ↔
      eStarMinimalClass x = eStarMinimalClass y := by
  rw [← crossLikelihoodProportional_iff_positiveScale eStar eStar x y
    (hierarchical_models_strictly_positive.2.2 .one x)
    (hierarchical_models_strictly_positive.2.2 .one y)]
  exact eStar_proportional_iff_same_minimal_class x y

theorem e3_minimal_partition_has_two_classes :
    (Finset.univ.image e3MinimalClass).card = 2 := by
  decide

theorem eStar_minimal_partition_has_four_classes :
    (Finset.univ.image eStarMinimalClass).card = 4 := by
  decide

theorem e3_minimal_partition_fibers :
    (Finset.univ.filter fun x => e3MinimalClass x = .outer) = {.d1, .d3} ∧
    (Finset.univ.filter fun x => e3MinimalClass x = .middle) = {.d2} := by
  decide

theorem eStar_minimal_partition_fibers :
    (Finset.univ.filter fun x => eStarMinimalClass x = .dieOuter) = {.s01, .s03} ∧
    (Finset.univ.filter fun x => eStarMinimalClass x = .dieMiddle) = {.s02} ∧
    (Finset.univ.filter fun x => eStarMinimalClass x = .coinZero) = {.s10} ∧
    (Finset.univ.filter fun x => eStarMinimalClass x = .coinOne) = {.s11} := by
  decide

theorem pB_likelihoods_proportional :
    crossLikelihoodProportional eStar e3 .s01 .d1 := by
  norm_num [crossLikelihoodProportional, eStar, e3]

theorem pB_exact_half_scaling (theta : Parameter) :
    eStar theta .s01 = (1 / 2) * e3 theta .d1 := by
  rfl

theorem pB_positive_proportionality :
    PositivelyProportional eStar e3 .s01 .d1 := by
  exact (crossLikelihoodProportional_iff_positiveScale eStar e3 .s01 .d1
    (hierarchical_models_strictly_positive.2.2 .one .s01)
    (hierarchical_models_strictly_positive.1 .one .d1)).1
    pB_likelihoods_proportional

theorem pB_minimal_partition_counts_differ :
    Fintype.card EStarMinimalClass = 4 ∧ Fintype.card E3MinimalClass = 2 := by
  decide

theorem no_bijection_between_pB_minimal_partitions :
    ¬ Nonempty (EStarMinimalClass ≃ E3MinimalClass) := by
  rintro ⟨h⟩
  have hcard := Fintype.card_congr h
  have hStar : Fintype.card EStarMinimalClass = 4 := by decide
  have hThree : Fintype.card E3MinimalClass = 2 := by decide
  omega

/-! ## The E5/E6 likelihood-ratio p-value example -/

inductive E5Outcome where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

@[simp] theorem sum_E5Outcome {R : Type*} [AddCommMonoid R]
    (f : E5Outcome → R) :
    (∑ z, f z) = f .x + f .y := by
  rw [show (Finset.univ : Finset E5Outcome) = {.x, .y} by decide]
  simp

inductive E6Outcome where
  | u
  | v
  deriving DecidableEq, Fintype, Repr

@[simp] theorem sum_E6Outcome {R : Type*} [AddCommMonoid R]
    (f : E6Outcome → R) :
    (∑ z, f z) = f .u + f .v := by
  rw [show (Finset.univ : Finset E6Outcome) = {.u, .v} by decide]
  simp

def e5 : Parameter → E5Outcome → ℚ
  | .one, .x => 1 / 10
  | .one, .y => 9 / 10
  | .two, .x => 1 / 5
  | .two, .y => 4 / 5

def e6 : Parameter → E6Outcome → ℚ
  | .one, .u => 1 / 5
  | .one, .v => 4 / 5
  | .two, .u => 2 / 5
  | .two, .v => 3 / 5

/-- LR for the singleton null `{theta1}` against `{theta2}` in `E5`. -/
def lr5 (z : E5Outcome) : ℚ := e5 .one z / e5 .two z

/-- LR for the singleton null `{theta1}` against `{theta2}` in `E6`. -/
def lr6 (z : E6Outcome) : ℚ := e6 .one z / e6 .two z

def lrRegion5 (z : E5Outcome) : Finset E5Outcome :=
  Finset.univ.filter fun w => lr5 w ≤ lr5 z

def lrRegion6 (z : E6Outcome) : Finset E6Outcome :=
  Finset.univ.filter fun w => lr6 w ≤ lr6 z

/-- The singleton-null LR p-value for `E5`. -/
def pValue5 (z : E5Outcome) : ℚ := ∑ w ∈ lrRegion5 z, e5 .one w

/-- The singleton-null LR p-value for `E6`. -/
def pValue6 (z : E6Outcome) : ℚ := ∑ w ∈ lrRegion6 z, e6 .one w

theorem e5_e6_probability_tables :
    e5 .one .x = 1 / 10 ∧ e5 .two .x = 1 / 5 ∧
    e5 .one .y = 9 / 10 ∧ e5 .two .y = 4 / 5 ∧
    e6 .one .u = 1 / 5 ∧ e6 .two .u = 2 / 5 ∧
    e6 .one .v = 4 / 5 ∧ e6 .two .v = 3 / 5 := by
  norm_num [e5, e6]

theorem e5_e6_normalized (theta : Parameter) :
    (∑ z, e5 theta z) = 1 ∧ (∑ z, e6 theta z) = 1 := by
  cases theta <;> norm_num [e5, e6]

theorem e5_e6_strictly_positive :
    (∀ theta z, 0 < e5 theta z) ∧ (∀ theta z, 0 < e6 theta z) := by
  constructor <;> intro theta z <;> cases theta <;> cases z <;> norm_num [e5, e6]

theorem observed_e6_likelihood_is_twice_e5 (theta : Parameter) :
    e6 theta .u = 2 * e5 theta .x := by
  cases theta <;> norm_num [e5, e6]

theorem observed_e5_e6_likelihoods_proportional :
    crossLikelihoodProportional e5 e6 .x .u := by
  norm_num [crossLikelihoodProportional, e5, e6]

theorem observed_e5_e6_positive_proportionality :
    PositivelyProportional e5 e6 .x .u := by
  exact (crossLikelihoodProportional_iff_positiveScale e5 e6 .x .u
    (e5_e6_strictly_positive.1 .one .x)
    (e5_e6_strictly_positive.2 .one .u)).1
    observed_e5_e6_likelihoods_proportional

theorem e5_likelihood_ratios : lr5 .x = 1 / 2 ∧ lr5 .y = 9 / 8 := by
  norm_num [lr5, e5]

theorem e6_likelihood_ratios : lr6 .u = 1 / 2 ∧ lr6 .v = 4 / 3 := by
  norm_num [lr6, e6]

theorem e5_lr_ordering : lr5 .x < lr5 .y := by
  norm_num [lr5, e5]

theorem e6_lr_ordering : lr6 .u < lr6 .v := by
  norm_num [lr6, e6]

theorem e5_observed_lr_region : lrRegion5 .x = {.x} := by
  ext z
  cases z <;> simp [lrRegion5, lr5, e5] <;> norm_num

theorem e6_observed_lr_region : lrRegion6 .u = {.u} := by
  ext z
  cases z <;> simp [lrRegion6, lr6, e6] <;> norm_num

theorem exact_lr_p_values :
    pValue5 .x = 1 / 10 ∧ pValue6 .u = 1 / 5 := by
  simp [pValue5, pValue6, e5_observed_lr_region, e6_observed_lr_region, e5, e6]

theorem proportional_likelihoods_but_different_p_values :
    crossLikelihoodProportional e5 e6 .x .u ∧ pValue5 .x ≠ pValue6 .u := by
  constructor
  · exact observed_e5_e6_likelihoods_proportional
  · rw [exact_lr_p_values.1, exact_lr_p_values.2]
    norm_num

/-! ## Heterogeneous inference bases and the paper's listed memberships -/

/-- A genuinely heterogeneous finite type containing every inference base in
the manuscript's `E0`, `E1`, `E2`, and `ET` examples. -/
inductive InitialInferenceBase where
  | atE0 (x : E0Outcome)
  | atE1 (x : BitValue)
  | atE2 (x : BitValue)
  | atET (x : TOutcome)
  deriving DecidableEq, Fintype, Repr

/-- The likelihood vector attached to a tagged initial inference base. -/
def initialLikelihood : Parameter → InitialInferenceBase → ℚ
  | theta, .atE0 x => e0 theta x
  | theta, .atE1 x => e1 theta x
  | theta, .atE2 x => e2 theta x
  | theta, .atET x => eT theta x

theorem initialLikelihood_strictly_positive
    (theta : Parameter) (i : InitialInferenceBase) :
    0 < initialLikelihood theta i := by
  cases theta <;> cases i with
  | atE0 x => cases x <;> norm_num [initialLikelihood, e0]
  | atE1 x => cases x <;>
      simp [initialLikelihood, e1, inducedMass, firstCoordinate, e0] <;> norm_num
  | atE2 x => cases x <;>
      simp [initialLikelihood, e2, inducedMass, secondCoordinate, e0] <;> norm_num
  | atET x => cases x <;>
      simp [initialLikelihood, eT, inducedMass, totalStatistic, e0] <;> norm_num

/-- The paper's likelihood relation restricted to the four initial models. -/
def initialLikelihoodRelation : StatisticalRelation InitialInferenceBase :=
  fun i j => PositivelyProportional initialLikelihood initialLikelihood i j

theorem initial_L_e0_x00_eT_t0 :
    initialLikelihoodRelation (.atE0 .x00) (.atET .t0) := by
  refine ⟨1, by norm_num, ?_⟩
  intro theta
  cases theta <;>
    simp [initialLikelihood, eT, inducedMass, totalStatistic, e0]

theorem initial_L_e0_x11_eT_t2 :
    initialLikelihoodRelation (.atE0 .x11) (.atET .t2) := by
  refine ⟨1, by norm_num, ?_⟩
  intro theta
  cases theta <;>
    simp [initialLikelihood, eT, inducedMass, totalStatistic, e0]

theorem initial_L_e1_b0_e2_b0 :
    initialLikelihoodRelation (.atE1 .b0) (.atE2 .b0) := by
  refine ⟨1, by norm_num, ?_⟩
  intro theta
  cases theta <;>
    simp [initialLikelihood, e1, e2, inducedMass,
      firstCoordinate, secondCoordinate, e0]

theorem initial_L_e1_b1_e2_b1 :
    initialLikelihoodRelation (.atE1 .b1) (.atE2 .b1) := by
  refine ⟨1, by norm_num, ?_⟩
  intro theta
  cases theta <;>
    simp [initialLikelihood, e1, e2, inducedMass,
      firstCoordinate, secondCoordinate, e0]

theorem initial_L_e1_b0_e2_b1 :
    initialLikelihoodRelation (.atE1 .b0) (.atE2 .b1) := by
  refine ⟨1, by norm_num, ?_⟩
  intro theta
  cases theta <;>
    (simp [initialLikelihood, e1, e2, inducedMass,
      firstCoordinate, secondCoordinate, e0]; norm_num)

theorem initial_L_e1_b1_e2_b0 :
    initialLikelihoodRelation (.atE1 .b1) (.atE2 .b0) := by
  refine ⟨1, by norm_num, ?_⟩
  intro theta
  cases theta <;>
    (simp [initialLikelihood, e1, e2, inducedMass,
      firstCoordinate, secondCoordinate, e0]; norm_num)

theorem six_listed_initial_L_memberships :
    initialLikelihoodRelation (.atE0 .x00) (.atET .t0) ∧
    initialLikelihoodRelation (.atE0 .x11) (.atET .t2) ∧
    initialLikelihoodRelation (.atE1 .b0) (.atE2 .b0) ∧
    initialLikelihoodRelation (.atE1 .b1) (.atE2 .b1) ∧
    initialLikelihoodRelation (.atE1 .b0) (.atE2 .b1) ∧
    initialLikelihoodRelation (.atE1 .b1) (.atE2 .b0) :=
  ⟨initial_L_e0_x00_eT_t0, initial_L_e0_x11_eT_t2,
    initial_L_e1_b0_e2_b0, initial_L_e1_b1_e2_b1,
    initial_L_e1_b0_e2_b1, initial_L_e1_b1_e2_b0⟩

/-- A proof-bearing common-code version of the sufficiency relation.  Each
code is certified by the likelihood-proportionality criterion, the observed
codes agree, and the two induced models on the common code space agree. -/
structure CommonMinimalCodeWitness {X Y : Type*} [Fintype X] [Fintype Y]
    (p : Parameter → X → ℚ) (q : Parameter → Y → ℚ) (x : X) (y : Y) where
  codeLeft : X → BitValue
  codeRight : Y → BitValue
  leftMinimal : ∀ a b,
    codeLeft a = codeLeft b ↔ likelihoodProportional p a b
  rightMinimal : ∀ a b,
    codeRight a = codeRight b ↔ likelihoodProportional q a b
  observedCode : codeLeft x = codeRight y
  inducedModelsEqual : ∀ theta code,
    inducedMass (p theta) codeLeft code = inducedMass (q theta) codeRight code

def CommonCodeSufficiency {X Y : Type*} [Fintype X] [Fintype Y]
    (p : Parameter → X → ℚ) (q : Parameter → Y → ℚ) (x : X) (y : Y) : Prop :=
  Nonempty (CommonMinimalCodeWitness p q x y)

theorem e0_e0_commonCodeSufficiency_of_m_eq {x y : E0Outcome}
    (hxy : mStatistic x = mStatistic y) :
    CommonCodeSufficiency e0 e0 x y := by
  refine ⟨{
    codeLeft := mStatistic
    codeRight := mStatistic
    leftMinimal := mStatistic_minimal_sufficient_criterion
    rightMinimal := mStatistic_minimal_sufficient_criterion
    observedCode := hxy
    inducedModelsEqual := ?_ }⟩
  intro theta code
  rfl

theorem e0_eT_commonCodeSufficiency_of_m_eq {x : E0Outcome} {t : TOutcome}
    (hxt : mStatistic x = mTStatistic t) :
    CommonCodeSufficiency e0 eT x t := by
  refine ⟨{
    codeLeft := mStatistic
    codeRight := mTStatistic
    leftMinimal := mStatistic_minimal_sufficient_criterion
    rightMinimal := mTStatistic_minimal_sufficient_criterion
    observedCode := hxt
    inducedModelsEqual := ?_ }⟩
  exact induced_m_models_coincide

theorem eT_e0_commonCodeSufficiency_of_m_eq {t : TOutcome} {x : E0Outcome}
    (htx : mTStatistic t = mStatistic x) :
    CommonCodeSufficiency eT e0 t x := by
  refine ⟨{
    codeLeft := mTStatistic
    codeRight := mStatistic
    leftMinimal := mTStatistic_minimal_sufficient_criterion
    rightMinimal := mStatistic_minimal_sufficient_criterion
    observedCode := htx
    inducedModelsEqual := ?_ }⟩
  intro theta code
  exact (induced_m_models_coincide theta code).symm

/-- The common-minimal-code sufficiency relation on the initial tagged bases.
The remaining tags are outside the particular common-code witness used in the
six displayed sufficiency memberships. -/
def initialSufficiencyRelation : StatisticalRelation InitialInferenceBase
  | .atE0 x, .atE0 y => CommonCodeSufficiency e0 e0 x y
  | .atE0 x, .atET t => CommonCodeSufficiency e0 eT x t
  | .atET t, .atE0 x => CommonCodeSufficiency eT e0 t x
  | .atET t, .atET u => CommonCodeSufficiency eT eT t u
  | _, _ => False

theorem initial_S_e0_x00_eT_t0 :
    initialSufficiencyRelation (.atE0 .x00) (.atET .t0) :=
  e0_eT_commonCodeSufficiency_of_m_eq rfl

theorem initial_S_e0_x11_eT_t2 :
    initialSufficiencyRelation (.atE0 .x11) (.atET .t2) :=
  e0_eT_commonCodeSufficiency_of_m_eq rfl

theorem initial_S_e0_x01_eT_t1 :
    initialSufficiencyRelation (.atE0 .x01) (.atET .t1) :=
  e0_eT_commonCodeSufficiency_of_m_eq rfl

theorem initial_S_e0_x10_eT_t1 :
    initialSufficiencyRelation (.atE0 .x10) (.atET .t1) :=
  e0_eT_commonCodeSufficiency_of_m_eq rfl

theorem initial_S_e0_x00_e0_x11 :
    initialSufficiencyRelation (.atE0 .x00) (.atE0 .x11) :=
  e0_e0_commonCodeSufficiency_of_m_eq rfl

theorem initial_S_e0_x01_e0_x10 :
    initialSufficiencyRelation (.atE0 .x01) (.atE0 .x10) :=
  e0_e0_commonCodeSufficiency_of_m_eq rfl

theorem six_listed_initial_S_memberships :
    initialSufficiencyRelation (.atE0 .x00) (.atET .t0) ∧
    initialSufficiencyRelation (.atE0 .x11) (.atET .t2) ∧
    initialSufficiencyRelation (.atE0 .x01) (.atET .t1) ∧
    initialSufficiencyRelation (.atE0 .x10) (.atET .t1) ∧
    initialSufficiencyRelation (.atE0 .x00) (.atE0 .x11) ∧
    initialSufficiencyRelation (.atE0 .x01) (.atE0 .x10) :=
  ⟨initial_S_e0_x00_eT_t0, initial_S_e0_x11_eT_t2,
    initial_S_e0_x01_eT_t1, initial_S_e0_x10_eT_t1,
    initial_S_e0_x00_e0_x11, initial_S_e0_x01_e0_x10⟩

/-! ### Observation-sensitive witnesses for pA and pB -/

/-- A general proof-bearing sufficiency witness based on the two exact
minimal likelihood-proportionality partitions, including the bijection and
equality of induced models required by the paper. -/
structure MinimalPartitionWitness
    {X Y C D : Type*} [Fintype X] [Fintype Y]
    [DecidableEq C] [DecidableEq D]
    (p : Parameter → X → ℚ) (q : Parameter → Y → ℚ)
    (classLeft : X → C) (classRight : Y → D) (x : X) (y : Y) where
  leftMinimal : ∀ a b,
    classLeft a = classLeft b ↔ likelihoodProportional p a b
  rightMinimal : ∀ a b,
    classRight a = classRight b ↔ likelihoodProportional q a b
  relabel : D ≃ C
  observedClass : classLeft x = relabel (classRight y)
  inducedModelsEqual : ∀ theta d,
    inducedMass (p theta) classLeft (relabel d) =
      inducedMass (q theta) classRight d

def MinimalPartitionSufficiency
    {X Y C D : Type*} [Fintype X] [Fintype Y]
    [DecidableEq C] [DecidableEq D]
    (p : Parameter → X → ℚ) (q : Parameter → Y → ℚ)
    (classLeft : X → C) (classRight : Y → D) (x : X) (y : Y) : Prop :=
  Nonempty (MinimalPartitionWitness p q classLeft classRight x y)

/-- Tagged inference bases sufficient to state the two ordered pairs `pA` and
`pB` with their observations retained. -/
inductive ComparisonInferenceBase where
  | atE0 (x : E0Outcome)
  | atEStar (x : EStarOutcome)
  | atE3 (x : E3Outcome)
  deriving DecidableEq, Fintype, Repr

/-- Sufficiency on the comparison bases, defined through certified minimal
partitions rather than a table of selected memberships. -/
def comparisonSufficiency : StatisticalRelation ComparisonInferenceBase
  | .atE0 x, .atE0 y =>
      MinimalPartitionSufficiency e0 e0 e0MinimalClass e0MinimalClass x y
  | .atEStar x, .atEStar y =>
      MinimalPartitionSufficiency eStar eStar
        eStarMinimalClass eStarMinimalClass x y
  | .atE3 x, .atE3 y =>
      MinimalPartitionSufficiency e3 e3 e3MinimalClass e3MinimalClass x y
  | .atEStar x, .atE3 y =>
      MinimalPartitionSufficiency eStar e3
        eStarMinimalClass e3MinimalClass x y
  | .atE3 x, .atEStar y =>
      MinimalPartitionSufficiency e3 eStar
        e3MinimalClass eStarMinimalClass x y
  | _, _ => False

/-- Ordinary conditionality retains the observed value and requires the
target model to arise by an ancillary conditioning step. -/
def OrdinarySameExperimentConditionality {X : Type*} [Fintype X]
    (p : Parameter → X → ℚ) (x y : X) : Prop :=
  x = y ∧ DirectConditioning p p

/-- The exact mixed-experiment conditionality witness from `EStar` to `E3`. -/
def StarE3Conditionality (s : EStarOutcome) (x : E3Outcome) : Prop :=
  s = embedE3 x ∧ IsAncillary eStar selector ∧
    (∀ theta, 0 < inducedMass (eStar theta) selector .b0) ∧
    ∀ theta y,
      conditionedModel eStar selector .b0 theta (embedE3 y) = e3 theta y

/-- Observation-sensitive conditionality on the comparison bases.  Mixed
`EStar`/`E3` steps use the selector witness; same-model steps use ordinary
ancillary conditioning and therefore require identical observations. -/
def comparisonConditionality : StatisticalRelation ComparisonInferenceBase
  | .atE0 x, .atE0 y => OrdinarySameExperimentConditionality e0 x y
  | .atEStar x, .atEStar y => OrdinarySameExperimentConditionality eStar x y
  | .atE3 x, .atE3 y => OrdinarySameExperimentConditionality e3 x y
  | .atEStar s, .atE3 x => StarE3Conditionality s x
  | .atE3 x, .atEStar s => StarE3Conditionality s x
  | _, _ => False

def pA : ComparisonInferenceBase × ComparisonInferenceBase :=
  (.atE0 .x00, .atE0 .x11)

def pB : ComparisonInferenceBase × ComparisonInferenceBase :=
  (.atEStar .s01, .atE3 .d1)

theorem pA_in_comparisonSufficiency : comparisonSufficiency pA.1 pA.2 := by
  refine ⟨{
    leftMinimal := fun a b => (e0_proportional_iff_same_minimal_class a b).symm
    rightMinimal := fun a b => (e0_proportional_iff_same_minimal_class a b).symm
    relabel := Equiv.refl E0MinimalClass
    observedClass := rfl
    inducedModelsEqual := ?_ }⟩
  intro theta code
  rfl

theorem pA_not_in_comparisonConditionality :
    ¬ comparisonConditionality pA.1 pA.2 := by
  intro h
  exact E0Outcome.noConfusion h.1

theorem pA_in_S_diff_C :
    comparisonSufficiency pA.1 pA.2 ∧
      ¬ comparisonConditionality pA.1 pA.2 :=
  ⟨pA_in_comparisonSufficiency, pA_not_in_comparisonConditionality⟩

theorem pB_in_comparisonConditionality : comparisonConditionality pB.1 pB.2 := by
  refine ⟨rfl, selector_ancillary, ?_, ?_⟩
  · intro theta
    rw [selector_mass_table theta .b0]
    norm_num
  · intro theta y
    have hy : selector (embedE3 y) = .b0 := by
      cases y <;> rfl
    simp only [conditionedModel, hy, if_true]
    exact condition_on_selector_zero_is_e3 theta y

theorem pB_not_in_comparisonSufficiency :
    ¬ comparisonSufficiency pB.1 pB.2 := by
  rintro ⟨w⟩
  exact no_bijection_between_pB_minimal_partitions ⟨w.relabel.symm⟩

theorem pB_in_C_diff_S :
    comparisonConditionality pB.1 pB.2 ∧
      ¬ comparisonSufficiency pB.1 pB.2 :=
  ⟨pB_in_comparisonConditionality, pB_not_in_comparisonSufficiency⟩

end FiniteExamples
end VennDiagrams
