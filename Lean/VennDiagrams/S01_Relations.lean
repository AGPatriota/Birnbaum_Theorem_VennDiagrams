import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Relation

/-!
# S01 — Relations, procedures, and equivalence closure

This module formalizes the set-theoretic core used throughout the manuscript.
A statistical procedure is represented exactly as the paper defines it: a
binary relation between inference bases and outputs.  `output Ev i` is its
fiber at `i`.
-/

open Set

namespace VennDiagrams

universe u v

/-- A binary relation on inference bases. -/
abbrev StatisticalRelation (ι : Type u) := ι → ι → Prop

/-- The union of two statistical relations. -/
def relationUnion {ι : Type u} (D₁ D₂ : StatisticalRelation ι) :
    StatisticalRelation ι :=
  fun i j ↦ D₁ i j ∨ D₂ i j

/-- The identity relation appearing in the manuscript's chain description. -/
def identityRelation {ι : Type u} : StatisticalRelation ι :=
  fun i j ↦ i = j

/-- The equivalence closure (smallest equivalence relation containing `D`). -/
def equivalenceClosure {ι : Type u} (D : StatisticalRelation ι) :
    StatisticalRelation ι :=
  Relation.EqvGen D

/-- A statistical procedure is a relation between inference bases and outputs. -/
abbrev Procedure (ι : Type u) (A : Type v) := Set (ι × A)

/-- The output set (fiber) of a relation-valued procedure at an inference base. -/
def output {ι : Type u} {A : Type v} (Ev : Procedure ι A) (i : ι) : Set A :=
  {a | (i, a) ∈ Ev}

/-- The graph relation associated with an ordinary function. -/
def graphProcedure {ι : Type u} {A : Type v} (f : ι → A) : Procedure ι A :=
  {(i, a) | a = f i}

/-- A procedure preserves a relation when related inputs have identical fibers. -/
def Preserves {ι : Type u} {A : Type v} (Ev : Procedure ι A)
    (D : StatisticalRelation ι) : Prop :=
  ∀ ⦃i j⦄, D i j → output Ev i = output Ev j

/-- The manuscript's class `G_D^(A)` of all procedures preserving `D`. -/
def preservingClass {ι : Type u} (A : Type v) (D : StatisticalRelation ι) :
    Set (Procedure ι A) :=
  {Ev | Preserves Ev D}

/-- The equivalence class of `i` under a relation. -/
def relationClass {ι : Type u} (D : StatisticalRelation ι) (i : ι) : Set ι :=
  {j | D i j}

@[simp] theorem output_graphProcedure {ι : Type u} {A : Type v} (f : ι → A) (i : ι) :
    output (graphProcedure f) i = {f i} := by
  ext a
  simp [output, graphProcedure]

/-- Ordinary functions give precisely singleton-fiber procedures. -/
theorem exists_function_of_unique_outputs {ι : Type u} {A : Type v}
    (Ev : Procedure ι A) (h : ∀ i, ∃! a, a ∈ output Ev i) :
    ∃ f : ι → A, Ev = graphProcedure f := by
  classical
  choose f hf huniq using h
  refine ⟨f, ?_⟩
  ext p
  rcases p with ⟨i, a⟩
  constructor
  · intro ha
    have ha' : a ∈ output Ev i := ha
    have : a = f i := huniq i a ha'
    exact this
  · intro ha
    change a = f i at ha
    simpa [output, ha] using hf i

/-- Every function graph has one and only one output at each input. -/
theorem graphProcedure_unique_outputs {ι : Type u} {A : Type v} (f : ι → A) :
    ∀ i, ∃! a, a ∈ output (graphProcedure f) i := by
  intro i
  refine ⟨f i, ?_, ?_⟩
  · simp [output_graphProcedure]
  · intro a ha
    simpa [output_graphProcedure] using ha

/-- A constant singleton-output relation preserves every relation. -/
def constantProcedure {ι : Type u} {A : Type v} (a₀ : A) : Procedure ι A :=
  {p | p.2 = a₀}

@[simp] theorem output_constantProcedure {ι : Type u} {A : Type v} (a₀ : A) (i : ι) :
    output (constantProcedure a₀) i = {a₀} := by
  ext a
  simp [output, constantProcedure]

/-- `G_D^(A)` is nonempty for every output type: the empty relation works. -/
theorem preservingClass_nonempty {ι : Type u} {A : Type v}
    (D : StatisticalRelation ι) : (preservingClass A D).Nonempty := by
  refine ⟨(∅ : Procedure ι A), ?_⟩
  intro i j _
  simp [output]

/-- Lemma A.3(a) (manuscript id: lemma-a): preservation classes reverse inclusions of relations. -/
theorem preservingClass_antitone {ι : Type u} {A : Type v}
    {D₁ D₂ : StatisticalRelation ι} (h : D₁ ≤ D₂) :
    preservingClass A D₂ ⊆ preservingClass A D₁ := by
  intro Ev hEv i j hij
  exact hEv (h _ _ hij)

/-- Lemma A.3(b) (manuscript id: lemma-a), pointwise form. -/
theorem preserves_union_iff {ι : Type u} {A : Type v}
    (Ev : Procedure ι A) (D₁ D₂ : StatisticalRelation ι) :
    Preserves Ev (relationUnion D₁ D₂) ↔ Preserves Ev D₁ ∧ Preserves Ev D₂ := by
  constructor
  · intro h
    constructor
    · intro i j hij
      exact h (Or.inl hij)
    · intro i j hij
      exact h (Or.inr hij)
  · rintro ⟨h₁, h₂⟩ i j (hij | hij)
    · exact h₁ hij
    · exact h₂ hij

/-- Lemma A.3(b) (manuscript id: lemma-a): preserving a union is preserving both constituent relations. -/
theorem preservingClass_union {ι : Type u} {A : Type v}
    (D₁ D₂ : StatisticalRelation ι) :
    preservingClass A (relationUnion D₁ D₂) =
      preservingClass A D₁ ∩ preservingClass A D₂ := by
  ext Ev
  exact preserves_union_iff Ev D₁ D₂

/-- Every relation is contained in its equivalence closure. -/
theorem relation_le_equivalenceClosure {ι : Type u} (D : StatisticalRelation ι) :
    D ≤ equivalenceClosure D := by
  intro i j hij
  exact Relation.EqvGen.rel i j hij

/-- The equivalence closure is an equivalence relation. -/
theorem equivalenceClosure_isEquivalence {ι : Type u} (D : StatisticalRelation ι) :
    Equivalence (equivalenceClosure D) :=
  Relation.EqvGen.is_equivalence D

/-- Minimality: every equivalence relation containing `D` contains its closure. -/
theorem equivalenceClosure_minimal {ι : Type u} {D R : StatisticalRelation ι}
    (hR : Equivalence R) (hDR : D ≤ R) : equivalenceClosure D ≤ R := by
  intro i j hij
  induction hij with
  | rel i j hij => exact hDR _ _ hij
  | refl i => exact hR.1 i
  | symm i j _ ih => exact hR.2 ih
  | trans i j k _ _ hij hjk => exact hR.3 hij hjk

/-- Mathlib's reflexive-transitive symmetric-step closure is the manuscript's
finite-chain presentation of equivalence closure. -/
theorem equivalenceClosure_eq_zigzagClosure {ι : Type u} (D : StatisticalRelation ι) :
    equivalenceClosure D = Relation.ReflTransGen (Relation.SymmGen D) := by
  exact (Relation.EqvGen.reflTransGen_symmGen (r := D)).symm

/-- Lemma A.5 (manuscript id: FT), pointwise form: preserving a relation is equivalent to preserving
its equivalence closure. -/
theorem preserves_equivalenceClosure_iff {ι : Type u} {A : Type v}
    (Ev : Procedure ι A) (D : StatisticalRelation ι) :
    Preserves Ev (equivalenceClosure D) ↔ Preserves Ev D := by
  constructor
  · intro h i j hij
    exact h (Relation.EqvGen.rel i j hij)
  · intro h i j hij
    induction hij with
    | rel i j hij => exact h hij
    | refl i => rfl
    | symm i j _ ih => exact ih.symm
    | trans i j k _ _ hij hjk => exact hij.trans hjk

/-- Lemma A.5 (manuscript id: FT): `G_D^(A) = G_closure(D)^(A)`. -/
theorem preservingClass_equivalenceClosure {ι : Type u} {A : Type v}
    (D : StatisticalRelation ι) :
    preservingClass A D = preservingClass A (equivalenceClosure D) := by
  ext Ev
  exact (preserves_equivalenceClosure_iff Ev D).symm

/-- Lemma on equivalence classes: unrelated points have disjoint classes. -/
theorem disjoint_relationClasses_of_not_related {ι : Type u}
    {R : StatisticalRelation ι} (hR : Equivalence R) {i j : ι} (hij : ¬ R i j) :
    Disjoint (relationClass R i) (relationClass R j) := by
  rw [Set.disjoint_left]
  intro z hiz hjz
  exact hij (hR.3 hiz (hR.2 hjz))

/-- Converse class lemma: disjoint equivalence classes have unrelated bases. -/
theorem not_related_of_disjoint_relationClasses {ι : Type u}
    {R : StatisticalRelation ι} (hR : Equivalence R) {i j : ι}
    (hdisj : Disjoint (relationClass R i) (relationClass R j)) : ¬ R i j := by
  intro hij
  have hi : j ∈ relationClass R i := hij
  have hj : j ∈ relationClass R j := hR.1 j
  exact Set.disjoint_left.1 hdisj hi hj

/-- Lemma A.2 (manuscript id: bl:3): equivalence-class disjointness characterizes
failure of relatedness. -/
theorem not_related_iff_disjoint_relationClasses {ι : Type u}
    {R : StatisticalRelation ι} (hR : Equivalence R) (i j : ι) :
    ¬ R i j ↔ Disjoint (relationClass R i) (relationClass R j) := by
  exact ⟨disjoint_relationClasses_of_not_related hR,
    not_related_of_disjoint_relationClasses hR⟩

/-- The class-indicator witness used to reverse a strict inclusion. -/
def classIndicatorProcedure {ι : Type u} {A : Type v}
    (R : StatisticalRelation ι) (base : ι) (a₀ : A) : Procedure ι A :=
  {p | R base p.1 ∧ p.2 = a₀}

/-- A class indicator preserves the equivalence relation defining the class. -/
theorem classIndicator_preserves {ι : Type u} {A : Type v}
    {R : StatisticalRelation ι} (hR : Equivalence R) (base : ι) (a₀ : A) :
    Preserves (classIndicatorProcedure R base a₀) R := by
  intro i j hij
  ext a
  constructor
  · rintro ⟨hbi, ha⟩
    exact ⟨hR.3 hbi hij, ha⟩
  · rintro ⟨hbj, ha⟩
    exact ⟨hR.3 hbj (hR.2 hij), ha⟩

/-- Lemma A.4 (manuscript id: lemma-b): strict inclusion of equivalence relations reverses to a strict
inclusion of preservation classes for every nonempty output type. -/
theorem preservingClass_strict_antitone {ι : Type u} {A : Type v} [Nonempty A]
    {R₁ R₂ : StatisticalRelation ι} (hR₁ : Equivalence R₁)
    (hsub : R₁ ≤ R₂) (hstrict : ∃ i j, R₂ i j ∧ ¬ R₁ i j) :
    preservingClass A R₂ ⊂ preservingClass A R₁ := by
  refine ⟨preservingClass_antitone hsub, ?_⟩
  rcases hstrict with ⟨i, j, hR₂ij, hnR₁ij⟩
  let a₀ : A := Classical.choice inferInstance
  let Ev := classIndicatorProcedure R₁ i a₀
  have hEvR₁ : Ev ∈ preservingClass A R₁ := classIndicator_preserves hR₁ i a₀
  have hnot : Ev ∉ preservingClass A R₂ := by
    intro hEvR₂
    have hout := hEvR₂ hR₂ij
    have ha_left : a₀ ∈ output Ev i := by
      exact ⟨hR₁.1 i, rfl⟩
    have ha_right : a₀ ∉ output Ev j := by
      intro ha
      exact hnR₁ij ha.1
    exact ha_right (hout ▸ ha_left)
  intro hreverse
  exact hnot (hreverse hEvR₁)

/-- Inclusion between classes of all relation-valued procedures recovers the
oppositely directed inclusion between equivalence closures. -/
theorem equivalenceClosure_le_of_preservingClass_subset
    {ι : Type u} {A : Type v} [Nonempty A]
    {D₁ D₂ : StatisticalRelation ι}
    (hG : preservingClass A D₂ ⊆ preservingClass A D₁) :
    equivalenceClosure D₁ ≤ equivalenceClosure D₂ := by
  intro i j hij
  let a₀ : A := Classical.choice inferInstance
  let Ev := classIndicatorProcedure (equivalenceClosure D₂) i a₀
  have hEqv₂ : Equivalence (equivalenceClosure D₂) :=
    equivalenceClosure_isEquivalence D₂
  have hEvClosure₂ : Preserves Ev (equivalenceClosure D₂) :=
    classIndicator_preserves hEqv₂ i a₀
  have hEvD₂ : Ev ∈ preservingClass A D₂ :=
    (preserves_equivalenceClosure_iff Ev D₂).mp hEvClosure₂
  have hEvD₁ : Ev ∈ preservingClass A D₁ := hG hEvD₂
  have hEvClosure₁ : Preserves Ev (equivalenceClosure D₁) :=
    (preserves_equivalenceClosure_iff Ev D₁).mpr hEvD₁
  have hout := hEvClosure₁ hij
  have ha_left : a₀ ∈ output Ev i := ⟨hEqv₂.1 i, rfl⟩
  have ha_right : a₀ ∈ output Ev j := hout ▸ ha_left
  exact ha_right.1

/-- Equality of all preservation classes is equivalent to equality of the
underlying equivalence closures.  This supplies the precise converse needed
for the paper's "if and only if" formulation. -/
theorem preservingClass_eq_iff_equivalenceClosure_eq
    {ι : Type u} {A : Type v} [Nonempty A]
    (D₁ D₂ : StatisticalRelation ι) :
    preservingClass A D₁ = preservingClass A D₂ ↔
      equivalenceClosure D₁ = equivalenceClosure D₂ := by
  constructor
  · intro hG
    apply le_antisymm
    · exact equivalenceClosure_le_of_preservingClass_subset
        (fun Ev hEv ↦ hG.symm ▸ hEv)
    · exact equivalenceClosure_le_of_preservingClass_subset
        (fun Ev hEv ↦ hG ▸ hEv)
  · intro hclosure
    calc
      preservingClass A D₁ = preservingClass A (equivalenceClosure D₁) :=
        preservingClass_equivalenceClosure D₁
      _ = preservingClass A (equivalenceClosure D₂) := by rw [hclosure]
      _ = preservingClass A D₂ := (preservingClass_equivalenceClosure D₂).symm

/-- Precise preservation semantics for the manuscript's Birnbaum/Evans
equivalence.  The quantification over all relation-valued procedures is
encoded as equality of preservation classes. -/
theorem birnbaum_semantics_iff_evans_closure
    {ι : Type u} {A : Type v} [Nonempty A]
    {C S L : StatisticalRelation ι} (hL : Equivalence L) :
    preservingClass A L = preservingClass A C ∩ preservingClass A S ↔
      equivalenceClosure (relationUnion C S) = L := by
  rw [← preservingClass_union]
  rw [preservingClass_eq_iff_equivalenceClosure_eq]
  have hLclosure : equivalenceClosure L = L := hL.eqvGen_eq
  rw [hLclosure]
  exact eq_comm

/-- The procedure-level identity induced by `closure(C) = L`. -/
theorem conditional_preserving_eq_likelihood_preserving {ι : Type u} {A : Type v}
    {C L : StatisticalRelation ι} (hCL : equivalenceClosure C = L) :
    preservingClass A L = preservingClass A C := by
  rw [← hCL, ← preservingClass_equivalenceClosure]

/-- The joint procedure-level identity induced by `closure(C ∪ S) = L`. -/
theorem joint_preserving_eq_likelihood_preserving {ι : Type u} {A : Type v}
    {C S L : StatisticalRelation ι}
    (hCSL : equivalenceClosure (relationUnion C S) = L) :
    preservingClass A L = preservingClass A C ∩ preservingClass A S := by
  rw [← hCSL, ← preservingClass_equivalenceClosure, preservingClass_union]

/-- Abstract strict-case helper for Theorem 3.1. The full finite-model result is
`VennDiagrams.Certification.PaperSignature.theorem_BT1_procedure_classes` in S06. -/
theorem theorem_BT1 {ι : Type u} {A : Type v} [Nonempty A]
    {C S L : StatisticalRelation ι}
    (hC : equivalenceClosure C = L)
    (hS_equiv : Equivalence S)
    (hSL : S ≤ L)
    (hSL_strict : ∃ i j, L i j ∧ ¬ S i j)
    (hCS : equivalenceClosure (relationUnion C S) = L) :
    preservingClass A L = preservingClass A C ∧
      preservingClass A L ⊂ preservingClass A S ∧
      preservingClass A L = preservingClass A C ∩ preservingClass A S := by
  refine ⟨conditional_preserving_eq_likelihood_preserving hC, ?_,
    joint_preserving_eq_likelihood_preserving hCS⟩
  exact preservingClass_strict_antitone hS_equiv hSL hSL_strict

/-- Abstract form of Corollary 3.1: `C`-preservation gives agreement on `L \ C`. -/
theorem corollary_BT2 {ι : Type u} {A : Type v}
    {C L : StatisticalRelation ι} (hC : equivalenceClosure C = L)
    {Ev : Procedure ι A} (hEv : Preserves Ev C) {i j : ι}
    (hij : L i j ∧ ¬ C i j) : output Ev i = output Ev j := by
  have hclasses := conditional_preserving_eq_likelihood_preserving (A := A) hC
  have : Ev ∈ preservingClass A L := hclasses.symm ▸ hEv
  exact this hij.1

/-- Abstract form of Corollary 3.2: joint `S`- and `C`-preservation gives agreement on
`L \ (S ∪ C)`. -/
theorem corollary_BT3 {ι : Type u} {A : Type v}
    {C S L : StatisticalRelation ι}
    (hCS : equivalenceClosure (relationUnion C S) = L)
    {Ev : Procedure ι A} (hEvS : Preserves Ev S) (hEvC : Preserves Ev C)
    {i j : ι} (hij : L i j ∧ ¬ relationUnion S C i j) :
    output Ev i = output Ev j := by
  have hjoint := joint_preserving_eq_likelihood_preserving (A := A) hCS
  have hmem : Ev ∈ preservingClass A C ∩ preservingClass A S := ⟨hEvC, hEvS⟩
  have hEvL : Ev ∈ preservingClass A L := hjoint.symm ▸ hmem
  exact hEvL hij.1

end VennDiagrams
