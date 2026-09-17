# Manuscript coverage

The tables document the correspondence between *Birnbaum’s principles in Venn diagrams: Extended version with Lean verification* and its formal statements in Lean. `L`, `S` and `C` denote likelihood, sufficiency and direct conditionality; `closure` means equivalence closure.

All base have a finite effective sample space, probability mass functions (PMFs), outcome codes and an observation. The parameter space is nonempty, finite and is common to all bases.

Declarations in the following tables are written as `VennDiagrams.Certification.PaperSignature.`.

## Paper results

| Paper statement | Manuscript labels | Lean declaration | 
|---|---|---|
| Definition 3.1 | `procedure` | `definition_procedure_output` | 
| Definition 3.2 | `preserving` | `definition_preserves_relation` | 
| Definition 3.3 | `joint-preserving` | `definition_joint_preservation` | 
| Theorem 3.1 | `BT1` | `theorem_BT1_procedure_classes` | 
| Corollary 3.1 | `BT2` | `corollary_BT2_conditional_pairs` | 
| Corollary 3.2 | `BT3` | `corollary_BT3_joint_pairs` |
| Lemma A.1 | `bl:1` | `lemma_bl1_equivalence_closure` | 
| Lemma A.2 | `bl:3` | `lemma_bl3_disjoint_classes` |
| Lemma A.3 | `lemma-a` | `lemma_a_preserving_classes` | 
| Lemma A.4 | `lemma-b` | `lemma_b_strict_antitone` | 
| Lemma A.5 | `FT` | `lemma_FT_preservation_closure` |

The inclusion in Theorem 3.1(b) is strict when there is more than one parameter value in the statistical model and the codomain is nonempty. With a singleton parameter space, `S = L` and all three preservation classes coincide.

## Evans (2013) results from our definitions

Results 1–2 hold for arbitrary sets and relations; 3–8 for every nonempty finite parameter space; 9–10 require at least two parameter values. 

| Evans (2013) result | Certified statement | Lean declaration |
|---|---|---|
| Lemma 1 | Equivalence closure equals connectivity by finite chains, allowing reversal | `evans2013_lemma1` |
| Lemma 2 | `closure(closure(R₁) ∪ closure(R₂)) = closure(R₁ ∪ R₂)` | `evans2013_lemma2` |
| Lemma 3 | `L` is an equivalence relation | `evans2013_lemma3_packed` |
| Lemma 4 | The likelihood-class statistic is minimal sufficient | `evans2013_lemma4_packed` |
| Lemma 5 | `S` is an equivalence relation and `S ⊆ L` | `evans2013_lemma5_packed` |
| Lemma 6 | `C` is reflexive, symmetric, not transitive; `C ⊆ L` | `evans2013_lemma6_packed` |
| Theorem 7 | `C ⊊ closure(C) = L` | `evans2013_theorem7_packed` |
| Theorem 8 | `C ∪ S ⊆ L ⊆ closure(C ∪ S)` | `evans2013_theorem8_packed` |
| Theorem 9 | `C ∪ S ⊊ L = closure(C ∪ S)` | `evans2013_theorem9_packed` |
| Corollary 10 | `C ∪ S ⊊ closure(C) = L`, `S ⊊ closure(C)` | `evans2013_corollary10_packed` |

## Examples and finite closure

| Paper statement | Lean declaration | 
|---|---|
| Example 2.2: six sufficiency pairs | `PackedRelationExample.six_listed_initial_packedS_memberships` |
| Example 2.3: nontransitivity | `PackedRelationExample.packed_e0_conditionality_nontransitivity_witness` | 
| Example 2.4: five conditionality pairs | `PackedRelationExample.five_listed_hierarchical_packedC_memberships` |
| Example 2.5: `pA ∈ S \ C`, `pB ∈ C \ S` | `PackedRelationExample.pA_in_packedS`, `PackedRelationExample.pA_not_in_packedC`, `PackedRelationExample.pB_in_packedC`, `PackedRelationExample.pB_not_in_packedS` |
| Example 3.7: `E5/E6` in `L`, outside `C` and `S` | `PackedPValueExample.packedE5X_packedE6U_joint_strict_witness` | 
| Example 3.7: p-values `1/10` and `1/5` | `packed_e5_e6_lr_pvalue_separation` | 
| Finite partition into nonempty null and alternative sets: lower-tail likelihood-ratio p-values preserve `S`, violate `L` | `finite_lr_pvalue_separation` |
| Appendix A: four `C`-steps join every pair in `L` | `evans2013_four_step_chain_packed` | 

## Reduced-model stable conditionality

`SC_red` uses minimal sufficient reduction and conditioning on laminal cells: `VennDiagrams.packedFiniteReducedStableConditionalityRelation`.

| Certified statement | Lean declaration |
|---|---|
| `S ⊆ SC_red`, every nonempty finite parameter space | `reduced_stable_sufficiency` |
| `pA ∈ SC_red` and `pA ∉ C`, Example 2.5 with two parameter values | `reduced_stable_counterexample` |
| `SC_red ⊈ C`, every nonempty finite parameter space | `reduced_stable_not_le_conditionality` |

## Finite sufficiency

The following declarations use `VennDiagrams.`. The likelihood ratio (LR) uses
`ENNReal`: a/0 = ∞ for a > 0, and 0/0 = 0.

| Certified statement | Lean declaration |
|---|---|
| Neyman–Fisher factorization | `finite_neyman_fisher_factorization` |
| Minimal sufficiency and the likelihood-class criterion | `finite_minimal_sufficiency_iff_likelihoodFiberCriterion` |
| Minimal sufficient reduction preserves lower-tail LR p-values | `packedLowerTailLRPValue_eq_reduced` |
| Lower-tail LR p-values preserve `S` | `packedLowerTailLRPValueProcedure_preserves_sufficiency` |
| Pθ(p ≤ α) ≤ α under the null hypothesis, α ≥ 0 | `lowerTailLRPValue_superuniform` |

See [verification records and instructions](VERIFICATION.md) and the
[manuscript assertion index](MANUSCRIPT_ASSERTION_INDEX.csv).
