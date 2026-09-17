# Birnbaum's principles in Venn diagrams

We present Lean 4 proofs and verification tools for the paper *Birnbaum’s principles in Venn diagrams: Extended version with Lean verification*. 

The conditionality principle is equivalent to the likelihood principle for the finite models and the statistical procedures defined in the paper. Every procedure that preserves the likelihood principle also preserves sufficiency, but some procedures that preserve the sufficiency principle do not preserve likelihood, and hence conditionality, when the parameter space has more than one parameter value and the codomain is non-empty. The likelihood-ratio $p$-value illustrates this strict inclusion.

The Lean development also certifies some results derived in Evans (2013). 

## Verification

Requires GNU/Linux or WSL, Bash, Git, curl, Python 3.11+ and Elan.

```bash
git clone https://github.com/AGPatriota/Birnbaum_Theorem_VennDiagrams.git
cd Birnbaum_Theorem_VennDiagrams
bash verify.sh --code-only
sha256sum -c REPLICATION_MANIFEST.sha256
```

See [verification instructions](VERIFICATION.md) and
[manuscript coverage](PAPER_COVERAGE.md).

Code and documentation: [Apache 2.0](LICENSE).


## Statements and proofs

The statements in [Challenge.lean](Challenge.lean) use the definitions in the
paper. The proofs are supplied by [Solution.lean](Solution.lean).

[Correspondence](formalization.yaml) and [verification instructions](VERIFICATION.md).

## Declaration on the use of generative artificial intelligence

The authors used GPT-6 Astra to assist with formal proofs in Lean and cross-checking the manuscript against the formalization. The correspondence with the manuscript is author-audited. The authors remain responsible for the article and its accompanying code.
