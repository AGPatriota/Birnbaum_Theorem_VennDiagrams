# Verification

## What is verified

The verification script compiles the Lean proofs, checks the theorem records, and rejects unfinished proofs or unapproved axioms.

All displayed probability, maximum likelihood estimate (MLE) and likelihood ratio (LR) tables are checked exactly without numeric approximations.

The correspondence between the manuscript and the Lean statements was audited by the authors. See [paper coverage](PAPER_COVERAGE.md) for the theorem and example mapping.

## How to rerun

Use GNU/Linux or WSL, Bash, Git, curl, Python 3.11+ and Elan for Lean/Lake.
Lean 4.32.2 and dependency revisions (`lake-manifest.json`) are fixed. The first
run downloads the toolchain, dependencies and compiled Mathlib files.

In the public repository:

```bash
bash verify.sh --code-only
sha256sum -c REPLICATION_MANIFEST.sha256
```

Logs: `verification.log` and `axiom-audit.log`.
`REPLICATION_MANIFEST.sha256` covers every distributed file other than itself.

## Records

| File | Contents |
|---|---|
| [MANUSCRIPT_ASSERTION_INDEX.csv](MANUSCRIPT_ASSERTION_INDEX.csv) | Manuscript labels and audited mathematical statements, with their Lean declarations |
| [PAPER_SIGNATURE_INDEX.csv](PAPER_SIGNATURE_INDEX.csv) | Exact signatures and associated declarations |
| [LEAN_DECLARATION_CATALOGUE.csv](LEAN_DECLARATION_CATALOGUE.csv) | Declaration names and source locations |
| [AXIOM_WHITELIST.csv](AXIOM_WHITELIST.csv) | Expected axiom dependencies for promoted declarations |


## Statements and proofs

The statements in `Challenge.lean` have `sorry`; the proofs are supplied by
`Solution.lean`, through `Lean/VennDiagrams/S06_PaperSignatures.lean`.
The definitions and hypotheses are the same. The definitions have no `sorry`.
The statements are given in `comparator.json`; the correspondence is given
in `formalization.yaml`.

The verification of `Challenge.lean` and `Solution.lean` is not included in
`verify.sh`.

```bash
lake build Challenge Solution
```

[Code and verification instructions](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
