#!/usr/bin/env python3
"""Check exact Lean signatures against the index and numbered sources.

Expected PAPER_SIGNATURE_INDEX.csv schema:
    manuscript_id,kind,signature_declaration,status,library_declarations

Declarations are fully qualified; multiple supporting library declarations are
separated by ``|``. Each signature theorem in the numbered Lean sources must be
introduced by a line ``-- manuscript-id: <manuscript_id>``.
"""

from __future__ import annotations

import argparse
import csv
import re
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
INDEX = ROOT / "PAPER_SIGNATURE_INDEX.csv"
SOURCE = ROOT / "Lean" / "VennDiagrams"
PROJECT_MODULE = "VennDiagrams"
PROJECT_NAMESPACE = "VennDiagrams."
EXPECTED_COLUMNS = [
    "manuscript_id",
    "kind",
    "signature_declaration",
    "status",
    "library_declarations",
]
FORMAL_KINDS = {"definition", "theorem", "lemma", "proposition", "corollary"}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LEAN_NAME = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)


def fail(message: str) -> None:
    raise SystemExit("PAPER_SIGNATURE_AUDIT_FAILED: " + message)


def declaration_list(field: str, context: str, *, allow_empty: bool) -> list[str]:
    if not field.strip():
        if allow_empty:
            return []
        fail(f"{context} has no declaration")
    pieces = [piece.strip() for piece in field.split("|")]
    if any(not piece for piece in pieces):
        fail(f"{context} has an empty declaration between separators")
    for declaration in pieces:
        if LEAN_NAME.fullmatch(declaration) is None:
            fail(f"{context} has malformed Lean declaration {declaration!r}")
    return pieces


def read_rows() -> list[dict[str, str]]:
    if not INDEX.is_file():
        fail(f"missing {INDEX.name}; expected columns: {','.join(EXPECTED_COLUMNS)}")
    with INDEX.open(encoding="utf-8", newline="") as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames != EXPECTED_COLUMNS:
            fail("columns must be " + ",".join(EXPECTED_COLUMNS))
        rows = list(reader)
    if not rows:
        fail("empty paper-signature index")
    if any(None in row or any(value is None for value in row.values()) for row in rows):
        fail("malformed CSV row")
    return rows


def source_registry(rows_by_id: dict[str, dict[str, str]]) -> dict[str, str]:
    marker_pattern = re.compile(
        r"^\s*--\s*manuscript-id:\s*([^\s]+)\s*$", flags=re.MULTILINE
    )
    declaration_pattern = re.compile(
        r"\s*(?:/--[\s\S]*?-/\s*)?"
        r"(?:@\[[^\]]*\]\s*)*"
        r"theorem\s+([A-Za-z_][A-Za-z0-9_']*)\b"
    )
    registry: dict[str, str] = {}
    local_names: set[str] = set()
    for path in sorted(SOURCE.rglob("*.lean")):
        source = path.read_text(encoding="utf-8")
        for marker in marker_pattern.finditer(source):
            manuscript_id = marker.group(1)
            declaration = declaration_pattern.match(source, marker.end())
            if declaration is None:
                fail(
                    f"{path.relative_to(ROOT)}: source marker for {manuscript_id} "
                    "is not followed by a theorem"
                )
            local_name = declaration.group(1)
            if manuscript_id in registry:
                fail(f"duplicate source marker for {manuscript_id}")
            if local_name in local_names:
                fail(f"duplicate marked paper-signature theorem name {local_name}")
            if manuscript_id not in rows_by_id:
                fail(f"unexpected source manuscript marker {manuscript_id}")
            expected = rows_by_id[manuscript_id]["signature_declaration"].strip()
            if expected.rsplit(".", 1)[-1] != local_name:
                fail(
                    f"source marker {manuscript_id} names theorem {local_name}, "
                    f"but index names {expected}"
                )
            registry[manuscript_id] = expected
            local_names.add(local_name)
    return registry


def parse_axiom_reports(output: str) -> dict[str, set[str]]:
    pattern = re.compile(
        r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]"
        r"|does not depend on any axioms)",
        flags=re.DOTALL,
    )
    reports: dict[str, set[str]] = {}
    for match in pattern.finditer(output):
        name = match.group(1)
        if name in reports:
            fail(f"duplicate #print axioms report for {name}")
        body = match.group(2) or ""
        reports[name] = {
            item.strip()
            for item in body.replace("\\n", " ").replace("\n", " ").split(",")
            if item.strip()
        }
    return reports


FINITE_PARAMETER_SCOPE_PROBE = r"""
namespace FiniteParameterScopeProbe
open Set VennDiagrams VennDiagrams.Certification.PaperSignature
universe u v w
variable {Theta : Type u} [Fintype Theta] [Nonempty Theta] {A : Type w}

example : preservingClass A (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) = preservingClass A (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) :=
  (theorem_BT1_procedure_classes (Theta := Theta) (A := A)).1
example : preservingClass A (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) ⊆ preservingClass A (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) :=
  (theorem_BT1_procedure_classes (Theta := Theta) (A := A)).2.1.1
example : (preservingClass A (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) ⊂ preservingClass A (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) ↔ Nontrivial Theta ∧ Nonempty A) :=
  (theorem_BT1_procedure_classes (Theta := Theta) (A := A)).2.1.2
example : preservingClass A (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) = preservingClass A (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∩ preservingClass A (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) :=
  (theorem_BT1_procedure_classes (Theta := Theta) (A := A)).2.2
example [Subsingleton Theta] : (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) = (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) :=
  (singleton_parameter_procedure_classes (Theta := Theta) (A := A)).1
example [IsEmpty A] (Ev : Procedure (PackedFiniteInferenceBase.{u, v} Theta) A) :
    Ev = ∅ := procedure_eq_empty_of_isEmpty_output Ev
example : (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) < equivalenceClosure (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧ equivalenceClosure (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) = (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) :=
  evans2013_theorem7_packed
example [Nontrivial Theta] : relationUnion (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) < (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) :=
  (evans2013_theorem9_packed (Theta := Theta)).1
example [Nontrivial Theta] : RelationsIncomparable (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) :=
  packed_sufficiency_conditionality_incomparable
example : (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) ≤ packedFiniteReducedStableConditionalityRelation.{u, v} :=
  reduced_stable_sufficiency
example : ¬ packedFiniteReducedStableConditionalityRelation.{u, v}
    (Theta := Theta) ≤ (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) := reduced_stable_not_le_conditionality

example {Ev : Procedure (PackedFiniteInferenceBase.{u, v} Theta) A}
    (hEv : Preserves Ev packedFiniteConditionalityRelation)
    {I J : PackedFiniteInferenceBase.{u, v} Theta}
    (hIJ : packedFiniteLikelihoodRelation I J ∧ ¬ packedFiniteConditionalityRelation I J) :
    output Ev I = output Ev J := corollary_BT2_conditional_pairs hEv hIJ
example {Ev : Procedure (PackedFiniteInferenceBase.{u, v} Theta) A}
    (hS : Preserves Ev packedFiniteSufficiencyRelation)
    (hC : Preserves Ev packedFiniteConditionalityRelation)
    {I J : PackedFiniteInferenceBase.{u, v} Theta}
    (hIJ : packedFiniteLikelihoodRelation I J ∧
      ¬ relationUnion packedFiniteSufficiencyRelation packedFiniteConditionalityRelation I J) :
    output Ev I = output Ev J := corollary_BT3_joint_pairs ⟨hS, hC⟩ hIJ

example (P : ParameterPartition Theta) :
    packedLowerTailLRPValueProcedure.{u, v} P ∈
      preservingClass (Set.Icc (0 : ℝ) 1) packedFiniteSufficiencyRelation \
        preservingClass (Set.Icc (0 : ℝ) 1) packedFiniteLikelihoodRelation :=
  (finite_lr_pvalue_separation P).1
example (P : ParameterPartition Theta) :
    ∃ I J : PackedFiniteInferenceBase.{u, v} Theta,
      packedFiniteLikelihoodRelation I J ∧
        packedLowerTailLRPValue P I = 1 / 10 ∧
        packedLowerTailLRPValue P J = 1 / 5 :=
  (finite_lr_pvalue_separation P).2

end FiniteParameterScopeProbe
"""


EVANS_RESULTS_PROBE = r"""
namespace EvansResultsProbe
open VennDiagrams VennDiagrams.Certification.PaperSignature
universe u v w

-- Each application must close the exact result without an Evans hypothesis.
example {I : Type w} (R : StatisticalRelation I) :
    equivalenceClosure R = Relation.ReflTransGen (Relation.SymmGen R) :=
  evans2013_lemma1 R
example {I : Type w} (R T : StatisticalRelation I) :
    equivalenceClosure (relationUnion (equivalenceClosure R) (equivalenceClosure T)) =
      equivalenceClosure (relationUnion R T) := evans2013_lemma2 R T

variable {Theta : Type u} [Fintype Theta] [Nonempty Theta]

example : Equivalence (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) := evans2013_lemma3_packed
example (I : PackedFiniteInferenceBase.{u, v} Theta) :
    letI : Fintype I.Sample := I.sampleFintype
    letI : Nonempty I.Sample := I.sampleNonempty
    FiniteMinimalSufficient I.model (canonicalMinimalSufficient I.likelihoodFamily) :=
  evans2013_lemma4_packed I
example : Equivalence (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) ∧ (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) ≤ (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) := evans2013_lemma5_packed
example : Reflexive (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧ Symmetric (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧ ¬ Transitive (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧ (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ≤ (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) :=
  evans2013_lemma6_packed
example : (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) < equivalenceClosure (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧ equivalenceClosure (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) = (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) :=
  evans2013_theorem7_packed
example : relationUnion (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) ≤ (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) ∧ (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) ≤ equivalenceClosure (relationUnion (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta))) :=
  evans2013_theorem8_packed
example [Nontrivial Theta] :
    relationUnion (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) < (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) ∧ equivalenceClosure (relationUnion (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta))) = (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) :=
  evans2013_theorem9_packed
example [Nontrivial Theta] :
    relationUnion (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) < equivalenceClosure (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) ∧ equivalenceClosure (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) = (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) ∧
      (packedFiniteSufficiencyRelation.{u, v} (Theta := Theta)) < equivalenceClosure (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) := evans2013_corollary10_packed

-- The appendix claims four direct steps in the same inference-base universe.
example (I J : PackedFiniteInferenceBase.{u, v} Theta) (h : (packedFiniteLikelihoodRelation.{u, v} (Theta := Theta)) I J) :
    ∃ M H N : PackedFiniteInferenceBase.{u, v} Theta,
      (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) I M ∧ (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) M H ∧ (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) H N ∧ (packedFiniteConditionalityRelation.{u, v} (Theta := Theta)) N J := evans2013_four_step_chain_packed I J h

end EvansResultsProbe
"""


def compile_probe(declarations: list[str]) -> None:
    probe = (
        f"import {PROJECT_MODULE}\n\n"
        + "\n".join(f"#check {name}" for name in declarations)
        + "\n\n"
        + "\n".join(f"#print axioms {name}" for name in declarations)
        + "\n"
        + FINITE_PARAMETER_SCOPE_PROBE
        + EVANS_RESULTS_PROBE
    )
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", encoding="utf-8", delete=False
    ) as stream:
        stream.write(probe)
        probe_path = Path(stream.name)
    try:
        completed = subprocess.run(
            ["lake", "env", "lean", str(probe_path)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
    finally:
        probe_path.unlink(missing_ok=True)
    if completed.returncode != 0:
        fail("compiled signature probe failed:\n" + completed.stdout.rstrip())
    reports = parse_axiom_reports(completed.stdout)
    if len(reports) != len(declarations):
        fail(
            "compiled signature axiom-report count mismatch: "
            f"expected {len(declarations)}, found {len(reports)}"
        )
    for declaration, actual in reports.items():
        forbidden = sorted(actual - ALLOWED_AXIOMS)
        if forbidden:
            fail(
                f"{declaration} has forbidden dependencies: "
                + ", ".join(forbidden)
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--static-only",
        action="store_true",
        help="check index/source agreement but defer Lean elaboration",
    )
    parser.add_argument(
        "--code-only",
        action="store_true",
        help=argparse.SUPPRESS,
    )
    args = parser.parse_args()

    required_paths = (INDEX, SOURCE)
    for path in required_paths:
        if not path.exists():
            fail(f"missing required path {path}")
    rows = read_rows()
    ids = [row["manuscript_id"].strip() for row in rows]
    if any(not manuscript_id for manuscript_id in ids):
        fail("blank manuscript id")
    if len(ids) != len(set(ids)):
        fail("duplicate paper-signature manuscript id")
    rows_by_id = {manuscript_id: row for manuscript_id, row in zip(ids, rows)}

    signatures: list[str] = []
    declarations: list[str] = []
    for row, manuscript_id in zip(rows, ids):
        kind = row["kind"].strip()
        if kind not in FORMAL_KINDS:
            fail(f"{manuscript_id} has unrecognized formal kind {kind!r}")
        if row["status"].strip() != "compiled":
            fail(f"{manuscript_id} status is not compiled")
        signature = declaration_list(
            row["signature_declaration"], manuscript_id, allow_empty=False
        )[0]
        if not signature.startswith(PROJECT_NAMESPACE):
            fail(
                f"{manuscript_id} signature is not fully qualified in "
                f"{PROJECT_NAMESPACE}: {signature}"
            )
        if signature in signatures:
            fail(f"duplicate signature declaration {signature}")
        signatures.append(signature)
        declarations.append(signature)
        supporting = declaration_list(
            row["library_declarations"], manuscript_id, allow_empty=True
        )
        for declaration in supporting:
            if declaration not in declarations:
                declarations.append(declaration)

    registry = source_registry(rows_by_id)
    expected_registry = {
        manuscript_id: row["signature_declaration"].strip()
        for manuscript_id, row in rows_by_id.items()
    }
    if registry != expected_registry:
        missing = sorted(set(expected_registry.items()) - set(registry.items()))
        unexpected = sorted(set(registry.items()) - set(expected_registry.items()))
        fail(
            "paper-signature source registry mismatch: "
            f"missing={missing}, unexpected={unexpected}"
        )

    print(f"INDEXED_EXACT_PAPER_SIGNATURES={len(signatures)}")
    print("PAPER_SIGNATURE_SOURCE_REGISTRY_OK")
    if args.static_only:
        print("COMPILED_PAPER_SIGNATURE_PROBE_DEFERRED")
        return
    compile_probe(declarations)
    print("ALL_FINITE_PARAMETER_SCOPES_COMPILE_OK")
    print("EXACT_EVANS_2013_RESULTS_COMPILE_OK=10")
    print("EVANS_FOUR_DIRECT_CONDITIONALITY_STEPS_COMPILE_OK")
    print(f"COMPILED_PAPER_SIGNATURES={len(signatures)}")
    print(f"COMPILED_SIGNATURE_AND_LIBRARY_DECLARATIONS={len(declarations)}")
    print("ALL_PAPER_RESULTS_HAVE_EXACT_COMPILED_SIGNATURES_OK")
    print("PAPER_SIGNATURE_DECLARATION_AXIOMS_STANDARD_ONLY_OK")


if __name__ == "__main__":
    main()
