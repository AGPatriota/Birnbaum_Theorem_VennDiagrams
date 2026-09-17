#!/usr/bin/env python3
"""Compare terminal #print reports with the exact promoted-theorem whitelist.

Expected AXIOM_WHITELIST.csv schema:
    declaration,native_evaluation_axiom

The second column must be blank. The declaration set must agree exactly with
the union of signature/support declarations in PAPER_SIGNATURE_INDEX.csv and
with S07_FinalAxiomAudit.lean.
"""

from __future__ import annotations

import argparse
import csv
import re
from pathlib import Path


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SIGNATURE_COLUMNS = [
    "manuscript_id",
    "kind",
    "signature_declaration",
    "status",
    "library_declarations",
]
WHITELIST_COLUMNS = ["declaration", "native_evaluation_axiom"]
TERMINAL = Path("Lean/VennDiagrams/S07_FinalAxiomAudit.lean")


def fail(message: str) -> None:
    raise SystemExit("AXIOM_WHITELIST_AUDIT_FAILED: " + message)


def strip_comments(source: str) -> str:
    out: list[str] = []
    index = 0
    depth = 0
    while index < len(source):
        if source.startswith("/-", index):
            depth += 1
            index += 2
            continue
        if depth and source.startswith("-/", index):
            depth -= 1
            index += 2
            continue
        if depth:
            if source[index] == "\n":
                out.append("\n")
            index += 1
            continue
        if source.startswith("--", index):
            newline = source.find("\n", index)
            if newline < 0:
                break
            out.append("\n")
            index = newline + 1
            continue
        out.append(source[index])
        index += 1
    if depth:
        fail("unterminated block comment in terminal audit")
    return "".join(out)


def parse_reports(output: str) -> dict[str, set[str]]:
    pattern = re.compile(
        r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]"
        r"|does not depend on any axioms)",
        flags=re.DOTALL,
    )
    reports: dict[str, set[str]] = {}
    for match in pattern.finditer(output):
        declaration = match.group(1)
        if declaration in reports:
            fail(f"duplicate #print axioms report for {declaration}")
        body = match.group(2) or ""
        reports[declaration] = {
            item.strip()
            for item in body.replace("\\n", " ").replace("\n", " ").split(",")
            if item.strip()
        }
    return reports


def read_whitelist(path: Path) -> dict[str, set[str]]:
    with path.open(encoding="utf-8", newline="") as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames != WHITELIST_COLUMNS:
            fail("whitelist columns must be " + ",".join(WHITELIST_COLUMNS))
        rows = list(reader)
    if not rows:
        fail("empty whitelist")
    if any(None in row or any(value is None for value in row.values()) for row in rows):
        fail("malformed whitelist CSV row")
    whitelist: dict[str, set[str]] = {}
    for row in rows:
        declaration = row["declaration"].strip()
        if not declaration:
            fail("blank declaration in whitelist")
        if declaration in whitelist:
            fail(f"duplicate whitelist declaration {declaration}")
        extra_axiom = row["native_evaluation_axiom"].strip()
        if extra_axiom:
            fail(f"{declaration} designates forbidden extra dependency {extra_axiom}")
        whitelist[declaration] = ALLOWED_AXIOMS
    return whitelist


def read_signatures(path: Path) -> set[str]:
    """Return every exact signature and supporting declaration named by the index."""
    with path.open(encoding="utf-8", newline="") as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames != SIGNATURE_COLUMNS:
            fail("paper-signature columns must be " + ",".join(SIGNATURE_COLUMNS))
        rows = list(reader)
    if not rows:
        fail("empty paper-signature index")
    declarations: list[str] = []
    for row in rows:
        manuscript_id = row["manuscript_id"].strip()
        if row["status"].strip() != "compiled":
            fail(f"paper signature is not compiled: {manuscript_id}")
        signature = row["signature_declaration"].strip()
        if not signature:
            fail(f"compiled paper signature is blank: {manuscript_id}")
        declarations.append(signature)
        supporting = [
            item.strip()
            for item in row["library_declarations"].split("|")
            if item.strip()
        ]
        declarations.extend(supporting)
    return set(declarations)


def inventory_delta(reference: set[str], label: str, actual: set[str]) -> str:
    return (
        f"{label} missing={sorted(reference - actual)} "
        f"extra={sorted(actual - reference)}"
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Check every promoted theorem against an exact axiom whitelist."
    )
    parser.add_argument("output", type=Path, help="complete Lean #print axioms output")
    parser.add_argument("whitelist", type=Path, help="CSV declaration whitelist")
    args = parser.parse_args()

    for path in (args.output, args.whitelist):
        if not path.is_file():
            fail(f"missing required file {path}")
    root = args.whitelist.resolve().parent
    signature_index = root / "PAPER_SIGNATURE_INDEX.csv"
    terminal_path = root / TERMINAL
    for path in (signature_index, terminal_path):
        if not path.is_file():
            fail(f"missing promotion inventory source {path}")

    whitelist = read_whitelist(args.whitelist)
    reference = set(whitelist)
    paper_inventory = read_signatures(signature_index)
    terminal_body = strip_comments(terminal_path.read_text(encoding="utf-8"))
    terminal_list = re.findall(
        r"(?m)^\s*#print\s+axioms\s+([^\s]+)\s*$", terminal_body
    )
    if len(terminal_list) != len(set(terminal_list)):
        fail("duplicate #print axioms target in terminal audit source")
    terminal = set(terminal_list)
    reports = parse_reports(args.output.read_text(encoding="utf-8"))
    report_names = set(reports)

    inventories = [
        ("paper signature/support declarations", paper_inventory),
        ("terminal audit", terminal),
        ("compiled reports", report_names),
    ]
    disagreements = [
        inventory_delta(reference, label, actual)
        for label, actual in inventories
        if actual != reference
    ]
    if disagreements:
        fail("promotion inventories disagree: " + "; ".join(disagreements))

    for declaration, actual in reports.items():
        forbidden = sorted(actual - whitelist[declaration])
        if forbidden:
            fail(
                f"{declaration} has forbidden dependencies: "
                + ", ".join(forbidden)
            )

    print(f"PROMOTED_THEOREM_AXIOM_REPORTS={len(reports)}")
    print("FORBIDDEN_EXTRA_AXIOM_DEPENDENCIES=0")
    print("PROMOTED_THEOREM_MANIFEST_EXACT_OK")
    print("EXACT_AXIOM_WHITELIST_OK")
    print("ONLY_PROPEXT_CLASSICAL_CHOICE_QUOT_SOUND_PERMITTED_OK")


if __name__ == "__main__":
    main()
