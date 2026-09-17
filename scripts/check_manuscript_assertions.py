#!/usr/bin/env python3
"""Check the assertion index and elaborate every referenced declaration.

Expected MANUSCRIPT_ASSERTION_INDEX.csv schema:
    id,kind,status,lean_declarations

Each indexed assertion has a unique id and a completed status. Lean declarations
are fully qualified names separated by ``|``.
"""

from __future__ import annotations

import argparse
import csv
import re
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
INDEX = ROOT / "MANUSCRIPT_ASSERTION_INDEX.csv"
SOURCE = ROOT / "Lean" / "VennDiagrams"
PROJECT_MODULE = "VennDiagrams"
PROJECT_NAMESPACE = "VennDiagrams."
EXPECTED_COLUMNS = ["id", "kind", "status", "lean_declarations"]
# A result assumed as a formal hypothesis is not a completed certification.
ALLOWED_STATUSES = {"defined", "proved", "section"}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LEAN_NAME = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)


def fail(message: str) -> None:
    raise SystemExit("MANUSCRIPT_ASSERTION_AUDIT_FAILED: " + message)


def strip_lean_comments(source: str) -> str:
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
        fail("unterminated Lean block comment")
    return "".join(out)


def declaration_list(field: str, row_id: str) -> list[str]:
    if not field.strip():
        return []
    pieces = [piece.strip() for piece in field.split("|")]
    if any(not piece for piece in pieces):
        fail(f"{row_id} has an empty declaration between separators")
    for declaration in pieces:
        if LEAN_NAME.fullmatch(declaration) is None:
            fail(f"{row_id} has malformed Lean declaration {declaration!r}")
        if not declaration.startswith(PROJECT_NAMESPACE):
            fail(
                f"{row_id} declaration is not fully qualified in "
                f"{PROJECT_NAMESPACE}: {declaration}"
            )
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
        fail("empty assertion index")
    if any(None in row or any(value is None for value in row.values()) for row in rows):
        fail("malformed CSV row")
    return rows


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


def compile_declaration_probe(declarations: list[str]) -> None:
    probe = (
        f"import {PROJECT_MODULE}\n\n"
        + "\n".join(f"#check {name}" for name in declarations)
        + "\n\n"
        + "\n".join(f"#print axioms {name}" for name in declarations)
        + "\n"
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
        fail("compiled declaration probe failed:\n" + completed.stdout.rstrip())

    reports = parse_axiom_reports(completed.stdout)
    if len(reports) != len(declarations):
        fail(
            "compiled assertion axiom-report count mismatch: "
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
        "--labels-only",
        action="store_true",
        help="run structural checks but defer compiled #check/#print probes",
    )
    parser.add_argument(
        "--code-only",
        action="store_true",
        help=argparse.SUPPRESS,
    )
    args = parser.parse_args()

    rows = read_rows()
    ids = [row["id"].strip() for row in rows]
    if any(not row_id for row_id in ids):
        fail("blank assertion-index id")
    if len(ids) != len(set(ids)):
        fail("duplicate assertion-index id")
    statuses = {row["status"].strip() for row in rows}
    bad_statuses = sorted(statuses - ALLOWED_STATUSES)
    if bad_statuses:
        fail("forbidden/unrecognized status: " + ", ".join(bad_statuses))
    if any(not row["kind"].strip() for row in rows):
        fail("blank assertion kind")

    all_declarations: list[str] = []
    for row, row_id in zip(rows, ids):
        declarations = declaration_list(row["lean_declarations"], row_id)
        if not declarations:
            fail(f"{row_id} has no Lean declaration")
        for declaration in declarations:
            if declaration not in all_declarations:
                all_declarations.append(declaration)

    if not SOURCE.is_dir():
        fail(f"missing Lean source directory {SOURCE.relative_to(ROOT)}")
    source_text = "\n".join(
        strip_lean_comments(path.read_text(encoding="utf-8"))
        for path in sorted(SOURCE.rglob("*.lean"))
    )
    for declaration in all_declarations:
        local_name = declaration.rsplit(".", 1)[-1]
        if re.search(
            rf"(?<![A-Za-z0-9_']){re.escape(local_name)}(?![A-Za-z0-9_'])",
            source_text,
        ) is None:
            fail(f"index references absent source declaration {declaration}")

    print("DECLARATION_SOURCE_REFERENCES_PRESENT_OK")
    print("UNPROVED_ASSERTION_STATUSES=0")
    print(f"MANUSCRIPT_ASSERTIONS={len(rows)}")
    print(f"INDEXED_LEAN_DECLARATIONS={len(all_declarations)}")
    if args.labels_only:
        print("COMPILED_DECLARATION_AND_AXIOM_AUDIT_DEFERRED")
        return

    compile_declaration_probe(all_declarations)
    print(f"COMPILED_ASSERTION_DECLARATIONS={len(all_declarations)}")
    print("COMPILED_DECLARATION_REFERENCES_RESOLVE_OK")
    print("ASSERTION_DECLARATION_AXIOMS_STANDARD_ONLY_OK")


if __name__ == "__main__":
    main()
