#!/usr/bin/env python3
"""Validate the generated declaration catalogue against source and Lean."""

from __future__ import annotations

import csv
import re
import subprocess
import tempfile
from pathlib import Path

from check_axiom_whitelist import ALLOWED_AXIOMS, parse_reports


ROOT = Path(__file__).resolve().parents[1]
CSV_PATH = ROOT / "LEAN_DECLARATION_CATALOGUE.csv"
SOURCE_DIR = ROOT / "Lean" / "VennDiagrams"
FIELDS = [
    "tracking_id", "file_number", "module", "source_path", "source_line",
    "lean_kind", "source_name", "fqn", "source_header",
]


def fail(message: str) -> None:
    raise SystemExit("LEAN_DECLARATION_CATALOGUE_AUDIT_FAILED: " + message)


DECL_RE = re.compile(
    r"^\s*(?:@\[[^]]+\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?"
    r"(abbrev|def|structure|inductive|theorem|lemma|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_']*)\s*$")
SECTION_RE = re.compile(r"^\s*section(?:\s+([A-Za-z_][A-Za-z0-9_']*))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_']*))?\s*$")


def authored_declarations(path: Path) -> list[dict[str, str]]:
    scopes: list[tuple[str, str | None]] = []
    rows: list[dict[str, str]] = []
    counters = {"D": 0, "R": 0}
    module_id = path.name[:3]
    module = f"VennDiagrams.{path.stem}"

    for line_number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if match := NAMESPACE_RE.match(raw):
            scopes.append(("namespace", match.group(1)))
            continue
        if match := SECTION_RE.match(raw):
            scopes.append(("section", match.group(1)))
            continue
        if match := END_RE.match(raw):
            name = match.group(1)
            if not scopes:
                continue
            if name is None:
                scopes.pop()
            else:
                for index in range(len(scopes) - 1, -1, -1):
                    if scopes[index][1] == name:
                        del scopes[index:]
                        break
            continue
        match = DECL_RE.match(raw)
        if not match:
            continue
        kind, source_name = match.groups()
        namespaces = [name for scope_kind, name in scopes
                      if scope_kind == "namespace" and name]
        if "." in source_name:
            fqn = ".".join([*namespaces, source_name])
        else:
            fqn = ".".join([*namespaces, source_name])
        result_kind = "R" if kind in {"theorem", "lemma"} else "D"
        counters[result_kind] += 1
        rows.append({
            "tracking_id": f"{module_id}.{result_kind}{counters[result_kind]:03d}",
            "file_number": module_id,
            "module": module,
            "source_path": str(path.relative_to(ROOT / "Lean")),
            "source_line": str(line_number),
            "lean_kind": kind,
            "source_name": source_name,
            "fqn": fqn,
            "source_header": raw.strip(),
        })
    return rows


def main() -> None:
    if not CSV_PATH.is_file():
        fail(f"missing {CSV_PATH.name}")
    with CSV_PATH.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames != FIELDS:
            fail("unexpected CSV schema")
        actual = list(reader)

    expected = []
    for path in sorted(SOURCE_DIR.glob("S*.lean")):
        expected.extend(authored_declarations(path))
    if actual != expected:
        fail("CSV does not match the Lean sources")

    ids = [row["tracking_id"] for row in actual]
    fqns = [row["fqn"] for row in actual]
    if len(ids) != len(set(ids)):
        fail("duplicate tracking id")
    if len(fqns) != len(set(fqns)):
        fail("duplicate fully qualified declaration")

    probe = "import VennDiagrams\n" + "".join(
        f"#check {name}\n#print axioms {name}\n" for name in fqns
    )
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", encoding="utf-8", dir=ROOT, delete=False
    ) as handle:
        handle.write(probe)
        probe_path = Path(handle.name)
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(probe_path)], cwd=ROOT,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
    finally:
        probe_path.unlink(missing_ok=True)
    if result.returncode:
        print(result.stdout)
        fail("at least one catalogued FQN does not elaborate")

    reports = parse_reports(result.stdout)
    if set(reports) != set(fqns):
        fail("compiled axiom reports do not match the complete catalogue")
    for name, axioms in reports.items():
        forbidden = sorted(axioms - ALLOWED_AXIOMS)
        if forbidden:
            fail(f"{name} has forbidden axiom dependencies: {', '.join(forbidden)}")

    print(f"LEAN_DECLARATION_CATALOGUE_ENTRIES={len(actual)}")
    print("LEAN_DECLARATION_CATALOGUE_SOURCE_EXACT_OK")
    print("LEAN_DECLARATION_CATALOGUE_IDENTIFIERS_UNIQUE_OK")
    print("LEAN_DECLARATION_CATALOGUE_FQNS_ELABORATE_OK")
    print(f"CATALOGUED_DECLARATION_AXIOM_REPORTS={len(reports)}")
    print("ALL_CATALOGUED_DECLARATION_AXIOMS_STANDARD_ONLY_OK")


if __name__ == "__main__":
    main()
