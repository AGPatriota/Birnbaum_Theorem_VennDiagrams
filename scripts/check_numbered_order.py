#!/usr/bin/env python3
"""Validate the numbered source inventory and its import dependency order.

Expected NUMBERED_MODULE_ORDER.csv schema:
    step,file,module,purpose

`file` is relative to Lean/, and `module` is its dotted Lean module name.
"""

from __future__ import annotations

import csv
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOT = ROOT / "Lean"
PROJECT = "VennDiagrams"
INDEX = ROOT / "NUMBERED_MODULE_ORDER.csv"
EXPECTED_COLUMNS = ["step", "file", "module", "purpose"]


def fail(message: str) -> None:
    raise SystemExit("NUMBERED_ORDER_AUDIT_FAILED: " + message)


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
                index = len(source)
                continue
            out.append("\n")
            index = newline + 1
            continue
        out.append(source[index])
        index += 1
    if depth:
        fail("unterminated block comment")
    return "".join(out)


def read_rows() -> list[dict[str, str]]:
    if not INDEX.is_file():
        fail(f"missing {INDEX.name}")
    with INDEX.open(encoding="utf-8", newline="") as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames != EXPECTED_COLUMNS:
            fail("columns must be " + ",".join(EXPECTED_COLUMNS))
        rows = list(reader)
    if not rows:
        fail("empty numbered-module index")
    if any(None in row or any(value is None for value in row.values()) for row in rows):
        fail("malformed CSV row")
    return rows


def main() -> None:
    rows = read_rows()
    try:
        steps = [int(row["step"].strip()) for row in rows]
    except ValueError:
        fail("every step must be an integer")
    if steps != list(range(1, len(rows) + 1)):
        fail(f"numbering is not contiguous: {steps}")

    files = [row["file"].strip() for row in rows]
    modules = [row["module"].strip() for row in rows]
    if any(not item for item in files + modules):
        fail("blank file or module")
    if len(files) != len(set(files)):
        fail("duplicate numbered filename")
    if len(modules) != len(set(modules)):
        fail("duplicate numbered module")

    module_step = {module: step for module, step in zip(modules, steps)}
    indexed_paths: set[str] = set()
    for row, step, file_name, module in zip(rows, steps, files, modules):
        path = SOURCE_ROOT / file_name
        try:
            path.resolve(strict=True).relative_to(SOURCE_ROOT.resolve())
        except (FileNotFoundError, ValueError):
            fail(f"missing or escaping source path {file_name}")
        if not path.is_file():
            fail(f"not a source file: {file_name}")
        indexed_paths.add(path.relative_to(SOURCE_ROOT).as_posix())
        if not path.name.startswith(f"S{step:02d}_"):
            fail(f"wrong numbered filename {path.name} for step {step}")
        expected_module = path.relative_to(SOURCE_ROOT).with_suffix("").as_posix().replace("/", ".")
        if module != expected_module:
            fail(
                f"module/file mismatch for step {step}: "
                f"expected {expected_module}, found {module}"
            )
        if not module.startswith(PROJECT + "."):
            fail(f"module is outside {PROJECT}: {module}")

        body = strip_comments(path.read_text(encoding="utf-8"))
        imports: list[str] = []
        seen_content = False
        for line_no, raw in enumerate(body.splitlines(), 1):
            line = raw.strip()
            if not line:
                continue
            if line.startswith("import "):
                if seen_content:
                    fail(f"{file_name}:{line_no}: import after content")
                imported = line.split(None, 1)[1].strip()
                if not re.fullmatch(
                    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*",
                    imported,
                ):
                    fail(f"{file_name}:{line_no}: malformed import {imported!r}")
                imports.append(imported)
            else:
                seen_content = True
        if not imports:
            fail(f"{file_name}: no imports")
        for imported in imports:
            if not imported.startswith(PROJECT + "."):
                continue
            numbered = re.search(r"(?:^|\.)S\d+_[A-Za-z0-9_']+$", imported)
            if numbered is None:
                continue
            if imported not in module_step:
                fail(f"{file_name}: unknown local numbered import {imported}")
            if module_step[imported] >= step:
                fail(
                    f"S{step:02d} imports non-earlier "
                    f"S{module_step[imported]:02d}: {imported}"
                )

    discovered = {
        path.relative_to(SOURCE_ROOT).as_posix()
        for path in (SOURCE_ROOT / PROJECT).rglob("S[0-9][0-9]_*.lean")
    }
    missing_from_index = sorted(discovered - indexed_paths)
    nonexistent_indexed = sorted(indexed_paths - discovered)
    if missing_from_index or nonexistent_indexed:
        fail(
            "numbered source inventory mismatch: "
            f"unindexed={missing_from_index}, nonnumbered_index_entries={nonexistent_indexed}"
        )

    root_path = SOURCE_ROOT / f"{PROJECT}.lean"
    if not root_path.is_file():
        fail(f"missing unified root Lean/{PROJECT}.lean")
    root_body = strip_comments(root_path.read_text(encoding="utf-8"))
    root_imports = re.findall(r"(?m)^\s*import\s+(\S+)\s*$", root_body)
    numbered_root_imports = [
        imported
        for imported in root_imports
        if imported.startswith(PROJECT + ".")
        and re.search(r"(?:^|\.)S\d+_[A-Za-z0-9_']+$", imported)
    ]
    if numbered_root_imports != modules:
        fail(
            f"{PROJECT}.lean does not import every numbered module in CSV order; "
            f"expected={modules}, actual={numbered_root_imports}"
        )

    print("UNIFIED_SINGLE_SOURCE_DIRECTORY_OK")
    print(f"GLOBAL_NUMBERING_S01_S{len(rows):02d}_OK")
    print(f"NUMBERED_MODULES={len(rows)}")
    print("NUMBERED_IMPORT_ORDER_OK")


if __name__ == "__main__":
    main()
