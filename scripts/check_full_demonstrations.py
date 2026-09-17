#!/usr/bin/env python3
"""Reject proof holes and declaration-level escape hatches in Lean sources."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "Lean"


def strip_comments(source: str) -> str:
    """Remove nested Lean comments while preserving source line numbers."""
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
        raise ValueError("unterminated block comment")
    return "".join(out)


DECLARATION_ESCAPE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:axioms?|constants?|opaque)\b"
)


def findings() -> tuple[list[str], list[tuple[Path, list[tuple[int, str, str]]]]]:
    errors: list[str] = []
    results: list[tuple[Path, list[tuple[int, str, str]]]] = []
    paths = sorted(SOURCE.rglob("*.lean"))
    if not paths:
        return ["no Lean source files found"], results
    for path in paths:
        try:
            body = strip_comments(path.read_text(encoding="utf-8"))
        except ValueError as exc:
            errors.append(f"{path.relative_to(ROOT).as_posix()}: {exc}")
            continue
        hits: list[tuple[int, str, str]] = []
        for line_no, line in enumerate(body.splitlines(), 1):
            checks = [
                (r"\bsorry\b", "PROOF_HOLE", "sorry"),
                (r"\badmit\b", "PROOF_HOLE", "admit"),
                (r"\bsorryAx\b", "DIRECT_SORRYAX", "sorryAx"),
                (r"\bnative_decide\b", "NATIVE_DECIDE", "native_decide"),
            ]
            for pattern, kind, text in checks:
                if re.search(pattern, line):
                    hits.append((line_no, kind, text))
            if DECLARATION_ESCAPE.search(line):
                keyword = DECLARATION_ESCAPE.search(line)
                assert keyword is not None
                hits.append((line_no, "DECLARATION_ESCAPE", line.strip()))
        if hits:
            results.append((path, hits))
    return errors, results


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--report-only",
        action="store_true",
        help="report failures without returning a nonzero status",
    )
    args = parser.parse_args()
    errors, result = findings()
    if errors or result:
        print("FULL_DEMONSTRATIONS_INCOMPLETE")
        for error in errors:
            print(f"  SOURCE_ERROR: {error}")
        for path, hits in result:
            print(path.relative_to(ROOT).as_posix())
            for line, kind, text in hits:
                print(f"  {kind} line {line}: {text}")
        if not args.report_only:
            raise SystemExit(2)
    else:
        print("FULL_DEMONSTRATION_SOURCE_AUDIT_OK")
        print(
            "NO_SORRY_ADMIT_SORRYAX_NATIVE_DECIDE_"
            "CUSTOM_AXIOM_CONSTANT_OR_OPAQUE_OK"
        )


if __name__ == "__main__":
    main()
