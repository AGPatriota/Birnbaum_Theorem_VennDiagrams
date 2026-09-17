#!/usr/bin/env python3
"""Check the toolchain and every materialized Git dependency against the pins."""

from __future__ import annotations

import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.32.2"
EXPECTED_MATHLIB_REV = "905b95818eb32af7874a58b427f50c1711a5e96c"


def main() -> None:
    errors: list[str] = []
    manifest_path = ROOT / "lake-manifest.json"
    lakefile_path = ROOT / "lakefile.toml"
    toolchain_path = ROOT / "lean-toolchain"

    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except Exception as exc:
        print(f"DEPENDENCY_REVISION_ERROR=invalid lake-manifest.json: {exc}", file=sys.stderr)
        raise SystemExit(1)
    try:
        with lakefile_path.open("rb") as stream:
            lakefile = tomllib.load(stream)
    except Exception as exc:
        print(f"DEPENDENCY_REVISION_ERROR=invalid lakefile.toml: {exc}", file=sys.stderr)
        raise SystemExit(1)

    try:
        toolchain = toolchain_path.read_text(encoding="utf-8").strip()
    except OSError as exc:
        errors.append(f"cannot read lean-toolchain: {exc}")
        toolchain = ""
    if toolchain != EXPECTED_TOOLCHAIN:
        errors.append(
            f"lean-toolchain is {toolchain!r}, expected {EXPECTED_TOOLCHAIN!r}"
        )

    if manifest.get("packagesDir") != ".lake/packages":
        errors.append("lake-manifest packagesDir is not .lake/packages")

    manifest_packages = manifest.get("packages")
    if not isinstance(manifest_packages, list):
        errors.append("lake-manifest packages is not a list")
        manifest_packages = []
    manifest_mathlib = [
        entry for entry in manifest_packages
        if isinstance(entry, dict) and entry.get("name") == "mathlib"
    ]
    if len(manifest_mathlib) != 1:
        errors.append("lake-manifest must contain exactly one mathlib dependency")
    elif manifest_mathlib[0].get("rev") != EXPECTED_MATHLIB_REV:
        errors.append(
            "lake-manifest mathlib revision is "
            f"{manifest_mathlib[0].get('rev')!r}, expected {EXPECTED_MATHLIB_REV}"
        )

    requires = lakefile.get("require", [])
    lake_mathlib = [
        entry for entry in requires
        if isinstance(entry, dict) and entry.get("name") == "mathlib"
    ] if isinstance(requires, list) else []
    if len(lake_mathlib) != 1:
        errors.append("lakefile.toml must contain exactly one mathlib requirement")
    elif lake_mathlib[0].get("rev") != EXPECTED_MATHLIB_REV:
        errors.append(
            "lakefile.toml mathlib revision is "
            f"{lake_mathlib[0].get('rev')!r}, expected {EXPECTED_MATHLIB_REV}"
        )

    packages_root = (ROOT / ".lake" / "packages").resolve()
    if not packages_root.is_dir():
        errors.append(f"package directory is missing: {packages_root}")

    checked: list[tuple[str, str]] = []
    for entry in manifest_packages:
        if not isinstance(entry, dict) or entry.get("type") != "git":
            continue
        name = entry.get("name")
        expected = entry.get("rev")
        if not isinstance(name, str) or not name:
            errors.append("git dependency has no valid name")
            continue
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{40}", expected):
            errors.append(f"{name}: manifest revision is not a full Git commit")
            continue
        package = packages_root / name
        try:
            resolved = package.resolve(strict=True)
            resolved.relative_to(packages_root)
        except (FileNotFoundError, ValueError):
            errors.append(f"{name}: package directory is missing or escapes the package store")
            continue
        process = subprocess.run(
            ["git", "-C", str(resolved), "rev-parse", "--verify", "HEAD"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
        actual = process.stdout.strip()
        if process.returncode != 0:
            errors.append(f"{name}: cannot read Git HEAD: {process.stderr.strip()}")
        elif actual != expected:
            errors.append(f"{name}: checkout {actual} differs from manifest {expected}")
        else:
            checked.append((name, expected))

    if errors:
        print(
            "\n".join(f"DEPENDENCY_REVISION_ERROR={error}" for error in errors),
            file=sys.stderr,
        )
        raise SystemExit(1)
    if not checked:
        print("DEPENDENCY_REVISION_ERROR=no Git dependencies were checked", file=sys.stderr)
        raise SystemExit(1)

    print(f"LEAN_TOOLCHAIN_PIN_OK={EXPECTED_TOOLCHAIN}")
    print(f"MATHLIB_PIN_OK={EXPECTED_MATHLIB_REV}")
    print(f"PINNED_DEPENDENCY_CHECKOUTS_OK={len(checked)}")
    for name, revision in sorted(checked):
        print(f"PINNED_DEPENDENCY={name}:{revision}")


if __name__ == "__main__":
    main()
