#!/usr/bin/env bash
set -Eeuo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
cd "$ROOT"

# Keep the documented flag as an alias for the standalone default.
case "$#" in
  0) ;;
  1)
    if [[ "$1" != "--code-only" ]]; then
      printf 'usage: ./verify.sh [--code-only]\n' >&2
      exit 2
    fi
    ;;
  *)
    printf 'usage: ./verify.sh [--code-only]\n' >&2
    exit 2
    ;;
esac

VERIFICATION_LOG="${VERIFICATION_LOG:-$ROOT/verification.log}"
AXIOM_AUDIT_LOG="${AXIOM_AUDIT_LOG:-$ROOT/axiom-audit.log}"
: > "$VERIFICATION_LOG"
exec > >(tee "$VERIFICATION_LOG") 2>&1
printf 'VERIFICATION_LOG=%s\n' "$VERIFICATION_LOG"
printf 'AXIOM_AUDIT_LOG=%s\n' "$AXIOM_AUDIT_LOG"

if ! command -v python3 >/dev/null 2>&1; then
  printf 'ERROR: Python 3.11 or later is required; python3 was not found.\n' >&2
  exit 1
fi
python3 -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) else "ERROR: Python 3.11 or later is required to run verification.")'
command -v lake >/dev/null
command -v git >/dev/null

bash ./scripts/setup_packages.sh

if [[ ! -L "$ROOT/.lake/packages" && -z "${MATHLIB_CACHE_DIR:-}" ]]; then
  export MATHLIB_CACHE_DIR="$ROOT/.lake/cache/mathlib"
fi
if [[ -n "${MATHLIB_CACHE_DIR:-}" ]]; then
  printf 'MATHLIB_CACHE_DIR=%s\n' "$MATHLIB_CACHE_DIR"
fi

if [[ "${VENN_SKIP_CACHE_DOWNLOAD:-0}" == "1" ]]; then
  printf 'CACHE_DOWNLOAD_SKIPPED=1 (using installed dependencies)\n'
else
  if ! command -v curl >/dev/null 2>&1; then
    printf 'ERROR: curl is required to download the Mathlib binary cache.\n' >&2
    exit 1
  fi
  if ! lake exe cache get; then
    printf 'WARNING: Mathlib binary cache unavailable; building missing dependencies may require additional tools such as Node.js/npm.\n' >&2
  fi
fi

printf '[1/9] Source completeness and numbered structure\n'
python3 scripts/check_full_demonstrations.py
python3 scripts/check_numbered_order.py

printf '[2/9] Static assertion and signature records\n'
python3 scripts/check_manuscript_assertions.py --labels-only
python3 scripts/check_paper_signatures.py --static-only

printf '[3/9] Pinned Lean toolchain\n'
LEAN_VERSION="$(lake env lean --version)"
if [[ "$LEAN_VERSION" != *'version 4.32.2'* ]]; then
  printf 'ERROR: expected Lean 4.32.2, got %s\n' "$LEAN_VERSION" >&2
  exit 1
fi
printf 'LEAN_VERSION=%s\n' "${LEAN_VERSION%%$'\n'*}"

printf '[4/9] Pinned dependency revisions\n'
python3 scripts/check_dependency_revisions.py

printf '[5/9] Sequential numbered build\n'
while IFS=$'\t' read -r step file module; do
  printf 'BUILDING_S%02d=%s (%s)\n' "$step" "$file" "$module"
  lake build "$module"
done < <(
  python3 -c \
    'import csv; rows=csv.DictReader(open("NUMBERED_MODULE_ORDER.csv", encoding="utf-8")); [print(r["step"], r["file"], r["module"], sep="\t") for r in rows]'
)
printf 'ALL_NUMBERED_MODULES_ELABORATE_OK\n'

printf '[6/9] Unified root build\n'
lake build VennDiagrams
printf 'UNIFIED_ROOT_BUILD_OK\n'

printf '[7/9] Complete compiled declaration catalogue\n'
python3 scripts/check_lean_declaration_catalogue.py

printf '[8/9] Exact promoted-declaration axiom audit\n'
: > "$AXIOM_AUDIT_LOG"
lake env lean Lean/VennDiagrams/S07_FinalAxiomAudit.lean 2>&1 | tee "$AXIOM_AUDIT_LOG"
python3 scripts/check_axiom_whitelist.py "$AXIOM_AUDIT_LOG" AXIOM_WHITELIST.csv

printf '[9/9] Compiled assertion records and exact signatures\n'
python3 scripts/check_manuscript_assertions.py
python3 scripts/check_paper_signatures.py

printf 'FULL_FOUNDATIONAL_VERIFICATION_OK\n'
printf 'CODE_ONLY_REPLICATION_PROFILE_OK\n'
printf 'EXACT_PAPER_SIGNATURES_COMPILE_OK\n'
printf 'LEAN_VERIFICATION_WITH_STANDARD_MATHLIB_AXIOMS_ONLY_OK\n'
