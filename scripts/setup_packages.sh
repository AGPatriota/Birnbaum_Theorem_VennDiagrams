#!/usr/bin/env bash
set -Eeuo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
LOCAL_PACKAGES="$ROOT/.lake/packages"
MODE="${LEAN_PACKAGES_MODE:-}"
SHARED_PACKAGES="${LEAN_SHARED_PACKAGES:-$HOME/.cache/lean/shared-packages}"

canonical() {
  readlink -f -- "$1"
}

# New checkouts are self-contained. Preserve an existing shared-store setup
# unless the caller explicitly selects a different mode.
if [[ -z "$MODE" ]]; then
  if [[ -n "${LEAN_SHARED_PACKAGES:-}" ]]; then
    MODE=shared
  elif [[ -L "$LOCAL_PACKAGES" ]]; then
    MODE=shared
    SHARED_PACKAGES="$(canonical "$LOCAL_PACKAGES")"
  else
    MODE=local
  fi
fi

case "$MODE" in
  shared|local) ;;
  *)
    printf 'ERROR: LEAN_PACKAGES_MODE must be shared or local; got %s\n' "$MODE" >&2
    exit 2
    ;;
esac

mkdir -p "$ROOT/.lake"

if [[ "$MODE" == local ]]; then
  if [[ -L "$LOCAL_PACKAGES" ]]; then
    printf 'ERROR: %s is a shared-store symlink. Remove it before selecting local mode.\n' \
      "$LOCAL_PACKAGES" >&2
    exit 2
  fi
  mkdir -p "$LOCAL_PACKAGES"
  printf 'PACKAGE_STORE_MODE=local\n'
  printf 'PACKAGES_RESOLVED=%s\n' "$(canonical "$LOCAL_PACKAGES")"
  exit 0
fi

if [[ "$SHARED_PACKAGES" != /* ]]; then
  printf 'ERROR: LEAN_SHARED_PACKAGES must be an absolute path; got %s\n' \
    "$SHARED_PACKAGES" >&2
  exit 2
fi

mkdir -p "$SHARED_PACKAGES"

if [[ -L "$LOCAL_PACKAGES" ]]; then
  if [[ "$(canonical "$LOCAL_PACKAGES")" != "$(canonical "$SHARED_PACKAGES")" ]]; then
    printf 'ERROR: %s points to %s, not %s.\n' \
      "$LOCAL_PACKAGES" "$(canonical "$LOCAL_PACKAGES")" \
      "$(canonical "$SHARED_PACKAGES")" >&2
    exit 2
  fi
elif [[ -e "$LOCAL_PACKAGES" ]]; then
  printf 'ERROR: %s is a real local path; refusing to overwrite it.\n' \
    "$LOCAL_PACKAGES" >&2
  printf 'Move that directory to a backup, then run this script again.\n' >&2
  exit 2
else
  ln -s "$SHARED_PACKAGES" "$LOCAL_PACKAGES"
fi

printf 'PACKAGE_STORE_MODE=shared\n'
printf 'PACKAGES_LINK=%s\n' "$(readlink "$LOCAL_PACKAGES")"
printf 'PACKAGES_RESOLVED=%s\n' "$(canonical "$LOCAL_PACKAGES")"
printf 'SHARED_PACKAGES_READY_OK\n'
