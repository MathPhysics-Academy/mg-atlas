#!/bin/bash
set -euo pipefail

certificate_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [[ -z "${LEAN_ROOT:-}" ]]; then
  for lean_env in "${MG_ATLAS_LEAN_ENV:-}" \
    "$certificate_dir/../../lean/env.sh" \
    "$certificate_dir/../../../lean/env.sh"; do
    if [[ -f "$lean_env" ]]; then
      source "$lean_env"
      break
    fi
  done
fi
if [[ -z "${LEAN_ROOT:-}" ]]; then
  echo "Set LEAN_ROOT or MG_ATLAS_LEAN_ENV to your external Lean setup." >&2
  exit 1
fi

# Reuse the external-drive Mathlib checkout and its compiled dependencies.
# lake env does not build Mathlib or download packages.
cd "$LEAN_ROOT/mathlib4"
case "${1:-all}" in
  all|baseline)
    lake env lean "$certificate_dir/S4Certificate.lean"
    lake env lean "$certificate_dir/BaselineCertificates.lean"
    ;;
  more) ;;
  *) echo "Usage: bash lean/check.sh [all|baseline|more] [more-certificate filenames]" >&2; exit 2 ;;
esac
if [[ "${1:-all}" != baseline ]]; then
  if [[ $# -gt 0 ]]; then shift; fi
  python3 "$certificate_dir/../tools/check_more.py" "$@"
fi
