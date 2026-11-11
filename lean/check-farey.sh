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
python3 "$certificate_dir/../tools/check_farey.py" "$@"
