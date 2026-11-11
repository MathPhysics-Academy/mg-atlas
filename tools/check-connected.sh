#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
case "${1:-}" in
  psl13) label='PSL(2,13)' ;;
  psl17) label='PSL(2,17)' ;;
  a7) label='A7' ;;
  *) echo 'Usage: bash tools/check-connected.sh {psl13|psl17|a7}' >&2; exit 2 ;;
esac
slug="$1"
out=".ci-runs/$slug"
if [[ -e "$out" ]]; then
  echo "Output already exists: $out. Move or remove it before a fresh run." >&2
  exit 1
fi
gap_bin="${GAP_EXECUTABLE:-gap}"
mkdir -p "$out/input" "$out/actions"
export PYTHONDONTWRITEBYTECODE=1

"$gap_bin" -q -b --quitonbreak "gap/run-table5-$slug.g" > "$out/enumeration.log" 2>&1
python3 - "$out/enumeration.log" "$out/input/gap-table5-$slug.jsonl" "$label" <<'PY'
import json, sys
from pathlib import Path
records = [json.loads(s[7:]) for s in Path(sys.argv[1]).read_text().splitlines() if s.startswith('@@JSON ')]
if len(records) != 1 or records[0]['group'] != sys.argv[3] or not records[0]['components']:
    raise SystemExit('Missing or unexpected GAP enumeration output')
Path(sys.argv[2]).write_text(json.dumps(records[0]) + '\n')
PY

python3 tools/export-table5-farey.py --groups "$slug" \
  --input-dir "$out/input" --output-dir "$out/farey-data"
"$gap_bin" -q -b --quitonbreak "$out/farey-data/export.g" > "$out/farey.log" 2>&1
python3 - "$out/farey.log" "$out/farey-data" <<'PY'
import json, sys
from pathlib import Path
out = Path(sys.argv[2])
records = [json.loads(s[7:]) for s in Path(sys.argv[1]).read_text().splitlines() if s.startswith('@@JSON ')]
expected = json.loads((out / 'inputs.json').read_text())
if len(records) != len(expected) or {r['name'] for r in records} != {r['name'] for r in expected}:
    raise SystemExit('Incomplete GAP Farey output')
(out / 'exports.json').write_text(json.dumps(records) + '\n')
PY

python3 tools/generate_more.py --input "$out/input/gap-table5-$slug.jsonl" \
  --output-dir "$out/actions" --summary-output "$out/action-inputs.json"
python3 tools/generate_farey.py --data-dir "$out/farey-data" \
  --output-dir "$out/farey-certificates" --group "$label"
python3 tools/bundle_table5_pilot.py --action-dir "$out/actions" \
  --farey-dir "$out/farey-certificates" --output-dir "$out/bundles"
bash lean/check-farey.sh --source-dir "$out/bundles" \
  --results-dir "$out/lean-results" --jobs 1
