#!/usr/bin/env python3
"""Compile action certificates and record verification results."""
import hashlib
import argparse
import json
import os
import re
import subprocess
import time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]

def write_status(manifest, log_dir):
    checked = []
    for entry in manifest:
        receipt = log_dir / Path(entry['file']).with_suffix('.json')
        if receipt.exists():
            record = json.loads(receipt.read_text())
            if record['passed'] and record['sha256'] == entry['sha256']:
                checked.append(record)
    status = {
        'complete': len(checked) == len(manifest),
        'checked_groups': len(checked),
        'total_groups': len(manifest),
        'checked_components': sum((r['components'] for r in checked)),
        'checked_obstructions': sum((r['obstructions'] for r in checked)),
        'checked_declarations': sum((r['declarations'] for r in checked)),
        'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'groups': checked,
    }
    (ROOT / 'results/lean-more-status.json').write_text(json.dumps(status, indent=2) + '\n')
    lines = ['# Additional Lean certificate checks', '', (f"Status: {'complete' if status['complete'] else 'in progress'}. "
             f"{status['checked_groups']}/{status['total_groups']} groups; "
             f"{status['checked_components']} components; "
             f"{status['checked_obstructions']} obstruction witnesses."), '', 'All successful files passed the axiom audit allowing only `propext`,', '`Classical.choice`, and `Quot.sound`. Computation uses `decide +kernel`.', '', '[Certificate scope](../lean/README.md)', '', '| Group | Components | Largest degree | Obstructions | Declarations | Seconds |', '|---|---:|---:|---:|---:|---:|']
    for r in checked:
        source_link = f"[{r['group']}](../lean/more/{r['file']})"
        lines.append((f"| {source_link} | {r['components']} | {r['max_degree']} | "
                     f"{r['obstructions']} | {r['declarations']} | {r['seconds']} |"))
    (ROOT / 'results/lean-more-summary.md').write_text('\n'.join(lines) + '\n')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--resume', action='store_true', help='reuse successful receipts for identical sources')
    parser.add_argument('files', nargs='*', help='optional certificate filenames')
    args = parser.parse_args()
    lean_root = Path(os.environ['LEAN_ROOT'])
    all_manifest = json.loads((ROOT / 'lean/more/manifest.json').read_text())
    manifest = all_manifest
    if args.files:
        selected = set(args.files)
        manifest = [entry for entry in manifest if entry['file'] in selected]
        if len(manifest) != len(selected):
            raise SystemExit('Unknown certificate filename')
    log_dir = ROOT / 'results/lean-more'
    log_dir.mkdir(exist_ok=True)
    records = []
    for entry in manifest:
        path = ROOT / 'lean/more' / entry['file']
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        assert digest == entry['sha256'], f'Source changed: {path}'
        receipt_path = log_dir / path.with_suffix('.json').name
        if args.resume and receipt_path.exists():
            receipt = json.loads(receipt_path.read_text())
            if receipt['passed'] and receipt['sha256'] == digest:
                records.append(receipt)
                print(f"Reusing checked source: {entry['group']}", flush=True)
                continue
        print((f"Checking {entry['group']}: {entry['components']} components, "
              f"largest degree {entry['max_degree']}"), flush=True)
        log_path = log_dir / path.with_suffix('.log').name
        start = time.monotonic()
        with log_path.open('w') as log:
            result = subprocess.run(
                ['lake', 'env', 'lean', str(path)],
                cwd=lean_root / 'mathlib4',
                stdout=log,
                stderr=subprocess.STDOUT,
            )
        output = log_path.read_text()
        audit = re.search('Axiom audit passed for all (\\d+) ChenMore declarations', output)
        passed = result.returncode == 0 and audit is not None
        record = dict(
            entry,
            passed=passed,
            exit_code=result.returncode,
            declarations=int(audit[1]) if audit else None,
            seconds=round(time.monotonic() - start, 3),
        )
        records.append(record)
        receipt_path.write_text(json.dumps(record, indent=2) + '\n')
        write_status(all_manifest, log_dir)
        if not passed:
            print(output[-12000:], flush=True)
            raise SystemExit(f"FAILED: {entry['group']}; see {log_path}")
        print((f"PASS: {entry['group']}; {record['declarations']} declarations; "
              f"{record['seconds']} seconds"), flush=True)
    print((f"PASS: {len(records)} groups, {sum(r['components'] for r in records)} components, "
          f"{sum(r['obstructions'] for r in records)} obstructions; "
          'axioms restricted to propext, Classical.choice, Quot.sound.'), flush=True)
    write_status(all_manifest, log_dir)
if __name__ == '__main__':
    main()
