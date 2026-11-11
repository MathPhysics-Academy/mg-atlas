#!/usr/bin/env python3
"""Compile certificates and record compiler results and source hashes."""
import argparse, concurrent.futures, fcntl, hashlib, json, os, subprocess, tempfile, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('names', nargs='*')
parser.add_argument('--jobs', type=int, default=2)
parser.add_argument('--reverse', action='store_true')
parser.add_argument('--exclude', action='append', default=[])
parser.add_argument('--source-dir', default='lean/farey')
parser.add_argument('--results-dir', default='results/table4-graphs/lean')
args = parser.parse_args()
source_dir = ROOT / args.source_dir
manifest = json.loads((source_dir / 'manifest.json').read_text())
out = ROOT / args.results_dir
out.mkdir(parents=True, exist_ok=True)
for r in manifest:
    if 'name' not in r:
        r['name'] = Path(r['file']).stem
    if 'source' not in r:
        r['source'] = str((source_dir / r['file']).relative_to(ROOT))
selected = [r for r in manifest if (not args.names or r['name'] in args.names) and r['name'] not in args.exclude]
if args.reverse:
    selected.reverse()
assert not args.names or len(selected) == len(set(args.names))
if not os.environ.get('LEAN_ROOT'):
    raise SystemExit('Source your Lean env.sh or use lean/check-farey.sh first')
mathlib = Path(os.environ['LEAN_ROOT']) / 'mathlib4'

def check(r):
    with (out / (r['name'] + '.lock')).open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        return check_locked(r)

def check_locked(r):
    source = ROOT / r['source']
    sha = hashlib.sha256(source.read_bytes()).hexdigest()
    receipt = out / (r['name'] + '.json')
    log = out / (r['name'] + '.log')
    if receipt.exists():
        prior = json.loads(receipt.read_text())
        if prior.get('passed') and prior.get('source_sha256') == sha and log.exists():
            return prior
    started = time.monotonic()
    with tempfile.NamedTemporaryFile(mode='w', dir=out, prefix=r['name'] + '.', suffix='.tmp', delete=False) as f:
        temporary = Path(f.name)
        try:
            p = subprocess.run(
                ['lake', 'env', 'lean', str(source)],
                cwd=mathlib,
                stdout=f,
                stderr=subprocess.STDOUT,
            )
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise
    text = temporary.read_text()
    passed = p.returncode == 0 and 'Axiom audit passed for all ' in text and (hashlib.sha256(source.read_bytes()).hexdigest() == sha)
    temporary.replace(log)
    result = dict(
        r,
        passed=passed,
        exit_code=p.returncode,
        source_sha256=sha,
        wall_seconds=round(time.monotonic() - started, 3),
    )
    temporary_receipt = receipt.with_suffix('.json.tmp')
    temporary_receipt.write_text(json.dumps(result, indent=2) + '\n')
    temporary_receipt.replace(receipt)
    print(f"{'PASS' if passed else 'FAIL'} {r['name']} {result['wall_seconds']}s", flush=True)
    return result
started = time.monotonic()
with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
    results = list(pool.map(check, selected))
summary = dict(
    complete=len(results) == len(manifest) and all((x['passed'] for x in results)),
    checked_components=sum((x.get('components', 1) for x in results if x['passed'])),
    selected_components=sum((x.get('components', 1) for x in results)),
    checked_files=sum((x['passed'] for x in results)),
    selected_files=len(results),
    wall_seconds=round(time.monotonic() - started, 3),
    allowed_axioms=['propext', 'Classical.choice', 'Quot.sound'],
    results=results,
)
(out / ('status-reverse.json' if args.reverse else 'status.json')).write_text(json.dumps(summary, indent=2) + '\n')
print(
    'Checked',
    summary['checked_components'],
    '/',
    summary['selected_components'],
    'components in',
    summary['checked_files'],
    'files',
    flush=True,
)
raise SystemExit(0 if all((x['passed'] for x in results)) else 1)
