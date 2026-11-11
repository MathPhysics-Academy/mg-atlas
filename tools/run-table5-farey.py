#!/usr/bin/env python3
"""Run GAP Farey construction and render the resulting graphs."""
import argparse, json, os, shlex, shutil, subprocess, sys, time
from pathlib import Path
from table5_lean_status import verified_pilots
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results/table5-graphs'

def main():
    global OUT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', required=True)
    parser.add_argument('--groups', nargs='+')
    parser.add_argument('--data-dir', default='results/table5-graphs')
    parser.add_argument('--input-dir', default='results')
    args = parser.parse_args()
    OUT = ROOT / args.data_dir
    gap_executable = os.environ.get('GAP_EXECUTABLE') or shutil.which('gap')
    if not gap_executable:
        gap_executable = next((parent / 'gap-4.16.1/gap' for parent in ROOT.parents if (parent / 'gap-4.16.1/gap').is_file()), None)
    if not gap_executable:
        raise SystemExit('Set GAP_EXECUTABLE or put gap on PATH.')
    archive = OUT / 'runs' / args.archive
    if archive.exists():
        raise RuntimeError(f'Archive already exists: {archive}')
    command = [
        sys.executable,
        str(ROOT / 'tools/export-table5-farey.py'),
        '--input-dir',
        args.input_dir,
        '--output-dir',
        args.data_dir,
    ]
    if args.groups:
        command += ['--groups'] + args.groups
    subprocess.run(command, cwd=ROOT, check=True)
    start = time.monotonic()
    with (OUT / 'gap.log').open('w') as f:
        p = subprocess.run(
            [str(gap_executable), '-q', '-b', '--quitonbreak', str(OUT / 'export.g')],
            cwd=ROOT,
            stdout=f,
            stderr=subprocess.STDOUT,
        )
    wall = time.monotonic() - start
    rows = [json.loads(s[7:]) for s in (OUT / 'gap.log').read_text().splitlines() if s.startswith('@@JSON ')]
    expected = json.loads((OUT / 'inputs.json').read_text())
    if p.returncode or {r['name'] for r in rows} != {r['name'] for r in expected} or len(rows) != len(expected):
        raise RuntimeError((p.returncode, len(rows), len(expected), (OUT / 'gap.log').read_text()[-2000:]))
    (OUT / 'exports.json').write_text(json.dumps(rows) + '\n')
    groups = []
    for label in dict.fromkeys((r['group'] for r in rows)):
        rs = [r for r in rows if r['group'] == label]
        groups.append(dict(
            group=label,
            components=len(rs),
            gap_runtime_ms=sum((r['gap_ms'] for r in rs)),
            max_psl_degree=max((r['farey']['check']['mu'] for r in rs)),
        ))
    pilots = verified_pilots(ROOT, OUT)
    summary = dict(
        lean_checked_groups=sorted(pilots),
        lean_checked_components=sum((r['checked_components'] for r in pilots.values())),
        complete=True,
        groups=groups,
        components=len(rows),
        process_wall_seconds=round(wall, 3),
        exit_code=p.returncode,
        lean_checked=False,
        timing_scope='Each component timing includes two Farey calls: JSON export and graph/invariant comparison.',
    )
    (OUT / 'timings.json').write_text(json.dumps(summary, indent=2) + '\n')
    archive.mkdir(parents=True)
    for name in ['inputs.json', 'exports.json', 'gap.log', 'timings.json', 'export.g']:
        shutil.copy2(OUT / name, archive / name)
    print(json.dumps(summary, indent=2), flush=True)
    subprocess.run([
        sys.executable,
        str(ROOT / 'tools/render-table4-graphs.py'),
        '--data-dir',
        args.data_dir,
        '--table',
        '5',
    ], cwd=ROOT, check=True)
    subprocess.run([sys.executable, str(ROOT / 'tools/render-table4-domains.py'), '--data-dir', args.data_dir], cwd=ROOT, check=True)
    reproduce = [
        'python3',
        'tools/run-table5-farey.py',
        '--archive',
        'RUN-NAME',
        '--data-dir',
        args.data_dir,
        '--input-dir',
        args.input_dir,
    ]
    if args.groups:
        reproduce += ['--groups'] + args.groups
    checked = sum((record['checked_components'] for record in pilots.values()))
    audits = ', '.join(('[' + group + '](' + record['audit_file'] + ')' for group, record in pilots.items()))
    lines = [
        '# Farey construction',
        '',
        f'{len(groups)} groups and {len(rows)} components.',
        '',
        '[Inputs](inputs.json) · [Exports](exports.json) · [Timing data](timings.json) · [GAP log](gap.log)',
        '',
        '`gap/farey.g` constructs Farey polygons and checks boundary determinants, side-pairing words and elliptic traces. `gap/graph-export-lib.g` computes the graph actions and checks their invariants.',
        '',
        f'Lean certificates cover {checked} components. ' + audits,
        '',
        '[Certificate scope](../../lean/README.md)',
        '',
        '## Timings',
        '',
        '| Group | Components | GAP seconds |',
        '|---|---:|---:|',
    ]
    for group in groups:
        lines.append(f"| {group['group']} | {group['components']} | {group['gap_runtime_ms']/1000:.3f} |")
    lines += [
        '',
        f'Process wall time was {wall:.3f} seconds, including startup. Component times include two Farey calls for export and invariant comparison.',
        '',
        '## Reproduce',
        '',
        '```sh',
        shlex.join(reproduce),
        '```',
    ]
    (OUT / 'CERTIFICATES.md').write_text('\n'.join(lines) + '\n')
if __name__ == '__main__':
    main()
