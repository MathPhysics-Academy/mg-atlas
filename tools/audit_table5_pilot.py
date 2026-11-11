#!/usr/bin/env python3
"""Check Table 5 certificate coverage, source hashes and receipts."""
import argparse, hashlib, json, re, shlex, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results/table5-graphs'
sys.path.insert(0, str(ROOT / 'tools'))
from table5_lean_status import data_fingerprint, verified_pilots

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def load(p):
    return json.loads((ROOT / p).read_text())

def receipt(source, folder, name, markers):
    r = json.loads((OUT / folder / (name + '.json')).read_text())
    log = (OUT / folder / (name + '.log')).read_text()
    assert r['passed'] and r['exit_code'] == 0, (name, 'compiler did not pass')
    assert r['source_sha256'] == sha(source), (name, 'stale source')
    for marker in markers:
        assert re.search('Axiom audit passed for all \\d+ ' + marker + ' declarations', log), (name, marker)
    assert not re.search('\\bsorry\\b|\\bnative_decide\\b|\\baxiom\\s', source.read_text())
    return r

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--groups', nargs='+', default=['psl13'])
    args = parser.parse_args()
    am = load('lean/table5-actions/manifest.json')
    fm = load('lean/table5-farey/manifest.json')
    bm = load('lean/table5-bundles/manifest.json')
    all_inputs = load('results/table5-graphs/inputs.json')
    all_exports = load('results/table5-graphs/exports.json')
    for r in load('results/table4-final-audit.json')['groups']:
        assert sha(ROOT / r['source']) == r['source_sha256']
    for r in load('results/table4-graphs/lean-audit.json')['results']:
        assert sha(ROOT / r['source']) == r['source_sha256']
    for p in OUT.glob('lean-*-audit.json'):
        old = json.loads(p.read_text())
        if old.get('complete') and 'action' in old:
            for r in [old['action'], old['bundle']] + old['farey']:
                assert sha(ROOT / r['source']) == r['source_sha256']
    summaries = []
    for slug in args.groups:
        raw_path = f'results/gap-table5-{slug}.jsonl'
        raw = load(raw_path)
        label = raw['group']
        count = len(raw['components'])
        inputs = [r for r in all_inputs if r['group'] == label]
        exports = [r for r in all_exports if r['group'] == label]
        assert len(inputs) == len(exports) == count
        for r in inputs:
            c = raw['components'][r['component']]
            assert r['S'] == c['S'] and r['T'] == c['T']
        assert {r['component'] for r in exports} == set(range(count))
        a = next((r for r in am if r['group'] == label))
        b = next((r for r in bm if r['group'] == label))
        assert a['components'] == b['components'] == count and a['obstructions'] == b['obstructions']
        asource = ROOT / 'lean/table5-actions' / a['file']
        bsource = ROOT / b['source']
        action = receipt(asource, 'lean-actions', Path(a['file']).stem, ['ChenMore'])
        bundle = receipt(bsource, 'lean-bundles', b['name'], ['ChenMore', 'ChenFarey'])
        assert asource.read_text().count('theorem no_factor_mod') == a['obstructions']
        assert bsource.read_text().count('theorem no_factor_mod') == a['obstructions']
        assert bsource.read_text().count('theorem action_tables_agree') == count
        selected = sorted([r for r in fm if r['group'] == label], key=lambda r: r['component'])
        assert {r['name'] for r in selected} == {r['name'] for r in inputs}
        assert [r['component'] for r in selected] == list(range(count))
        farey = [receipt(ROOT / r['source'], 'lean', r['name'], ['ChenFarey']) for r in selected]
        summary = dict(
            complete=True,
            group=label,
            checked_components=count,
            checked_obstructions=a['obstructions'],
            checked_action_table_bridges=count,
            allowed_axioms=['propext', 'Classical.choice', 'Quot.sound'],
            action=action,
            farey=farey,
            bundle=bundle,
            source_data_path=raw_path,
            source_data_sha256=sha(ROOT / raw_path),
            selected_data_sha256=data_fingerprint(inputs, exports, label),
            table4_sources_unchanged=True,
            scope='Supplied finite actions; finite graph partitions; algebraic Farey witnesses; explicit action-table equality bridges. Enumeration completeness, group identification, merged multiplicities, geometric fundamental-domain correctness, genus interpretation and general level theorems are not proved.',
        )
        summaries.append((slug, summary))
    for slug, s in summaries:
        count = s['checked_components']
        a = s['action']
        b = s['bundle']
        f = s['farey']
        label = s['group']
        audit_name = f'lean-{slug}-audit'
        (OUT / (audit_name + '.json')).write_text(json.dumps(s, indent=2) + '\n')
        lines = [
            f'# {label}: Lean certificate audit',
            '',
            f"**Complete: all {count} components; {s['checked_obstructions']} finite-level factorization obstructions; {count} explicit action-table bridges.**",
            '',
            'Lean checked the action and Farey certificates and their table-equality bridges. All transitive axiom dependencies were audited against `propext`, `Classical.choice`, and `Quot.sound`. Computation uses `decide +kernel`. ',
            '',
            f"[Combined certificate](../../{b['source']}) · [Standalone action certificate](../../{a['source']}) · [Machine-readable audit]({audit_name}.json)",
            '',
            f"Action certificate: {a['wall_seconds']:.3f} s. Combined certificate with bridges: {b['wall_seconds']:.3f} s. Separate Farey files: {sum(r['wall_seconds'] for r in f):.3f} s summed over {count} files.",
            '',
            'Wall times include startup and concurrent load.',
            '',
            '[Certificate scope](../../lean/README.md)',
            '',
            '## Reproduce',
            '',
            'From the project root:',
            '',
            '```sh',
            'python3 tools/generate_more.py ' + ' '.join(('--input results/gap-table5-' + x + '.jsonl' for x in args.groups)) + ' --output-dir lean/table5-actions --summary-output results/lean-table5-action-inputs.json',
            'python3 tools/generate_farey.py --data-dir results/table5-graphs --output-dir lean/table5-farey ' + ' '.join(('--group ' + shlex.quote(load(f'results/gap-table5-{x}.jsonl')['group']) for x in args.groups)),
            'bash lean/check-farey.sh --source-dir lean/table5-actions --results-dir results/table5-graphs/lean-actions --jobs 2',
            'bash lean/check-farey.sh --source-dir lean/table5-farey --results-dir results/table5-graphs/lean --jobs 3',
            'python3 tools/bundle_table5_pilot.py',
            'bash lean/check-farey.sh --source-dir lean/table5-bundles --results-dir results/table5-graphs/lean-bundles --jobs 2',
            'python3 tools/audit_table5_pilot.py --groups ' + ' '.join(args.groups),
            '```',
            '',
            '| Component | PSL degree | Standalone Farey seconds | Source |',
            '|---|---:|---:|---|',
        ]
        for r in f:
            lines.append(f"| {r['name']} | {r['psl_degree']} | {r['wall_seconds']} | [Lean](../../{r['source']}) |")
        (OUT / (audit_name + '.md')).write_text('\n'.join(lines) + '\n')
        print(f"PASS {label}: {count} components, {s['checked_obstructions']} obstructions, {count} bridges", flush=True)
    verified = verified_pilots(ROOT, OUT)
    coverage = dict(
        checked_groups=len(verified),
        checked_components=sum((r['checked_components'] for r in verified.values())),
        checked_obstructions=sum((r['checked_obstructions'] for r in verified.values())),
        allowed_axioms=['propext', 'Classical.choice', 'Quot.sound'],
        groups=[dict(group=g, components=r['checked_components'], obstructions=r['checked_obstructions'], bundle_seconds=r['bundle']['wall_seconds'], audit=r['audit_file']) for g, r in verified.items()],
    )
    (OUT / 'lean-coverage.json').write_text(json.dumps(coverage, indent=2) + '\n')
    lines = [
        '# Table 5 Lean coverage',
        '',
        f"{coverage['checked_groups']} groups / {coverage['checked_components']} components / {coverage['checked_obstructions']} finite-level factorization obstructions. Every component also has an explicit action-table bridge.",
        '',
        '[Certificate scope](../../lean/README.md)',
        '',
        '| Group | Components | Obstructions | Combined certificate seconds |',
        '|---|---:|---:|---:|',
    ]
    for r in coverage['groups']:
        lines.append(f"| [{r['group']}]({r['audit']}) | {r['components']} | {r['obstructions']} | {r['bundle_seconds']} |")
    (OUT / 'lean-coverage.md').write_text('\n'.join(lines) + '\n')
    print(f"Coverage: {coverage['checked_groups']} groups / {coverage['checked_components']} components; prior proof sources unchanged")
if __name__ == '__main__':
    main()
