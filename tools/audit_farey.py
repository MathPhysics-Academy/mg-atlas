#!/usr/bin/env python3
"""Check Table 4 Farey certificate coverage and receipts."""
import hashlib, json, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results/table4-graphs'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    prior = json.loads((ROOT / 'results/table4-final-audit.json').read_text())
    manifest = json.loads((ROOT / 'lean/farey/manifest.json').read_text())
    inputs = json.loads((OUT / 'inputs.json').read_text())
    exports = json.loads((OUT / 'exports.json').read_text())
    assert len(manifest) == len(inputs) == len(exports) == 376
    for r in manifest:
        for view in ['cosets', 'ribbon', 'domain', 'map-domain']:
            assert (OUT / 'drawings' / (r['name'] + '-' + view + '.svg')).is_file(), (r['name'], view)
    assert {r['group'] for r in manifest} == {r['group'] for r in prior['groups']}
    assert {r['name'] for r in manifest} == {r['name'] for r in exports} == {r['name'] for r in inputs}
    for g in prior['groups']:
        assert sha(ROOT / g['source']) == g['source_sha256']
    original = {}
    for p in sorted((ROOT / 'results').glob('gap-*.jsonl')):
        for line in p.read_text().splitlines():
            r = json.loads(line)
            label = r.get('group')
            if not label and 'index' in r:
                label = f"SmallGroup({r['order']},{r['index']})"
            if label and 'components' in r:
                original[label] = r['components']
    for r in inputs:
        c = original[r['group']][r['component']]
        assert r['S'] == c['S'] and r['T'] == c['T']
    required = [
        'quotient_relations',
        'projection_compatible',
        'central_quotient',
        'vertices_partition',
        'vertices_cycles',
        'edges_partition',
        'edges_cycles',
        'faces_partition',
        'faces_cycles',
        'vertex_valencies',
        'edge_valencies',
        'cusp_widths',
        'elliptic_counts',
        'euler_arithmetic',
        'lift_words',
        'lift_matrices_match',
        'side_pairing_words',
        'boundary_farey_neighbors',
        'boundary_matches_darts',
        'boundary_order',
        'paired_sides',
    ]
    checked = []
    missing = []
    for r in manifest:
        receipt = OUT / 'lean' / (r['name'] + '.json')
        log = OUT / 'lean' / (r['name'] + '.log')
        if not receipt.exists():
            missing.append(r['name'])
            continue
        result = json.loads(receipt.read_text())
        source = ROOT / r['source']
        assert result['passed'] and result['exit_code'] == 0, (r['name'], 'compiler failed')
        assert result['source_sha256'] == sha(source), (r['name'], 'stale source')
        assert 'Axiom audit passed for all ' in log.read_text()
        text = source.read_text()
        for name in required:
            assert re.search('\\btheorem ' + name + '\\b', text), (r['name'], name)
        assert not re.search('\\bsorry\\b|\\bnative_decide\\b|\\baxiom\\s', text)
        checked.append(result)
    checked_names = {c['name'] for c in checked}
    groups = {r['group'] for r in manifest if all((k['name'] in checked_names for k in manifest if k['group'] == r['group']))}
    summary = dict(
        complete=not missing,
        checked_groups=len(groups),
        checked_components=len(checked),
        expected_groups=218,
        expected_components=376,
        remaining_components=missing,
        allowed_axioms=['propext', 'Classical.choice', 'Quot.sound'],
        scope='Finite action graph cycle partitions, central projection, explicit matrix words for lifts and side pairings, boundary Farey neighbors and edge matches. No geometric fundamental-domain, tessellation, non-overlap, or generating-pair enumeration theorem.',
        sage_checked=False,
        lean_toolchain=(ROOT / 'lean/lean-toolchain').read_text().strip(),
        source_hashes=dict(input=sha(OUT / 'inputs.json'), export=sha(OUT / 'exports.json')),
        total_certificate_wall_seconds=round(sum((c['wall_seconds'] for c in checked)), 3),
        results=checked,
    )
    (OUT / 'lean-audit.json').write_text(json.dumps(summary, indent=2) + '\n')
    lines = [
        '# Table 4 graph/Farey Lean certificate audit',
        '',
        f"Status: {len(checked)}/376 components; {len(groups)}/218 complete group labels.",
        '',
        '[Certificate scope](../../lean/README.md)',
        '',
        'Receipts record the compiler exit status, source hash and allowed axioms.',
        '',
        '| Component | PSL degree | Lean seconds | Certificate |',
        '|---|---:|---:|---|',
    ]
    for c in checked:
        lines.append(f"| {c['name']} | {c['psl_degree']} | {c['wall_seconds']} | [Lean](../../{c['source']}) |")
    (OUT / 'lean-audit.md').write_text('\n'.join(lines) + '\n')
    print(f"{'COMPLETE' if not missing else 'IN PROGRESS'} {len(checked)}/376 components; {len(groups)}/218 groups")
if __name__ == '__main__':
    main()
