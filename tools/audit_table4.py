#!/usr/bin/env python3
"""Check Table 4 coverage, source hashes and Lean receipts."""
import hashlib
import json
import re
import subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
ALLOWED = ['propext', 'Classical.choice', 'Quot.sound']
REQUIRED_THEOREMS = [
    'action_relations',
    'transitive_certificate',
    'central_quotient',
    'quotient_exact',
    'central_sign',
    'elliptic_counts',
    'cusp_certificate',
    'genus_arithmetic',
    'cusp_lcm',
]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check_component(source, namespace):
    block = source.split(f'namespace {namespace}\n', 1)[1].split(f'end {namespace}\n', 1)[0]
    for theorem in REQUIRED_THEOREMS:
        assert re.search(rf'^theorem {theorem}\b', block, re.M), f'{namespace}: missing {theorem}'
    return block

def main():
    pdf = ROOT / 'results/reference/chen-moduli-interpretations-for-noncongruence-modular-curves.pdf'
    paper = subprocess.run(['pdftotext', '-layout', str(pdf), '-'], capture_output=True, text=True, check=True).stdout
    table = paper.split('Table 4: Noncongruence Groups of Order')[1].split('Table 5: First 23')[0]
    ids = {(int(m[1]), int(m[2])) for m in re.finditer('^[ \\t]{0,3}(\\d+)[ \\t]+(\\d+)[ \\t]+\\S', table, re.M) if 24 <= int(m[1]) <= 255}
    assert len(ids) == 218, 'PDF extraction did not yield the 218 Table 4 groups'
    baseline = json.loads((ROOT / 'results/table4-baseline-check.json').read_text())
    assert baseline['compiler_exit_code'] == 0
    for filename, sha in baseline['sources'].items():
        assert digest(ROOT / filename) == sha, f'Baseline source changed: {filename}'
    baseline_log = (ROOT / baseline['log']).read_text()
    assert 'error:' not in baseline_log and 'sorryAx' not in baseline_log
    for namespace in ('ChenS4', 'ChenBaseline'):
        assert re.search(rf'Axiom audit passed for all \d+ {namespace} declarations', baseline_log)
    source = (ROOT / 'lean/BaselineCertificates.lean').read_text()
    baseline_components = {}
    baseline_obstructions = {}
    for n, i, c in re.findall('^namespace G(\\d+)_(\\d+)_C(\\d+)$', source, re.M):
        key = (int(n), int(i))
        baseline_components.setdefault(key, set()).add(int(c))
        namespace = f'G{n}_{i}_C{c}'
        block = check_component(source, namespace)
        baseline_obstructions[key] = baseline_obstructions.get(key, 0) + len(re.findall('^theorem no_factor_mod\\d+\\b', block, re.M))
    covered = {}
    for line in (ROOT / 'results/gap-baseline.jsonl').read_text().splitlines():
        group = json.loads(line)
        key = (group['order'], group['i'])
        count = sum((row['m'] for row in group['rows']))
        assert baseline_components[key] == set(range(count))
        if key in ids:
            covered[key] = dict(
                group=group['group'],
                components=count,
                obstructions=baseline_obstructions[key],
                source='lean/BaselineCertificates.lean',
                source_sha256=digest(ROOT / 'lean/BaselineCertificates.lean'),
            )
    manifest = json.loads((ROOT / 'lean/more/manifest.json').read_text())
    for entry in manifest:
        path = ROOT / 'lean/more' / entry['file']
        receipt_path = ROOT / 'results/lean-more' / path.with_suffix('.json').name
        receipt = json.loads(receipt_path.read_text())
        assert receipt['passed'] and receipt['exit_code'] == 0, entry['group']
        assert entry['sha256'] == receipt['sha256'] == digest(path), entry['group']
        log = receipt_path.with_suffix('.log').read_text()
        assert 'error:' not in log and 'sorryAx' not in log, entry['group']
        assert re.search('Axiom audit passed for all \\d+ ChenMore declarations', log)
        match = re.fullmatch('SmallGroup\\((\\d+),(\\d+)\\)', entry['group'])
        if match is None:
            continue
        key = tuple(map(int, match.groups()))
        if key not in ids:
            continue
        assert key not in covered, f'Duplicate Table 4 group: {key}'
        prefix = f'G{key[0]}_{key[1]}_C'
        components = {int(c) for c in re.findall(rf'^namespace {re.escape(prefix)}(\d+)$', path.read_text(), re.M)}
        assert components == set(range(entry['components'])), entry['group']
        for c in components:
            check_component(path.read_text(), f'{prefix}{c}')
        assert len(re.findall('^theorem no_factor_mod\\d+\\b', path.read_text(), re.M)) == entry['obstructions']
        covered[key] = dict(
            group=entry['group'],
            components=entry['components'],
            obstructions=entry['obstructions'],
            source=str(path.relative_to(ROOT)),
            source_sha256=digest(path),
        )
    assert set(covered) == ids, f'Missing Table 4 groups: {sorted(ids-set(covered))}'
    report = dict(complete=True, table=4, paper_groups=218, checked_groups=len(covered), checked_components=sum((g['components'] for g in covered.values())), checked_obstructions=sum((g['obstructions'] for g in covered.values())), allowed_axioms=ALLOWED, paper_sha256=digest(pdf), groups=[covered[key] for key in sorted(covered)], scope=('Certificates for supplied finite actions and numerical signatures. '
                        'GAP enumeration completeness, group-label identification, merged-row '
                        'multiplicities, and the geometric and level theorems are not formalized.'))
    (ROOT / 'results/table4-final-audit.json').write_text(json.dumps(report, indent=2) + '\n')
    lines = [
        '# Table 4 certificate audit',
        '',
        f"**All {len(covered)} Table 4 group labels are covered.**",
        '',
        f"- {report['checked_components']} supplied finite-action components.",
        f"- {report['checked_obstructions']} finite-level factorization obstructions.",
        '- Each source matches a successful Lean check and axiom audit.',
        '- Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.',
        '',
        'Group coverage matches Table 4 in the paper.',
        '',
        '[Certificate scope](../lean/README.md)',
        '',
        '[Final batch timings](table4-final-timings.md) · [Machine-readable audit](table4-final-audit.json)',
        '',
        '| Group | Components | Obstructions |',
        '|---|---:|---:|',
    ]
    for key in sorted(covered):
        g = covered[key]
        lines.append(f"| [{g['group']}](../{g['source']}) | {g['components']} | {g['obstructions']} |")
    (ROOT / 'results/table4-final-audit.md').write_text('\n'.join(lines) + '\n')
    print((f"PASS: all {len(covered)} Table 4 groups; {report['checked_components']} supplied components; "
          f"{report['checked_obstructions']} factorization obstructions; "
          'every source matches a successful Lean check and the three-axiom audit.'))
if __name__ == '__main__':
    main()
