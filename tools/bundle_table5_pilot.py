#!/usr/bin/env python3
"""Combine action and Farey certificates with table-equality proofs."""
import argparse, json
from pathlib import Path
from generate_baseline import AUDIT
ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--action-dir', default='lean/table5-actions')
parser.add_argument('--farey-dir', default='lean/table5-farey')
parser.add_argument('--output-dir', default='lean/table5-bundles')
args = parser.parse_args()
actions = ROOT / args.action_dir
fareys = ROOT / args.farey_dir
out = ROOT / args.output_dir
out.mkdir(parents=True, exist_ok=True)
am = json.loads((actions / 'manifest.json').read_text())
fm = json.loads((fareys / 'manifest.json').read_text())
manifest = []
for a in am:
    rows = [r for r in fm if r['group'] == a['group']]
    if len(rows) != a['components']:
        raise ValueError('Incomplete Farey component set')
    rows.sort(key=lambda r: r['component'])
    if [r['component'] for r in rows] != list(range(a['components'])):
        raise ValueError('Incorrect component numbering')
    action_namespace = Path(a['file']).stem
    first = (ROOT / rows[0]['source']).read_text()
    head = first.split('namespace ' + rows[0]['name'] + '\n', 1)[0]
    imports = [line for line in head.splitlines() if line.startswith('import ')]
    prelude = '\n'.join((line for line in head.splitlines() if not line.startswith('import '))) + '\n'
    action_text = (actions / a['file']).read_text()
    action_body = '\n'.join((line for line in action_text.splitlines() if not line.startswith('import '))) + '\n'
    parts = ['\n'.join(imports) + '\n\n', action_body, prelude]
    for r in rows:
        text = (ROOT / r['source']).read_text()
        name = r['name']
        ns = action_namespace + '_C' + str(r['component'])
        body = text.split('namespace ' + name + '\n', 1)[1].split('end ' + name + '\n', 1)[0]
        statement = (f'theorem action_tables_agree :\n'
      f' (∀ p : Fin {r["degree"]}, originalS p = ChenMore.{ns}.S p) ∧\n'
      f' (∀ p : Fin {r["degree"]}, originalT p = ChenMore.{ns}.T p) := by decide +kernel\n')
        parts += ['namespace ' + name + '\n', body, statement, 'end ' + name + '\n']
    parts.append(AUDIT.replace('ChenBaseline', 'ChenFarey'))
    path = out / a['file']
    path.write_text(''.join(parts))
    manifest.append(dict(
        name=action_namespace,
        group=a['group'],
        components=a['components'],
        obstructions=a['obstructions'],
        max_degree=a['max_degree'],
        source=str(path.relative_to(ROOT)),
    ))
    print('Generated linked bundle', path.relative_to(ROOT), 'with', len(rows), 'action-table bridges')
(out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
