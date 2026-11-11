#!/usr/bin/env python3
"""Prepare GAP Farey exports for Table 4."""
import json, re
from pathlib import Path
root = Path(__file__).resolve().parents[1]
audit = json.loads((root / 'results/table4-final-audit.json').read_text())
wanted = {g['group'] for g in audit['groups']}
groups = {}
for path in sorted((root / 'results').glob('gap-*.jsonl')):
    for line in path.read_text().splitlines():
        g = json.loads(line)
        label = g.get('group')
        if not label and 'index' in g:
            label = f"SmallGroup({g['order']},{g['index']})"
        if label in wanted and 'components' in g:
            if label in groups:
                assert groups[label]['components'] == g['components']
            groups[label] = g
assert set(groups) == wanted
out = root / 'results/table4-graphs'
out.mkdir(exist_ok=True)
records = []
code = [
    'Read("gap/export-lib.g");;',
    'Read("gap/mg.g");;',
    'Read("gap/farey.g");;',
    'Read("gap/graph-export-lib.g");;',
]
for label in sorted(groups, key=lambda s: tuple(map(int, re.findall('\\d+', s)))):
    for k, c in enumerate(groups[label]['components']):
        name = 'G' + '_'.join(re.findall('\\d+', label)) + f'_c{k}'
        record = dict(name=name, group=label, component=k, S=c['S'], T=c['T'])
        records.append(record)
        code.append('c := rec(S := ' + str([p + 1 for p in c['S']]) + ', T := ' + str([p + 1 for p in c['T']]) + ');;')
        prefix = json.dumps(dict(name=name, group=label, component=k))[:-1] + ',"farey":'
        code.append('EmitJSON(Concatenation(' + json.dumps(prefix) + ', MGFareyJSON(c), ' + json.dumps(',"graph":') + ', MGGraphJSON(c, MGFarey(c)), "}"));')
code.append('QUIT;')
assert len(records) == audit['checked_components']
(out / 'inputs.json').write_text(json.dumps(records) + '\n')
(out / 'export.g').write_text('\n'.join(code) + '\n')
print(f'Prepared {len(groups)} groups, {len(records)} components')
