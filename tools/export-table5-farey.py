#!/usr/bin/env python3
"""Prepare GAP Farey exports for Table 5."""
import argparse, json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
groups = [
    ('a5', 'A5'),
    ('psl7', 'PSL2_7'),
    ('a6', 'A6'),
    ('psl8', 'PSL2_8'),
    ('psl11', 'PSL2_11'),
    ('psl13', 'PSL2_13'),
    ('psl17', 'PSL2_17'),
    ('a7', 'A7'),
    ('psl19', 'PSL2_19'),
    ('psl16', 'PSL2_16'),
    ('psl3-3', 'PSL3_3'),
    ('psu3-3', 'PSU3_3'),
    ('psl23', 'PSL2_23'),
    ('psl25', 'PSL2_25'),
    ('m11', 'M11'),
    ('psl27', 'PSL2_27'),
    ('psl29', 'PSL2_29'),
    ('psl31', 'PSL2_31'),
    ('a8', 'A8'),
    ('psl3-4', 'PSL3_4'),
    ('psl37', 'PSL2_37'),
    ('psp4-3', 'PSp4_3'),
    ('sz8', 'Sz8'),
]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--groups', nargs='+', choices=[slug for slug, _ in groups])
parser.add_argument('--input-dir', default='results')
parser.add_argument('--output-dir', default='results/table5-graphs')
args = parser.parse_args()
input_dir = ROOT / args.input_dir
OUT = ROOT / args.output_dir
OUT.mkdir(parents=True, exist_ok=True)
records = []
code = [
    'Read("gap/export-lib.g");;',
    'Read("gap/mg.g");;',
    'Read("gap/farey.g");;',
    'Read("gap/graph-export-lib.g");;',
]
if args.groups:
    groups = [group for group in groups if group[0] in args.groups]
for slug, prefix in groups:
    source = input_dir / f'gap-table5-{slug}.jsonl'
    if not source.is_file():
        source = input_dir / f'{slug}.json'
    if not source.is_file() and input_dir == ROOT / 'results':
        source = input_dir / 'table5-gap' / f'{slug}.json'
    g = json.loads(source.read_text())
    for k, c in enumerate(g['components']):
        name = f'{prefix}_c{k}'
        record = dict(name=name, group=g['group'], component=k, S=c['S'], T=c['T'])
        records.append(record)
        code.append('c := rec(S := ' + str([p + 1 for p in c['S']]) + ', T := ' + str([p + 1 for p in c['T']]) + ');;')
        code += [
            'started := Runtime();;',
            'fareyJSON := MGFareyJSON(c);;',
            'graphJSON := MGGraphJSON(c, MGFarey(c));;',
        ]
        lead = json.dumps(dict(name=name, group=g['group'], component=k))[:-1] + ',"farey":'
        code.append('EmitJSON(Concatenation(' + json.dumps(lead) + ', fareyJSON, ' + json.dumps(',"graph":') + ', graphJSON, ' + json.dumps(',"gap_ms":') + ', String(Runtime()-started), "}"));')
code.append('QUIT;')
(OUT / 'inputs.json').write_text(json.dumps(records) + '\n')
(OUT / 'export.g').write_text('\n'.join(code) + '\n')
print(f'Prepared {len(records)} components for {len(groups)} groups')
