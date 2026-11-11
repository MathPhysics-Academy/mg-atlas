#!/usr/bin/env python3
"""Render coset and ribbon graphs from GAP exports."""
import argparse, json, math, html
from table5_lean_status import verified_pilots
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--data-dir', default='results/table4-graphs')
parser.add_argument('--table', type=int, default=4)
args = parser.parse_args()
OUT = ROOT / args.data_dir
D = OUT / 'drawings'
D.mkdir(exist_ok=True)
inputs = {r['name']: r for r in json.loads((OUT / 'inputs.json').read_text())}
rows = json.loads((OUT / 'exports.json').read_text())
pilots = verified_pilots(ROOT, OUT) if args.table == 5 else {}

def svg_start(title, size=1000):
    return [
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {size} {size}"><rect width="100%" height="100%" fill="white"/>',
        f'<text x="{size/2}" y="30" text-anchor="middle" font-family="sans-serif" font-size="20">{html.escape(title)}</text>',
        '<defs><marker id="arr" markerWidth="5" markerHeight="5" refX="5" refY="2.5" orient="auto"><path d="M0 0L5 2.5L0 5" fill="context-stroke"/></marker></defs>',
    ]

def circle_layout(n):
    return [(500 + 400 * math.cos(2 * math.pi * i / n), 520 + 400 * math.sin(2 * math.pi * i / n)) for i in range(n)]

def draw_graph(name, perms, labels, title):
    n = len(labels)
    pos = circle_layout(n)
    parts = svg_start(title)
    fs = max(3, min(12, 800 / max(n, 1)))
    for perm, color in perms:
        for i, j in enumerate(perm):
            x, y = pos[i]
            a, b = pos[j]
            if i == j:
                parts.append(f'<circle cx="{x+5}" cy="{y-5}" r="7" fill="none" stroke="{color}"/>')
            else:
                parts.append(f'<path d="M{x},{y} Q{(x+a)/2+(b-y)*.08},{(y+b)/2+(x-a)*.08} {a},{b}" fill="none" stroke="{color}" stroke-opacity=".5" stroke-width=".8" marker-end="url(#arr)"/>')
    for (x, y), label in zip(pos, labels):
        parts.append(f'<circle cx="{x}" cy="{y}" r="2" fill="black"/><text x="{x*1.025-12.5}" y="{y*1.025-13}" font-size="{fs}" text-anchor="middle">{html.escape(str(label))}</text>')
    (D / (name + '.svg')).write_text('\n'.join(parts + ['</svg>']))
intro = f"{len(set(row['group'] for row in rows))} groups and {len(rows)} components. "
if args.table == 4:
    intro += '[Lean audit](lean-audit.md) · [Construction](CERTIFICATES.md).'
else:
    intro += f"Lean certificates cover {sum(row['checked_components'] for row in pilots.values())} components. [Construction](CERTIFICATES.md)."
index = [
    f'# Table {args.table} graph and Farey data',
    '',
    intro,
    '',
    'Coset graphs show the SL₂ action. Ribbon graphs use PSL darts with vertex rotation U = T ∘ S, edge involution S and cusp cycles T. Vertex labels give cyclic dart order. Squares mark order-two elliptic points.',
    '',
    '| Component | SL / PSL degree | Vertices / edge orbits / cusps | Genus | Data and drawings |',
    '|---|---:|---:|---:|---|',
]
for r in rows:
    name = r['name']
    src = inputs[name]
    g = r['graph']
    f = r['farey']
    n = len(g['S'])
    (OUT / (name + '.json')).write_text(json.dumps(dict(r, cosetAction=dict(S=src['S'], T=src['T'])), indent=2) + '\n')
    draw_graph(
        name + '-cosets',
        [(src['S'], 'royalblue'), (src['T'], 'darkorange')],
        list(range(len(src['S']))),
        name + ' cosets: S blue, T orange',
    )
    vs = g['vertices']
    owner = {p: i for i, v in enumerate(vs) for p in v}
    pos = circle_layout(len(vs))
    parts = svg_start(name + ' ribbon graph: vertex labels give cyclic dart order')
    counts = {}
    for e in g['edges']:
        i = owner[e[0]]
        x, y = pos[i]
        if len(e) == 1:
            a = 500 + (x - 500) * 1.12
            b = 520 + (y - 520) * 1.12
            parts.append(f'<path d="M{x},{y} L{a},{b}" stroke="gray"/><rect x="{a-3}" y="{b-3}" width="6" height="6" fill="gray"/>')
        else:
            j = owner[e[1]]
            a, b = pos[j]
            key = tuple(sorted((i, j)))
            k = counts.get(key, 0)
            counts[key] = k + 1
            if i == j:
                parts.append(f'<circle cx="{x+15}" cy="{y-15}" r="22" fill="none" stroke="purple"/>')
            else:
                offset = 0.12 * (k // 2 + 1) * (1 if k % 2 else -1)
                cx = (x + a) / 2 + (b - y) * offset
                cy = (y + b) / 2 + (x - a) * offset
                parts.append(f'<path d="M{x},{y} Q{cx},{cy} {a},{b}" fill="none" stroke="purple" stroke-width="1.5"><title>{e}</title></path>')
    for (x, y), v in zip(pos, vs):
        parts.append(f'<circle cx="{x}" cy="{y}" r="4" fill="indigo"/><text x="{500+(x-500)*1.10}" y="{520+(y-520)*1.10}" text-anchor="middle" font-size="{max(3,min(12,800/len(vs)))}">{html.escape(str(tuple(v)))}</text>')
    (D / (name + '-ribbon.svg')).write_text('\n'.join(parts + ['</svg>']))
    lean_link = f' · [Lean](../../lean/farey/{name}.lean)' if args.table == 4 else f' · [Lean bundle](../../{pilots[r["group"]]["bundle"]["source"]})' if r['group'] in pilots else ''
    index.append(f'| {name} | {len(src["S"])} / {n} | {len(vs)} / {len(g["edges"])} / {len(g["faces"])} | {g["genus"]} | [JSON]({name}.json) · [cosets](drawings/{name}-cosets.svg) · [ribbon](drawings/{name}-ribbon.svg){lean_link} |')
(OUT / 'README.md').write_text('\n'.join(index) + '\n')
print('Wrote exact JSON and coset/ribbon SVGs for', len(rows), 'components')
