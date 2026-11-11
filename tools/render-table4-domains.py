#!/usr/bin/env python3
"""Render Farey polygons and their embedded maps."""
import argparse, json, math, cmath, html
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--data-dir', default='results/table4-graphs')
args = parser.parse_args()
OUT = ROOT / args.data_dir
D = OUT / 'drawings'
rows = json.loads((OUT / 'exports.json').read_text())
count = 0
for row in rows:
    f = row['farey']
    g = row['graph']
    name = row['name']
    xs = [a / b for a, b in f['x']]
    left = min(xs)
    right = max(xs)
    scale = 900 / (right - left)
    base = 850
    top = 100

    def px(x):
        return 50 + (x - left) * scale

    def py(y):
        return base - y * scale

    def edge(a, b, col, width):
        if a is None or b is None:
            x = b if a is None else a
            return f'<path d="M{px(x):.5f},{base} V{top}" stroke="{col}" stroke-width="{width}" fill="none"/>'
        a, b = sorted((a, b))
        r = (b - a) / 2
        return f'<path d="M{px(a):.5f},{base} A{r*scale:.5f},{r*scale:.5f} 0 0 1 {px(b):.5f},{base}" stroke="{col}" stroke-width="{width}" fill="none"/>'

    def mob(m, z):
        a, b, c, d = m
        if z is None:
            return a / c if c else None
        return (a * z + b) / (c * z + d) if c * z + d else None

    def arc(z, w):
        if abs(z.real - w.real) < 1e-12:
            return [(z.real, z.imag), (w.real, w.imag)]
        cx = (abs(w) ** 2 - abs(z) ** 2) / (2 * (w.real - z.real))
        r = abs(z - cx)
        a = cmath.phase(z - cx)
        b = cmath.phase(w - cx)
        return [(cx + r * math.cos(a + (b - a) * i / 20), r * math.sin(a + (b - a) * i / 20)) for i in range(21)]

    def ideal_arc(z, a):
        if a is None:
            return f'<path d="M{px(z.real):.5f},{py(z.imag):.5f} V{top}" stroke="black" stroke-width="1.5" fill="none"/>'
        if abs(z.real - a) < 1e-12:
            points = [(a, 0), (z.real, z.imag)]
        else:
            cx = (abs(z) ** 2 - a * a) / (2 * (z.real - a))
            r = abs(a - cx)
            t0 = 0 if a > cx else math.pi
            t1 = cmath.phase(z - cx)
            points = [(cx + r * math.cos(t0 + (t1 - t0) * i / 40), r * math.sin(t0 + (t1 - t0) * i / 40)) for i in range(41)]
        coords = ' '.join((f'{px(x):.5f},{py(y):.5f}' for x, y in points))
        return f'<polyline points="{coords}" fill="none" stroke="black" stroke-width="1.5"/>'
    rho = complex(-0.5, math.sqrt(3) / 2)
    for dual in [False, True]:
        parts = ['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1000 950"><rect width="100%" height="100%" fill="white"/>', f'<text x="500" y="30" text-anchor="middle" font-family="sans-serif" font-size="18">{name}: ' + ('trivalent map in the Farey polygon' if dual else 'Farey polygon and triangulation') + '</text>']
        if not dual:
            for v in g['vertices']:
                m = f['darts'][v[0]]
                if len(v) == 1:
                    parts.append(edge(mob(m, 0), mob(m, None), '#aaaadd', 0.7))
                    continue
                points = [mob(m, -1), mob(m, 0), mob(m, None)]
                for a, b in zip(points, points[1:] + points[:1]):
                    parts.append(edge(a, b, '#aaaadd', 0.7))
        else:
            rho = complex(-0.5, math.sqrt(3) / 2)
            for m in f['darts']:
                z = mob(m, rho)
                w = mob(m, 1j)
                points = arc(z, w)
                coords = ' '.join((f'{px(x):.4f},{py(y):.4f}' for x, y in points))
                parts.append(f'<polyline points="{coords}" fill="none" stroke="#7863cf" stroke-width="1.7"/>')
            for v in g['vertices']:
                z = mob(f['darts'][v[0]], rho)
                parts.append(f'<circle cx="{px(z.real):.5f}" cy="{py(z.imag):.5f}" r="2" fill="#7863cf"/>')
        xx = [None] + xs + [None]
        for i, (a, b) in enumerate(zip(xx, xx[1:])):
            lab = f['labels'][i]
            m = f['darts'][f['labelDarts'][i]]
            if lab == 'odd':
                z = mob(m, rho)
                parts.extend([ideal_arc(z, a), ideal_arc(z, b)])
                parts.append(f'<path d="M{px(z.real):.5f},{py(z.imag)-4:.5f} l-4,7 h8 Z" fill="#9c2525"><title>order 3 elliptic point</title></path>')
                parts.append(f'<text x="{px(z.real)+7:.5f}" y="{py(z.imag):.5f}" font-size="12" fill="#9c2525">3</text>')
                continue
            parts.append(edge(a, b, 'black', 1.5))
            if lab == 'even':
                z = mob(m, 1j)
                parts.append(f'<circle cx="{px(z.real):.5f}" cy="{py(z.imag):.5f}" r="3" fill="#9c2525"><title>order 2 elliptic point</title></circle>')
            x = (a + b) / 2 if a is not None and b is not None else b if a is None else a
            y = py(abs(b - a) / 2) - 8 if a is not None and b is not None else top + 30
            parts.append(f'<text x="{px(x):.5f}" y="{y:.5f}" text-anchor="middle" font-size="14" fill="#9c2525">{f["labels"][i]}</text>')
        for (a, b), x in zip(f['x'], xs):
            lab = str(a) if b == 1 else f'{a}/{b}'
            parts.append(f'<text transform="translate({px(x):.5f},{base+20}) rotate(60)" font-size="12">{lab}</text>')
        (D / (name + ('-map-domain.svg' if dual else '-domain.svg'))).write_text('\n'.join(parts + ['</svg>']))
    count += 1
p = OUT / 'README.md'
lines = [line for line in p.read_text().splitlines() if not line.startswith(('Polygon and embedded-map SVGs', 'Elliptic points of orders'))]
names = {r['name'] for r in rows}
for i, line in enumerate(lines):
    if line.startswith('| '):
        name = line.split('|')[1].strip()
        if name in names:
            line = line.split(' · [polygon]')[0].rstrip().rstrip('|').rstrip() + ' |'
            lines[i] = line[:-1] + f' · [polygon](drawings/{name}-domain.svg) · [map in polygon](drawings/{name}-map-domain.svg) |'
lines.insert(4, 'Elliptic points of orders 2 and 3 are marked.')
p.write_text('\n'.join(lines) + '\n')
print('Rendered', count, 'special polygons and embedded maps')
