#!/usr/bin/env python3
"""Generate Lean certificates for Farey and graph data."""
import argparse, json, sys
from pathlib import Path
from generate_baseline import literal, lookup_tree, function, AUDIT
ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--data-dir', default='results/table4-graphs')
parser.add_argument('--output-dir', default='lean/farey')
parser.add_argument('--group', action='append')
args = parser.parse_args()
DATA = ROOT / args.data_dir
OUT = ROOT / args.output_dir
OUT.mkdir(parents=True, exist_ok=True)
inputs = {x['name']: x for x in json.loads((DATA / 'inputs.json').read_text())}
exports = json.loads((DATA / 'exports.json').read_text())
if args.group:
    exports = [r for r in exports if r['group'] in args.group]
    if {r['group'] for r in exports} != set(args.group):
        raise ValueError('Group missing from Farey data')
shared = (ROOT / 'lean/FareyChecks.lean').read_text().rsplit('end ChenFarey', 1)[0]
shared += (ROOT / 'lean/LookupTree.lean').read_text().split('namespace ChenMore', 1)[1].rsplit('end ChenMore', 1)[0]
shared += (ROOT / 'lean/CuspPartition.lean').read_text().split('namespace ChenMore', 1)[1].rsplit('end ChenMore', 1)[0]
shared = shared.replace('namespace ChenFarey', 'set_option maxRecDepth 32768\nset_option maxHeartbeats 0\nnamespace ChenFarey', 1)

def mat(m):
    return '⟨' + ','.join(map(str, m)) + '⟩'

def mul(a, b):
    A, B, C, D = a
    E, F, G, H = b
    return [A * E + B * G, A * F + B * H, C * E + D * G, C * F + D * H]

def inv(a):
    return [a[3], -a[1], -a[2], a[0]]
MS = [0, -1, 1, 0]
MU = [0, -1, 1, 1]

def word(m):
    a, b, c, d = m
    out = []
    while c:
        r = a % c
        q = (a - r) // c
        out += [f'.t ({q})', '.s']
        a, b = (a - q * c, b - q * d)
        a, b, c, d = (c, d, -a, -b)
    assert a in (-1, 1)
    out += [f'.t ({b//a})']
    return '[' + ','.join(out) + ']'

def witness(m, p):
    return '⟨' + mat(m) + ',' + word(m) + ',' + str(p) + '⟩'

def tree_def(name, values, typ, domain):
    return f'def {name}Data : LookupTree ({typ}) :=\n {lookup_tree(values)}\ndef {name} (p : Fin {domain}) : {typ} := tableLookup {name}Data p.val\n'

def thm(name, statement):
    return f'theorem {name} : {statement} := by decide +kernel\n'
manifest = []
for row in exports:
    name = row['name']
    src = inputs[name]
    g = row['graph']
    f = row['farey']
    n = len(src['S'])
    m = len(g['S'])
    parts = [shared, f'namespace {name}\n']
    for key, vals, dom, cod in [
        ('originalS', src['S'], n, n),
        ('originalT', src['T'], n, n),
        ('projection', g['projection'], n, m),
        ('representative', g['representatives'], m, n),
        ('S', g['S'], m, m),
        ('T', g['T'], m, m),
        ('Ti', [g['T'].index(i) for i in range(m)], m, m),
    ]:
        parts.append(function(key, vals, dom, cod, tree=True))
    parts.append(f'def U (p : Fin {m}) : Fin {m} := T (S p)\n')
    parts.append(thm('quotient_relations', f'(∀ p : Fin {m}, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p)'))
    parts.append(thm('projection_compatible', f'∀ p : Fin {n}, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p)'))
    parts.append(thm('central_quotient', f'(∀ p : Fin {n}, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin {m}, projection (representative q) = q)'))
    for key, P in [('vertices', 'U'), ('edges', 'S'), ('faces', 'T')]:
        cs = g[key]
        flat = sum(cs, [])
        idx = [flat.index(i) for i in range(m)]
        parts.append(f'def {key} : List (List (Fin {m})) := {literal(cs)}\n')
        parts.append(tree_def(key + 'Index', list(map(str, idx)), f'Fin {m}', m))
        parts.append(tree_def(key + 'Back', list(map(str, flat)), f'Fin {m}', m))
        parts.append(thm(key + '_index_inverse', f'∀ p : Fin {m}, {key}Back ({key}Index p) = p'))
        parts.append(thm(key + '_enumeration', f'{key}.flatten.map {key}Index = List.finRange {m}'))
        parts.append(f'theorem {key}_partition : ∀ p : Fin {m}, ({key}.flatten.filter (· == p)).length = 1 :=\n partition_from_index {key} {key}Index {key}Back {key}_index_inverse {key}_enumeration\n')
        parts.append(thm(key + '_cycles', f'{key}.all (follows {P}) = true'))
    parts.append(thm('vertex_valencies', 'vertices.all (fun v => v.length == 1 || v.length == 3) = true'))
    parts.append(thm('edge_valencies', 'edges.all (fun e => e.length == 1 || e.length == 2) = true'))
    widths = g['widths']
    genus = g['genus']
    c4 = f['check']['c4']
    c6 = f['check']['c6']
    parts.append(thm('cusp_widths', f'faces.map List.length = {literal([len(x) for x in g["faces"]])}'))
    parts.append(thm('euler_arithmetic', f'(2 - 2 * {genus} : Int) = {len(g["vertices"])} - {len(g["edges"])} + {len(g["faces"])} + {c4}'))
    parts.append(thm('elliptic_counts', f'(edges.filter (fun e => e.length == 1)).length = {c4} ∧ (vertices.filter (fun v => v.length == 1)).length = {c6}'))
    mats = f['darts']
    parts.append(tree_def('liftMatrix', [mat(x) for x in mats], 'Mat', m))
    parts.append(f'def lifts : List (Witness {m}) := [' + ','.join((witness(x, i) for i, x in enumerate(mats))) + ']\n')
    parts.append(f'theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=\n all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)\n')
    parts.append(thm('lift_matrices_match', f'lifts.length = {m} ∧ ((List.finRange {m}).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true'))
    sides = []
    for dart, lab in zip(f['labelDarts'], f['labels']):
        if lab == 'even':
            k = -2
            sm = mul(mul(mats[dart], MS), inv(mats[dart]))
        elif lab == 'odd':
            k = -3
            sm = mul(mul(mats[dart], MU), inv(mats[dart]))
        else:
            k = lab
            sm = f['pairs'][k - 1]
            sm = sm if dart < g['S'][dart] else inv(sm)
        sides.append('⟨' + str(dart) + ',' + str(k) + ',' + witness(sm, 0) + '⟩')
    parts.append(f'def sides : List (Side {m}) := [' + ','.join(sides) + ']\n')
    parts.append('theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=\n all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)\n')
    xs = [(1, 0)] + [tuple(x) for x in f['x']] + [(1, 0)]
    parts.append('def boundary : List (Int × Int) := [' + ','.join((f'({a},{b})' for a, b in xs)) + ']\n')
    parts.append('theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=\n all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)\n')
    parts.append(thm('boundary_matches_darts', '(adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true'))
    parts.append(thm('boundary_order', '(adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true'))
    labels = sorted({x for x in f['labels'] if isinstance(x, int)})
    parts.append(f'def freeLabels : List Int := {literal(labels)}\n')
    parts.append(thm('paired_sides', 'freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true'))
    parts.append(f'end {name}\n')
    parts.append(AUDIT.replace('ChenBaseline', 'ChenFarey'))
    text = ''.join(parts).replace('\ndef ', '\nnoncomputable def ').replace('\ninstance ', '\nnoncomputable instance ')
    path = OUT / (name + '.lean')
    path.write_text(text)
    manifest.append(dict(
        name=name,
        group=row['group'],
        component=row['component'],
        degree=n,
        psl_degree=m,
        source=str(path.relative_to(ROOT)),
    ))
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(f'Generated {len(manifest)} standalone certificates')
