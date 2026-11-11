# Farey certificates

218 Table 4 groups and 376 components.

[Data and diagrams](README.md) · [Lean audit](lean-audit.md) · [Certificate scope](../../lean/README.md)

`gap/farey.g` constructs the polygons. The Lean files in `lean/farey/` check
graph partitions, matrix and word witnesses, side pairings and Farey boundaries.
The matrix-word statements use the PSL quotient, with signs identified.

## Reproduce

Run from the project root with GAP on `PATH`.

```sh
python3 tools/export-table4-farey.py
gap -q -b --quitonbreak results/table4-graphs/export.g > results/table4-graphs/gap.log 2>&1
python3 -c 'import json,pathlib; p=pathlib.Path("results/table4-graphs"); (p/"exports.json").write_text(json.dumps([json.loads(s[7:]) for s in (p/"gap.log").read_text().splitlines() if s.startswith("@@JSON ")])+"\n")'
python3 tools/generate_farey.py
bash lean/check-farey.sh --jobs 2
python3 tools/audit_farey.py
python3 tools/render-table4-graphs.py
python3 tools/render-table4-domains.py
```

Receipts record compiler results and source hashes. Per-file wall times include
startup and concurrent load.
