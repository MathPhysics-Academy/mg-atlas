# Farey construction

23 groups and 652 components.

[Inputs](inputs.json) · [Exports](exports.json) · [Timing data](timings.json) · [GAP log](gap.log)

`gap/farey.g` constructs the polygons and checks boundary determinants, side-pairing words and elliptic traces. `gap/graph-export-lib.g` computes graph actions and checks their invariants.

Lean certificates cover 56 components. [PSL(2,17)](lean-psl17-audit.md) · [A7](lean-a7-audit.md) · [PSL(2,13)](lean-psl13-audit.md)

[Certificate scope](../../lean/README.md)

## Timings

| Group | Components | GAP seconds |
|---|---:|---:|
| A5 | 3 | 0.002 |
| PSL(2,7) | 5 | 0.003 |
| A6 | 10 | 0.009 |
| PSL(2,8) | 7 | 0.020 |
| PSL(2,11) | 10 | 0.015 |
| PSL(2,13) | 13 | 0.036 |
| PSL(2,17) | 17 | 0.150 |
| A7 | 26 | 0.039 |
| PSL(2,19) | 19 | 0.095 |
| PSL(2,16) | 15 | 0.181 |
| PSL(3,3) | 15 | 0.116 |
| PSU(3,3) | 13 | 0.134 |
| PSL(2,23) | 23 | 0.174 |
| PSL(2,25) | 25 | 0.273 |
| M11 | 12 | 0.171 |
| PSL(2,27) | 27 | 0.293 |
| PSL(2,29) | 29 | 0.411 |
| PSL(2,31) | 31 | 0.466 |
| A8 | 26 | 0.418 |
| PSL(3,4) | 205 | 0.404 |
| PSL(2,37) | 37 | 0.912 |
| PSp(4,3) | 42 | 0.644 |
| Sz(8) | 42 | 0.837 |

Process wall time was 8.843 seconds, including startup. Component times include two Farey calls for export and invariant comparison.

## Reproduce

```sh
python3 tools/run-table5-farey.py --archive RUN-NAME --input-dir results/table5-gap
```
