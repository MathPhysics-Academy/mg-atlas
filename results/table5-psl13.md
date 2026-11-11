# Table 5 pilot: PSL(2,13)

Group order: 1092. GAP reported 2.984 seconds for table computation plus the separate component-action export; total process wall time was 5.419 seconds, including startup.

Generating-pair classes modulo inner conjugacy: 990. Supplied transitive action components: 13. Merged table rows: 12.

Visual comparison matched the 12 Table 5 rows.

[Farey/graph data and drawings](table5-graphs/README.md) · [the Lean audit](table5-graphs/lean-psl13-audit.md)

| m | SL degree | c4 | c6 | c−1 | Cusp widths (width^count) | Genus | e |
|---:|---:|---:|---:|---:|---|---:|---|
| 2 | 52 | 0 | 1 | 1 | 2^3 3^2 6^1 7^3 13^1 | 0 | 13 |
| 1 | 56 | 0 | 1 | 0 | 2^1 3^2 6^1 7^2 | 0 | 7 |
| 1 | 56 | 0 | 1 | 0 | 2^1 3^2 6^1 7^2 | 0 | 7 |
| 1 | 56 | 0 | 1 | 0 | 2^1 3^2 6^1 7^2 | 0 | 7 |
| 1 | 64 | 0 | 2 | 0 | 2^1 3^1 6^1 7^3 | 0 | 2 |
| 1 | 72 | 0 | 0 | 0 | 1^1 2^1 3^2 6^1 7^3 | 0 | 6 |
| 1 | 72 | 0 | 0 | 0 | 1^1 2^1 3^2 6^1 7^3 | 0 | 6 |
| 1 | 98 | 0 | 2 | 1 | 2^3 3^4 6^2 7^6 13^2 | 0 | 7 |
| 1 | 98 | 0 | 2 | 1 | 2^3 3^4 6^2 7^6 13^2 | 0 | 7 |
| 1 | 98 | 0 | 2 | 1 | 2^3 3^4 6^2 7^6 13^2 | 0 | 7 |
| 1 | 108 | 0 | 0 | 1 | 2^2 3^8 6^2 7^6 13^2 | 0 | 3 |
| 1 | 108 | 0 | 0 | 1 | 2^2 3^4 6^4 7^6 13^2 | 1 | 3 |

[Full rows and all component S,T arrays](gap-table5-psl13.jsonl) · [Timing record](table5-psl13-timings.json)

Reproduce from the project root:

```sh
../gap-4.16.1/gap -q -b --quitonbreak gap/run-table5-psl13.g
```
