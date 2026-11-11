# Table 5: PSL(2,17)

Group order: 2448. GAP computation and separate full component export: 12.994 seconds. Whole process including startup: 14.818 seconds.

Generating-pair classes modulo inner conjugacy: 2264. Transitive components: 17. Merged rows: 16.

Row signatures were compared visually with the paper.

[Farey/graph data and drawings](table5-graphs/README.md) · [the Lean audit](table5-graphs/lean-psl17-audit.md)

| m | SL degree | c4 | c6 | c−1 | Cusp widths (width^count) | Genus | e |
|---:|---:|---:|---:|---:|---|---:|---|
| 2 | 85 | 1 | 1 | 1 | 2^4 3^3 4^2 8^2 9^3 17^1 | 0 | 17 |
| 1 | 108 | 0 | 0 | 0 | 1^1 2^1 3^3 4^2 8^2 9^2 | 0 | 9 |
| 1 | 108 | 0 | 3 | 0 | 1^1 2^1 4^2 8^2 9^3 | 0 | 3 |
| 1 | 108 | 0 | 0 | 0 | 1^1 2^1 3^3 4^2 8^2 9^2 | 0 | 9 |
| 1 | 108 | 0 | 0 | 0 | 1^1 2^1 3^3 4^2 8^2 9^2 | 0 | 9 |
| 1 | 128 | 0 | 1 | 0 | 2^2 3^3 4^2 8^2 9^3 | 0 | 8 |
| 1 | 128 | 0 | 1 | 0 | 2^2 3^3 4^2 8^2 9^3 | 0 | 8 |
| 1 | 128 | 0 | 1 | 0 | 2^2 3^3 4^2 8^2 9^3 | 0 | 8 |
| 1 | 128 | 0 | 1 | 0 | 2^2 3^3 4^2 8^2 9^3 | 0 | 8 |
| 1 | 144 | 0 | 6 | 1 | 2^2 3^4 4^2 8^4 9^6 17^2 | 1 | 3 |
| 1 | 162 | 2 | 0 | 1 | 2^4 3^6 4^4 8^4 9^6 17^2 | 1 | 9 |
| 1 | 162 | 2 | 0 | 1 | 2^4 3^6 4^4 8^4 9^6 17^2 | 1 | 9 |
| 1 | 162 | 2 | 0 | 1 | 2^4 3^6 4^4 8^4 9^6 17^2 | 1 | 9 |
| 1 | 168 | 4 | 0 | 1 | 2^2 3^4 4^8 8^4 9^6 17^2 | 1 | 2 |
| 1 | 176 | 0 | 2 | 1 | 1^2 2^2 3^6 4^4 8^6 9^6 17^2 | 1 | 4 |
| 1 | 176 | 0 | 2 | 1 | 1^2 2^2 3^6 4^4 8^6 9^6 17^2 | 1 | 4 |

[Full rows and component actions](gap-table5-psl17.jsonl) · [Timings](table5-psl17-timings.json)

Reproduce from the project root:

```sh
../gap-4.16.1/gap -q -b --quitonbreak gap/run-table5-psl17.g
```
