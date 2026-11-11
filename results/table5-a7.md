# Table 5: A7

Group order: 2520. GAP computation and separate full component export: 7.861 seconds. Whole process including startup: 9.513 seconds.

Generating-pair classes modulo inner conjugacy: 1832. Transitive components: 26. Merged rows: 17.

Row signatures were compared visually with the paper.

[Farey/graph data and drawings](table5-graphs/README.md) · [the Lean audit](table5-graphs/lean-a7-audit.md)

| m | SL degree | c4 | c6 | c−1 | Cusp widths (width^count) | Genus | e |
|---:|---:|---:|---:|---:|---|---:|---|
| 2 | 21 | 1 | 0 | 1 | 3^2 4^1 5^1 6^1 | 0 | 7 |
| 2 | 21 | 1 | 0 | 1 | 3^2 4^1 5^1 6^1 | 0 | 7 |
| 1 | 32 | 0 | 1 | 0 | 1^1 3^1 5^1 7^1 | 0 | 2 |
| 1 | 48 | 0 | 0 | 0 | 1^1 2^1 4^2 6^1 7^1 | 0 | 6 |
| 2 | 48 | 0 | 0 | 0 | 1^1 3^1 4^2 5^1 7^1 | 0 | 6 |
| 2 | 56 | 0 | 1 | 0 | 4^4 5^1 7^1 | 0 | 7 |
| 1 | 60 | 0 | 0 | 0 | 2^1 3^1 4^3 6^1 7^1 | 0 | 5 |
| 1 | 72 | 0 | 0 | 0 | 1^1 3^3 5^1 7^3 | 0 | 3 |
| 1 | 72 | 0 | 0 | 0 | 2^1 4^4 5^1 6^1 7^1 | 0 | 3 |
| 1 | 72 | 0 | 0 | 0 | 1^1 2^1 3^1 5^2 6^1 7^2 | 0 | 6 |
| 1 | 80 | 0 | 1 | 0 | 2^1 3^2 5^1 6^1 7^3 | 0 | 5 |
| 2 | 84 | 0 | 0 | 0 | 3^2 4^3 5^2 7^2 | 0 | 7 |
| 2 | 84 | 0 | 0 | 0 | 3^2 4^3 5^2 7^2 | 0 | 7 |
| 2 | 96 | 0 | 0 | 0 | 3^2 4^3 5^2 6^1 7^2 | 0 | 4 |
| 2 | 96 | 0 | 0 | 0 | 3^2 4^3 5^2 6^1 7^2 | 0 | 4 |
| 2 | 120 | 0 | 0 | 0 | 3^2 4^4 5^2 7^4 | 0 | 5 |
| 1 | 144 | 0 | 0 | 0 | 2^1 3^3 5^4 6^1 7^5 | 0 | 3 |

[Full rows and component actions](gap-table5-a7.jsonl) · [Timings](table5-a7-timings.json)

Reproduce from the project root:

```sh
../gap-4.16.1/gap -q -b --quitonbreak gap/run-table5-a7.g
```
