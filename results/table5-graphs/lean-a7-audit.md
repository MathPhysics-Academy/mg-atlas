# A7: Lean certificate audit

**Complete: all 26 components; 48 finite-level factorization obstructions; 26 explicit action-table bridges.**

Lean checked the action and Farey certificates and their table-equality bridges. All transitive axiom dependencies were audited against `propext`, `Classical.choice`, and `Quot.sound`. Computation uses `decide +kernel`. 

[Combined certificate](../../lean/table5-bundles/A7.lean) · [Standalone action certificate](../../lean/table5-actions/A7.lean) · [Machine-readable audit](lean-a7-audit.json)

Action certificate: 157.605 s. Combined certificate with bridges: 251.026 s. Separate Farey files: 540.151 s summed over 26 files.

Wall times include startup and concurrent load.

[Certificate scope](../../lean/README.md)

## Reproduce

From the project root:

```sh
python3 tools/generate_more.py --input results/gap-table5-psl13.jsonl --input results/gap-table5-psl17.jsonl --input results/gap-table5-a7.jsonl --output-dir lean/table5-actions --summary-output results/lean-table5-action-inputs.json
python3 tools/generate_farey.py --data-dir results/table5-graphs --output-dir lean/table5-farey --group 'PSL(2,13)' --group 'PSL(2,17)' --group A7
bash lean/check-farey.sh --source-dir lean/table5-actions --results-dir results/table5-graphs/lean-actions --jobs 2
bash lean/check-farey.sh --source-dir lean/table5-farey --results-dir results/table5-graphs/lean --jobs 3
python3 tools/bundle_table5_pilot.py
bash lean/check-farey.sh --source-dir lean/table5-bundles --results-dir results/table5-graphs/lean-bundles --jobs 2
python3 tools/audit_table5_pilot.py --groups psl13 psl17 a7
```

| Component | PSL degree | Standalone Farey seconds | Source |
|---|---:|---:|---|
| A7_c0 | 30 | 26.403 | [Lean](../../lean/table5-farey/A7_c0.lean) |
| A7_c1 | 40 | 26.769 | [Lean](../../lean/table5-farey/A7_c1.lean) |
| A7_c2 | 72 | 31.475 | [Lean](../../lean/table5-farey/A7_c2.lean) |
| A7_c3 | 24 | 24.318 | [Lean](../../lean/table5-farey/A7_c3.lean) |
| A7_c4 | 36 | 24.379 | [Lean](../../lean/table5-farey/A7_c4.lean) |
| A7_c5 | 16 | 22.688 | [Lean](../../lean/table5-farey/A7_c5.lean) |
| A7_c6 | 36 | 25.147 | [Lean](../../lean/table5-farey/A7_c6.lean) |
| A7_c7 | 36 | 23.446 | [Lean](../../lean/table5-farey/A7_c7.lean) |
| A7_c8 | 60 | 25.323 | [Lean](../../lean/table5-farey/A7_c8.lean) |
| A7_c9 | 60 | 24.544 | [Lean](../../lean/table5-farey/A7_c9.lean) |
| A7_c10 | 21 | 18.919 | [Lean](../../lean/table5-farey/A7_c10.lean) |
| A7_c11 | 21 | 17.397 | [Lean](../../lean/table5-farey/A7_c11.lean) |
| A7_c12 | 42 | 18.416 | [Lean](../../lean/table5-farey/A7_c12.lean) |
| A7_c13 | 42 | 16.586 | [Lean](../../lean/table5-farey/A7_c13.lean) |
| A7_c14 | 48 | 18.266 | [Lean](../../lean/table5-farey/A7_c14.lean) |
| A7_c15 | 48 | 18.954 | [Lean](../../lean/table5-farey/A7_c15.lean) |
| A7_c16 | 48 | 19.09 | [Lean](../../lean/table5-farey/A7_c16.lean) |
| A7_c17 | 48 | 19.345 | [Lean](../../lean/table5-farey/A7_c17.lean) |
| A7_c18 | 42 | 18.52 | [Lean](../../lean/table5-farey/A7_c18.lean) |
| A7_c19 | 21 | 16.6 | [Lean](../../lean/table5-farey/A7_c19.lean) |
| A7_c20 | 42 | 18.355 | [Lean](../../lean/table5-farey/A7_c20.lean) |
| A7_c21 | 21 | 16.453 | [Lean](../../lean/table5-farey/A7_c21.lean) |
| A7_c22 | 24 | 17.03 | [Lean](../../lean/table5-farey/A7_c22.lean) |
| A7_c23 | 24 | 17.247 | [Lean](../../lean/table5-farey/A7_c23.lean) |
| A7_c24 | 28 | 17.656 | [Lean](../../lean/table5-farey/A7_c24.lean) |
| A7_c25 | 28 | 16.825 | [Lean](../../lean/table5-farey/A7_c25.lean) |
