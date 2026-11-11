# PSL(2,13): Lean certificate audit

**Complete: all 13 components; 19 finite-level factorization obstructions; 13 explicit action-table bridges.**

Lean checked the action and Farey certificates and their table-equality bridges. All transitive axiom dependencies were audited against `propext`, `Classical.choice`, and `Quot.sound`. Computation uses `decide +kernel`. 

[Combined certificate](../../lean/table5-bundles/PSL_2_13.lean) · [Standalone action certificate](../../lean/table5-actions/PSL_2_13.lean) · [Machine-readable audit](lean-psl13-audit.json)

Action certificate: 77.030 s. Combined certificate with bridges: 76.673 s. Separate Farey files: 231.495 s summed over 13 files.

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
| PSL2_13_c0 | 108 | 38.161 | [Lean](../../lean/table5-farey/PSL2_13_c0.lean) |
| PSL2_13_c1 | 32 | 34.254 | [Lean](../../lean/table5-farey/PSL2_13_c1.lean) |
| PSL2_13_c2 | 98 | 18.876 | [Lean](../../lean/table5-farey/PSL2_13_c2.lean) |
| PSL2_13_c3 | 108 | 19.849 | [Lean](../../lean/table5-farey/PSL2_13_c3.lean) |
| PSL2_13_c4 | 28 | 13.802 | [Lean](../../lean/table5-farey/PSL2_13_c4.lean) |
| PSL2_13_c5 | 98 | 18.01 | [Lean](../../lean/table5-farey/PSL2_13_c5.lean) |
| PSL2_13_c6 | 28 | 13.523 | [Lean](../../lean/table5-farey/PSL2_13_c6.lean) |
| PSL2_13_c7 | 28 | 11.857 | [Lean](../../lean/table5-farey/PSL2_13_c7.lean) |
| PSL2_13_c8 | 36 | 11.944 | [Lean](../../lean/table5-farey/PSL2_13_c8.lean) |
| PSL2_13_c9 | 36 | 11.587 | [Lean](../../lean/table5-farey/PSL2_13_c9.lean) |
| PSL2_13_c10 | 52 | 11.992 | [Lean](../../lean/table5-farey/PSL2_13_c10.lean) |
| PSL2_13_c11 | 98 | 14.937 | [Lean](../../lean/table5-farey/PSL2_13_c11.lean) |
| PSL2_13_c12 | 52 | 12.703 | [Lean](../../lean/table5-farey/PSL2_13_c12.lean) |
