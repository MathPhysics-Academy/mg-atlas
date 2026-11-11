# PSL(2,17): Lean certificate audit

**Complete: all 17 components; 25 finite-level factorization obstructions; 17 explicit action-table bridges.**

Lean checked the action and Farey certificates and their table-equality bridges. All transitive axiom dependencies were audited against `propext`, `Classical.choice`, and `Quot.sound`. Computation uses `decide +kernel`. 

[Combined certificate](../../lean/table5-bundles/PSL_2_17.lean) · [Standalone action certificate](../../lean/table5-actions/PSL_2_17.lean) · [Machine-readable audit](lean-psl17-audit.json)

Action certificate: 266.525 s. Combined certificate with bridges: 378.403 s. Separate Farey files: 600.677 s summed over 17 files.

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
| PSL2_17_c0 | 176 | 40.673 | [Lean](../../lean/table5-farey/PSL2_17_c0.lean) |
| PSL2_17_c1 | 54 | 32.986 | [Lean](../../lean/table5-farey/PSL2_17_c1.lean) |
| PSL2_17_c2 | 162 | 39.591 | [Lean](../../lean/table5-farey/PSL2_17_c2.lean) |
| PSL2_17_c3 | 64 | 18.64 | [Lean](../../lean/table5-farey/PSL2_17_c3.lean) |
| PSL2_17_c4 | 54 | 20.821 | [Lean](../../lean/table5-farey/PSL2_17_c4.lean) |
| PSL2_17_c5 | 64 | 22.242 | [Lean](../../lean/table5-farey/PSL2_17_c5.lean) |
| PSL2_17_c6 | 64 | 24.607 | [Lean](../../lean/table5-farey/PSL2_17_c6.lean) |
| PSL2_17_c7 | 168 | 43.755 | [Lean](../../lean/table5-farey/PSL2_17_c7.lean) |
| PSL2_17_c8 | 85 | 30.059 | [Lean](../../lean/table5-farey/PSL2_17_c8.lean) |
| PSL2_17_c9 | 54 | 30.307 | [Lean](../../lean/table5-farey/PSL2_17_c9.lean) |
| PSL2_17_c10 | 64 | 29.875 | [Lean](../../lean/table5-farey/PSL2_17_c10.lean) |
| PSL2_17_c11 | 162 | 47.061 | [Lean](../../lean/table5-farey/PSL2_17_c11.lean) |
| PSL2_17_c12 | 54 | 29.394 | [Lean](../../lean/table5-farey/PSL2_17_c12.lean) |
| PSL2_17_c13 | 144 | 47.018 | [Lean](../../lean/table5-farey/PSL2_17_c13.lean) |
| PSL2_17_c14 | 162 | 53.448 | [Lean](../../lean/table5-farey/PSL2_17_c14.lean) |
| PSL2_17_c15 | 176 | 53.928 | [Lean](../../lean/table5-farey/PSL2_17_c15.lean) |
| PSL2_17_c16 | 85 | 36.272 | [Lean](../../lean/table5-farey/PSL2_17_c16.lean) |
