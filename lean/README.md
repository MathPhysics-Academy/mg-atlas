# Lean certificates

| Dataset | Groups | Components | Finite-level obstructions |
|---|---:|---:|---:|
| Table 4 | 218 | 376 | 639 |
| Table 5 | 3 | 56 | 92 |

[Table 4 action audit](../results/table4-final-audit.md) · [Table 4 Farey audit](../results/table4-graphs/lean-audit.md) · [Table 5 coverage](../results/table5-graphs/lean-coverage.md)

The action certificates verify permutations, modular relations, transitivity,
central quotients, elliptic counts, cusp cycles and widths, genus arithmetic,
and finite-modulus word collisions.

The Farey certificates verify graph partitions, determinant-one matrix lifts,
word witnesses, side pairings and boundary determinants. Table 5 combined
certificates also prove equality between the action tables used by both layers.
Matrix-word statements in the Farey layer use the PSL quotient, with signs identified.

Lean checks finite computations by kernel reduction. Axiom audits permit
`propext`, `Classical.choice` and `Quot.sound`.

Enumeration completeness, identification with the named groups, merged-row
multiplicities, geometric fundamental-domain correctness, the geometric genus
interpretation and general congruence-level theorems remain open.

## Sources

- `BaselineCertificates.lean` and `S4Certificate.lean` contain the initial cases.
- `more/` contains the remaining action certificates and earlier simple-group examples.
- `farey/` contains Table 4 graph and Farey certificates.
- `table5-actions/`, `table5-farey/` and `table5-bundles/` contain Table 5 certificates.
- `CuspPartition.lean`, `LookupTree.lean` and `FareyChecks.lean` provide shared definitions.
- `../tools/` contains certificate generators, compiler runners and receipt audits.

## Checking

Run commands from the project root.

```sh
bash lean/check.sh baseline
bash lean/check.sh more --resume
bash lean/check-farey.sh --jobs 2
bash lean/check-farey.sh --source-dir lean/table5-bundles \
  --results-dir results/table5-graphs/lean-bundles --jobs 2
python3 tools/audit_table4.py
python3 tools/audit_farey.py
python3 tools/audit_table5_pilot.py --groups psl13 psl17 a7
```

The shell runners use `LEAN_ROOT` or source an existing external `lean/env.sh`.
`MG_ATLAS_LEAN_ENV` selects another environment script. The recorded toolchain
is Lean 4.35.0-rc4 with a precompiled Mathlib checkout at `$LEAN_ROOT/mathlib4`.
Receipts include source hashes, compiler exit codes and axiom-audit results.

Generators read the saved GAP JSON files in `results/`. Construction and
regeneration commands are linked from the dataset audit reports.
