# Tools

These scripts reproduce the Farey exports and diagrams, generate Lean sources,
and run Lean checks. Run them from the project root. Python checks of receipts
and coverage do not replace Lean compilation.

| Scripts | Purpose |
|---|---|
| `export-table4-farey.py`, `export-table5-farey.py` | Prepare GAP Farey export jobs from saved actions |
| `run-table5-farey.py` | Run the Table 5 export job and render its output |
| `render-table4-graphs.py`, `render-table4-domains.py` | Render diagrams for either table |
| `generate_baseline.py`, `generate_more.py` | Generate action certificates; the baseline module also supplies shared generator functions |
| `generate_farey.py` | Generate graph and Farey certificates |
| `bundle_table5_pilot.py` | Combine Table 5 action and Farey certificates with equality bridges |
| `check_more.py`, `check_farey.py` | Invoke Lean and record compiler results and axiom audits; normally called through `lean/check*.sh` |
| `audit_table4.py`, `audit_farey.py`, `audit_table5_pilot.py` | Check coverage and match current sources to saved Lean receipts |
| `table5_lean_status.py` | Shared receipt and source-fingerprint checks used by the audit and rendering scripts |

See the [GAP guide](../gap/README.md) for export commands and the
[Lean guide](../lean/README.md) for checking commands.
