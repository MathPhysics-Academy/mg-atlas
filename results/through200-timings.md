# Finish Table 4 through order 200

All eight groups passed: eight supplied components and 16 factorization obstructions.
Every file passed the audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

GAP wall time including startup: **10.502 seconds**.
Lean wall time for these eight groups: **693.575 seconds**.

Single fresh sequential Lean invocation per new group; wall time includes Lake startup, Mathlib imports, kernel checking, and the axiom audit. Previously checked sources were reused by hash and excluded from these timings. GAP group times are CPU time; GAP total includes startup.

| Group | Components | Largest degree | Obstructions | GAP CPU seconds | Lean wall seconds |
|---|---:|---:|---:|---:|---:|
| [SmallGroup(192,183)](../lean/more/G192_183.lean) | 1 | 576 | 2 | 0.685 | 62.506 |
| [SmallGroup(192,186)](../lean/more/G192_186.lean) | 1 | 576 | 2 | 0.744 | 55.017 |
| [SmallGroup(192,187)](../lean/more/G192_187.lean) | 1 | 576 | 2 | 0.586 | 53.188 |
| [SmallGroup(192,996)](../lean/more/G192_996.lean) | 1 | 768 | 2 | 1.123 | 91.335 |
| [SmallGroup(192,997)](../lean/more/G192_997.lean) | 1 | 768 | 2 | 1.149 | 85.228 |
| [SmallGroup(192,1012)](../lean/more/G192_1012.lean) | 1 | 768 | 2 | 1.163 | 78.817 |
| [SmallGroup(192,200)](../lean/more/G192_200.lean) | 1 | 1536 | 2 | 1.263 | 138.618 |
| [SmallGroup(192,204)](../lean/more/G192_204.lean) | 1 | 1536 | 2 | 1.246 | 128.866 |

These certify the supplied finite actions. Enumeration completeness, merged-row
multiplicities, and the geometric and level theorems remain outside this formalization.

Fresh Lean timing run from the repository root:

```sh
bash lean/check.sh more G192_183.lean G192_186.lean G192_187.lean G192_996.lean G192_997.lean G192_1012.lean G192_200.lean G192_204.lean
```
