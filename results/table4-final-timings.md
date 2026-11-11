# Final Table 4 batch

All 20 groups passed: 43 supplied components and 70 factorization obstructions.
Every file passed the audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

GAP wall time including startup: **16.567 seconds**.
Lean wall time for these 20 groups: **1278.518 seconds**.

Single fresh sequential Lean invocation per new group; wall time includes Lake startup, Mathlib imports, kernel checking, and the axiom audit. Previously checked sources were reused by hash and excluded from these timings. GAP group times are CPU time; GAP total includes startup. The separate final baseline refresh is excluded.

| Group | Components | Largest degree | Obstructions | GAP CPU seconds | Lean wall seconds |
|---|---:|---:|---:|---:|---:|
| [SmallGroup(240,194)](../lean/more/G240_194.lean) | 2 | 18 | 2 | 0.318 | 25.948 |
| [SmallGroup(240,197)](../lean/more/G240_197.lean) | 4 | 18 | 4 | 0.356 | 9.838 |
| [SmallGroup(240,105)](../lean/more/G240_105.lean) | 4 | 36 | 4 | 0.301 | 12.076 |
| [SmallGroup(240,106)](../lean/more/G240_106.lean) | 4 | 36 | 8 | 0.308 | 11.172 |
| [SmallGroup(240,107)](../lean/more/G240_107.lean) | 4 | 36 | 8 | 0.369 | 11.287 |
| [SmallGroup(240,192)](../lean/more/G240_192.lean) | 2 | 36 | 4 | 0.148 | 9.803 |
| [SmallGroup(240,189)](../lean/more/G240_189.lean) | 3 | 48 | 3 | 0.287 | 11.812 |
| [SmallGroup(240,108)](../lean/more/G240_108.lean) | 2 | 96 | 4 | 0.363 | 13.111 |
| [SmallGroup(240,109)](../lean/more/G240_109.lean) | 2 | 96 | 4 | 0.376 | 13.170 |
| [SmallGroup(240,190)](../lean/more/G240_190.lean) | 3 | 108 | 3 | 0.529 | 16.278 |
| [SmallGroup(216,25)](../lean/more/G216_25.lean) | 2 | 432 | 4 | 0.421 | 49.548 |
| [SmallGroup(240,196)](../lean/more/G240_196.lean) | 1 | 432 | 2 | 0.934 | 29.117 |
| [SmallGroup(216,89)](../lean/more/G216_89.lean) | 1 | 648 | 2 | 0.777 | 50.131 |
| [SmallGroup(216,38)](../lean/more/G216_38.lean) | 2 | 864 | 4 | 1.304 | 161.653 |
| [SmallGroup(216,40)](../lean/more/G216_40.lean) | 2 | 864 | 4 | 1.329 | 166.523 |
| [SmallGroup(240,102)](../lean/more/G240_102.lean) | 1 | 864 | 2 | 0.833 | 75.533 |
| [SmallGroup(240,103)](../lean/more/G240_103.lean) | 1 | 864 | 2 | 0.831 | 74.945 |
| [SmallGroup(240,104)](../lean/more/G240_104.lean) | 1 | 864 | 2 | 1.009 | 74.632 |
| [SmallGroup(240,153)](../lean/more/G240_153.lean) | 1 | 2304 | 2 | 1.595 | 228.885 |
| [SmallGroup(240,154)](../lean/more/G240_154.lean) | 1 | 2304 | 2 | 1.606 | 233.056 |

[Full Table 4 audit](table4-final-audit.md)

These certify the supplied finite actions. Enumeration completeness, group-label
identification, merged-row multiplicities, and the geometric and level theorems
remain outside this formalization.

Fresh Lean timing run from the repository root:

```sh
bash lean/check.sh more G240_194.lean G240_197.lean G240_105.lean G240_106.lean G240_107.lean G240_192.lean G240_189.lean G240_108.lean G240_109.lean G240_190.lean G216_25.lean G240_196.lean G216_89.lean G216_38.lean G216_40.lean G240_102.lean G240_103.lean G240_104.lean G240_153.lean G240_154.lean
```
