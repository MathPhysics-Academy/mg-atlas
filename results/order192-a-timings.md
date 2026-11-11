# First order-192 batch

All 20 groups passed: 37 supplied components and 74 factorization obstructions.
Every file passed the audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

GAP wall time including startup: **7.141 seconds**.
Lean wall time for these 20 groups: **285.202 seconds**.

Single fresh sequential Lean invocation per new group; wall time includes Lake startup, Mathlib imports, kernel checking, and the axiom audit. Previously checked sources were reused by hash and excluded from these timings. GAP group times are CPU time; GAP total includes startup.

| Group | Components | Largest degree | Obstructions | GAP CPU seconds | Lean wall seconds |
|---|---:|---:|---:|---:|---:|
| [SmallGroup(192,180)](../lean/more/G192_180.lean) | 1 | 144 | 2 | 0.260 | 27.352 |
| [SmallGroup(192,181)](../lean/more/G192_181.lean) | 2 | 72 | 4 | 0.192 | 11.241 |
| [SmallGroup(192,182)](../lean/more/G192_182.lean) | 1 | 144 | 2 | 0.259 | 12.803 |
| [SmallGroup(192,184)](../lean/more/G192_184.lean) | 1 | 72 | 2 | 0.116 | 10.655 |
| [SmallGroup(192,185)](../lean/more/G192_185.lean) | 2 | 36 | 4 | 0.109 | 11.318 |
| [SmallGroup(192,189)](../lean/more/G192_189.lean) | 4 | 96 | 8 | 0.337 | 18.277 |
| [SmallGroup(192,190)](../lean/more/G192_190.lean) | 4 | 96 | 8 | 0.329 | 18.495 |
| [SmallGroup(192,194)](../lean/more/G192_194.lean) | 2 | 96 | 4 | 0.202 | 13.307 |
| [SmallGroup(192,195)](../lean/more/G192_195.lean) | 2 | 96 | 4 | 0.200 | 13.113 |
| [SmallGroup(192,196)](../lean/more/G192_196.lean) | 2 | 96 | 4 | 0.202 | 13.198 |
| [SmallGroup(192,197)](../lean/more/G192_197.lean) | 2 | 96 | 4 | 0.202 | 13.069 |
| [SmallGroup(192,198)](../lean/more/G192_198.lean) | 2 | 96 | 4 | 0.201 | 13.424 |
| [SmallGroup(192,199)](../lean/more/G192_199.lean) | 2 | 96 | 4 | 0.217 | 14.050 |
| [SmallGroup(192,201)](../lean/more/G192_201.lean) | 3 | 96 | 6 | 0.188 | 13.570 |
| [SmallGroup(192,202)](../lean/more/G192_202.lean) | 2 | 96 | 4 | 0.183 | 13.372 |
| [SmallGroup(192,944)](../lean/more/G192_944.lean) | 1 | 72 | 2 | 0.256 | 9.988 |
| [SmallGroup(192,945)](../lean/more/G192_945.lean) | 1 | 144 | 2 | 0.325 | 12.495 |
| [SmallGroup(192,946)](../lean/more/G192_946.lean) | 1 | 288 | 2 | 0.551 | 20.366 |
| [SmallGroup(192,947)](../lean/more/G192_947.lean) | 1 | 144 | 2 | 0.356 | 12.719 |
| [SmallGroup(192,948)](../lean/more/G192_948.lean) | 1 | 144 | 2 | 0.331 | 12.390 |

These certify the supplied finite actions. Enumeration completeness, merged-row
multiplicities, and the geometric and level theorems remain outside this formalization.

Fresh Lean timing run from the repository root:

```sh
bash lean/check.sh more G192_180.lean G192_181.lean G192_182.lean G192_184.lean G192_185.lean G192_189.lean G192_190.lean G192_194.lean G192_195.lean G192_196.lean G192_197.lean G192_198.lean G192_199.lean G192_201.lean G192_202.lean G192_944.lean G192_945.lean G192_946.lean G192_947.lean G192_948.lean
```
