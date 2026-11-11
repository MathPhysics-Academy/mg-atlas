# Smaller remaining order-216 actions

All 19 groups passed: 36 supplied components and 66 factorization obstructions.
Every file passed the audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

GAP wall time including startup: **7.967 seconds**.
Lean wall time for these 19 groups: **318.366 seconds**.

Single fresh sequential Lean invocation per new group; wall time includes Lake startup, Mathlib imports, kernel checking, and the axiom audit. Previously checked sources were reused by hash and excluded from these timings. GAP group times are CPU time; GAP total includes startup.

| Group | Components | Largest degree | Obstructions | GAP CPU seconds | Lean wall seconds |
|---|---:|---:|---:|---:|---:|
| [SmallGroup(216,33)](../lean/more/G216_33.lean) | 1 | 72 | 1 | 0.245 | 9.103 |
| [SmallGroup(216,34)](../lean/more/G216_34.lean) | 1 | 72 | 2 | 0.324 | 9.460 |
| [SmallGroup(216,35)](../lean/more/G216_35.lean) | 2 | 36 | 4 | 0.213 | 9.920 |
| [SmallGroup(216,36)](../lean/more/G216_36.lean) | 1 | 72 | 2 | 0.246 | 10.882 |
| [SmallGroup(216,37)](../lean/more/G216_37.lean) | 2 | 36 | 4 | 0.218 | 10.146 |
| [SmallGroup(216,39)](../lean/more/G216_39.lean) | 2 | 288 | 4 | 0.471 | 32.630 |
| [SmallGroup(216,41)](../lean/more/G216_41.lean) | 2 | 288 | 4 | 0.463 | 32.762 |
| [SmallGroup(216,42)](../lean/more/G216_42.lean) | 6 | 96 | 12 | 0.452 | 22.675 |
| [SmallGroup(216,86)](../lean/more/G216_86.lean) | 1 | 144 | 2 | 0.131 | 12.818 |
| [SmallGroup(216,87)](../lean/more/G216_87.lean) | 3 | 24 | 3 | 0.113 | 10.564 |
| [SmallGroup(216,88)](../lean/more/G216_88.lean) | 2 | 108 | 4 | 0.198 | 16.433 |
| [SmallGroup(216,90)](../lean/more/G216_90.lean) | 1 | 72 | 2 | 0.219 | 10.578 |
| [SmallGroup(216,91)](../lean/more/G216_91.lean) | 3 | 72 | 6 | 0.373 | 14.273 |
| [SmallGroup(216,92)](../lean/more/G216_92.lean) | 1 | 72 | 2 | 0.220 | 11.323 |
| [SmallGroup(216,100)](../lean/more/G216_100.lean) | 2 | 216 | 4 | 0.401 | 31.425 |
| [SmallGroup(216,157)](../lean/more/G216_157.lean) | 1 | 192 | 2 | 0.323 | 18.498 |
| [SmallGroup(216,158)](../lean/more/G216_158.lean) | 1 | 48 | 2 | 0.180 | 12.371 |
| [SmallGroup(216,159)](../lean/more/G216_159.lean) | 2 | 24 | 2 | 0.137 | 10.735 |
| [SmallGroup(216,163)](../lean/more/G216_163.lean) | 2 | 216 | 4 | 0.757 | 31.770 |

These certify the supplied finite actions. Enumeration completeness, merged-row
multiplicities, and the geometric and level theorems remain outside this formalization.

Fresh Lean timing run from the repository root:

```sh
bash lean/check.sh more G216_33.lean G216_34.lean G216_35.lean G216_36.lean G216_37.lean G216_39.lean G216_41.lean G216_42.lean G216_86.lean G216_87.lean G216_88.lean G216_90.lean G216_91.lean G216_92.lean G216_100.lean G216_157.lean G216_158.lean G216_159.lean G216_163.lean
```
