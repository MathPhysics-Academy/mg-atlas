# Remaining small actions through order 200

All 17 groups passed: 21 supplied components and 35 factorization obstructions.
Every file passed the audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

GAP wall time including startup: **7.726 seconds**.
Lean wall time for these 17 groups: **261.025 seconds**.

Single fresh sequential Lean invocation per new group; wall time includes Lake startup, Mathlib imports, kernel checking, and the axiom audit. Previously checked sources were reused by hash and excluded from these timings. GAP group times are CPU time; GAP total includes startup.

| Group | Components | Largest degree | Obstructions | GAP CPU seconds | Lean wall seconds |
|---|---:|---:|---:|---:|---:|
| [SmallGroup(192,1003)](../lean/more/G192_1003.lean) | 1 | 192 | 2 | 0.620 | 30.339 |
| [SmallGroup(192,1004)](../lean/more/G192_1004.lean) | 1 | 192 | 2 | 0.511 | 16.048 |
| [SmallGroup(192,1005)](../lean/more/G192_1005.lean) | 1 | 192 | 2 | 0.533 | 20.237 |
| [SmallGroup(192,1006)](../lean/more/G192_1006.lean) | 1 | 192 | 2 | 0.532 | 18.215 |
| [SmallGroup(192,1007)](../lean/more/G192_1007.lean) | 1 | 192 | 2 | 0.529 | 17.519 |
| [SmallGroup(192,1017)](../lean/more/G192_1017.lean) | 1 | 96 | 2 | 0.332 | 13.255 |
| [SmallGroup(192,1018)](../lean/more/G192_1018.lean) | 1 | 96 | 2 | 0.328 | 14.440 |
| [SmallGroup(192,1019)](../lean/more/G192_1019.lean) | 1 | 96 | 2 | 0.326 | 14.711 |
| [SmallGroup(192,1489)](../lean/more/G192_1489.lean) | 1 | 72 | 1 | 0.190 | 13.001 |
| [SmallGroup(192,1490)](../lean/more/G192_1490.lean) | 1 | 72 | 2 | 0.192 | 11.472 |
| [SmallGroup(192,1491)](../lean/more/G192_1491.lean) | 3 | 36 | 3 | 0.152 | 13.213 |
| [SmallGroup(192,1492)](../lean/more/G192_1492.lean) | 1 | 72 | 2 | 0.164 | 12.019 |
| [SmallGroup(192,1493)](../lean/more/G192_1493.lean) | 2 | 36 | 4 | 0.156 | 12.091 |
| [SmallGroup(192,1494)](../lean/more/G192_1494.lean) | 1 | 72 | 1 | 0.156 | 15.456 |
| [SmallGroup(192,1495)](../lean/more/G192_1495.lean) | 2 | 36 | 4 | 0.259 | 13.112 |
| [SmallGroup(192,1538)](../lean/more/G192_1538.lean) | 1 | 36 | 1 | 0.251 | 11.978 |
| [SmallGroup(200,43)](../lean/more/G200_43.lean) | 1 | 72 | 1 | 0.121 | 13.919 |

These certify the supplied finite actions. Enumeration completeness, merged-row
multiplicities, and the geometric and level theorems remain outside this formalization.

Fresh Lean timing run from the repository root:

```sh
bash lean/check.sh more G192_1003.lean G192_1004.lean G192_1005.lean G192_1006.lean G192_1007.lean G192_1017.lean G192_1018.lean G192_1019.lean G192_1489.lean G192_1490.lean G192_1491.lean G192_1492.lean G192_1493.lean G192_1494.lean G192_1495.lean G192_1538.lean G200_43.lean
```
