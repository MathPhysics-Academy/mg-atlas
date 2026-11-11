# Remaining proposed Table 4 groups

All 17 remaining groups passed Lean: 58 supplied components and 92
factorization obstructions. Every file passed the audit allowing only
`propext`, `Classical.choice`, and `Quot.sound`.

Together with the three order-96 groups, all 20 proposed groups are checked:
62 supplied components and 98 factorization obstructions.

GAP wall time including startup: **7.431 seconds**.
Lean wall time for these 17 groups: **262.330 seconds**.

Single fresh sequential Lean invocation per new group; wall time includes Lake startup, Mathlib imports, kernel checking, and the axiom audit. Previously checked groups were reused by source hash and excluded from these timings. GAP group times are CPU time; GAP total includes startup.

| Group | Components | Largest degree | Obstructions | GAP CPU seconds | Lean wall seconds |
|---|---:|---:|---:|---:|---:|
| [SmallGroup(128,134)](../lean/more/G128_134.lean) | 1 | 96 | 2 | 0.139 | 8.763 |
| [SmallGroup(128,136)](../lean/more/G128_136.lean) | 1 | 96 | 2 | 0.129 | 9.793 |
| [SmallGroup(128,137)](../lean/more/G128_137.lean) | 1 | 96 | 2 | 0.133 | 10.058 |
| [SmallGroup(144,117)](../lean/more/G144_117.lean) | 2 | 48 | 4 | 0.195 | 10.052 |
| [SmallGroup(144,157)](../lean/more/G144_157.lean) | 2 | 288 | 4 | 0.542 | 31.633 |
| [SmallGroup(160,234)](../lean/more/G160_234.lean) | 6 | 15 | 6 | 0.084 | 10.690 |
| [SmallGroup(168,23)](../lean/more/G168_23.lean) | 6 | 32 | 12 | 0.158 | 13.695 |
| [SmallGroup(168,43)](../lean/more/G168_43.lean) | 2 | 56 | 4 | 0.091 | 10.933 |
| [SmallGroup(168,46)](../lean/more/G168_46.lean) | 6 | 9 | 6 | 0.148 | 9.940 |
| [SmallGroup(180,19)](../lean/more/G180_19.lean) | 3 | 144 | 6 | 0.298 | 16.599 |
| [SmallGroup(216,21)](../lean/more/G216_21.lean) | 9 | 9 | 9 | 0.239 | 10.661 |
| [SmallGroup(216,153)](../lean/more/G216_153.lean) | 4 | 32 | 8 | 0.087 | 11.120 |
| [SmallGroup(240,90)](../lean/more/G240_90.lean) | 3 | 96 | 6 | 0.502 | 13.999 |
| [SmallGroup(240,91)](../lean/more/G240_91.lean) | 3 | 96 | 6 | 0.324 | 13.836 |
| [SmallGroup(240,92)](../lean/more/G240_92.lean) | 3 | 216 | 6 | 0.597 | 22.428 |
| [SmallGroup(240,93)](../lean/more/G240_93.lean) | 3 | 216 | 6 | 0.678 | 22.297 |
| [SmallGroup(240,94)](../lean/more/G240_94.lean) | 3 | 216 | 3 | 0.663 | 35.833 |

These certify supplied finite actions and signatures. Completeness of the
generating-pair enumeration, merged-row multiplicities, and the geometric
and level theorems remain outside this formalization.

Fresh Lean timing run from the repository root:

```sh
bash lean/check.sh more G128_134.lean G128_136.lean G128_137.lean G144_117.lean G144_157.lean G160_234.lean G168_23.lean G168_43.lean G168_46.lean G180_19.lean G216_21.lean G216_153.lean G240_90.lean G240_91.lean G240_92.lean G240_93.lean G240_94.lean
```
