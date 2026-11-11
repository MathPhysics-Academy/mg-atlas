# Table 4 through order 180

All 21 groups passed: 29 supplied components and 51 factorization obstructions.
Every file passed the audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

GAP wall time including startup: **7.800 seconds**.
Lean wall time for these 21 groups: **547.159 seconds**.

Single fresh sequential Lean invocation per new group; wall time includes Lake startup, Mathlib imports, kernel checking, and the axiom audit. Previously checked sources were reused by hash and excluded from these timings. GAP group times are CPU time; GAP total includes startup.

| Group | Components | Largest degree | Obstructions | GAP CPU seconds | Lean wall seconds |
|---|---:|---:|---:|---:|---:|
| [SmallGroup(144,31)](../lean/more/G144_31.lean) | 3 | 36 | 3 | 0.161 | 27.389 |
| [SmallGroup(144,32)](../lean/more/G144_32.lean) | 3 | 36 | 6 | 0.223 | 10.236 |
| [SmallGroup(144,33)](../lean/more/G144_33.lean) | 3 | 36 | 6 | 0.178 | 10.482 |
| [SmallGroup(144,36)](../lean/more/G144_36.lean) | 1 | 864 | 2 | 0.603 | 81.567 |
| [SmallGroup(144,109)](../lean/more/G144_109.lean) | 3 | 18 | 3 | 0.171 | 10.817 |
| [SmallGroup(144,115)](../lean/more/G144_115.lean) | 1 | 96 | 2 | 0.146 | 10.988 |
| [SmallGroup(144,116)](../lean/more/G144_116.lean) | 1 | 96 | 2 | 0.150 | 11.083 |
| [SmallGroup(144,118)](../lean/more/G144_118.lean) | 1 | 96 | 2 | 0.130 | 11.347 |
| [SmallGroup(144,121)](../lean/more/G144_121.lean) | 1 | 288 | 2 | 0.285 | 21.986 |
| [SmallGroup(144,122)](../lean/more/G144_122.lean) | 1 | 288 | 2 | 0.289 | 22.461 |
| [SmallGroup(144,123)](../lean/more/G144_123.lean) | 1 | 288 | 2 | 0.360 | 21.047 |
| [SmallGroup(144,127)](../lean/more/G144_127.lean) | 1 | 96 | 2 | 0.212 | 11.154 |
| [SmallGroup(144,128)](../lean/more/G144_128.lean) | 1 | 96 | 2 | 0.194 | 11.307 |
| [SmallGroup(144,182)](../lean/more/G144_182.lean) | 1 | 48 | 2 | 0.066 | 9.571 |
| [SmallGroup(144,183)](../lean/more/G144_183.lean) | 1 | 18 | 1 | 0.116 | 8.980 |
| [SmallGroup(144,188)](../lean/more/G144_188.lean) | 1 | 144 | 2 | 0.342 | 12.890 |
| [SmallGroup(150,5)](../lean/more/G150_5.lean) | 1 | 72 | 2 | 0.121 | 10.477 |
| [SmallGroup(162,10)](../lean/more/G162_10.lean) | 1 | 216 | 2 | 0.239 | 18.257 |
| [SmallGroup(162,14)](../lean/more/G162_14.lean) | 1 | 216 | 2 | 0.228 | 21.814 |
| [SmallGroup(168,22)](../lean/more/G168_22.lean) | 1 | 1536 | 2 | 0.794 | 164.284 |
| [SmallGroup(168,45)](../lean/more/G168_45.lean) | 1 | 432 | 2 | 0.491 | 39.022 |

These certify the supplied finite actions. Enumeration completeness, merged-row
multiplicities, and the geometric and level theorems remain outside this formalization.

Fresh Lean timing run from the repository root:

```sh
bash lean/check.sh more G144_31.lean G144_32.lean G144_33.lean G144_36.lean G144_109.lean G144_115.lean G144_116.lean G144_118.lean G144_121.lean G144_122.lean G144_123.lean G144_127.lean G144_128.lean G144_182.lean G144_183.lean G144_188.lean G150_5.lean G162_10.lean G162_14.lean G168_22.lean G168_45.lean
```
