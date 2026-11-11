# Table 4 through order 128

All 22 groups passed: 30 supplied components and 47 factorization obstructions.
Every file passed the audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

GAP wall time including startup: **5.271 seconds**.
Lean wall time for these 22 groups: **242.163 seconds**.

Single fresh sequential Lean invocation per new group; wall time includes Lake startup, Mathlib imports, kernel checking, and the axiom audit. Previously checked sources were reused by hash and excluded from these timings. GAP group times are CPU time; GAP total includes startup.

| Group | Components | Largest degree | Obstructions | GAP CPU seconds | Lean wall seconds |
|---|---:|---:|---:|---:|---:|
| [SmallGroup(48,33)](../lean/more/G48_33.lean) | 1 | 96 | 2 | 0.087 | 22.307 |
| [SmallGroup(48,48)](../lean/more/G48_48.lean) | 1 | 18 | 1 | 0.050 | 7.736 |
| [SmallGroup(72,40)](../lean/more/G72_40.lean) | 1 | 24 | 1 | 0.046 | 8.543 |
| [SmallGroup(72,42)](../lean/more/G72_42.lean) | 1 | 72 | 2 | 0.158 | 9.997 |
| [SmallGroup(96,3)](../lean/more/G96_3.lean) | 4 | 32 | 8 | 0.093 | 11.115 |
| [SmallGroup(96,64)](../lean/more/G96_64.lean) | 1 | 36 | 2 | 0.074 | 9.226 |
| [SmallGroup(96,65)](../lean/more/G96_65.lean) | 1 | 144 | 2 | 0.171 | 12.523 |
| [SmallGroup(96,66)](../lean/more/G96_66.lean) | 1 | 144 | 2 | 0.137 | 12.478 |
| [SmallGroup(96,67)](../lean/more/G96_67.lean) | 1 | 144 | 2 | 0.137 | 12.835 |
| [SmallGroup(96,185)](../lean/more/G96_185.lean) | 1 | 36 | 1 | 0.096 | 9.888 |
| [SmallGroup(96,186)](../lean/more/G96_186.lean) | 1 | 72 | 2 | 0.167 | 10.521 |
| [SmallGroup(96,189)](../lean/more/G96_189.lean) | 1 | 72 | 2 | 0.129 | 10.006 |
| [SmallGroup(96,190)](../lean/more/G96_190.lean) | 1 | 36 | 2 | 0.088 | 9.113 |
| [SmallGroup(96,192)](../lean/more/G96_192.lean) | 1 | 72 | 2 | 0.139 | 9.961 |
| [SmallGroup(96,193)](../lean/more/G96_193.lean) | 1 | 36 | 1 | 0.092 | 9.313 |
| [SmallGroup(96,194)](../lean/more/G96_194.lean) | 1 | 72 | 2 | 0.167 | 10.614 |
| [SmallGroup(96,195)](../lean/more/G96_195.lean) | 1 | 36 | 2 | 0.098 | 9.507 |
| [SmallGroup(96,227)](../lean/more/G96_227.lean) | 1 | 18 | 1 | 0.062 | 9.244 |
| [SmallGroup(108,17)](../lean/more/G108_17.lean) | 1 | 18 | 1 | 0.064 | 9.297 |
| [SmallGroup(120,35)](../lean/more/G120_35.lean) | 3 | 54 | 3 | 0.140 | 11.775 |
| [SmallGroup(120,37)](../lean/more/G120_37.lean) | 1 | 216 | 2 | 0.270 | 16.449 |
| [SmallGroup(120,38)](../lean/more/G120_38.lean) | 4 | 9 | 4 | 0.095 | 9.715 |

These certify the supplied finite actions. Enumeration completeness, merged-row
multiplicities, and the geometric and level theorems remain outside this formalization.

Fresh Lean timing run from the repository root:

```sh
bash lean/check.sh more G48_33.lean G48_48.lean G72_40.lean G72_42.lean G96_3.lean G96_64.lean G96_65.lean G96_66.lean G96_67.lean G96_185.lean G96_186.lean G96_189.lean G96_190.lean G96_192.lean G96_193.lean G96_194.lean G96_195.lean G96_227.lean G108_17.lean G120_35.lean G120_37.lean G120_38.lean
```
