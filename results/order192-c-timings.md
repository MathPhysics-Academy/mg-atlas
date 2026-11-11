# Third order-192 batch

All 23 groups passed: 28 supplied components and 56 factorization obstructions.
Every file passed the audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

GAP wall time including startup: **10.563 seconds**.
Lean wall time for these 23 groups: **392.959 seconds**.

Single fresh sequential Lean invocation per new group; wall time includes Lake startup, Mathlib imports, kernel checking, and the axiom audit. Previously checked sources were reused by hash and excluded from these timings. GAP group times are CPU time; GAP total includes startup.

| Group | Components | Largest degree | Obstructions | GAP CPU seconds | Lean wall seconds |
|---|---:|---:|---:|---:|---:|
| [SmallGroup(192,969)](../lean/more/G192_969.lean) | 2 | 144 | 4 | 0.755 | 32.836 |
| [SmallGroup(192,970)](../lean/more/G192_970.lean) | 1 | 144 | 2 | 0.382 | 12.556 |
| [SmallGroup(192,971)](../lean/more/G192_971.lean) | 2 | 72 | 4 | 0.391 | 11.712 |
| [SmallGroup(192,972)](../lean/more/G192_972.lean) | 2 | 72 | 4 | 0.382 | 12.037 |
| [SmallGroup(192,973)](../lean/more/G192_973.lean) | 1 | 72 | 2 | 0.224 | 11.307 |
| [SmallGroup(192,974)](../lean/more/G192_974.lean) | 2 | 36 | 4 | 0.216 | 11.745 |
| [SmallGroup(192,975)](../lean/more/G192_975.lean) | 1 | 72 | 2 | 0.225 | 17.564 |
| [SmallGroup(192,976)](../lean/more/G192_976.lean) | 1 | 72 | 2 | 0.236 | 13.150 |
| [SmallGroup(192,977)](../lean/more/G192_977.lean) | 1 | 288 | 2 | 0.544 | 44.308 |
| [SmallGroup(192,978)](../lean/more/G192_978.lean) | 1 | 144 | 2 | 0.334 | 16.689 |
| [SmallGroup(192,979)](../lean/more/G192_979.lean) | 1 | 144 | 2 | 0.396 | 16.173 |
| [SmallGroup(192,980)](../lean/more/G192_980.lean) | 1 | 144 | 2 | 0.327 | 16.052 |
| [SmallGroup(192,981)](../lean/more/G192_981.lean) | 1 | 288 | 2 | 0.537 | 26.038 |
| [SmallGroup(192,982)](../lean/more/G192_982.lean) | 1 | 144 | 2 | 0.374 | 14.417 |
| [SmallGroup(192,983)](../lean/more/G192_983.lean) | 1 | 288 | 2 | 0.540 | 26.042 |
| [SmallGroup(192,984)](../lean/more/G192_984.lean) | 1 | 144 | 2 | 0.333 | 17.254 |
| [SmallGroup(192,985)](../lean/more/G192_985.lean) | 1 | 144 | 2 | 0.365 | 15.606 |
| [SmallGroup(192,986)](../lean/more/G192_986.lean) | 1 | 144 | 2 | 0.322 | 15.295 |
| [SmallGroup(192,987)](../lean/more/G192_987.lean) | 1 | 72 | 2 | 0.204 | 11.503 |
| [SmallGroup(192,988)](../lean/more/G192_988.lean) | 1 | 72 | 2 | 0.206 | 11.889 |
| [SmallGroup(192,989)](../lean/more/G192_989.lean) | 1 | 72 | 2 | 0.202 | 12.719 |
| [SmallGroup(192,990)](../lean/more/G192_990.lean) | 1 | 72 | 2 | 0.198 | 11.776 |
| [SmallGroup(192,991)](../lean/more/G192_991.lean) | 2 | 72 | 4 | 0.393 | 14.291 |

These certify the supplied finite actions. Enumeration completeness, merged-row
multiplicities, and the geometric and level theorems remain outside this formalization.

Fresh Lean timing run from the repository root:

```sh
bash lean/check.sh more G192_969.lean G192_970.lean G192_971.lean G192_972.lean G192_973.lean G192_974.lean G192_975.lean G192_976.lean G192_977.lean G192_978.lean G192_979.lean G192_980.lean G192_981.lean G192_982.lean G192_983.lean G192_984.lean G192_985.lean G192_986.lean G192_987.lean G192_988.lean G192_989.lean G192_990.lean G192_991.lean
```
