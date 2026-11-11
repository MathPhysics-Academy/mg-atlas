# Second order-192 batch

All 20 groups passed: 32 supplied components and 48 factorization obstructions.
Every file passed the audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

GAP wall time including startup: **9.505 seconds**.
Lean wall time for these 20 groups: **290.903 seconds**.

Single fresh sequential Lean invocation per new group; wall time includes Lake startup, Mathlib imports, kernel checking, and the axiom audit. Previously checked sources were reused by hash and excluded from these timings. GAP group times are CPU time; GAP total includes startup.

| Group | Components | Largest degree | Obstructions | GAP CPU seconds | Lean wall seconds |
|---|---:|---:|---:|---:|---:|
| [SmallGroup(192,949)](../lean/more/G192_949.lean) | 2 | 72 | 2 | 0.412 | 18.269 |
| [SmallGroup(192,950)](../lean/more/G192_950.lean) | 1 | 144 | 1 | 0.312 | 14.375 |
| [SmallGroup(192,951)](../lean/more/G192_951.lean) | 1 | 288 | 2 | 0.512 | 22.218 |
| [SmallGroup(192,952)](../lean/more/G192_952.lean) | 2 | 72 | 4 | 0.315 | 13.582 |
| [SmallGroup(192,953)](../lean/more/G192_953.lean) | 1 | 144 | 2 | 0.340 | 13.621 |
| [SmallGroup(192,954)](../lean/more/G192_954.lean) | 2 | 72 | 4 | 0.315 | 12.818 |
| [SmallGroup(192,955)](../lean/more/G192_955.lean) | 2 | 18 | 2 | 0.131 | 12.002 |
| [SmallGroup(192,956)](../lean/more/G192_956.lean) | 1 | 36 | 1 | 0.134 | 10.267 |
| [SmallGroup(192,957)](../lean/more/G192_957.lean) | 2 | 36 | 2 | 0.272 | 10.352 |
| [SmallGroup(192,958)](../lean/more/G192_958.lean) | 1 | 288 | 2 | 0.661 | 20.804 |
| [SmallGroup(192,959)](../lean/more/G192_959.lean) | 1 | 144 | 2 | 0.394 | 13.486 |
| [SmallGroup(192,960)](../lean/more/G192_960.lean) | 2 | 36 | 4 | 0.270 | 11.142 |
| [SmallGroup(192,961)](../lean/more/G192_961.lean) | 4 | 18 | 4 | 0.268 | 11.243 |
| [SmallGroup(192,962)](../lean/more/G192_962.lean) | 2 | 36 | 2 | 0.244 | 10.658 |
| [SmallGroup(192,963)](../lean/more/G192_963.lean) | 1 | 288 | 2 | 0.529 | 26.956 |
| [SmallGroup(192,964)](../lean/more/G192_964.lean) | 1 | 144 | 2 | 0.370 | 14.743 |
| [SmallGroup(192,965)](../lean/more/G192_965.lean) | 2 | 36 | 4 | 0.246 | 10.680 |
| [SmallGroup(192,966)](../lean/more/G192_966.lean) | 2 | 36 | 2 | 0.247 | 10.910 |
| [SmallGroup(192,967)](../lean/more/G192_967.lean) | 1 | 288 | 2 | 0.652 | 20.465 |
| [SmallGroup(192,968)](../lean/more/G192_968.lean) | 1 | 144 | 2 | 0.385 | 12.312 |

These certify the supplied finite actions. Enumeration completeness, merged-row
multiplicities, and the geometric and level theorems remain outside this formalization.

Fresh Lean timing run from the repository root:

```sh
bash lean/check.sh more G192_949.lean G192_950.lean G192_951.lean G192_952.lean G192_953.lean G192_954.lean G192_955.lean G192_956.lean G192_957.lean G192_958.lean G192_959.lean G192_960.lean G192_961.lean G192_962.lean G192_963.lean G192_964.lean G192_965.lean G192_966.lean G192_967.lean G192_968.lean
```
