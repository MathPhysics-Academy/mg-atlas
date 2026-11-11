# Order-96 timing run

All three Lean certificates passed, covering four supplied components and six
factorization obstructions. Every declaration passed the three-axiom audit.

| Group | Components | Largest action | GAP CPU seconds | Lean wall seconds |
|---|---:|---:|---:|---:|
| [SmallGroup(96,187)](../lean/more/G96_187.lean) | 2 | 18 | 0.111 | 25.496 |
| [SmallGroup(96,198)](../lean/more/G96_198.lean) | 1 | 192 | 0.347 | 24.097 |
| [SmallGroup(96,200)](../lean/more/G96_200.lean) | 1 | 192 | 0.274 | 21.029 |

GAP total wall time: **3.309 seconds**.
Lean total wall time: **70.622 seconds**.

One fresh sequential Lean invocation per group; wall time includes Lake startup, Mathlib imports, kernel proofs, and axiom audit. GAP per-group times are CPU time; GAP total is wall time including startup. Source generation excluded.

Reproduce:

```sh
../gap-4.16.1/gap -q -b --quitonbreak gap/run-order96.g
bash lean/check.sh more G96_187.lean G96_198.lean G96_200.lean
```
