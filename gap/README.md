# Running the GAP code

Run commands from the project root, the directory containing `gap/`, `lean/`,
`tools/` and `results/`. The computations were run with GAP 4.16.1 and its
standard group libraries, including SmallGrp for `SmallGroup` examples.
The commands below assume `gap` is on your `PATH`.

## Run a table example

This enumerates PSL(2,13), computes the merged table rows, and exports every
component's action:

```sh
mkdir -p results/local
gap -q -b --quitonbreak gap/run-table5-psl13.g > results/local/psl13.log 2>&1
```

For the three order-96 examples from Table 4:

```sh
gap -q -b --quitonbreak gap/run-order96.g > results/local/order96.log 2>&1
```

Other `run-*.g` files select other batches; their group lists are in the files.
`run-baseline.g` includes S3 and A4 as controls as well as Table 4 examples.
The `--quitonbreak` option stops GAP on an error instead of entering a break loop.

Logs contain a version header and records prefixed with `@@JSON `. To extract
the records as JSON Lines without changing the original log:

```sh
sed -n 's/^@@JSON //p' results/local/psl13.log > results/local/psl13.jsonl
```

## Compute another group

Start `gap -q -b --quitonbreak` from the project root, then enter:

```gap
Read("gap/export-lib.g");;
Read("gap/mg.g");;
Read("gap/example-lib.g");;
MGRunExample("PSL(2,13)", PSL(2,13));
```

Replace the label and group expression as needed, for example with
`"SmallGroup(96,187)"` and `SmallGroup(96,187)`. The label identifies the output;
the second argument determines the group computed.

For interactive access to the components, without the merged-table congruence
search, use:

```gap
D := MGComponents(PSL(2,13));;
Length(D.comps);
c := D.comps[1];;
```

Each component has `S` and `T` action lists. GAP uses indices starting at 1;
the JSON exporters convert action indices to start at 0.

## Construct Farey and graph data

Continuing the interactive example:

```gap
Read("gap/farey.g");;
Read("gap/graph-export-lib.g");;
F := MGFarey(c);;
F.info;
Print(MGFareyJSON(c), "\n");
Print(MGGraphJSON(c, F), "\n");
```

`MGFarey` constructs the polygon and side-pairing data. `MGGraphJSON` exports
the projective quotient action and its vertex, edge and face cycles, checking
that its invariants agree with the Farey data.

To regenerate Farey data and SVG diagrams from the saved PSL(2,13) actions:

```sh
python3 tools/run-table5-farey.py \
  --groups psl13 \
  --data-dir results/local/psl13-farey \
  --archive run-01
```

This requires Python 3 for orchestration and rendering; GAP performs the Farey
and graph computations. The runner uses `GAP_EXECUTABLE` if set, otherwise
looks for GAP on `PATH` or in a nearby `gap-4.16.1/` directory. Use a new archive
name for each run. Omitting `--groups` selects all Table 5 groups; keep a separate
`--data-dir` to preserve the published collection.

For the full Table 4 reconstruction commands, see
[the Table 4 Farey guide](../results/table4-graphs/CERTIFICATES.md).

## Read the output

`MGRunExample` emits the group order, generating-pair class count, runtime in
milliseconds, merged `rows`, and the unmerged `components` with their actions.
In each row:

| Field | Meaning |
|---|---|
| `m` | Number of components with isomorphic actions merged into this row |
| `d` | Degree of the SL2(Z) action |
| `c4`, `c6` | Fixed-point counts for the elliptic generators |
| `cm1` | Whether the central element −I acts trivially (`1` or `0`) |
| `widths` | Cusp widths as `[width, multiplicity]` pairs |
| `genus` | Genus calculated from the projective action |
| `cong` | Congruence result: `true`, `false`, or `null` for unresolved |
| `level` | Level value returned by the congruence search; read with `cong` |
| `es` | Commutator orders for the merged components |

The congruence search has a six-million-state cap. A `null` result means the
search did not settle the question. In the saved Table 5 collection, 33 merged
rows remain unresolved: 15 for PSL(2,31) and 18 for PSL(2,37).

## Files and saved results

| File | Purpose |
|---|---|
| `mg.g` | Generating-pair orbits, component actions, invariants and merged tables |
| `farey.g` | Farey construction and action/polygon exports |
| `graph-export-lib.g` | Quotient graph export and invariant comparisons |
| `export-lib.g` | Group serialization and output helpers |
| `example-lib.g` | Combined table-row and component-action export |
| `export-actions.g` | Baseline component-action export |
| `run-*.g` | Group selections for computation batches |
| `check-table5-aliases.g` | Checks named-group/SmallGroup identifications |

Saved data and diagrams:

- [Table 5 enumerations](../results/table5-gap/README.md): 23 groups, 652 components.
- [Table 4 graphs and domains](../results/table4-graphs/README.md): 218 groups, 376 components.
- [Table 5 graphs and domains](../results/table5-graphs/README.md): 23 groups, 652 components.
- [Lean coverage and certificate scope](../lean/README.md).
