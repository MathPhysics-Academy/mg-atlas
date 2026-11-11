# Export every component, before merging isomorphic actions.
# Run from the repository root with GAP 4.16.1.
Read("gap/export-lib.g");
Read("gap/mg.g");
for id in [[6,1], [12,3], [24,12], [24,3], [48,28], [48,29],
           [48,30], [48,32], [60,5], [168,42]] do
  D := MGComponents(SmallGroup(id[1], id[2]));
  chunks := [];
  for c in D.comps do
    Add(chunks, Concatenation("{\"S\":", MGJson(List(c.S, x -> x-1)),
      ",\"T\":", MGJson(List(c.T, x -> x-1)), ",\"e\":", String(c.e), "}"));
  od;
  EmitJSON(Concatenation("{\"order\":", String(D.N), ",\"index\":", String(id[2]),
    ",\"pairs\":", String(D.pairs), ",\"components\":[",
    JoinStringsWithSeparator(chunks, ","), "]}"));
od;
QUIT;
