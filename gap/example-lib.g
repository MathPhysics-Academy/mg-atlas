# Requires export-lib.g and mg.g to be loaded first.
MGRunExample := function(label, G)
  local start, table, data, chunks, c;
  start := Runtime();
  table := MGTable(G);
  data := MGComponents(G);
  if table.pairs <> data.pairs then Error("inconsistent pair counts"); fi;
  chunks := [];
  for c in data.comps do
    Add(chunks, Concatenation("{\"S\":", MGJson(List(c.S, x -> x-1)),
      ",\"T\":", MGJson(List(c.T, x -> x-1)), ",\"e\":", String(c.e), "}"));
  od;
  EmitJSON(Concatenation("{\"group\":\"", label, "\",\"order\":", String(table.order),
    ",\"pairs\":", String(table.pairs), ",\"ms\":", String(Runtime()-start),
    ",\"rows\":[", JoinStringsWithSeparator(List(table.rows, MGRowJSON), ","),
    "],\"components\":[", JoinStringsWithSeparator(chunks, ","), "]}"));
end;
