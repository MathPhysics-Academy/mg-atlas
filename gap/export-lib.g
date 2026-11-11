# Helpers for tools/export-groups.mjs, which starts one GAP process per group.
# (Originally a workaround for a "recursion depth trap"; the real trigger turned out to be
#  the StructureDescription/IsomorphismPermGroup order noted in GroupJSON. Separate processes
#  are kept anyway: one failing group can't take the others down.)

Esc := s -> ReplacedString(ReplacedString(s, "\\", "\\\\"), "\"", "\\\"");

GroupJSON := function(G, fields)
  local P, deg, gens, sl, sd;
  # StructureDescription must come BEFORE IsomorphismPermGroup: in GAP 4.16.1 the other
  # order hits "recursion depth trap" for some pc groups, e.g. SmallGroup(108,15), (150,5).
  sd := StructureDescription(G);
  P := Image(IsomorphismPermGroup(G));
  P := Image(SmallerDegreePermutationRepresentation(P));
  deg := Maximum(1, LargestMovedPoint(P));
  gens := SmallGeneratingSet(P);
  if IsSolvableGroup(G) then sl := String(DerivedLength(G)); else sl := "\"inf\""; fi;
  return Concatenation("{", fields,
    ",\"order\":", String(Size(G)),
    ",\"structure\":\"", Esc(sd), "\"",
    ",\"derivedLength\":", sl,
    ",\"degree\":", String(deg),
    ",\"gens\":[", JoinStringsWithSeparator(List(gens, g ->
        Concatenation("[", JoinStringsWithSeparator(List(ListPerm(g, deg), x -> String(x - 1)), ","), "]")), ","),
    "]}");
end;

# one line of JSON on stdout, between markers, with GAP's line wrapping off
EmitJSON := function(s)
  local out;
  out := OutputTextUser();
  SetPrintFormattingStatus(out, false);
  PrintTo(out, "@@JSON ", s, "\n");
end;

ExportSmallGroup := function(n, i)
  EmitJSON(GroupJSON(SmallGroup(n, i), Concatenation("\"table\":4,\"size\":", String(n), ",\"i\":", String(i))));
end;

# k-th nonabelian simple group of order <= 29120, in GAP's SimpleGroupsIterator order
ExportSimpleGroup := function(k)
  local it, G, j;
  it := SimpleGroupsIterator(60, 29120);
  for j in [1 .. k] do G := NextIterator(it); od;
  EmitJSON(GroupJSON(G, Concatenation("\"table\":5,\"size\":", String(Size(G)),
    ",\"name\":\"", Esc(IsomorphismTypeInfoFiniteSimpleGroup(G).name), "\"")));
end;
