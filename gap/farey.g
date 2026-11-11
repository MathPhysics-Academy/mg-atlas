# Farey construction and action exports.
# Load gap/export-lib.g and gap/mg.g before this file.

# Each row's representative SL2(Z)-set (S, T as 0-based images), for drawing coset graphs,
# trivalent maps and fundamental domains. fields: the identifying JSON fields of the group.
MGActionsJSON := function(G, fields)
  local T, rowJSON;
  T := MGTable(G);
  rowJSON := r -> Concatenation("{\"m\":", String(r.m), ",\"d\":", String(r.d),
    ",\"c4\":", String(r.c4), ",\"c6\":", String(r.c6), ",\"cm1\":", String(r.cm1),
    ",\"widths\":[", JoinStringsWithSeparator(List(Collected(r.widths), MGJson), ","), "]",
    ",\"genus\":\"", String(r.genus), "\"",
    ",\"S\":", MGJson(List(r.c.S, x -> x - 1)), ",\"T\":", MGJson(List(r.c.T, x -> x - 1)),
    ",\"farey\":", MGFareyJSON(r.c), "}");
  EmitJSON(Concatenation("{", fields, ",\"rows\":[", JoinStringsWithSeparator(List(T.rows, rowJSON), ","), "]}"));
end;
MGActionsSmallGroup := function(n, i)
  MGActionsJSON(SmallGroup(n, i), Concatenation("\"table\":4,\"size\":", String(n), ",\"i\":", String(i)));
end;
MGActionsSimpleGroup := function(k)
  local it, G, j;
  it := SimpleGroupsIterator(60, 29120);
  for j in [1 .. k] do G := NextIterator(it); od;
  G := Image(SmallerDegreePermutationRepresentation(Image(IsomorphismPermGroup(G))));
  MGActionsJSON(G, Concatenation("\"table\":5,\"size\":", String(Size(G)), ",\"k\":", String(k)));
end;

# ---------------------------------------------------------------------------------------------
# Farey symbol / special polygon (Kulkarni 1991) of one row's group Gamma, from its S, T action.
#
# PSL2(Z) acts simply transitively on oriented Farey edges; the coset of the PSL point p is the
# Gamma-orbit of the oriented edge g_p(0 -> oo), where x0 . g_p = p (right action). The Farey
# triangle on the left of that edge is g_p(Delta), Delta = (-1, 0, oo), rotated by U = ST.
# Map vertices (U-cycles) = Farey triangles mod Gamma, map edges (S-orbits) = shared sides.
# Lifting a spanning tree of the map gives a union of Farey triangles = a convex ideal polygon;
# a U-fixed vertex contributes one third of its triangle (odd side), an S-fixed dart an even side,
# each non-tree edge a pair of free sides glued by g_s S g_p^-1 in Gamma.
# All arithmetic is exact. Checks: every gluing element is rewritten as a word in S, T and applied
# to the base point (must fix it); the boundary must be a Farey sequence covered exactly once;
# counts must match c4, c6, cusps and 2g + t - 1 = number of free pairs.
MGFarey := function(c)
  local d, cl, mu, p, Sq, Tq, Ti, Uq, MS, MT, MU, g, tree, hi, lo, setVertex, take, s, t,
        cusp, ckey, sides, pairs, k, X, keys, inter, lab, act, i, a, b, cyc, ncyc, tcyc,
        ok, genusTwice, info, x0, nfree, neven, nodd, cuspOf, classes, iv;
  d := Length(c.S);
  cl := ListWithIdenticalEntries(d, 0); mu := 0;
  for p in [1 .. d] do if cl[p] = 0 then mu := mu + 1; cl[p] := mu; cl[c.S[c.S[p]]] := mu; fi; od;
  Sq := []; Tq := []; Ti := [];
  for p in [1 .. d] do Sq[cl[p]] := cl[c.S[p]]; Tq[cl[p]] := cl[c.T[p]]; od;
  for p in [1 .. mu] do Ti[Tq[p]] := p; od;
  Uq := List([1 .. mu], q -> Tq[Sq[q]]);                       # U = S then T
  MS := [[0, -1], [1, 0]]; MT := [[1, 1], [0, 1]]; MU := MS * MT;
  tcyc := ListWithIdenticalEntries(mu, 0); ncyc := 0;
  for p in [1 .. mu] do if tcyc[p] = 0 then ncyc := ncyc + 1; t := p; repeat tcyc[t] := ncyc; t := Tq[t]; until t = p; fi; od;

  # spanning tree, preferring darts whose edge ends at oo (so the cusp at oo gets its full width)
  g := []; tree := []; hi := []; lo := [];
  setVertex := function(q, m)
    local t;
    t := q;
    repeat g[t] := m; if m[2][1] = 0 then Add(hi, t); else Add(lo, t); fi; m := m * MU; t := Uq[t]; until t = q;
  end;
  setVertex(1, [[1, 0], [0, 1]]);
  while hi <> [] or lo <> [] do
    if hi <> [] then p := Remove(hi, 1); else p := Remove(lo, 1); fi;
    s := Sq[p];
    if s <> p and not IsBound(g[s]) then tree[p] := true; tree[s] := true; setVertex(s, g[p] * MS); fi;
  od;
  if Number([1 .. mu], q -> IsBound(g[q])) <> mu then Error("Farey: map not connected"); fi;

  cusp := v -> (function(a, c)                               # column vector -> cusp [a, c], c >= 0, oo = [1, 0]
      if c = 0 then return [1, 0]; fi;
      if c < 0 then return [-a, -c]; fi;
      return [a, c]; end)(v[1], v[2]);
  ckey := x -> Concatenation(String(x[1]), "/", String(x[2]));
  sides := []; pairs := []; nfree := 0; neven := 0; nodd := 0;
  for p in [1 .. mu] do
    s := Sq[p];
    if s = p then
      neven := neven + 1;
      Add(sides, rec(dart := p, lab := "even", elt := g[p] * MS * Inverse(g[p])));
    elif not IsBound(tree[p]) and p < s then
      nfree := nfree + 1;
      Add(pairs, g[s] * MS * Inverse(g[p]));
      Add(sides, rec(dart := p, lab := nfree, elt := pairs[nfree]));
      Add(sides, rec(dart := s, lab := nfree, elt := Inverse(pairs[nfree])));
    fi;
    if Uq[p] = p then
      nodd := nodd + 1;
      Add(sides, rec(dart := p, lab := "odd", elt := g[p] * MU * Inverse(g[p])));
    fi;
  od;

  # the polygon's cusps, in order along the real line; boundary intervals between neighbours
  X := Set(Concatenation(List([1 .. mu], q -> [cusp([g[q][1][1], g[q][2][1]]), cusp([g[q][1][2], g[q][2][2]])])));
  if not [1, 0] in X then Error("Farey: oo is not a vertex"); fi;
  X := Filtered(X, x -> x <> [1, 0]);
  SortBy(X, x -> x[1] / x[2]);
  inter := Concatenation([[[1, 0], X[1]]], List([1 .. Length(X) - 1], i -> [X[i], X[i + 1]]), [[X[Length(X)], [1, 0]]]);
  # consecutive cusps must be Farey neighbours
  for iv in inter do
    if AbsInt(iv[1][1] * iv[2][2] - iv[2][1] * iv[1][2]) <> 1 then Error("Farey: not a Farey sequence"); fi;
  od;
  keys := List(inter, iv -> Set([ckey(iv[1]), ckey(iv[2])]));
  lab := ListWithIdenticalEntries(Length(inter), fail);
  for s in sides do
    a := Set([ckey(cusp([g[s.dart][1][1], g[s.dart][2][1]])), ckey(cusp([g[s.dart][1][2], g[s.dart][2][2]]))]);
    i := Position(keys, a);
    if i = fail or lab[i] <> fail then Error("Farey: side not on the boundary exactly once"); fi;
    lab[i] := s;
  od;
  if fail in lab then Error("Farey: boundary interval without a side"); fi;

  # every gluing element must lie in Gamma: rewrite it as a word in S, T and act on the base point
  act := function(M)
    local R, ops, r, q, x, n, op;
    R := M; ops := [];
    while R[2][1] <> 0 do
      r := R[1][1] mod R[2][1]; q := (R[1][1] - r) / R[2][1];
      Add(ops, ["T", q]); R := [[1, -q], [0, 1]] * R;
      Add(ops, ["S", 1]); R := [[0, 1], [-1, 0]] * R;
    od;
    Add(ops, ["T", R[1][2] / R[1][1]]);
    x := 1;
    for op in ops do
      if op[1] = "S" then x := Sq[x];
      elif op[2] > 0 then for n in [1 .. op[2]] do x := Tq[x]; od;
      else for n in [1 .. -op[2]] do x := Ti[x]; od; fi;
    od;
    return x;
  end;
  for s in sides do
    if act(s.elt) <> 1 then Error("Farey: gluing element not in Gamma"); fi;
    if s.lab = "even" and TraceMat(s.elt) <> 0 then Error("Farey: even side not elliptic of order 2"); fi;
    if s.lab = "odd" and AbsInt(TraceMat(s.elt)) <> 1 then Error("Farey: odd side not elliptic of order 3"); fi;
  od;
  # invariants: elliptic counts, and free pairs = 2g + t - 1 (Euler characteristic of the polygon)
  genusTwice := nfree - ncyc + 1;
  info := rec(mu := mu, cusps := ncyc, c4 := neven, c6 := nodd, genus := genusTwice / 2);

  return rec(info := info, x := X,
    labels := List(lab, s -> s.lab), labelDarts := List(lab, s -> s.dart - 1),
    pairs := pairs, darts := List([1 .. mu], q -> Flat(g[q])), cuspOfDart := List([1 .. mu], q -> tcyc[q] - 1));
end;

MGFareyJSON := function(c)
  local F, lab;
  F := MGFarey(c);
  lab := l -> (function(l) if IsInt(l) then return String(l); fi; return Concatenation("\"", l, "\""); end)(l);
  return Concatenation("{\"x\":[", JoinStringsWithSeparator(List(F.x, MGJson), ","), "]",
    ",\"labels\":[", JoinStringsWithSeparator(List(F.labels, lab), ","), "]",
    ",\"labelDarts\":", MGJson(F.labelDarts),
    ",\"pairs\":[", JoinStringsWithSeparator(List(F.pairs, m -> MGJson(Flat(m))), ","), "]",
    ",\"darts\":[", JoinStringsWithSeparator(List(F.darts, MGJson), ","), "]",
    ",\"cuspOfDart\":", MGJson(F.cuspOfDart),
    ",\"check\":{\"mu\":", String(F.info.mu), ",\"cusps\":", String(F.info.cusps), ",\"c4\":", String(F.info.c4),
    ",\"c6\":", String(F.info.c6), ",\"genus\":\"", String(F.info.genus), "\"}}");
end;
