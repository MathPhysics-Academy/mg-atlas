# Components of M(G) (Chen, Appendix B): SL2(Z)-orbits on Epi(F2,G)/Inn(G), and their invariants.
# Right action: S: (x,y) -> (y, x^-1),  T: (x,y) -> (x, x*y).
# Needs export-lib.g loaded first (EmitJSON).

# Generating pairs up to conjugacy, with the S and T action on them.
MGPairs := function(G)
  local elts, N, pos, classes, clsOf, conjTo, orbIdx, pairId, pairs, k, r, C, t, i, orbs, o, y, lookup;
  elts := AsSSortedList(G); N := Length(elts);
  pos := g -> PositionSorted(elts, g);
  classes := ConjugacyClasses(G);
  clsOf := []; conjTo := []; orbIdx := []; pairId := []; pairs := [];
  for k in [1 .. Length(classes)] do
    r := Representative(classes[k]);
    C := Centralizer(classes[k]);
    # every a in the class: remember k and a conjugator taking a to r
    for t in RightTransversal(G, C) do
      i := pos(r^t); clsOf[i] := k; conjTo[i] := t^-1;
    od;
    if IsOne(r) then continue; fi;
    # pairs (r, y) up to conjugacy = C-orbits on G; keep the orbits whose rep generates with r
    orbs := OrbitsDomain(C, elts, OnPoints);
    orbIdx[k] := []; pairId[k] := [];
    for o in [1 .. Length(orbs)] do
      for y in orbs[o] do orbIdx[k][pos(y)] := o; od;
      y := orbs[o][1];
      if Size(Subgroup(G, [r, y])) = N then
        Add(pairs, [r, y]); pairId[k][o] := Length(pairs);
      else
        pairId[k][o] := 0;
      fi;
    od;
  od;
  lookup := function(a, b)   # index of the class of the pair (a, b)
    local i, k;
    i := pos(a); k := clsOf[i];
    return pairId[k][orbIdx[k][pos(b^conjTo[i])]];
  end;
  return rec(N := N, pairs := pairs,
    S := List(pairs, p -> lookup(p[2], p[1]^-1)),
    T := List(pairs, p -> lookup(p[1], p[1] * p[2])));
end;

# Orbits of <S,T>, each as a transitive SL2(Z)-set on [1..d] (point 1 = base pair), plus e.
MGComponents := function(G)
  local D, seen, comps, s, pts, loc, i, q;
  D := MGPairs(G);
  if 0 in D.S or 0 in D.T then Error("action left the set of generating pairs (bug)"); fi;
  seen := ListWithIdenticalEntries(Length(D.pairs), false); comps := [];
  for s in [1 .. Length(D.pairs)] do
    if not seen[s] then
      pts := [s]; seen[s] := true; i := 1;
      while i <= Length(pts) do
        for q in [D.S[pts[i]], D.T[pts[i]]] do
          if not seen[q] then seen[q] := true; Add(pts, q); fi;
        od;
        i := i + 1;
      od;
      loc := []; for i in [1 .. Length(pts)] do loc[pts[i]] := i; od;
      Add(comps, rec(S := List(pts, p -> loc[D.S[p]]), T := List(pts, p -> loc[D.T[p]]),
                     e := Order(Comm(D.pairs[s][1], D.pairs[s][2]))));
    fi;
  od;
  return rec(N := D.N, pairs := Length(D.pairs), comps := comps);
end;

# Invariants of one transitive SL2(Z)-set.
MGInvariants := function(c, n)
  local d, S, T, cl, mu, p, fixS, fixU, Tq, vis, widths, a, b, k;
  d := Length(c.S); S := c.S; T := c.T;
  cl := ListWithIdenticalEntries(d, 0); mu := 0;          # PSL2 points {p, -p}, -I = S^2
  for p in [1 .. d] do
    if cl[p] = 0 then mu := mu + 1; cl[p] := mu; cl[S[S[p]]] := mu; fi;
  od;
  fixS := []; fixU := [];
  for p in [1 .. d] do
    if cl[S[p]] = cl[p] then AddSet(fixS, cl[p]); fi;
    if cl[T[S[p]]] = cl[p] then AddSet(fixU, cl[p]); fi;   # ST: S then T
  od;
  Tq := []; for p in [1 .. d] do Tq[cl[p]] := cl[T[p]]; od;
  vis := ListWithIdenticalEntries(mu, false); widths := [];
  for a in [1 .. mu] do
    if not vis[a] then
      k := 0; b := a;
      while not vis[b] do vis[b] := true; b := Tq[b]; k := k + 1; od;
      Add(widths, k);
    fi;
  od;
  Sort(widths);
  if S[S[1]] = 1 then k := 1; else k := 0; fi;
  return rec(d := d, c4 := Length(fixS), c6 := Length(fixU), cm1 := k,
    widths := widths, genus := 1 + mu/12 - Length(fixS)/4 - Length(fixU)/3 - Length(widths)/2,
    e := c.e, g := 1 + n * (c.e - 1) / (2 * c.e));
end;

# Isomorphic transitive SL2(Z)-sets <=> conjugate stabilisers.
MGIsomorphic := function(a, b)
  local d, t, f, q, i, ok, p, pr, u, v;
  d := Length(a.S);
  if Length(b.S) <> d then return false; fi;
  for t in [1 .. d] do
    f := ListWithIdenticalEntries(d, 0); f[1] := t; q := [1]; i := 1; ok := true;
    while ok and i <= Length(q) do
      p := q[i];
      for pr in [[a.S, b.S], [a.T, b.T]] do
        u := pr[1][p]; v := pr[2][f[p]];
        if f[u] = 0 then f[u] := v; Add(q, u);
        elif f[u] <> v then ok := false; break; fi;
      od;
      i := i + 1;
    od;
    if ok then return true; fi;
  od;
  return false;
end;

# Gamma contains Gamma(N) <=> the action factors through SL2(Z/N).
# BFS over (matrix mod N, point); one matrix reached with two points => no. fail = hit the cap.
MGFactorsThrough := function(c, N, cap)
  local seen, count, q, i, m, p, nexts, nx, key, old;
  seen := NewDictionary(1, true, Integers); count := 1;
  key := m -> ((m[1] * N + m[2]) * N + m[3]) * N + m[4];
  AddDictionary(seen, key([1 mod N, 0, 0, 1 mod N]), 1);
  q := [[1 mod N, 0, 0, 1 mod N, 1]]; i := 1;
  while i <= Length(q) do
    m := q[i]; p := m[5];
    nexts := [[[m[2], (-m[1]) mod N, m[4], (-m[3]) mod N], c.S[p]],          # M*S, S = [[0,-1],[1,0]]
              [[m[1], (m[1] + m[2]) mod N, m[3], (m[3] + m[4]) mod N], c.T[p]]];  # M*T, T = [[1,1],[0,1]]
    for nx in nexts do
      old := LookupDictionary(seen, key(nx[1]));
      if old = fail then
        if count >= cap then return fail; fi;
        AddDictionary(seen, key(nx[1]), nx[2]); count := count + 1;
        Add(q, Concatenation(nx[1], [nx[2]]));
      elif old <> nx[2] then
        return false;
      fi;
    od;
    i := i + 1;
  od;
  return true;
end;

MGCongruence := function(c, inv, cap)
  local L, levels, unknown, N, r;
  L := Lcm(inv.widths);
  # if -1 is not in Gamma, a congruence Gamma has level L or 2L (Kiming-Schutt-Verrill)
  if inv.cm1 = 1 then levels := [L]; else levels := [L, 2 * L]; fi;
  unknown := false;
  for N in levels do
    r := MGFactorsThrough(c, N, cap);
    if r = true then return rec(cong := true, level := N); fi;
    if r = fail then unknown := true; fi;
  od;
  if unknown then return rec(cong := fail, level := L); fi;
  return rec(cong := false, level := L);
end;

# The rows for one group: isomorphic components merged (m), sorted by genus then d.
MGTable := function(G)
  local D, rows, c, inv, hit, cg;
  D := MGComponents(G); rows := [];
  for c in D.comps do
    inv := MGInvariants(c, D.N);
    hit := First(rows, r -> r.d = inv.d and r.c4 = inv.c4 and r.c6 = inv.c6 and r.cm1 = inv.cm1
                            and r.widths = inv.widths and MGIsomorphic(r.c, c));
    if hit <> fail then
      hit.m := hit.m + 1; Add(hit.es, c.e);
    else
      cg := MGCongruence(c, inv, 6000000);
      inv.c := c; inv.m := 1; inv.es := [c.e]; inv.cong := cg.cong; inv.level := cg.level;
      Add(rows, inv);
    fi;
  od;
  SortBy(rows, r -> [r.genus, r.d]);
  return rec(order := D.N, pairs := D.pairs, rows := rows);
end;

MGJson := function(L)   # list of ints -> "[a,b,...]"
  return Concatenation("[", JoinStringsWithSeparator(List(L, String), ","), "]");
end;

MGRowJSON := function(r)
  local cong;
  if r.cong = true then cong := "true"; elif r.cong = false then cong := "false"; else cong := "null"; fi;
  return Concatenation("{\"m\":", String(r.m), ",\"d\":", String(r.d),
    ",\"c4\":", String(r.c4), ",\"c6\":", String(r.c6), ",\"cm1\":", String(r.cm1),
    ",\"widths\":[", JoinStringsWithSeparator(List(Collected(r.widths), MGJson), ","), "]",
    ",\"genus\":\"", String(r.genus), "\"",
    ",\"cong\":", cong, ",\"level\":", String(r.level),
    ",\"es\":", MGJson(r.es), "}");
end;

# One Table 4 group: one @@JSON line with timing and all rows.
MGSmallGroup := function(n, i)
  local t0, T;
  t0 := Runtime();
  T := MGTable(SmallGroup(n, i));
  EmitJSON(Concatenation("{\"table\":4,\"size\":", String(n), ",\"i\":", String(i),
    ",\"pairs\":", String(T.pairs), ",\"ms\":", String(Runtime() - t0),
    ",\"rows\":[", JoinStringsWithSeparator(List(T.rows, MGRowJSON), ","), "]}"));
end;

# k-th Table 5 group (SimpleGroupsIterator order, as in export-lib.g), as a small-degree perm group.
MGSimpleGroup := function(k)
  local it, G, j, t0, T;
  it := SimpleGroupsIterator(60, 29120);
  for j in [1 .. k] do G := NextIterator(it); od;
  G := Image(SmallerDegreePermutationRepresentation(Image(IsomorphismPermGroup(G))));
  t0 := Runtime();
  T := MGTable(G);
  EmitJSON(Concatenation("{\"table\":5,\"size\":", String(Size(G)), ",\"k\":", String(k),
    ",\"pairs\":", String(T.pairs), ",\"ms\":", String(Runtime() - t0),
    ",\"rows\":[", JoinStringsWithSeparator(List(T.rows, MGRowJSON), ","), "]}"));
end;
