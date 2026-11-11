# Exact combinatorial graphs of the supplied action, computed in GAP.
# This is an untrusted producer; Lean certificates are separate.
MGGraphJSON := function(c, F)
  local n, cl, reps, p, mu, S, T, U, cycles, vertices, edges, faces, widths, c4, c6, genus;
  n := Length(c.S); cl := ListWithIdenticalEntries(n, 0); reps := [];
  for p in [1..n] do
    if cl[p] = 0 then Add(reps, p); cl[p] := Length(reps); cl[c.S[c.S[p]]] := Length(reps); fi;
  od;
  mu := Length(reps); S := List(reps, p -> cl[c.S[p]]); T := List(reps, p -> cl[c.T[p]]);
  U := List([1..mu], p -> T[S[p]]);
  if not ForAll([1..n], p -> cl[c.S[p]] = S[cl[p]] and cl[c.T[p]] = T[cl[p]]) then Error("graph quotient incompatible"); fi;
  if not ForAll([1..mu], p -> S[S[p]] = p and U[U[U[p]]] = p) then Error("graph relations failed"); fi;
  cycles := function(a)
    local unseen, out, p, q, cyc;
    unseen := ListWithIdenticalEntries(Length(a),true); out := [];
    for p in [1..Length(a)] do
      if unseen[p] then
        cyc := []; q := p;
        repeat Add(cyc,q-1); unseen[q] := false; q := a[q]; until q=p;
        Add(out,cyc);
      fi;
    od;
    return out;
  end;
  vertices := cycles(U); edges := cycles(S); faces := cycles(T);
  widths := SortedList(List(faces,Length)); c4 := Number(edges,e -> Length(e)=1); c6 := Number(vertices,v -> Length(v)=1);
  genus := 1+mu/12-c4/4-c6/3-Length(faces)/2;
  if F.info.mu <> mu or F.info.cusps <> Length(faces) or F.info.c4 <> c4 or F.info.c6 <> c6 or F.info.genus <> genus then Error("Farey/graph invariants disagree"); fi;
  return Concatenation("{\"projection\":", MGJson(List(cl,x->x-1)), ",\"representatives\":", MGJson(List(reps,x->x-1)),
    ",\"S\":", MGJson(List(S,x->x-1)), ",\"T\":", MGJson(List(T,x->x-1)),
    ",\"U\":", MGJson(List(U,x->x-1)), ",\"vertices\":", MGJson(vertices), ",\"edges\":", MGJson(edges),
    ",\"faces\":", MGJson(faces), ",\"widths\":", MGJson(widths), ",\"genus\":", String(genus), "}");
end;
