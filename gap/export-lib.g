# Write one JSON record per line without GAP line wrapping.
EmitJSON := function(s)
  local out;
  out := OutputTextUser();
  SetPrintFormattingStatus(out, false);
  PrintTo(out, "@@JSON ", s, "\n");
end;
