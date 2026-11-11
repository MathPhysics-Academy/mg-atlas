# Finish Table 4 through order 200: the eight remaining order-192 actions.
# Run from the repository root:
#   ../gap-4.16.1/gap -q -b --quitonbreak gap/run-through200.g
Read("gap/export-lib.g");
Read("gap/mg.g");
Read("gap/example-lib.g");
Print("GAP version: ", GAPInfo.Version, "\n");
for i in [183,186,187,996,997,1012,200,204] do
  MGRunExample(Concatenation("SmallGroup(192,", String(i), ")"), SmallGroup(192,i));
od;
QUIT;
