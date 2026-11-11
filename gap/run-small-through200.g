# Remaining small Table 4 actions through order 200.
# Run from the repository root:
#   ../gap-4.16.1/gap -q -b --quitonbreak gap/run-small-through200.g
Read("gap/export-lib.g");
Read("gap/mg.g");
Read("gap/example-lib.g");
Print("GAP version: ", GAPInfo.Version, "\n");
for i in [1003,1004,1005,1006,1007,1017,1018,1019,
          1489,1490,1491,1492,1493,1494,1495,1538] do
  MGRunExample(Concatenation("SmallGroup(192,", String(i), ")"), SmallGroup(192,i));
od;
MGRunExample("SmallGroup(200,43)", SmallGroup(200,43));
QUIT;
