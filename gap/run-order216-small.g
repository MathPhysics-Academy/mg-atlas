# Smaller remaining order-216 Table 4 actions (at most 288 points each).
# Run from the repository root:
#   ../gap-4.16.1/gap -q -b --quitonbreak gap/run-order216-small.g
Read("gap/export-lib.g");
Read("gap/mg.g");
Read("gap/example-lib.g");
Print("GAP version: ", GAPInfo.Version, "\n");
for i in [33,34,35,36,37,39,41,42,86,87,88,90,91,92,100,157,158,159,163] do
  MGRunExample(Concatenation("SmallGroup(216,", String(i), ")"), SmallGroup(216,i));
od;
QUIT;
