# Table 4 groups (96,187), (96,198), and (96,200).
# Run from the repository root:
#   ../gap-4.16.1/gap -q -b --quitonbreak gap/run-order96.g
Read("gap/export-lib.g");
Read("gap/mg.g");
Read("gap/example-lib.g");
Print("GAP version: ", GAPInfo.Version, "\n");
for i in [187, 198, 200] do
  MGRunExample(Concatenation("SmallGroup(96,", String(i), ")"), SmallGroup(96,i));
od;
QUIT;
