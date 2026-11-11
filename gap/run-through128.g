# Fill every remaining Table 4 gap through order 128.
# Run from the repository root:
#   ../gap-4.16.1/gap -q -b --quitonbreak gap/run-through128.g
Read("gap/export-lib.g");
Read("gap/mg.g");
Read("gap/example-lib.g");
Print("GAP version: ", GAPInfo.Version, "\n");
for id in [[48,33], [48,48], [72,40], [72,42],
           [96,3], [96,64], [96,65], [96,66], [96,67], [96,185],
           [96,186], [96,189], [96,190], [96,192], [96,193],
           [96,194], [96,195], [96,227], [108,17],
           [120,35], [120,37], [120,38]] do
  MGRunExample(Concatenation("SmallGroup(", String(id[1]), ",", String(id[2]), ")"),
               SmallGroup(id[1],id[2]));
od;
QUIT;
