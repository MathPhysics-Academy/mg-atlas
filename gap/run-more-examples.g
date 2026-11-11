# A second batch spanning positive genus, multiplicity, and larger simple groups.
# Run from the repository root:
#   ../gap-4.16.1/gap -q -b --quitonbreak gap/run-more-examples.g
Read("gap/export-lib.g");
Read("gap/mg.g");

Read("gap/example-lib.g");

Print("GAP version: ", GAPInfo.Version, "\n");
for id in [[72,3], [72,15], [72,25], [96,69], [96,74], [96,188],
           [96,191], [108,15], [120,5], [120,15], [120,34], [128,135],
           [144,35], [144,119], [144,156], [160,199], [162,12],
           [192,4], [216,3], [240,89]] do
  MGRunExample(Concatenation("SmallGroup(", String(id[1]), ",", String(id[2]), ")"),
               SmallGroup(id[1], id[2]));
od;
MGRunExample("A6", AlternatingGroup(6));
MGRunExample("PSL(2,8)", PSL(2,8));
MGRunExample("PSL(2,11)", PSL(2,11));
QUIT;
