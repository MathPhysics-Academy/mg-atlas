# Fill every remaining Table 4 gap through order 180.
# Run from the repository root:
#   ../gap-4.16.1/gap -q -b --quitonbreak gap/run-through180.g
Read("gap/export-lib.g");
Read("gap/mg.g");
Read("gap/example-lib.g");
Print("GAP version: ", GAPInfo.Version, "\n");
for id in [[144,31], [144,32], [144,33], [144,36], [144,109],
           [144,115], [144,116], [144,118], [144,121], [144,122],
           [144,123], [144,127], [144,128], [144,182], [144,183],
           [144,188], [150,5], [162,10], [162,14], [168,22], [168,45]] do
  MGRunExample(Concatenation("SmallGroup(", String(id[1]), ",", String(id[2]), ")"),
               SmallGroup(id[1],id[2]));
od;
QUIT;
