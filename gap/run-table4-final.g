# Final 20 Table 4 groups, ordered by expected action size for checking.
# Run from the repository root:
#   ../gap-4.16.1/gap -q -b --quitonbreak gap/run-table4-final.g
Read("gap/export-lib.g");
Read("gap/mg.g");
Read("gap/example-lib.g");
Print("GAP version: ", GAPInfo.Version, "\n");
for id in [[240,194], [240,197], [240,105], [240,106], [240,107],
           [240,192], [240,189], [240,108], [240,109], [240,190],
           [216,25], [240,196], [216,89], [216,38], [216,40],
           [240,102], [240,103], [240,104], [240,153], [240,154]] do
  MGRunExample(Concatenation("SmallGroup(", String(id[1]), ",", String(id[2]), ")"),
               SmallGroup(id[1],id[2]));
od;
QUIT;
