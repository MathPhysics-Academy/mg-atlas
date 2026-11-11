# Remaining 17 groups from the proposed 20-group Table 4 batch.
# The three order-96 groups were checked separately by run-order96.g.
# Run from the repository root:
#   ../gap-4.16.1/gap -q -b --quitonbreak gap/run-table4-rest.g
Read("gap/export-lib.g");
Read("gap/mg.g");
Read("gap/example-lib.g");
Print("GAP version: ", GAPInfo.Version, "\n");
for id in [[128,134], [128,136], [128,137], [144,117], [144,157],
           [160,234], [168,23], [168,43], [168,46], [180,19],
           [216,21], [216,153], [240,90], [240,91], [240,92],
           [240,93], [240,94]] do
  MGRunExample(Concatenation("SmallGroup(", String(id[1]), ",", String(id[2]), ")"),
               SmallGroup(id[1],id[2]));
od;
QUIT;
