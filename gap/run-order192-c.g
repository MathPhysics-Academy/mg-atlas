# Third batch of smaller order-192 Table 4 actions.
# Run from the repository root:
#   ../gap-4.16.1/gap -q -b --quitonbreak gap/run-order192-c.g
Read("gap/export-lib.g");
Read("gap/mg.g");
Read("gap/example-lib.g");
Print("GAP version: ", GAPInfo.Version, "\n");
for i in [969..991] do
  MGRunExample(Concatenation("SmallGroup(192,", String(i), ")"), SmallGroup(192,i));
od;
QUIT;
