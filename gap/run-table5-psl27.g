# Table 5 GAP enumeration and full component export.
Read("gap/export-lib.g");
Read("gap/mg.g");
Read("gap/example-lib.g");
Print("GAP version: ", GAPInfo.Version, "\n");
MGRunExample("PSL(2,27)", PSL(2,27));
QUIT;
