# Table 5: PSL(2,17), with merged rows and every component action.
Read("gap/export-lib.g");
Read("gap/mg.g");
Read("gap/example-lib.g");
Print("GAP version: ", GAPInfo.Version, "\n");
MGRunExample("PSL(2,17)", PSL(2,17));
QUIT;
