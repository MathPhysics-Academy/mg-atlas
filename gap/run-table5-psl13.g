# Table 5 pilot: save both the merged rows and every component's action.
Read("gap/export-lib.g");
Read("gap/mg.g");
Read("gap/example-lib.g");
Print("GAP version: ", GAPInfo.Version, "\n");
MGRunExample("PSL(2,13)", PSL(2,13));
QUIT;
