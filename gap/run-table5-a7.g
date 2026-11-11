# Table 5: A7, with merged rows and every component action.
Read("gap/export-lib.g");
Read("gap/mg.g");
Read("gap/example-lib.g");
Print("GAP version: ", GAPInfo.Version, "\n");
MGRunExample("A7", AlternatingGroup(7));
QUIT;
