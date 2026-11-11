# Table 5 GAP enumeration and full component export.
Read("gap/export-lib.g");
Read("gap/mg.g");
Read("gap/example-lib.g");
Print("GAP version: ", GAPInfo.Version, "\n");
MGRunExample("M11", MathieuGroup(11));
QUIT;
