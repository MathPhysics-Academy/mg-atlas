# Run from the chen-appendixB-tables repository root:
#   ../gap-4.16.1/gap -q -b --quitonbreak gap/run-baseline.g
# MGSmallGroup's "table":4 field identifies the exporter; S3 and A4 are
# congruence controls from Table 1, not entries in Appendix B Table 4.
Read("gap/export-lib.g");
Read("gap/mg.g");
Print("GAP version: ", GAPInfo.Version, "\n");
MGSmallGroup(6, 1);
MGSmallGroup(12, 3);
MGSmallGroup(24, 12);
MGSmallGroup(24, 3);
MGSmallGroup(48, 28);
MGSmallGroup(48, 29);
MGSmallGroup(48, 30);
MGSmallGroup(48, 32);
MGSmallGroup(60, 5);
MGSmallGroup(168, 42);
QUIT;
