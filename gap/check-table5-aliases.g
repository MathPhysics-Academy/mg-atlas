Read("gap/export-lib.g");
a5 := IsomorphismGroups(SmallGroup(60,5),AlternatingGroup(5)) <> fail;;
l27 := IsomorphismGroups(SmallGroup(168,42),PSL(2,7)) <> fail;;
if not a5 or not l27 then Error("Table 5 alias check failed"); fi;
EmitJSON(Concatenation("{\"A5_is_SmallGroup_60_5\":",String(a5),",\"PSL_2_7_is_SmallGroup_168_42\":",String(l27),"}"));
QUIT;
