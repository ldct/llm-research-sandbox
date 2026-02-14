s:=0;;for i in[1..NrSmallGroups(128)]do e:=AsList(SmallGroup(128,i));for g in e do for h in e do if g*h=h*g then s:=s+1;fi;od;od;od;Print(s,"\n");
