# Usage: echo 'n:=61;' | cat - compute_order.g | gap -q
# Or: generate with sed and pipe
for k in [1..NumberSmallGroups(n)] do
  G := SmallGroup(n, k);
  elements := AsList(G);
  id := Identity(G);
  inv1:=0; inv3:=0; inv5:=0; inv6:=0; inv13:=0; invA:=0; invB:=0; invC:=0;
  for a in elements do
    a2 := a^2;
    a3 := a*a2;
    a7 := a3*a3*a;
    for b in elements do
      ab := a*b;
      if ab = b*a then inv1:=inv1+1;
        if a2 = id then invA:=invA+1; fi;
      fi;
      if a2 = b^2 then inv3:=inv3+1; fi;
      if a3 = b^3 then inv5:=inv5+1; fi;
      if a2^2 = b^4 then inv6:=inv6+1; fi;
      if ab^2 = id then inv13:=inv13+1; fi;
      if ab^5 = id then invB:=invB+1; fi;
      if a7 = b^7 then invC:=invC+1; fi;
    od;
  od;
  Print(n,",",k,",",IsAbelian(G),",",inv1,",",inv3,",",inv5,",",inv6,",",inv13,",",invA,",",invB,",",invC,"\n");
od;
QUIT;
