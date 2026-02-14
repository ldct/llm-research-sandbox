# Additional structural invariants (lightweight)
# Usage: echo 'n:=128;;' | cat - compute_structural2.g | gap -q

SetPrintFormattingStatus("*stdout*", false);

for k in [1..NumberSmallGroups(n)] do
  G := SmallGroup(n, k);
  sz := Size(G);
  pp := SmallestPrimeDivisor(sz);
  
  Z1 := Center(G);
  Gp := DerivedSubgroup(G);
  phi := FrattiniSubgroup(G);
  
  # r1: |G/Z(G)|
  r1 := sz / Size(Z1);
  
  # r2: |G'/Phi(G')|
  if Size(Gp) > 1 then
    r2 := Size(Gp) / Size(FrattiniSubgroup(Gp));
  else
    r2 := 1;
  fi;
  
  # r3: # elements of order exactly p^2
  r3 := Length(Filtered(AsList(G), a -> Order(a) = pp*pp));
  
  # r4: # elements whose p-th power is identity (= |Omega_1| in a sense)
  r4 := Length(Filtered(AsList(G), a -> a^pp = Identity(G)));
  
  # r5: |G''|
  Gpp := DerivedSubgroup(Gp);
  r5 := Size(Gpp);
  
  # r6: number of abelian normal subgroups
  norms := NormalSubgroups(G);
  r6 := Length(Filtered(norms, IsAbelian));
  
  # r7: |Z(Phi(G))|
  r7 := Size(Center(phi));
  
  # r8: # normal subgroups of order p  
  r8 := Length(Filtered(norms, H -> Size(H) = pp));
  
  # r9: # normal subgroups of order p^2
  r9 := Length(Filtered(norms, H -> Size(H) = pp*pp));
  
  # r10: |Phi(G) ∩ Z(G)|
  r10 := Size(Intersection(phi, Z1));
  
  # r11: nilpotency class of G/Z(G)
  if Size(Z1) < sz then
    Q := G/Z1;
    if IsNilpotent(Q) then
      r11 := NilpotencyClassOfGroup(Q);
    else
      r11 := -1;
    fi;
  else
    r11 := 0;
  fi;
  
  # r12: |G' ∩ Z(G)|  
  r12 := Size(Intersection(Gp, Z1));
  
  # r13: number of conjugacy classes of maximal subgroups 
  r13 := Length(MaximalSubgroupClassReps(G));
  
  # r14: |G'/G''|
  r14 := Size(Gp) / Maximum(Size(Gpp), 1);
  
  # r15: exponent of Z(G)
  r15 := Exponent(Z1);
  
  # r16: # elements of order exactly p^3
  r16 := Length(Filtered(AsList(G), a -> Order(a) = pp^3));
  
  # r17: |Z(G')| center of derived subgroup
  r17 := Size(Center(Gp));
  
  # r18: rank of G' (minimal generators of derived subgroup)
  if Size(Gp) > 1 then
    r18 := Length(SmallGeneratingSet(Gp));
  else
    r18 := 0;
  fi;
  
  Print(n,",",k,",",r1,",",r2,",",r3,",",r4,",",r5,",",r6,",",r7,",",r8,",",r9,",",r10,",",r11,",",r12,",",r13,",",r14,",",r15,",",r16,",",r17,",",r18,"\n");
od;
QUIT;
