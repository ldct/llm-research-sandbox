# Phase 3: Deeper structural invariants for stubborn collision groups
# Usage: echo 'n:=64;;' | cat - compute_phase3.g | gap -q
#
# New invariants targeting 2-group structure:
#   t1: #{(a,b): (ab)^2 = (ba)^2}
#   t2: #{(a,b): a^2 = b*a*b^(-1)}  (a^2 is conjugate of a by b... i.e. b*a*b^-1 = a^2)
#   t3: #{(a,b): a*b*a^-1*b^-1*a = b}  (commutator-like)
#   t4: #{(a,b): (a*b*a)^2 = e}
#   t5: #{(a,b): a*b^2*a = b*a^2*b}
#   t6: #{(a,b): [a,[a,b]] = e}  (a commutes with [a,b])
#   t7: #{(a,b): [a,b]*[b,a] = e}  (always true if abelian; [a,b][b,a] = e iff [a,b]^2 = e since [b,a]=[a,b]^-1)
#   t8: #{(a,b): a*b^2 = b^2*a}  (b^2 centralizes a -- note this is NOT the same as a^2*b=b*a^2 which is mix2)
#   t9: #{(a,b): (a*b)^4 = e}
#   t10: #{(a,b): (a*b)^4 = (a*b^-1)^4}
#   t11: #{(a,b): a^2*b^2 = b^2*a^2}
#   t12: #{(a,b): (a*b*a^-1)^2 = b^2}  (conjugation preserves squaring)
#   t13: #{(a,b): a*b*a = b*a^2*b^-1*a}  -- simplified: aba = b*a^2*b^-1*a
#   t14: #{(a,b): [a,b]^4 = e}
#   t15: #{(a,b): a^4 = b^4}  (should already be inv6, skip -- wait inv6 is a^4=b^4 yes)
#   t16: #{(a,b): a*b*a^-1 = b^-1}  (a inverts b)

SetPrintFormattingStatus("*stdout*", false);
for k in [1..NumberSmallGroups(n)] do
  G := SmallGroup(n, k);
  elements := AsList(G);
  id := Identity(G);

  t1:=0; t2:=0; t3:=0; t4:=0; t5:=0; t6:=0;
  t8:=0; t9:=0; t10:=0; t11:=0; t12:=0; t14:=0; t16:=0;

  for a in elements do
    a2 := a^2;
    ainv := a^(-1);
    a4 := a2^2;
    for b in elements do
      ab := a*b;
      ba := b*a;
      binv := b^(-1);
      b2 := b^2;
      ab2 := ab^2;
      ba2 := ba^2;

      # t1: (ab)^2 = (ba)^2
      if ab2 = ba2 then t1:=t1+1; fi;

      # t2: b*a*b^-1 = a^2  (conjugation by b sends a to a^2)
      if b*a*binv = a2 then t2:=t2+1; fi;

      # t3: a*b*a^-1*b^-1*a = b  (i.e., [a,b]*a = b)
      if a*b*ainv*binv*a = b then t3:=t3+1; fi;

      # t4: (a*b*a)^2 = e
      if (a*ba)^2 = id then t4:=t4+1; fi;

      # t5: a*b^2*a = b*a^2*b
      if a*b2*a = b*a2*b then t5:=t5+1; fi;

      # t6: [a,[a,b]] = e  where [a,b] = a^-1*b^-1*a*b
      comm := ainv*binv*a*b;
      if ainv*comm^(-1)*a*comm = id then t6:=t6+1; fi;

      # t8: a*b^2 = b^2*a  (b^2 centralizes a)
      if a*b2 = b2*a then t8:=t8+1; fi;

      # t9: (ab)^4 = e
      if ab2^2 = id then t9:=t9+1; fi;

      # t10: (ab)^4 = (a*b^-1)^4
      abinv := a*binv;
      if ab2^2 = (abinv^2)^2 then t10:=t10+1; fi;

      # t11: a^2*b^2 = b^2*a^2
      if a2*b2 = b2*a2 then t11:=t11+1; fi;

      # t12: (a*b*a^-1)^2 = b^2  (conjugation preserves squares)
      conj := a*b*ainv;
      if conj^2 = b2 then t12:=t12+1; fi;

      # t14: [a,b]^4 = e
      if comm^4 = id then t14:=t14+1; fi;

      # t16: a*b*a^-1 = b^-1  (a inverts b)
      if conj = binv then t16:=t16+1; fi;
    od;
  od;
  Print(n,",",k,",",t1,",",t2,",",t3,",",t4,",",t5,",",t6,",",t8,",",t9,",",t10,",",t11,",",t12,",",t14,",",t16,"\n");
od;
QUIT;
