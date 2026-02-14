# Phase 4: Order-aware and commutator-depth invariants for 2-groups
# Usage: echo 'n:=64;;' | cat - compute_phase4.g | gap -q
#
# Strategy: use element orders and commutator structure
#   u1: #{(a,b): Order(a*b) = Order(a)*Order(b)}  -- rarely true in non-abelian
#   u2: #{(a,b): Order(a) = 2 and Order(b) = 2 and Order(a*b) = 2}  -- involution triple products
#   u3: #{(a,b): Order(a) = 2 and Order(b) = 2 and Order(a*b) = 4}
#   u4: #{(a,b): Order(a) = 4 and a^2 = b^2}  -- shared squares among order-4 elements  
#   u5: #{(a,b): Order(a) = 2 and a*b = b*a}  -- involutions in centralizer
#   u6: #{(a,b): Order(a*b) = 2}  -- already pr2, skip
#   u7: #{(a,b): Order([a,b]) = 2}  -- commutator is involution
#   u8: #{(a,b): Order(a) = Order(b) and a*b = b*a}  -- same-order commuting pairs
#   u9: #{(a,b): Order(a) = 2 and b*a*b^-1 = a}  -- fixed involutions under conjugation (=u5)
#   u10: #{(a,b): Order(a) = 4 and Order(b) = 4 and a^2 = b^2 and a*b = b*a}
#   u11: #{(a,b): Order(a*b*a^-1*b^-1) divides 2}  -- = mix5, skip
#   u12: #{(a,b): a^2*b^2 = (a*b)^2}  -- iff ab=ba for groups, = inv1? No! a^2*b^2=(ab)^2 iff ab=ba only when order of elements allows cancellation... Actually (ab)^2 = abab, a^2b^2 = aabb. So a^2b^2=(ab)^2 iff ab=ba. So this IS inv1. Skip.
#   u13: #{(a,b): (a*b)^2 = a^2*b^(-2)}  -- nontrivial twist
#   u14: #{(a,b): [a,b,a] = e}  where [a,b,a] = [[a,b],a]
#   u15: #{(a,b): [a,b,b] = e}  where [a,b,b] = [[a,b],b]
#   u16: #{(a,b): a*b^2*a^-1 = b^2}  -- a normalizes <b^2>... same as t8 (a*b^2=b^2*a) with different phrasing. Actually same: a*b^2*a^-1=b^2 iff a*b^2=b^2*a. Skip.
#   u17: #{(a,b): a*b^2*a^-1 = b^(-2)}  -- a inverts b^2
#   u18: #{(a,b): Order(a)=4 and Order(b)=2 and a*b!=b*a}
#   u19: #{(a,b): (a*b^-1*a*b)^2 = e}
#   u20: #{(a,b): a*b*a^-1*b*a*b^-1 = b*a*b^-1*a*b*a^-1}  -- symmetric commutator words

SetPrintFormattingStatus("*stdout*", false);
for k in [1..NumberSmallGroups(n)] do
  G := SmallGroup(n, k);
  elements := AsList(G);
  id := Identity(G);
  sz := Size(G);

  # Precompute orders
  ords := List(elements, Order);

  u2:=0; u3:=0; u4:=0; u5:=0; u7:=0; u8:=0; u10:=0;
  u13:=0; u14:=0; u15:=0; u17:=0; u18:=0; u19:=0; u20:=0;

  for i in [1..sz] do
    a := elements[i];
    oa := ords[i];
    a2 := a^2;
    ainv := a^(-1);
    for j in [1..sz] do
      b := elements[j];
      ob := ords[j];
      b2 := b^2;
      binv := b^(-1);
      ab := a*b;
      ba := b*a;

      # u2: Order(a)=2, Order(b)=2, Order(ab)=2
      if oa = 2 and ob = 2 and ab^2 = id then u2:=u2+1; fi;

      # u3: Order(a)=2, Order(b)=2, Order(ab)=4
      if oa = 2 and ob = 2 then
        ab2 := ab^2;
        if ab2 <> id and ab2^2 = id then u3:=u3+1; fi;
      fi;

      # u4: Order(a)=4, a^2=b^2
      if oa = 4 and a2 = b2 then u4:=u4+1; fi;

      # u5: Order(a)=2, ab=ba
      if oa = 2 and ab = ba then u5:=u5+1; fi;

      # u7: Order([a,b])=2
      comm := ainv*binv*a*b;
      if comm <> id and comm^2 = id then u7:=u7+1; fi;

      # u8: Order(a)=Order(b), ab=ba
      if oa = ob and ab = ba then u8:=u8+1; fi;

      # u10: Order(a)=4, Order(b)=4, a^2=b^2, ab=ba
      if oa = 4 and ob = 4 and a2 = b2 and ab = ba then u10:=u10+1; fi;

      # u13: (ab)^2 = a^2 * b^(-2)
      if (ab)^2 = a2*b^(-2) then u13:=u13+1; fi;

      # u14: [[a,b],a] = e
      if ainv*comm^(-1)*a*comm = id then u14:=u14+1; fi;

      # u15: [[a,b],b] = e
      if binv*comm^(-1)*b*comm = id then u15:=u15+1; fi;

      # u17: a*b^2*a^-1 = b^(-2)
      if a*b2*ainv = b^(-2) then u17:=u17+1; fi;

      # u18: Order(a)=4, Order(b)=2, ab!=ba
      if oa = 4 and ob = 2 and ab <> ba then u18:=u18+1; fi;

      # u19: (a*b^-1*a*b)^2 = e
      w := a*binv*a*b;
      if w^2 = id then u19:=u19+1; fi;

      # u20: a*b*a^-1*b*a*b^-1 = b*a*b^-1*a*b*a^-1
      lhs := a*b*ainv*b*a*binv;
      rhs := b*a*binv*a*b*ainv;
      if lhs = rhs then u20:=u20+1; fi;
    od;
  od;
  Print(n,",",k,",",u2,",",u3,",",u4,",",u5,",",u7,",",u8,",",u10,",",u13,",",u14,",",u15,",",u17,",",u18,",",u19,",",u20,"\n");
od;
QUIT;
