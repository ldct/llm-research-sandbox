# Phase 1: Extended pair-counting invariants for collision orders
# Usage: echo 'n:=64;' | cat - compute_extended.g | gap -q
#
# Computes for each SmallGroup(n, k):
#   #{(a,b): a^e = b^e} for e in {8, 9, 11, 13, 16, 25, 27}
#   #{(a,b): (ab)^e = e} for e in {2, 3, 4, 5, 7, 8, 9, 11, 13}
# Also Phase 2 mixed-operation invariants:
#   #{(a,b): (ab)^2 = a^2 * b^2}
#   #{(a,b): a^2 * b = b * a^2}
#   #{(a,b): a * b = b * a^2}
#   #{(a,b): a * b * a = b * a * b}  (braid)
#   #{(a,b): [a,b]^2 = e}

SetPrintFormattingStatus("*stdout*", false);
for k in [1..NumberSmallGroups(n)] do
  G := SmallGroup(n, k);
  elements := AsList(G);
  id := Identity(G);
  sz := Size(G);

  # Phase 1: power-equality invariants
  # a^e = b^e for e in {8, 9, 11, 13, 16, 25, 27}
  pe8:=0; pe9:=0; pe11:=0; pe13:=0; pe16:=0; pe25:=0; pe27:=0;
  # (ab)^e = e for e in {2, 3, 4, 5, 7, 8, 9, 11, 13}
  pr2:=0; pr3:=0; pr4:=0; pr5:=0; pr7:=0; pr8:=0; pr9:=0; pr11:=0; pr13:=0;
  # Phase 2: mixed-operation invariants
  mix1:=0; # (ab)^2 = a^2 b^2
  mix2:=0; # a^2 b = b a^2
  mix3:=0; # a b = b a^2
  mix4:=0; # a b a = b a b (braid)
  mix5:=0; # [a,b]^2 = e

  for a in elements do
    a2 := a^2;
    a8 := a2^4;
    a9 := a^9;
    a11 := a^11;
    a13 := a^13;
    a16 := a8^2;
    a25 := a^25;
    a27 := a9^3;
    for b in elements do
      ab := a*b;

      # Power-equality: a^e = b^e
      b8 := b^8;
      if a8 = b8 then pe8:=pe8+1; fi;
      if a9 = b^9 then pe9:=pe9+1; fi;
      if a11 = b^11 then pe11:=pe11+1; fi;
      if a13 = b^13 then pe13:=pe13+1; fi;
      if a16 = b8^2 then pe16:=pe16+1; fi;
      if a25 = b^25 then pe25:=pe25+1; fi;
      if a27 = b^27 then pe27:=pe27+1; fi;

      # Product-order: (ab)^e = e
      ab2 := ab^2;
      if ab2 = id then pr2:=pr2+1; fi;
      if ab2*ab = id then pr3:=pr3+1; fi;
      if ab2^2 = id then pr4:=pr4+1; fi;
      if ab^5 = id then pr5:=pr5+1; fi;
      if ab^7 = id then pr7:=pr7+1; fi;
      if ab^8 = id then pr8:=pr8+1; fi;
      if ab^9 = id then pr9:=pr9+1; fi;
      if ab^11 = id then pr11:=pr11+1; fi;
      if ab^13 = id then pr13:=pr13+1; fi;

      # Mixed-operation
      b2 := b^2;
      if ab2 = a2*b2 then mix1:=mix1+1; fi;
      if a2*b = b*a2 then mix2:=mix2+1; fi;
      if ab = b*a2 then mix3:=mix3+1; fi;
      if a*b*a = b*a*b then mix4:=mix4+1; fi;
      # [a,b] = a^-1 b^-1 a b
      comm := a^(-1)*b^(-1)*a*b;
      if comm^2 = id then mix5:=mix5+1; fi;
    od;
  od;
  Print(n,",",k,",",pe8,",",pe9,",",pe11,",",pe13,",",pe16,",",pe25,",",pe27,",",pr2,",",pr3,",",pr4,",",pr5,",",pr7,",",pr8,",",pr9,",",pr11,",",pr13,",",mix1,",",mix2,",",mix3,",",mix4,",",mix5,"\n");
od;
QUIT;
