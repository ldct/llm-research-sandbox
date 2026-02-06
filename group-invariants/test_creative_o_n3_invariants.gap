# Test creative O(n³) invariants on the 7 indistinguishable pairs

TestCreativeN3Invariants := function(n, i)
    local G, elements, e, a, b, c, inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8, inv9, inv10, inv11, inv12;

    G := SmallGroup(n, i);
    elements := AsList(G);
    e := One(G);

    # Invariant 1: abc = cab (original)
    inv1 := 0;
    for a in elements do
        for b in elements do
            for c in elements do
                if a*b*c = c*a*b then
                    inv1 := inv1 + 1;
                fi;
            od;
        od;
    od;

    # Invariant 2: abc = cba (reverse equals forward)
    inv2 := 0;
    for a in elements do
        for b in elements do
            for c in elements do
                if a*b*c = c*b*a then
                    inv2 := inv2 + 1;
                fi;
            od;
        od;
    od;

    # Invariant 3: abc = bca (cyclic permutation)
    inv3 := 0;
    for a in elements do
        for b in elements do
            for c in elements do
                if a*b*c = b*c*a then
                    inv3 := inv3 + 1;
                fi;
            od;
        od;
    od;

    # Invariant 4: (abc)^2 = e (triple is involution)
    inv4 := 0;
    for a in elements do
        for b in elements do
            for c in elements do
                if (a*b*c)^2 = e then
                    inv4 := inv4 + 1;
                fi;
            od;
        od;
    od;

    # Invariant 5: Order(abc) = 2
    inv5 := 0;
    for a in elements do
        for b in elements do
            for c in elements do
                if Order(a*b*c) = 2 then
                    inv5 := inv5 + 1;
                fi;
            od;
        od;
    od;

    # Invariant 6: Order(abc) = 4
    inv6 := 0;
    for a in elements do
        for b in elements do
            for c in elements do
                if Order(a*b*c) = 4 then
                    inv6 := inv6 + 1;
                fi;
            od;
        od;
    od;

    # Invariant 7: (ab)c = a(bc) but ab != ba (non-associativity with commutation)
    inv7 := 0;
    for a in elements do
        for b in elements do
            for c in elements do
                if (a*b)*c = a*(b*c) and a*b <> b*a then
                    inv7 := inv7 + 1;
                fi;
            od;
        od;
    od;

    # Invariant 8: [a,b]c = c[a,b] (commutator commutes with c)
    inv8 := 0;
    for a in elements do
        for b in elements do
            for c in elements do
                if (a^-1*b^-1*a*b)*c = c*(a^-1*b^-1*a*b) then
                    inv8 := inv8 + 1;
                fi;
            od;
        od;
    od;

    # Invariant 9: abc = a^2b^2c^2
    inv9 := 0;
    for a in elements do
        for b in elements do
            for c in elements do
                if a*b*c = a^2*b^2*c^2 then
                    inv9 := inv9 + 1;
                fi;
            od;
        od;
    od;

    # Invariant 10: ab*bc = a*bc*c (special factorization)
    inv10 := 0;
    for a in elements do
        for b in elements do
            for c in elements do
                if (a*b)*(b*c) = a*(b*c)*c then
                    inv10 := inv10 + 1;
                fi;
            od;
        od;
    od;

    # Invariant 11: aba*cbc = (ac)(ba)(bc) (special product)
    inv11 := 0;
    for a in elements do
        for b in elements do
            for c in elements do
                if (a*b*a)*(c*b*c) = (a*c)*(b*a)*(b*c) then
                    inv11 := inv11 + 1;
                fi;
            od;
        od;
    od;

    # Invariant 12: abc = acb (b and c commute with a in between)
    inv12 := 0;
    for a in elements do
        for b in elements do
            for c in elements do
                if a*b*c = a*c*b then
                    inv12 := inv12 + 1;
                fi;
            od;
        od;
    od;

    return [inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8, inv9, inv10, inv11, inv12];
end;

# Test the 7 problematic pairs
pairs := [
    [32, 2], [32, 24],
    [32, 13], [32, 15],
    [32, 27], [32, 34],
    [32, 30], [32, 31],
    [32, 37], [32, 38],
    [32, 40], [32, 42],
    [50, 1], [50, 4]
];

for pair in pairs do
    result := TestCreativeN3Invariants(pair[1], pair[2]);
    Print(pair[1], ",", pair[2]);
    for val in result do
        Print(",", val);
    od;
    Print("\n");
od;
