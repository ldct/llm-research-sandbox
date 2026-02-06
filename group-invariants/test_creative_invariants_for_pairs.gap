# Test creative O(n²) invariants on the 7 indistinguishable pairs
# Goal: find a single invariant that can distinguish most or all of them

TestCreativeInvariants := function(n, i)
    local G, elements, e, a, b;
    local inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8, inv9, inv10;
    local inv11, inv12, inv13, inv14, inv15;

    G := SmallGroup(n, i);
    elements := AsList(G);
    e := One(G);

    # Invariant 1: a^5 = b^5
    inv1 := 0;
    for a in elements do
        for b in elements do
            if a^5 = b^5 then
                inv1 := inv1 + 1;
            fi;
        od;
    od;

    # Invariant 2: (ab)^5 = (ba)^5
    inv2 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^5 = (b*a)^5 then
                inv2 := inv2 + 1;
            fi;
        od;
    od;

    # Invariant 3: Order(a) = Order(b)
    inv3 := 0;
    for a in elements do
        for b in elements do
            if Order(a) = Order(b) then
                inv3 := inv3 + 1;
            fi;
        od;
    od;

    # Invariant 4: a^2b = ba^2 (b normalizes a^2)
    inv4 := 0;
    for a in elements do
        for b in elements do
            if a^2 * b = b * a^2 then
                inv4 := inv4 + 1;
            fi;
        od;
    od;

    # Invariant 5: a^3b = ba^3 (b normalizes a^3)
    inv5 := 0;
    for a in elements do
        for b in elements do
            if a^3 * b = b * a^3 then
                inv5 := inv5 + 1;
            fi;
        od;
    od;

    # Invariant 6: aba = a^2b
    inv6 := 0;
    for a in elements do
        for b in elements do
            if a*b*a = a^2*b then
                inv6 := inv6 + 1;
            fi;
        od;
    od;

    # Invariant 7: aba^-1 = b^2
    inv7 := 0;
    for a in elements do
        for b in elements do
            if a*b*a^-1 = b^2 then
                inv7 := inv7 + 1;
            fi;
        od;
    od;

    # Invariant 8: [a,b]^2 = identity (commutator is involution)
    inv8 := 0;
    for a in elements do
        for b in elements do
            if (a^-1 * b^-1 * a * b)^2 = e then
                inv8 := inv8 + 1;
            fi;
        od;
    od;

    # Invariant 9: (aba)^2 = identity
    inv9 := 0;
    for a in elements do
        for b in elements do
            if (a*b*a)^2 = e then
                inv9 := inv9 + 1;
            fi;
        od;
    od;

    # Invariant 10: Order(ab) = 2
    inv10 := 0;
    for a in elements do
        for b in elements do
            if Order(a*b) = 2 then
                inv10 := inv10 + 1;
            fi;
        od;
    od;

    # Invariant 11: Order(ab) = 4
    inv11 := 0;
    for a in elements do
        for b in elements do
            if Order(a*b) = 4 then
                inv11 := inv11 + 1;
            fi;
        od;
    od;

    # Invariant 12: Order(ab) = 5
    inv12 := 0;
    for a in elements do
        for b in elements do
            if Order(a*b) = 5 then
                inv12 := inv12 + 1;
            fi;
        od;
    od;

    # Invariant 13: abab = a^2b^2
    inv13 := 0;
    for a in elements do
        for b in elements do
            if a*b*a*b = a^2*b^2 then
                inv13 := inv13 + 1;
            fi;
        od;
    od;

    # Invariant 14: (ab)^-1 = ba (ab and ba are inverses)
    inv14 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^-1 = b*a then
                inv14 := inv14 + 1;
            fi;
        od;
    od;

    # Invariant 15: a^2b^2 = (ab)^2
    inv15 := 0;
    for a in elements do
        for b in elements do
            if a^2*b^2 = (a*b)^2 then
                inv15 := inv15 + 1;
            fi;
        od;
    od;

    return [inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8, inv9, inv10, inv11, inv12, inv13, inv14, inv15];
end;

# Test only the 7 problematic pairs
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
    result := TestCreativeInvariants(pair[1], pair[2]);
    Print(pair[1], ",", pair[2]);
    for val in result do
        Print(",", val);
    od;
    Print("\n");
od;
