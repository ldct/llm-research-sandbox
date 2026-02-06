# Test additional truly O(n²) invariants on all indistinguishable pairs

TestAdditionalInvariants := function(n, i)
    local G, elements, inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8, a, b, e;

    G := SmallGroup(n, i);
    elements := AsList(G);
    e := One(G);

    # Invariant 1: a³ = b³
    inv1 := 0;
    for a in elements do
        for b in elements do
            if a^3 = b^3 then
                inv1 := inv1 + 1;
            fi;
        od;
    od;

    # Invariant 2: a⁴ = b⁴
    inv2 := 0;
    for a in elements do
        for b in elements do
            if a^4 = b^4 then
                inv2 := inv2 + 1;
            fi;
        od;
    od;

    # Invariant 3: ab³ = b³a
    inv3 := 0;
    for a in elements do
        for b in elements do
            if a * b^3 = b^3 * a then
                inv3 := inv3 + 1;
            fi;
        od;
    od;

    # Invariant 4: a³b = ba³
    inv4 := 0;
    for a in elements do
        for b in elements do
            if a^3 * b = b * a^3 then
                inv4 := inv4 + 1;
            fi;
        od;
    od;

    # Invariant 5: a²b² = b²a²
    inv5 := 0;
    for a in elements do
        for b in elements do
            if a^2 * b^2 = b^2 * a^2 then
                inv5 := inv5 + 1;
            fi;
        od;
    od;

    # Invariant 6: Order(ab) = 3
    inv6 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^3 = e and (a*b) <> e and (a*b)^2 <> e then
                inv6 := inv6 + 1;
            fi;
        od;
    od;

    # Invariant 7: (ab)² = (ba)²
    inv7 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^2 = (b*a)^2 then
                inv7 := inv7 + 1;
            fi;
        od;
    od;

    # Invariant 8: (ab)³ = (ba)³
    inv8 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^3 = (b*a)^3 then
                inv8 := inv8 + 1;
            fi;
        od;
    od;

    return [inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8];
end;

# Compute for all groups
for n in [1..60] do
    for i in [1..NumberSmallGroups(n)] do
        result := TestAdditionalInvariants(n, i);
        Print(n, ",", i);
        for val in result do
            Print(",", val);
        od;
        Print("\n");
    od;
od;
