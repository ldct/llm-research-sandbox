# Test even more creative O(n²) invariants

TestMoreCreative2 := function(n, i)
    local G, elements, inv1, inv2, inv3, inv4, inv5, inv6, a, b, e;

    G := SmallGroup(n, i);
    elements := AsList(G);
    e := One(G);

    # Invariant 1: (ab)⁻¹ = ab (involution)
    inv1 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^-1 = a*b then
                inv1 := inv1 + 1;
            fi;
        od;
    od;

    # Invariant 2: aba = bab
    inv2 := 0;
    for a in elements do
        for b in elements do
            if a*b*a = b*a*b then
                inv2 := inv2 + 1;
            fi;
        od;
    od;

    # Invariant 3: aba⁻¹ = bab⁻¹
    inv3 := 0;
    for a in elements do
        for b in elements do
            if a*b*a^-1 = b*a*b^-1 then
                inv3 := inv3 + 1;
            fi;
        od;
    od;

    # Invariant 4: a²b³ = b³a²
    inv4 := 0;
    for a in elements do
        for b in elements do
            if a^2 * b^3 = b^3 * a^2 then
                inv4 := inv4 + 1;
            fi;
        od;
    od;

    # Invariant 5: (ab)⁴ = (ba)⁴
    inv5 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^4 = (b*a)^4 then
                inv5 := inv5 + 1;
            fi;
        od;
    od;

    # Invariant 6: bab⁻¹ = a² (conjugate gives square)
    inv6 := 0;
    for a in elements do
        for b in elements do
            if b*a*b^-1 = a^2 then
                inv6 := inv6 + 1;
            fi;
        od;
    od;

    return [inv1, inv2, inv3, inv4, inv5, inv6];
end;

# Compute for all groups
for n in [1..60] do
    for i in [1..NumberSmallGroups(n)] do
        result := TestMoreCreative2(n, i);
        Print(n, ",", i);
        for val in result do
            Print(",", val);
        od;
        Print("\n");
    od;
od;
