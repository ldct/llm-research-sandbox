# Test truly O(n²) invariants - explicit pair enumeration only
# Targeting the last 2 pairs: (32,23) vs (32,24) and (32,32) vs (32,35)

TestTrulyO_n2 := function(n, i)
    local G, elements, inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8, inv9, inv10, a, b, e;

    G := SmallGroup(n, i);
    elements := AsList(G);
    e := One(G);

    # Invariant 1: Order(ab) = 2
    inv1 := 0;
    for a in elements do
        for b in elements do
            if (a * b) * (a * b) = e then
                inv1 := inv1 + 1;
            fi;
        od;
    od;

    # Invariant 2: Order(ab) = 4
    inv2 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^4 = e and (a*b)^2 <> e then
                inv2 := inv2 + 1;
            fi;
        od;
    od;

    # Invariant 3: Order(ab) = 8
    inv3 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^8 = e and (a*b)^4 <> e then
                inv3 := inv3 + 1;
            fi;
        od;
    od;

    # Invariant 4: a² = e and b² = e
    inv4 := 0;
    for a in elements do
        for b in elements do
            if a^2 = e and b^2 = e then
                inv4 := inv4 + 1;
            fi;
        od;
    od;

    # Invariant 5: a⁴ = e (order divides 4)
    inv5 := 0;
    for a in elements do
        for b in elements do
            if a^4 = e and b^4 = e then
                inv5 := inv5 + 1;
            fi;
        od;
    od;

    # Invariant 6: [a,b] has order 2 (commutator squared is identity)
    inv6 := 0;
    for a in elements do
        for b in elements do
            if ((a^-1 * b^-1 * a * b)^2) = e then
                inv6 := inv6 + 1;
            fi;
        od;
    od;

    # Invariant 7: [a,b] = e (they commute)
    inv7 := 0;
    for a in elements do
        for b in elements do
            if a^-1 * b^-1 * a * b = e then
                inv7 := inv7 + 1;
            fi;
        od;
    od;

    # Invariant 8: a^-1 b a = b (b is in center relative to a)
    inv8 := 0;
    for a in elements do
        for b in elements do
            if a^-1 * b * a = b then
                inv8 := inv8 + 1;
            fi;
        od;
    od;

    # Invariant 9: (ab)² = a²b²
    inv9 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^2 = a^2 * b^2 then
                inv9 := inv9 + 1;
            fi;
        od;
    od;

    # Invariant 10: abab = baba
    inv10 := 0;
    for a in elements do
        for b in elements do
            if a*b*a*b = b*a*b*a then
                inv10 := inv10 + 1;
            fi;
        od;
    od;

    return [inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8, inv9, inv10];
end;

# Test the 4 groups
testGroups := [[32, 23], [32, 24], [32, 32], [32, 35]];

Print("order,index,ord_ab_2,ord_ab_4,ord_ab_8,both_ord2,both_ord4,comm_ord2,commute,b_central,ab2_a2b2,abab_baba\n");

for pair in testGroups do
    n := pair[1];
    i := pair[2];
    result := TestTrulyO_n2(n, i);
    Print(n, ",", i);
    for val in result do
        Print(",", val);
    od;
    Print("\n");
od;
