# Try creative O(n²) invariants for the last 2 pairs

TestCreativeInvariants := function(n, i)
    local G, elements, count1, count2, count3, count4, count5, count6, count7, a, b;

    G := SmallGroup(n, i);
    elements := AsList(G);

    # Invariant 1: a⁴ = b⁴
    count1 := 0;
    for a in elements do
        for b in elements do
            if a^4 = b^4 then
                count1 := count1 + 1;
            fi;
        od;
    od;

    # Invariant 2: ab³ = b³a
    count2 := 0;
    for a in elements do
        for b in elements do
            if a * b^3 = b^3 * a then
                count2 := count2 + 1;
            fi;
        od;
    od;

    # Invariant 3: a²b³ = b³a²
    count3 := 0;
    for a in elements do
        for b in elements do
            if a^2 * b^3 = b^3 * a^2 then
                count3 := count3 + 1;
            fi;
        od;
    od;

    # Invariant 4: Order(a²) = Order(b²)
    count4 := 0;
    for a in elements do
        for b in elements do
            if Order(a^2) = Order(b^2) then
                count4 := count4 + 1;
            fi;
        od;
    od;

    # Invariant 5: (ab)⁴ = a⁴b⁴
    count5 := 0;
    for a in elements do
        for b in elements do
            if (a * b)^4 = a^4 * b^4 then
                count5 := count5 + 1;
            fi;
        od;
    od;

    # Invariant 6: Order(a*b) ≤ 4
    count6 := 0;
    for a in elements do
        for b in elements do
            if Order(a * b) <= 4 then
                count6 := count6 + 1;
            fi;
        od;
    od;

    # Invariant 7: a and b generate same cyclic subgroup
    count7 := 0;
    for a in elements do
        for b in elements do
            if Subgroup(G, [a]) = Subgroup(G, [b]) then
                count7 := count7 + 1;
            fi;
        od;
    od;

    return [count1, count2, count3, count4, count5, count6, count7];
end;

# Test only the 2 remaining pairs
testGroups := [
    [32, 23], [32, 24],
    [32, 32], [32, 35]
];

Print("order,index,a4_eq_b4,ab3_eq_b3a,a2b3_eq_b3a2,ord_a2_eq_ord_b2,ab4_eq_a4b4,ord_ab_le4,same_cyclic\n");

for pair in testGroups do
    n := pair[1];
    i := pair[2];
    result := TestCreativeInvariants(n, i);
    Print(n, ",", i);
    for val in result do
        Print(",", val);
    od;
    Print("\n");
od;
