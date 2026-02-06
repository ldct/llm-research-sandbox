# Test final batch of O(n²) invariants focusing on remaining indistinguishable pairs

TestFinalInvariants := function(n, i)
    local G, elements, count1, count2, count3, count4, count5, a, b;

    G := SmallGroup(n, i);
    elements := AsList(G);

    # Invariant 1: [a,b]² = identity (commutator has order ≤ 2)
    count1 := 0;
    for a in elements do
        for b in elements do
            if (a^-1 * b^-1 * a * b)^2 = One(G) then
                count1 := count1 + 1;
            fi;
        od;
    od;

    # Invariant 2: Order(a) divides Order(b) or vice versa
    count2 := 0;
    for a in elements do
        for b in elements do
            if Order(a) mod Order(b) = 0 or Order(b) mod Order(a) = 0 then
                count2 := count2 + 1;
            fi;
        od;
    od;

    # Invariant 3: (ab)³ = a³b³
    count3 := 0;
    for a in elements do
        for b in elements do
            if (a * b)^3 = a^3 * b^3 then
                count3 := count3 + 1;
            fi;
        od;
    od;

    # Invariant 4: a²b = ab²
    count4 := 0;
    for a in elements do
        for b in elements do
            if a^2 * b = a * b^2 then
                count4 := count4 + 1;
            fi;
        od;
    od;

    # Invariant 5: (ab)⁻¹ = b⁻¹a⁻¹ (always true, but let's count for sanity)
    # Instead: Order(ab) = 2
    count5 := 0;
    for a in elements do
        for b in elements do
            if Order(a * b) = 2 then
                count5 := count5 + 1;
            fi;
        od;
    od;

    return [count1, count2, count3, count4, count5];
end;

# Test only the remaining indistinguishable pairs
testGroups := [
    [32, 4], [32, 12],
    [32, 23], [32, 24],
    [32, 27], [32, 34],
    [32, 29], [32, 33],
    [32, 30], [32, 31],
    [32, 32], [32, 35],
    [32, 37], [32, 38],
    [32, 40], [32, 42],
    [48, 12], [48, 13]
];

Print("order,index,comm_sq_id,ord_divides,ab3_eq_a3b3,a2b_eq_ab2,ord_ab_eq_2\n");

for pair in testGroups do
    n := pair[1];
    i := pair[2];
    result := TestFinalInvariants(n, i);
    Print(n, ",", i);
    for val in result do
        Print(",", val);
    od;
    Print("\n");
od;
