# Test more O(n²) invariants with different patterns

TestMoreInvariants := function(n, i)
    local G, elements, count1, count2, count3, count4, count5, count6, a, b;

    G := SmallGroup(n, i);
    elements := AsList(G);

    # Invariant 1: (ab)² = (ba)²
    count1 := 0;
    for a in elements do
        for b in elements do
            if (a * b)^2 = (b * a)^2 then
                count1 := count1 + 1;
            fi;
        od;
    od;

    # Invariant 2: aba⁻¹ = bab⁻¹ (conjugates commute)
    count2 := 0;
    for a in elements do
        for b in elements do
            if a * b * a^-1 = b * a * b^-1 then
                count2 := count2 + 1;
            fi;
        od;
    od;

    # Invariant 3: [a,b] = [b,a] (commutators are symmetric)
    count3 := 0;
    for a in elements do
        for b in elements do
            if a^-1 * b^-1 * a * b = b^-1 * a^-1 * b * a then
                count3 := count3 + 1;
            fi;
        od;
    od;

    # Invariant 4: a and b have same order
    count4 := 0;
    for a in elements do
        for b in elements do
            if Order(a) = Order(b) then
                count4 := count4 + 1;
            fi;
        od;
    od;

    # Invariant 5: a and b are conjugate
    count5 := 0;
    for a in elements do
        for b in elements do
            if IsConjugate(G, a, b) then
                count5 := count5 + 1;
            fi;
        od;
    od;

    # Invariant 6: Order(ab) = Order(ba)
    count6 := 0;
    for a in elements do
        for b in elements do
            if Order(a * b) = Order(b * a) then
                count6 := count6 + 1;
            fi;
        od;
    od;

    return [count1, count2, count3, count4, count5, count6];
end;

# Groups to test
testGroups := [
    [32, 4], [32, 12],
    [32, 10], [32, 13], [32, 14], [32, 15],
    [32, 23], [32, 24],
    [32, 27], [32, 34],
    [32, 29], [32, 33],
    [32, 30], [32, 31],
    [32, 32], [32, 35],
    [32, 37], [32, 38],
    [32, 40], [32, 42],
    [48, 12], [48, 13]
];

Print("order,index,ab2_eq_ba2,aba1_eq_bab1,comm_sym,same_order,conjugate,ord_ab_eq_ord_ba\n");

for pair in testGroups do
    n := pair[1];
    i := pair[2];
    result := TestMoreInvariants(n, i);
    Print(n, ",", i);
    for val in result do
        Print(",", val);
    od;
    Print("\n");
od;
