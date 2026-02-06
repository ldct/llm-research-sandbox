# Test multiple O(n²) invariants on specific groups

TestGroupInvariants := function(n, i)
    local G, elements, count1, count2, count3, count4, count5, a, b, startTime, endTime;

    G := SmallGroup(n, i);
    elements := AsList(G);

    startTime := Runtime();

    # Invariant 1: ab = ba² (left-right square)
    count1 := 0;
    for a in elements do
        for b in elements do
            if a * b = b * a^2 then
                count1 := count1 + 1;
            fi;
        od;
    od;

    # Invariant 2: a²b² = b²a²
    count2 := 0;
    for a in elements do
        for b in elements do
            if a^2 * b^2 = b^2 * a^2 then
                count2 := count2 + 1;
            fi;
        od;
    od;

    # Invariant 3: aba = bab
    count3 := 0;
    for a in elements do
        for b in elements do
            if a * b * a = b * a * b then
                count3 := count3 + 1;
            fi;
        od;
    od;

    # Invariant 4: ab² = b²a
    count4 := 0;
    for a in elements do
        for b in elements do
            if a * b^2 = b^2 * a then
                count4 := count4 + 1;
            fi;
        od;
    od;

    # Invariant 5: a³b = ba³
    count5 := 0;
    for a in elements do
        for b in elements do
            if a^3 * b = b * a^3 then
                count5 := count5 + 1;
            fi;
        od;
    od;

    endTime := Runtime();

    return [count1, count2, count3, count4, count5, endTime - startTime];
end;

# Groups to test (the indistinguishable pairs)
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

Print("order,index,ab_eq_ba2,a2b2_eq_b2a2,aba_eq_bab,ab2_eq_b2a,a3b_eq_ba3,time_ms\n");

for pair in testGroups do
    n := pair[1];
    i := pair[2];
    result := TestGroupInvariants(n, i);
    Print(n, ",", i);
    for val in result do
        Print(",", val);
    od;
    Print("\n");
od;
