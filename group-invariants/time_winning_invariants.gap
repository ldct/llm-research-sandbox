# Time the winning truly O(n²) invariants on all groups

TimeWinningInvariants := function(n, i)
    local G, elements, inv_same_sq, inv_conj_inv, a, b, startTime, endTime;

    G := SmallGroup(n, i);
    elements := AsList(G);

    startTime := Runtime();

    # Invariant: a² = b²
    inv_same_sq := 0;
    for a in elements do
        for b in elements do
            if a^2 = b^2 then
                inv_same_sq := inv_same_sq + 1;
            fi;
        od;
    od;

    # Invariant: a⁻¹ba = b⁻¹
    inv_conj_inv := 0;
    for a in elements do
        for b in elements do
            if a^-1 * b * a = b^-1 then
                inv_conj_inv := inv_conj_inv + 1;
            fi;
        od;
    od;

    endTime := Runtime();

    return [inv_same_sq, inv_conj_inv, endTime - startTime];
end;

# Time on all groups
totalTime := 0;
for n in [1..60] do
    for i in [1..NumberSmallGroups(n)] do
        result := TimeWinningInvariants(n, i);
        Print(n, ",", i, ",", result[1], ",", result[2], ",", result[3], "\n");
        totalTime := totalTime + result[3];
    od;
od;

Print("# Total time: ", totalTime, " ms\n");
