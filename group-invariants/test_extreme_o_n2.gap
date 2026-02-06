# Extreme creativity for the last 3 pairs - trying unusual patterns

TestExtreme := function(n, i)
    local G, elements, inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8, a, b, e, c;

    G := SmallGroup(n, i);
    elements := AsList(G);
    e := One(G);

    # Invariant 1: a⁻¹ba² = b (specific conjugacy pattern)
    inv1 := 0;
    for a in elements do
        for b in elements do
            if a^-1 * b * a^2 = b then
                inv1 := inv1 + 1;
            fi;
        od;
    od;

    # Invariant 2: (ab)⁻¹a(ab) = b (conjugate of a by ab equals b)
    inv2 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^-1 * a * (a*b) = b then
                inv2 := inv2 + 1;
            fi;
        od;
    od;

    # Invariant 3: a²b² = b²a²
    inv3 := 0;
    for a in elements do
        for b in elements do
            if a^2 * b^2 = b^2 * a^2 then
                inv3 := inv3 + 1;
            fi;
        od;
    od;

    # Invariant 4: (ab)² = a²b²
    inv4 := 0;
    for a in elements do
        for b in elements do
            if (a * b)^2 = a^2 * b^2 then
                inv4 := inv4 + 1;
            fi;
        od;
    od;

    # Invariant 5: bab⁻¹ = a² (conjugate by b gives square)
    inv5 := 0;
    for a in elements do
        for b in elements do
            if b * a * b^-1 = a^2 then
                inv5 := inv5 + 1;
            fi;
        od;
    od;

    # Invariant 6: (ab)² = (a²)(b²)
    inv6 := 0;
    for a in elements do
        for b in elements do
            if (a*b) * (a*b) = (a*a) * (b*b) then
                inv6 := inv6 + 1;
            fi;
        od;
    od;

    # Invariant 7: Order(ab) = 1 (product is identity)
    inv7 := 0;
    for a in elements do
        for b in elements do
            if a * b = e then
                inv7 := inv7 + 1;
            fi;
        od;
    od;

    # Invariant 8: b = a⁻¹ (inverse pairs)
    inv8 := 0;
    for a in elements do
        for b in elements do
            if b = a^-1 then
                inv8 := inv8 + 1;
            fi;
        od;
    od;

    return [inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8];
end;

# Test the 3 remaining pairs
testGroups := [[32, 27], [32, 34], [32, 30], [32, 31], [32, 37], [32, 38]];

Print("order,index,conj_a2,conj_ab,sq_comm,ab2_a2b2,conj_sq,ab2_dup,ab_id,inverse\n");

for pair in testGroups do
    n := pair[1];
    i := pair[2];
    result := TestExtreme(n, i);
    Print(n, ",", i);
    for val in result do
        Print(",", val);
    od;
    Print("\n");
od;
