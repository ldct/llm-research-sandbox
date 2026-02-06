# Final batch of truly O(n²) invariants for the last 4 pairs

TestFinalTrulyO_n2 := function(n, i)
    local G, elements, inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8, inv9, inv10, a, b, e;

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

    # Invariant 2: (ab)³ = e (order divides 3)
    inv2 := 0;
    for a in elements do
        for b in elements do
            if (a * b)^3 = e then
                inv2 := inv2 + 1;
            fi;
        od;
    od;

    # Invariant 3: a⁻¹b⁻¹ab = (ab)⁻² (commutator equals inverse square of product)
    inv3 := 0;
    for a in elements do
        for b in elements do
            if a^-1 * b^-1 * a * b = (a*b)^-2 then
                inv3 := inv3 + 1;
            fi;
        od;
    od;

    # Invariant 4: (ab)² = e and (ba)² = e
    inv4 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^2 = e and (b*a)^2 = e then
                inv4 := inv4 + 1;
            fi;
        od;
    od;

    # Invariant 5: a²b² = e (product of squares is identity)
    inv5 := 0;
    for a in elements do
        for b in elements do
            if a^2 * b^2 = e then
                inv5 := inv5 + 1;
            fi;
        od;
    od;

    # Invariant 6: aba = bab (interchange identity)
    inv6 := 0;
    for a in elements do
        for b in elements do
            if a * b * a = b * a * b then
                inv6 := inv6 + 1;
            fi;
        od;
    od;

    # Invariant 7: (ab)⁴ = (ba)⁴
    inv7 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^4 = (b*a)^4 then
                inv7 := inv7 + 1;
            fi;
        od;
    od;

    # Invariant 8: a⁻¹b⁻¹ab = ba⁻¹b⁻¹a (commutator symmetry)
    inv8 := 0;
    for a in elements do
        for b in elements do
            if a^-1 * b^-1 * a * b = b * a^-1 * b^-1 * a then
                inv8 := inv8 + 1;
            fi;
        od;
    od;

    # Invariant 9: a²ba = aba² (square commutes with sandwich)
    inv9 := 0;
    for a in elements do
        for b in elements do
            if a^2 * b * a = a * b * a^2 then
                inv9 := inv9 + 1;
            fi;
        od;
    od;

    # Invariant 10: Order(a²)=Order(b²) [checking if squares have same order]
    inv10 := 0;
    for a in elements do
        for b in elements do
            # Check orders by testing powers
            found := false;
            for k in [1..16] do
                if (a^2)^k = e and (b^2)^k = e then
                    # Both have order dividing k, check if same
                    same_ord := true;
                    for j in [1..k-1] do
                        if ((a^2)^j = e) <> ((b^2)^j = e) then
                            same_ord := false;
                            break;
                        fi;
                    od;
                    if same_ord then
                        inv10 := inv10 + 1;
                        found := true;
                    fi;
                    break;
                fi;
            od;
        od;
    od;

    return [inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8, inv9, inv10];
end;

# Test the 4 remaining pairs
testGroups := [[32, 27], [32, 34], [32, 30], [32, 31], [32, 37], [32, 38], [32, 40], [32, 42]];

Print("order,index,a3_b3,ab3_e,comm_prod,both_sq2,a2b2_e,aba_bab,ab4_ba4,comm_sym,sq_sandwich,sq_ord\n");

for pair in testGroups do
    n := pair[1];
    i := pair[2];
    result := TestFinalTrulyO_n2(n, i);
    Print(n, ",", i);
    for val in result do
        Print(",", val);
    od;
    Print("\n");
od;
