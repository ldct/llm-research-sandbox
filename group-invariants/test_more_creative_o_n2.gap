# More creative truly O(n²) invariants
# Focus on element order combinations and product orders

TestMoreCreative := function(n, i)
    local G, elements, inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8, a, b, e;

    G := SmallGroup(n, i);
    elements := AsList(G);
    e := One(G);

    # Invariant 1: Order(a)=2, Order(b)=2, Order(ab)=4
    inv1 := 0;
    for a in elements do
        if a^2 = e and a <> e then
            for b in elements do
                if b^2 = e and b <> e then
                    if (a*b)^4 = e and (a*b)^2 <> e then
                        inv1 := inv1 + 1;
                    fi;
                fi;
            od;
        fi;
    od;

    # Invariant 2: Order(a)=4, Order(b)=2, Order(ab)=4
    inv2 := 0;
    for a in elements do
        if a^4 = e and a^2 <> e then
            for b in elements do
                if b^2 = e and b <> e then
                    if (a*b)^4 = e and (a*b)^2 <> e then
                        inv2 := inv2 + 1;
                    fi;
                fi;
            od;
        fi;
    od;

    # Invariant 3: Order(a)=4, Order(b)=4, Order(ab)=2
    inv3 := 0;
    for a in elements do
        if a^4 = e and a^2 <> e then
            for b in elements do
                if b^4 = e and b^2 <> e then
                    if (a*b)^2 = e then
                        inv3 := inv3 + 1;
                    fi;
                fi;
            od;
        fi;
    od;

    # Invariant 4: Order(a)=4, Order(b)=4, Order(ab)=4
    inv4 := 0;
    for a in elements do
        if a^4 = e and a^2 <> e then
            for b in elements do
                if b^4 = e and b^2 <> e then
                    if (a*b)^4 = e and (a*b)^2 <> e then
                        inv4 := inv4 + 1;
                    fi;
                fi;
            od;
        fi;
    od;

    # Invariant 5: a² = b² (same square)
    inv5 := 0;
    for a in elements do
        for b in elements do
            if a^2 = b^2 then
                inv5 := inv5 + 1;
            fi;
        od;
    od;

    # Invariant 6: (ab)⁻¹ = ab (involution)
    inv6 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^-1 = a*b then
                inv6 := inv6 + 1;
            fi;
        od;
    od;

    # Invariant 7: a⁻¹ba = b⁻¹ (conjugate is inverse)
    inv7 := 0;
    for a in elements do
        for b in elements do
            if a^-1 * b * a = b^-1 then
                inv7 := inv7 + 1;
            fi;
        od;
    od;

    # Invariant 8: (ab)² = (ba)² (squares commute)
    inv8 := 0;
    for a in elements do
        for b in elements do
            if (a*b)^2 = (b*a)^2 then
                inv8 := inv8 + 1;
            fi;
        od;
    od;

    return [inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8];
end;

testGroups := [[32, 23], [32, 24], [32, 32], [32, 35]];

Print("order,index,o2_o2_o4,o4_o2_o4,o4_o4_o2,o4_o4_o4,same_sq,ab_involution,conj_inv,sq_commute\n");

for pair in testGroups do
    n := pair[1];
    i := pair[2];
    result := TestMoreCreative(n, i);
    Print(n, ",", i);
    for val in result do
        Print(",", val);
    od;
    Print("\n");
od;
