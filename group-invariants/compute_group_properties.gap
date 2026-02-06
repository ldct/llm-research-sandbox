# Compute 20 different numerical properties for groups of order <= 60

ComputeAllProperties := function(n, i)
    local G, props, center, derived, autG, elements, pairs, triples, a, b, c, count;

    G := SmallGroup(n, i);
    props := [];

    # 1. Exponent
    Add(props, Exponent(G));

    # 2. Size of center
    Add(props, Size(Center(G)));

    # 3. Size of derived subgroup
    Add(props, Size(DerivedSubgroup(G)));

    # 4. Number of conjugacy classes
    Add(props, Length(ConjugacyClasses(G)));

    # 5. Number of subgroups
    Add(props, Length(AllSubgroups(G)));

    # 6. Number of normal subgroups
    Add(props, Length(NormalSubgroups(G)));

    # 7. Number of maximal subgroups
    Add(props, Length(MaximalSubgroups(G)));

    # 8. Size of Frattini subgroup
    Add(props, Size(FrattiniSubgroup(G)));

    # 9. Number of cyclic subgroups
    count := 0;
    for a in AllSubgroups(G) do
        if IsCyclic(a) then
            count := count + 1;
        fi;
    od;
    Add(props, count);

    # 10. Number of abelian subgroups
    count := 0;
    for a in AllSubgroups(G) do
        if IsAbelian(a) then
            count := count + 1;
        fi;
    od;
    Add(props, count);

    # 11. Nilpotency class (0 if not nilpotent)
    if IsNilpotent(G) then
        Add(props, NilpotencyClassOfGroup(G));
    else
        Add(props, 0);
    fi;

    # 12. Derived length (0 if not solvable)
    if IsSolvable(G) then
        Add(props, DerivedLength(G));
    else
        Add(props, 0);
    fi;

    # 13. Number of elements of order 2
    count := 0;
    for a in G do
        if Order(a) = 2 then
            count := count + 1;
        fi;
    od;
    Add(props, count);

    # 14. Size of automorphism group
    autG := AutomorphismGroup(G);
    Add(props, Size(autG));

    # 15. Minimum number of generators
    Add(props, Length(MinimalGeneratingSet(G)));

    # 16. Number of commuting pairs
    count := 0;
    elements := AsList(G);
    for a in elements do
        for b in elements do
            if a * b = b * a then
                count := count + 1;
            fi;
        od;
    od;
    Add(props, count);

    # 17. Number of triples where a*b*c = c*a*b (only for small groups)
    if n <= 20 then
        count := 0;
        for a in elements do
            for b in elements do
                for c in elements do
                    if a * b * c = c * a * b then
                        count := count + 1;
                    fi;
                od;
            od;
        od;
        Add(props, count);
    else
        Add(props, -1);  # -1 means not computed
    fi;

    # 18. Is abelian (0 or 1)
    if IsAbelian(G) then
        Add(props, 1);
    else
        Add(props, 0);
    fi;

    # 19. Is cyclic (0 or 1)
    if IsCyclic(G) then
        Add(props, 1);
    else
        Add(props, 0);
    fi;

    # 20. Size of Fitting subgroup
    Add(props, Size(FittingSubgroup(G)));

    return props;
end;

# Main computation loop
for n in [1..60] do
    for i in [1..NumberSmallGroups(n)] do
        props := ComputeAllProperties(n, i);
        Print(n, ",", i);
        for p in props do
            Print(",", p);
        od;
        Print("\n");
    od;
od;
