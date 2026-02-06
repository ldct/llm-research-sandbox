# Time each of the 21 numerical properties separately

TimeProperty := function(n, i, prop_num)
    local G, elements, count, a, b, c, autG, startTime, endTime, result, subs;

    G := SmallGroup(n, i);

    startTime := Runtime();

    # Compute the property based on prop_num
    if prop_num = 1 then
        # Exponent
        result := Exponent(G);
    elif prop_num = 2 then
        # Center size
        result := Size(Center(G));
    elif prop_num = 3 then
        # Derived subgroup size
        result := Size(DerivedSubgroup(G));
    elif prop_num = 4 then
        # Number of conjugacy classes
        result := Length(ConjugacyClasses(G));
    elif prop_num = 5 then
        # Number of subgroups
        result := Length(AllSubgroups(G));
    elif prop_num = 6 then
        # Number of normal subgroups
        result := Length(NormalSubgroups(G));
    elif prop_num = 7 then
        # Number of maximal subgroups
        result := Length(MaximalSubgroups(G));
    elif prop_num = 8 then
        # Frattini subgroup size
        result := Size(FrattiniSubgroup(G));
    elif prop_num = 9 then
        # Number of cyclic subgroups
        count := 0;
        for a in AllSubgroups(G) do
            if IsCyclic(a) then
                count := count + 1;
            fi;
        od;
        result := count;
    elif prop_num = 10 then
        # Number of abelian subgroups
        count := 0;
        for a in AllSubgroups(G) do
            if IsAbelian(a) then
                count := count + 1;
            fi;
        od;
        result := count;
    elif prop_num = 11 then
        # Nilpotency class
        if IsNilpotent(G) then
            result := NilpotencyClassOfGroup(G);
        else
            result := 0;
        fi;
    elif prop_num = 12 then
        # Derived length
        if IsSolvable(G) then
            result := DerivedLength(G);
        else
            result := 0;
        fi;
    elif prop_num = 13 then
        # Number of elements of order 2
        count := 0;
        for a in G do
            if Order(a) = 2 then
                count := count + 1;
            fi;
        od;
        result := count;
    elif prop_num = 14 then
        # Automorphism group size
        autG := AutomorphismGroup(G);
        result := Size(autG);
    elif prop_num = 15 then
        # Minimum number of generators
        result := Length(MinimalGeneratingSet(G));
    elif prop_num = 16 then
        # Number of commuting pairs
        count := 0;
        elements := AsList(G);
        for a in elements do
            for b in elements do
                if a * b = b * a then
                    count := count + 1;
                fi;
            od;
        od;
        result := count;
    elif prop_num = 17 then
        # Number of triples where a*b*c = c*a*b
        count := 0;
        elements := AsList(G);
        for a in elements do
            for b in elements do
                for c in elements do
                    if a * b * c = c * a * b then
                        count := count + 1;
                    fi;
                od;
            od;
        od;
        result := count;
    elif prop_num = 18 then
        # Is abelian
        if IsAbelian(G) then
            result := 1;
        else
            result := 0;
        fi;
    elif prop_num = 19 then
        # Is cyclic
        if IsCyclic(G) then
            result := 1;
        else
            result := 0;
        fi;
    elif prop_num = 20 then
        # Fitting subgroup size
        result := Size(FittingSubgroup(G));
    elif prop_num = 21 then
        # Number of characteristic subgroups
        result := Length(CharacteristicSubgroups(G));
    fi;

    endTime := Runtime();

    return [result, endTime - startTime];
end;

# For each property, compute it for all groups and measure time
for prop_num in [1..21] do
    totalTime := 0;
    for n in [1..60] do
        for i in [1..NumberSmallGroups(n)] do
            result := TimeProperty(n, i, prop_num);
            totalTime := totalTime + result[2];
        od;
    od;
    Print(prop_num, ",", totalTime, "\n");
od;
