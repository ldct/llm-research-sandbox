# Compute number of pairs (a,b) where a^2*b = b^2*a for all groups of order <= 60

ComputeA2bEqB2a := function(n, i)
    local G, elements, count, a, b, startTime, endTime;

    G := SmallGroup(n, i);
    elements := AsList(G);
    count := 0;

    startTime := Runtime();

    for a in elements do
        for b in elements do
            if a^2 * b = b^2 * a then
                count := count + 1;
            fi;
        od;
    od;

    endTime := Runtime();

    return [count, endTime - startTime];
end;

# Compute for all groups
totalStartTime := Runtime();

for n in [1..60] do
    for i in [1..NumberSmallGroups(n)] do
        result := ComputeA2bEqB2a(n, i);
        count := result[1];
        timeMs := result[2];
        Print(n, ",", i, ",", count, ",", timeMs, "\n");
    od;
od;

totalEndTime := Runtime();
Print("# Total time: ", totalEndTime - totalStartTime, " ms\n");
