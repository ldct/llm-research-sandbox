# Compute number of triples where a*b*c = c*a*b for ALL groups of order <= 60

ComputeTriplesProperty := function(n, i)
    local G, elements, count, a, b, c, startTime, endTime;

    G := SmallGroup(n, i);
    elements := AsList(G);
    count := 0;

    startTime := Runtime();

    for a in elements do
        for b in elements do
            for c in elements do
                if a * b * c = c * a * b then
                    count := count + 1;
                fi;
            od;
        od;
    od;

    endTime := Runtime();

    return [count, endTime - startTime];
end;

# Compute for all groups
totalStartTime := Runtime();

for n in [1..60] do
    for i in [1..NumberSmallGroups(n)] do
        result := ComputeTriplesProperty(n, i);
        count := result[1];
        timeMs := result[2];
        Print(n, ",", i, ",", count, ",", timeMs, "\n");
    od;
od;

totalEndTime := Runtime();
Print("# Total time: ", totalEndTime - totalStartTime, " ms\n");
