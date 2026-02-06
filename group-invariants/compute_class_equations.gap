# Compute class equation for the 14 groups in the 7 indistinguishable pairs
# Class equation: |G| = |Z(G)| + sum of sizes of non-central conjugacy classes

ComputeClassEquation := function(n, i)
    local G, center_size, classes, class_sizes, class_sizes_sorted, size;

    G := SmallGroup(n, i);

    # Get center size
    center_size := Size(Center(G));

    # Get conjugacy classes
    classes := ConjugacyClasses(G);

    # Get sizes of each conjugacy class
    class_sizes := List(classes, Size);

    # Sort for canonical representation
    class_sizes_sorted := ShallowCopy(class_sizes);
    Sort(class_sizes_sorted);

    # Return: group order, center size, sorted class sizes
    return [Size(G), center_size, class_sizes_sorted];
end;

# The 7 problematic pairs
pairs := [
    [32, 2], [32, 24],
    [32, 13], [32, 15],
    [32, 27], [32, 34],
    [32, 30], [32, 31],
    [32, 37], [32, 38],
    [32, 40], [32, 42],
    [50, 1], [50, 4]
];

Print("Group,Order,CenterSize,ClassSizes\n");

for pair in pairs do
    result := ComputeClassEquation(pair[1], pair[2]);
    Print("SmallGroup(", pair[1], ",", pair[2], "),", result[1], ",", result[2], ",\"");

    # Print class sizes as a comma-separated list
    for i in [1..Length(result[3])] do
        Print(result[3][i]);
        if i < Length(result[3]) then
            Print(",");
        fi;
    od;
    Print("\"\n");
od;
