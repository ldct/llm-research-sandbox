# Compute element order distribution for the 14 groups

ComputeElementOrders := function(n, i)
    local G, elements, order_counts, e, ord, orders_list;

    G := SmallGroup(n, i);
    elements := Elements(G);

    # Count elements by order
    order_counts := [];

    for e in elements do
        ord := Order(e);
        if not IsBound(order_counts[ord]) then
            order_counts[ord] := 0;
        fi;
        order_counts[ord] := order_counts[ord] + 1;
    od;

    # Convert to list of [order, count] pairs
    orders_list := [];
    for ord in [1..Length(order_counts)] do
        if IsBound(order_counts[ord]) and order_counts[ord] > 0 then
            Add(orders_list, [ord, order_counts[ord]]);
        fi;
    od;

    return orders_list;
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

Print("Group,Order,ElementOrders\n");

for pair in pairs do
    result := ComputeElementOrders(pair[1], pair[2]);
    Print("SmallGroup(", pair[1], ",", pair[2], "),", pair[1], ",\"");

    # Print as comma-separated order:count pairs
    for i in [1..Length(result)] do
        Print(result[i][1], ":", result[i][2]);
        if i < Length(result) then
            Print(",");
        fi;
    od;
    Print("\"\n");
od;
