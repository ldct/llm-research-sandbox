# Compute number of characteristic subgroups for all groups of order <= 60

for n in [1..60] do
    for i in [1..NumberSmallGroups(n)] do
        G := SmallGroup(n, i);
        numChar := Length(CharacteristicSubgroups(G));
        Print(n, ",", i, ",", numChar, "\n");
    od;
od;
