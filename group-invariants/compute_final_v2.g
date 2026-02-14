# Compute only for the 187 collision groups
# Use a layered approach: quotient hash first, then max subgroup hash for remaining,
# then more expensive invariants only as needed

LoadPackage("HAP");

collision_groups := [
[128,96],[128,97],[128,382],[128,384],[128,451],[128,452],[128,555],[128,556],
[128,650],[128,653],[128,651],[128,652],[128,719],[128,720],[128,807],[128,808],
[128,818],[128,819],[128,831],[128,832],[128,1078],[128,1079],[128,1158],[128,1223],
[128,1190],[128,1206],[128,1207],[128,1210],[128,1213],[128,1220],[128,1214],[128,1293],
[128,1226],[128,1227],[128,1240],[128,1241],[128,1252],[128,1320],[128,1254],[128,1319],
[128,1296],[128,1311],[128,1306],[128,1321],[128,1308],[128,1310],[128,1317],[128,1322],
[128,1383],[128,1532],[128,1404],[128,1413],[128,1418],[128,1428],[128,1436],[128,1452],
[128,1437],[128,1443],[128,1442],[128,1462],[128,1449],[128,1460],[128,1453],[128,1457],
[128,1481],[128,1510],[128,1487],[128,1506],[128,1490],[128,1494],[128,1500],[128,1522],
[128,1501],[128,1526],[128,1523],[128,1534],[128,1563],[128,1570],[128,1597],[128,1598],
[128,1970],[128,1971],[128,2048],[128,2052],[128,2080],[128,2082],[128,2279],[128,2286],
[160,70],[160,71],[189,4],[189,5],[192,503],[192,504],[192,638],[192,652],
[128,278],[128,280],[128,281],[128,1211],[128,1253],[128,1292],
[128,1256],[128,1260],[128,1265],[128,1385],[128,1469],[128,1483],
[128,1421],[128,1422],[128,1430],[128,1423],[128,1433],[128,1438],
[128,1426],[128,1439],[128,1450],[128,1434],[128,1447],[128,1455],
[128,1475],[128,1478],[128,1482],[192,40],[192,41],[192,45],[192,212],[192,213],[192,214],
[128,1192],[128,1198],[128,1200],[128,1202],[128,1199],[128,1203],[128,1208],[128,1289],
[128,1257],[128,1261],[128,1326],[128,1328],[128,1380],[128,1485],[128,1488],[128,1529],
[128,1382],[128,1486],[128,1507],[128,1530],[128,1387],[128,1498],[128,1499],[128,1508],
[128,1247],[128,1262],[128,1305],[128,1307],[128,1309],
[128,1248],[128,1250],[128,1258],[128,1263],[128,1327],[128,1329],
[128,1386],[128,1504],[128,1505],[128,1509],[128,1515],[128,1525],
[128,1384],[128,1470],[128,1471],[128,1476],[128,1479],[128,1497],[128,1502],[128,1519],
[128,1381],[128,1472],[128,1473],[128,1489],[128,1493],[128,1511],[128,1513],[128,1518],[128,1528]
];

Print("order,index,qhash,mhash,h3,h4,schash,pchash\n");

for p in collision_groups do
    G := SmallGroup(p[1], p[2]);
    
    # 1. Quotient profile
    norms := NormalSubgroups(G);
    qids := [];
    for N in norms do
        if Size(N) > 1 and Size(N) < Size(G) then
            Add(qids, IdSmallGroup(G / N));
        fi;
    od;
    Sort(qids);
    # Simple hash: concatenate all IDs
    qhash := Sum(List([1..Length(qids)], i -> (i * 10007 + qids[i][1]) * 100003 + qids[i][2])) mod (2^53);
    
    # 2. Maximal subgroup IDs
    maxsubs := MaximalSubgroups(G);
    maxids := List(maxsubs, H -> IdSmallGroup(H));
    Sort(maxids);
    mhash := Sum(List([1..Length(maxids)], i -> (i * 10007 + maxids[i][1]) * 100003 + maxids[i][2])) mod (2^53);
    
    # 3. H^3
    h3 := GroupCohomology(G, 3);
    Sort(h3);
    
    # 4. H^4
    h4 := GroupCohomology(G, 4);
    Sort(h4);
    
    # 5. Structure constant hash (over the character table)
    ct := CharacterTable(G);
    ncc := NrConjugacyClasses(ct);
    scsum := 0;
    for i in [1..ncc] do
        for j in [i..ncc] do
            for kk in [1..ncc] do
                v := ClassMultiplicationCoefficient(ct, i, j, kk);
                if v > 0 then
                    scsum := scsum + (i * ncc * ncc + j * ncc + kk) * v;
                fi;
            od;
        od;
    od;
    schash := scsum mod (2^53);
    
    # 6. PC presentation hash
    pchash := 0;
    if IsSolvableGroup(G) then
        pcgs := FamilyPcgs(G);
        rels := RelativeOrders(pcgs);
        for i in [1..Length(pcgs)] do
            pp := rels[i];
            exp := ExponentsOfPcElement(pcgs, pcgs[i]^pp);
            pchash := (pchash + (i * 997 + pp) * 10007) mod (2^53);
            for j in [1..Length(exp)] do
                pchash := (pchash + i * 100 * j * (exp[j] + 1)) mod (2^53);
            od;
        od;
        for i in [1..Length(pcgs)] do
            for j in [i+1..Length(pcgs)] do
                exp := ExponentsOfPcElement(pcgs, pcgs[j]^pcgs[i]);
                for kk in [1..Length(exp)] do
                    pchash := (pchash + (i*1000+j) * kk * (exp[kk] + 3)) mod (2^53);
                od;
            od;
        od;
    fi;
    
    Print(p[1], ",", p[2], ",", qhash, ",", mhash, ",\"", h3, "\",\"", h4, "\",", schash, ",", pchash, "\n");
od;
