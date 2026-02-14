# Results: Extending 8 Invariants to Order 200

## Summary

The 8 O(n²) invariants from `eight_invariants.md` were tested on all **6,065 groups of order ≤ 200**.

- **4,856 unique signatures** out of 6,065 groups (80.1%) with the original 8 invariants
- **686 collision clusters** involving 1,895 groups
- **Zero cross-order collisions** — every collision is within a single order
- **Collisions occur at exactly 13 orders**, all divisible by p² for some prime p

## Extended Invariant Campaign

After the initial 8 invariants, we computed 84 additional invariants across 5 phases to resolve collisions. All computations targeted the 13 collision orders (4,768 groups).

### Invariant Phases

| Phase | File | # Invariants | Description |
|:-----:|------|:---:|-------------|
| Original | `invariants_data.csv` | 8 | O(n²) pair-counting: commutativity, power-equality, product-order |
| Phase 1 | `extended_invariants.csv` | 21 | O(n²): prime-power exponents (a^8=b^8, etc.), product orders ((ab)^k=e), basic mixed ops |
| Phase 3 | `phase3_invariants.csv` | 13 | O(n²): conjugation ((ab)²=(ba)², b·a·b⁻¹=a²), iterated commutators, braid relations |
| Phase 4 | `phase4_invariants.csv` | 14 | O(n²): order-aware (involution pairs, same-order commuting, element-order interactions) |
| Structural 1 | `structural_invariants.csv` | 18 | GAP structural: |Aut(G)|, conjugacy class counts, normal subgroup counts, nilpotency class, derived length, exponent, rank, Frattini, center, Omega₁ |
| Structural 2 | `structural2_invariants.csv` | 18 | GAP structural: |G/Z(G)|, |G'/Φ(G')|, |G''|, abelian normal subgroup count, |Z(Φ(G))|, normal subgroups by order, |Z(G')|, exponent of Z(G) |
| **Total** | | **92** | |

### Disambiguation Power

| Invariant Set | Clusters | Groups Colliding | % Distinguished |
|:---|:---:|:---:|:---:|
| Original 8 | 686 | 1,895 | 80.1% |
| + Structural 1 alone | 75 | 381 | 96.1% |
| + Structural 1+2 | 68 | 363 | 96.3% |
| + All 48 O(n²) pair-counting | 335 | 1,091 | 90.2% |
| **All 92 combined** | **70** | **187** | **96.9%** |

### Greedy Minimal Set

A greedy selection finds **17 invariants** (8 original + 9 new) that achieve the same as all 92:

| # | Invariant | Description | Source |
|:-:|:----------|:------------|:------:|
| 1 | inv1 | #{(a,b): ab=ba} | Original |
| 2 | inv3 | #{(a,b): a²=b²} | Original |
| 3 | inv5 | #{(a,b): a³=b³} | Original |
| 4 | inv6 | #{(a,b): a⁴=b⁴} | Original |
| 5 | inv13 | #{(a,b): (ab)²=e} | Original |
| 6 | invA | #{(a,b): ab=ba ∧ a²=e} | Original |
| 7 | invB | #{(a,b): (ab)⁵=e} | Original |
| 8 | invC | #{(a,b): a⁷=b⁷} | Original |
| 9 | s2 | # conjugacy classes of subgroups | Structural 1 |
| 10 | s9 | # characteristic subgroups | Structural 1 |
| 11 | r6 | # abelian normal subgroups | Structural 2 |
| 12 | u10 | #{(a,b): ord(a)=4, ord(b)=4, a²=b², ab=ba} | Phase 4 |
| 13 | u4 | #{(a,b): ord(a)=4, a²=b²} | Phase 4 |
| 14 | s18 | |Ω₁(G)| (subgroup gen. by elements of order p) | Structural 1 |
| 15 | s1 | |Aut(G)| | Structural 1 |
| 16 | s3 | # normal subgroups | Structural 1 |
| 17 | u3 | #{(a,b): ord(a)=2, ord(b)=2, ord(ab)=4} | Phase 4 |

## Remaining 70 Collision Clusters

All 92 invariants fail to distinguish 70 clusters involving 187 groups:

| Order | Clusters | Groups | Notes |
|:---:|:---:|:---:|:---|
| 128 (2⁷) | 64 | 173 | Hard core of 2-group degeneracy |
| 192 (2⁶·3) | 4 | 10 | |
| 160 (2⁵·5) | 1 | 2 | groups [70, 71] |
| 189 (3³·7) | 1 | 2 | groups [4, 5] |

### Cluster size distribution

| Size | Count |
|:---:|:---:|
| 2 | 48 |
| 3 | 11 |
| 4 | 6 |
| 5 | 1 |
| 6 | 2 |
| 8 | 1 |
| 9 | 1 |

Largest cluster: order 128, groups [1381, 1472, 1473, 1489, 1493, 1511, 1513, 1518, 1528] — 9 groups with identical values on all 92 invariants.

### Order 128 collision clusters

```
[96, 97] [278, 280, 281] [382, 384] [451, 452] [555, 556]
[650, 653] [651, 652] [719, 720] [807, 808] [818, 819]
[831, 832] [1078, 1079] [1158, 1223] [1190, 1206] 
[1192, 1198, 1200, 1202] [1199, 1203, 1208, 1289]
[1207, 1210] [1211, 1253, 1292] [1213, 1220] [1214, 1293]
[1226, 1227] [1240, 1241] [1247, 1262, 1305, 1307, 1309]
[1248, 1250, 1258, 1263, 1327, 1329] [1252, 1320] [1254, 1319]
[1256, 1260, 1265] [1257, 1261, 1326, 1328] [1296, 1311]
[1306, 1321] [1308, 1310] [1317, 1322]
[1380, 1485, 1488, 1529] [1381, 1472, 1473, 1489, 1493, 1511, 1513, 1518, 1528]
[1382, 1486, 1507, 1530] [1383, 1532] 
[1384, 1470, 1471, 1476, 1479, 1497, 1502, 1519]
[1385, 1469, 1483] [1386, 1504, 1505, 1509, 1515, 1525]
[1387, 1498, 1499, 1508] [1404, 1413] [1418, 1428]
[1421, 1422, 1430] [1423, 1433, 1438] [1426, 1439, 1450]
[1434, 1447, 1455] [1436, 1452] [1437, 1443] [1442, 1462]
[1449, 1460] [1453, 1457] [1475, 1478, 1482] [1481, 1510]
[1487, 1506] [1490, 1494] [1500, 1522] [1501, 1526]
[1523, 1534] [1563, 1570] [1597, 1598] [1970, 1971]
[2048, 2052] [2080, 2082] [2279, 2286]
```

### Other collision clusters

```
Order 160: [70, 71]
Order 189: [4, 5]
Order 192: [40, 41, 45] [212, 213, 214] [503, 504] [638, 652]
```

## Collision Orders (Original 8)

| Order | Factorization | # Groups | Collision Clusters | Groups in Collisions |
|------:|:-------------:|:--------:|:-----------------:|:--------------------:|
| 64 | 2⁶ | 267 | 30 | 66 |
| 81 | 3⁴ | 15 | 4 | 9 |
| 96 | 2⁵·3 | 231 | 4 | 8 |
| 100 | 2²·5² | 16 | 1 | 2 |
| 121 | 11² | 2 | 1 | 2 |
| 128 | 2⁷ | 2328 | 463 | 1401 |
| 147 | 3·7² | 6 | 1 | 2 |
| 160 | 2⁵·5 | 238 | 6 | 12 |
| 162 | 2·3⁴ | 55 | 7 | 16 |
| 169 | 13² | 2 | 1 | 2 |
| 189 | 3³·7 | 13 | 1 | 2 |
| 192 | 2⁶·3 | 1543 | 165 | 369 |
| 200 | 2³·5² | 52 | 2 | 4 |

## Key Findings

### 1. Structural invariants are far more powerful than pair-counting for 2-groups

Structural invariants (|Aut(G)|, subgroup conjugacy class count, characteristic subgroup count) resolved the majority of collisions. The 36 structural invariants alone leave only 68 clusters, vs 335 for all 48 O(n²) pair-counting invariants.

### 2. Pair-counting invariants degenerate on p-groups

For 2-groups, power-based invariants a^k=b^k collapse whenever gcd(k,2)=1 (the map is a bijection). Even with 48 different pair-counting formulas, they provide very limited discrimination among 2-groups.

### 3. The hard core is order 128

64 of 70 remaining clusters are at order 128 (2⁷). These groups have identical:
- All 48 O(n²) pair-counting values
- |Aut(G)|, subgroup structure, conjugacy classes
- Derived series, center, Frattini subgroup
- Element order distributions, character degree distributions

### 4. Zero cross-order collisions

No group of order m ever has the same signature as a group of order n ≠ m, even with just the original 8 invariants.

## Data Files

- `invariants_data.csv` — Original 8 invariants for all 6,065 groups
- `extended_invariants.csv` — Phase 1: 21 extended pair-counting invariants (collision orders)
- `phase3_invariants.csv` — Phase 3: 13 structural pair-counting invariants (8 collision orders)
- `phase4_invariants.csv` — Phase 4: 14 order-aware pair-counting invariants (8 collision orders)
- `structural_invariants.csv` — Structural 1: 18 GAP structural invariants (collision orders)
- `structural2_invariants.csv` — Structural 2: 18 deeper structural invariants (collision orders)
- `compute_extended.g`, `compute_phase3.g`, `compute_phase4.g`, `compute_structural.g`, `compute_structural2.g` — GAP computation scripts
- `analyze_combined.py` — Combined analysis and greedy selection
- `plan200.md` — Original plan for this campaign
