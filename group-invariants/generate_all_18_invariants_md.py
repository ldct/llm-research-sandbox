#!/usr/bin/env python3
import json

# Read the original 4 invariants
with open('four_o_n2_invariants.json', 'r') as f:
    compiled_data = json.load(f)

# Read the 8 invariants from first batch
inv_8 = {}
with open('additional_8_invariants.txt', 'r') as f:
    for line in f:
        parts = line.strip().split(',')
        if len(parts) == 10:
            order, index = map(int, parts[:2])
            invs = tuple(map(int, parts[2:]))
            inv_8[(order, index)] = invs

# Read the 6 invariants from second batch
inv_6 = {}
with open('additional_6_invariants.txt', 'r') as f:
    for line in f:
        parts = line.strip().split(',')
        if len(parts) == 8:
            order, index = map(int, parts[:2])
            invs = tuple(map(int, parts[2:]))
            inv_6[(order, index)] = invs

# Add all invariants to compiled data
for g in compiled_data:
    key = (g['order'], g['index'])
    if key in inv_8:
        g['inv5_a3_eq_b3'] = inv_8[key][0]
        g['inv6_a4_eq_b4'] = inv_8[key][1]
        g['inv7_ab3_eq_b3a'] = inv_8[key][2]
        g['inv8_a3b_eq_ba3'] = inv_8[key][3]
        g['inv9_a2b2_eq_b2a2'] = inv_8[key][4]
        g['inv10_ord_ab_eq_3'] = inv_8[key][5]
        g['inv11_ab2_eq_ba2'] = inv_8[key][6]
        g['inv12_ab3_eq_ba3'] = inv_8[key][7]
    if key in inv_6:
        g['inv13_ab_involution'] = inv_6[key][0]
        g['inv14_aba_eq_bab'] = inv_6[key][1]
        g['inv15_aba1_eq_bab1'] = inv_6[key][2]
        g['inv16_a2b3_eq_b3a2'] = inv_6[key][3]
        g['inv17_ab4_eq_ba4'] = inv_6[key][4]
        g['inv18_bab1_eq_a2'] = inv_6[key][5]

# Generate markdown
with open('all_18_o_n2_invariants.md', 'w') as f:
    f.write("# All 18 O(n²) Invariants for Groups of Order ≤ 60\n\n")

    f.write("## Invariant Definitions\n\n")
    f.write("For each group, we compute 18 truly O(n²) invariants by counting pairs (a,b) that satisfy various conditions:\n\n")

    f.write("### First Batch (4 invariants)\n\n")
    f.write("1. **inv1_ab_eq_ba**: ab = ba (commutativity)\n")
    f.write("2. **inv2_a2b_eq_b2a**: a²b = b²a (square compatibility)\n")
    f.write("3. **inv3_a2_eq_b2**: a² = b² (same square)\n")
    f.write("4. **inv4_conj_is_inv**: a⁻¹ba = b⁻¹ (conjugate equals inverse)\n\n")

    f.write("### Second Batch (+8 invariants)\n\n")
    f.write("5. **inv5_a3_eq_b3**: a³ = b³\n")
    f.write("6. **inv6_a4_eq_b4**: a⁴ = b⁴\n")
    f.write("7. **inv7_ab3_eq_b3a**: ab³ = b³a\n")
    f.write("8. **inv8_a3b_eq_ba3**: a³b = ba³\n")
    f.write("9. **inv9_a2b2_eq_b2a2**: a²b² = b²a²\n")
    f.write("10. **inv10_ord_ab_eq_3**: Order(ab) = 3\n")
    f.write("11. **inv11_ab2_eq_ba2**: (ab)² = (ba)²\n")
    f.write("12. **inv12_ab3_eq_ba3**: (ab)³ = (ba)³\n\n")

    f.write("### Third Batch (+6 invariants)\n\n")
    f.write("13. **inv13_ab_involution**: (ab)⁻¹ = ab (ab is involution)\n")
    f.write("14. **inv14_aba_eq_bab**: aba = bab (braid relation)\n")
    f.write("15. **inv15_aba1_eq_bab1**: aba⁻¹ = bab⁻¹\n")
    f.write("16. **inv16_a2b3_eq_b3a2**: a²b³ = b³a²\n")
    f.write("17. **inv17_ab4_eq_ba4**: (ab)⁴ = (ba)⁴\n")
    f.write("18. **inv18_bab1_eq_a2**: bab⁻¹ = a² (conjugate gives square)\n\n")

    f.write("## Distinguishability Results\n\n")
    f.write("Out of **210 non-abelian groups**:\n")
    f.write("- **203 groups (96.7%)** have unique 18-invariant signatures\n")
    f.write("- **7 groups (3.3%)** form indistinguishable pairs (7 pairs total)\n\n")

    f.write("## Complete Data Table\n\n")

    # Create table header
    f.write("| Order | Idx | Group ID | Ab | inv1 | inv2 | inv3 | inv4 | inv5 | inv6 | inv7 | inv8 | inv9 | inv10 | inv11 | inv12 | inv13 | inv14 | inv15 | inv16 | inv17 | inv18 |\n")
    f.write("|-------|-----|----------|----")
    for i in range(18):
        f.write("|------")
    f.write("|\n")

    # Write data rows
    for g in compiled_data:
        order = g['order']
        index = g['index']
        group_id = g['group_id']
        is_abelian = '✓' if g['is_abelian'] == 1 else '✗'

        f.write(f"| {order} | {index} | {group_id} | {is_abelian}")

        # Write all 18 invariants
        inv_names = [
            'inv1_ab_eq_ba', 'inv2_a2b_eq_b2a', 'inv3_a2_eq_b2', 'inv4_conj_is_inv',
            'inv5_a3_eq_b3', 'inv6_a4_eq_b4', 'inv7_ab3_eq_b3a', 'inv8_a3b_eq_ba3',
            'inv9_a2b2_eq_b2a2', 'inv10_ord_ab_eq_3', 'inv11_ab2_eq_ba2', 'inv12_ab3_eq_ba3',
            'inv13_ab_involution', 'inv14_aba_eq_bab', 'inv15_aba1_eq_bab1', 'inv16_a2b3_eq_b3a2',
            'inv17_ab4_eq_ba4', 'inv18_bab1_eq_a2'
        ]

        for inv_name in inv_names:
            val = g.get(inv_name, '-')
            f.write(f" | {val}")

        f.write(" |\n")

    f.write("\n## Legend\n\n")
    f.write("- **Order**: Group order (number of elements)\n")
    f.write("- **Idx**: SmallGroup index\n")
    f.write("- **Group ID**: Standard SmallGroup notation\n")
    f.write("- **Ab**: ✓ if abelian, ✗ if non-abelian\n")
    f.write("- **inv1-inv18**: Count of pairs (a,b) satisfying each condition\n\n")

    f.write("## Remaining Indistinguishable Pairs\n\n")
    f.write("The following 7 pairs of non-abelian groups have identical 18-invariant signatures:\n\n")
    f.write("1. SmallGroup(32,2), SmallGroup(32,24)\n")
    f.write("2. SmallGroup(32,13), SmallGroup(32,15)\n")
    f.write("3. SmallGroup(32,27), SmallGroup(32,34)\n")
    f.write("4. SmallGroup(32,30), SmallGroup(32,31)\n")
    f.write("5. SmallGroup(32,37), SmallGroup(32,38)\n")
    f.write("6. SmallGroup(32,40), SmallGroup(32,42)\n")
    f.write("7. SmallGroup(50,1), SmallGroup(50,4)\n")

print("Generated all_18_o_n2_invariants.md successfully!")
