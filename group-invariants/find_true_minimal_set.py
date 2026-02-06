#!/usr/bin/env python3
import json
from collections import defaultdict

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

all_inv_names = [
    'inv1_ab_eq_ba', 'inv2_a2b_eq_b2a', 'inv3_a2_eq_b2', 'inv4_conj_is_inv',
    'inv5_a3_eq_b3', 'inv6_a4_eq_b4', 'inv7_ab3_eq_b3a', 'inv8_a3b_eq_ba3',
    'inv9_a2b2_eq_b2a2', 'inv10_ord_ab_eq_3', 'inv11_ab2_eq_ba2', 'inv12_ab3_eq_ba3',
    'inv13_ab_involution', 'inv14_aba_eq_bab', 'inv15_aba1_eq_bab1', 'inv16_a2b3_eq_b3a2',
    'inv17_ab4_eq_ba4', 'inv18_bab1_eq_a2'
]

# Filter to non-abelian groups
non_abelian = [g for g in compiled_data if g['is_abelian'] == 0]

def count_distinguishable(groups, inv_names):
    """Count how many groups are distinguishable using given invariants"""
    by_order = defaultdict(list)
    for g in groups:
        by_order[g['order']].append(g)

    indistinguishable_sets = []
    for order, order_groups in by_order.items():
        if len(order_groups) < 2:
            continue

        sigs = {}
        for g in order_groups:
            sig = tuple(g.get(prop, -1) for prop in inv_names)
            if sig not in sigs:
                sigs[sig] = []
            sigs[sig].append(g)

        for sig, group_set in sigs.items():
            if len(group_set) > 1:
                indistinguishable_sets.append(group_set)

    distinguishable = len(groups) - sum(len(s) - 1 for s in indistinguishable_sets)
    return distinguishable

TARGET = 203

# Start with candidate minimal set (without inv7)
candidate_set = ['inv6_a4_eq_b4', 'inv13_ab_involution', 'inv3_a2_eq_b2', 'inv5_a3_eq_b3', 'inv1_ab_eq_ba']

print("Testing candidate minimal set (5 invariants):")
for inv in candidate_set:
    idx = all_inv_names.index(inv) + 1
    print(f"  inv{idx}: {inv}")

dist = count_distinguishable(non_abelian, candidate_set)
print(f"\nDistinguishability: {dist}/210 ({100*dist/210:.1f}%)")

if dist == TARGET:
    print("\n✓ This 5-invariant set achieves 96.7% distinguishability!")

    print("\nVerifying minimality - trying to remove each invariant:")
    all_essential = True
    for inv in candidate_set:
        test_set = [i for i in candidate_set if i != inv]
        test_dist = count_distinguishable(non_abelian, test_set)
        idx = all_inv_names.index(inv) + 1
        if test_dist < TARGET:
            print(f"  ✗ Cannot remove inv{idx} ({inv}): drops to {test_dist}/210")
        else:
            print(f"  ✓ Can remove inv{idx} ({inv}): still {test_dist}/210")
            all_essential = False

    if all_essential:
        print("\n" + "=" * 80)
        print("TRUE MINIMAL SET FOUND")
        print("=" * 80)
        print(f"\nOnly {len(candidate_set)} invariants are needed (down from 18)!")
        print(f"Reduction: {18 - len(candidate_set)} invariants can be removed")
        print(f"Savings: {100 * (18 - len(candidate_set)) / 18:.1f}% fewer invariants")
        print()
        print("The 5 essential O(n²) invariants:")
        for inv in candidate_set:
            idx = all_inv_names.index(inv) + 1
            # Get description
            descriptions = {
                'inv1_ab_eq_ba': 'ab = ba (commutativity)',
                'inv3_a2_eq_b2': 'a² = b² (same square)',
                'inv5_a3_eq_b3': 'a³ = b³',
                'inv6_a4_eq_b4': 'a⁴ = b⁴',
                'inv13_ab_involution': '(ab)⁻¹ = ab (ab is involution)',
            }
            print(f"  {idx}. {inv}: {descriptions.get(inv, '')}")
