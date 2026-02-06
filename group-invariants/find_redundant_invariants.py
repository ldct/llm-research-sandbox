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
    return distinguishable, indistinguishable_sets

# Baseline: all 18 invariants
baseline_dist, baseline_sets = count_distinguishable(non_abelian, all_inv_names)
print(f"Baseline with all 18 invariants: {baseline_dist}/210 distinguishable")
print()

# Test removing each invariant one at a time
redundant_invariants = []
essential_invariants = []

for i, inv_to_remove in enumerate(all_inv_names):
    remaining_invs = [inv for inv in all_inv_names if inv != inv_to_remove]
    dist, _ = count_distinguishable(non_abelian, remaining_invs)

    if dist == baseline_dist:
        redundant_invariants.append(inv_to_remove)
        print(f"✓ Can remove {inv_to_remove} (inv{i+1}): still {dist}/210 distinguishable")
    else:
        essential_invariants.append(inv_to_remove)
        print(f"✗ Cannot remove {inv_to_remove} (inv{i+1}): drops to {dist}/210 distinguishable")

print()
print("=" * 80)
print("SUMMARY")
print("=" * 80)
print(f"Total invariants: {len(all_inv_names)}")
print(f"Redundant invariants: {len(redundant_invariants)}")
print(f"Essential invariants: {len(essential_invariants)}")

if redundant_invariants:
    print()
    print("Redundant invariants (can be removed):")
    for inv in redundant_invariants:
        idx = all_inv_names.index(inv) + 1
        print(f"  - inv{idx}: {inv}")

    # Try removing all redundant ones at once
    print()
    print("Testing with all redundant invariants removed:")
    minimal_invs = [inv for inv in all_inv_names if inv not in redundant_invariants]
    dist, sets = count_distinguishable(non_abelian, minimal_invs)
    print(f"  With {len(minimal_invs)} invariants: {dist}/210 distinguishable")

    if dist == baseline_dist:
        print()
        print(f"✓ Confirmed: Can use just {len(minimal_invs)} invariants instead of 18!")
        print()
        print("Minimal set of invariants:")
        for inv in minimal_invs:
            idx = all_inv_names.index(inv) + 1
            print(f"  - inv{idx}: {inv}")
