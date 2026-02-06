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
        if len(parts) == 8:  # order, index, 6 invariants
            order, index = map(int, parts[:2])
            invs = tuple(map(int, parts[2:]))
            inv_6[(order, index)] = invs

print(f"Loaded {len(inv_8)} groups with 8 invariants")
print(f"Loaded {len(inv_6)} groups with 6 invariants")

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

# Now check with all 18 invariants (4 + 8 + 6)
all_inv_names = [
    'inv1_ab_eq_ba', 'inv2_a2b_eq_b2a', 'inv3_a2_eq_b2', 'inv4_conj_is_inv',
    'inv5_a3_eq_b3', 'inv6_a4_eq_b4', 'inv7_ab3_eq_b3a', 'inv8_a3b_eq_ba3',
    'inv9_a2b2_eq_b2a2', 'inv10_ord_ab_eq_3', 'inv11_ab2_eq_ba2', 'inv12_ab3_eq_ba3',
    'inv13_ab_involution', 'inv14_aba_eq_bab', 'inv15_aba1_eq_bab1', 'inv16_a2b3_eq_b3a2',
    'inv17_ab4_eq_ba4', 'inv18_bab1_eq_a2'
]

# Filter to non-abelian groups
non_abelian = [g for g in compiled_data if g['is_abelian'] == 0]

# Find indistinguishable groups with 18 invariants
by_order = defaultdict(list)
for g in non_abelian:
    by_order[g['order']].append(g)

indistinguishable_sets = []
for order, groups in by_order.items():
    if len(groups) < 2:
        continue

    sigs = {}
    for g in groups:
        sig = tuple(g.get(prop, -1) for prop in all_inv_names)
        if sig not in sigs:
            sigs[sig] = []
        sigs[sig].append(g)

    for sig, group_set in sigs.items():
        if len(group_set) > 1:
            indistinguishable_sets.append(group_set)

print("\n" + "=" * 80)
print("Results with 18 O(n²) invariants (4 + 8 + 6)")
print("=" * 80)
print(f"\nTotal non-abelian groups: {len(non_abelian)}")
print(f"Indistinguishable sets: {len(indistinguishable_sets)}")
print(f"Groups in indistinguishable sets: {sum(len(s) for s in indistinguishable_sets)}")
print(f"Distinguishable groups: {len(non_abelian) - sum(len(s)-1 for s in indistinguishable_sets)}")
print(f"Percentage: {100 * (len(non_abelian) - sum(len(s)-1 for s in indistinguishable_sets)) / len(non_abelian):.1f}%")

# Show progressive improvement
print(f"\n\nProgressive Improvement:")
print(f"  With  4 O(n²) invariants: 46 sets, 145/210 distinguishable (69.0%)")
print(f"  With 12 O(n²) invariants: 39 sets, 166/210 distinguishable (79.0%)")
print(f"  With 18 O(n²) invariants: {len(indistinguishable_sets)} sets, {len(non_abelian) - sum(len(s)-1 for s in indistinguishable_sets)}/210 distinguishable ({100 * (len(non_abelian) - sum(len(s)-1 for s in indistinguishable_sets)) / len(non_abelian):.1f}%)")

if len(indistinguishable_sets) > 0:
    print(f"\n\nRemaining {len(indistinguishable_sets)} indistinguishable sets:")
    print("-" * 80)
    for i, group_set in enumerate(indistinguishable_sets, 1):
        group_ids = ', '.join([g['group_id'] for g in group_set])
        print(f"{i}. {group_ids}")

print("\n" + "=" * 80)
print("SUMMARY")
print("=" * 80)
print(f"Starting point: 69.0% distinguishable with 4 invariants")
print(f"Final result:   {100 * (len(non_abelian) - sum(len(s)-1 for s in indistinguishable_sets)) / len(non_abelian):.1f}% distinguishable with 18 invariants")
print(f"Improvement:    +{100 * (len(non_abelian) - sum(len(s)-1 for s in indistinguishable_sets)) / len(non_abelian) - 69.0:.1f} percentage points")
print(f"Remaining:      {len(indistinguishable_sets)} indistinguishable sets ({sum(len(s) for s in indistinguishable_sets)} groups)")
