#!/usr/bin/env python3
import json
from collections import defaultdict

# Read the original 4 invariants
with open('four_o_n2_invariants.json', 'r') as f:
    compiled_data = json.load(f)

# Read the new 8 invariants
new_invs = {}
with open('additional_8_invariants.txt', 'r') as f:
    for line in f:
        parts = line.strip().split(',')
        if len(parts) == 10:  # order, index, 8 invariants
            order, index = map(int, parts[:2])
            invs = tuple(map(int, parts[2:]))
            new_invs[(order, index)] = invs

print(f"Loaded {len(new_invs)} groups with new invariants")

# Add new invariants to compiled data
for g in compiled_data:
    key = (g['order'], g['index'])
    if key in new_invs:
        g['inv5_a3_eq_b3'] = new_invs[key][0]
        g['inv6_a4_eq_b4'] = new_invs[key][1]
        g['inv7_ab3_eq_b3a'] = new_invs[key][2]
        g['inv8_a3b_eq_ba3'] = new_invs[key][3]
        g['inv9_a2b2_eq_b2a2'] = new_invs[key][4]
        g['inv10_ord_ab_eq_3'] = new_invs[key][5]
        g['inv11_ab2_eq_ba2'] = new_invs[key][6]
        g['inv12_ab3_eq_ba3'] = new_invs[key][7]

# Now check with all 12 invariants (4 original + 8 new)
all_inv_names = [
    'inv1_ab_eq_ba', 'inv2_a2b_eq_b2a', 'inv3_a2_eq_b2', 'inv4_conj_is_inv',
    'inv5_a3_eq_b3', 'inv6_a4_eq_b4', 'inv7_ab3_eq_b3a', 'inv8_a3b_eq_ba3',
    'inv9_a2b2_eq_b2a2', 'inv10_ord_ab_eq_3', 'inv11_ab2_eq_ba2', 'inv12_ab3_eq_ba3'
]

# Filter to non-abelian groups
non_abelian = [g for g in compiled_data if g['is_abelian'] == 0]

# Find indistinguishable groups with 12 invariants
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
print("Results with 12 O(n²) invariants (4 original + 8 new)")
print("=" * 80)
print(f"\nTotal non-abelian groups: {len(non_abelian)}")
print(f"Indistinguishable sets: {len(indistinguishable_sets)}")
print(f"Groups in indistinguishable sets: {sum(len(s) for s in indistinguishable_sets)}")
print(f"Distinguishable groups: {len(non_abelian) - sum(len(s)-1 for s in indistinguishable_sets)}")
print(f"Percentage: {100 * (len(non_abelian) - sum(len(s)-1 for s in indistinguishable_sets)) / len(non_abelian):.1f}%")

# Show improvement
print(f"\nImprovement from 4 invariants:")
print(f"  Before: 46 indistinguishable sets (145 distinguishable groups, 69.0%)")
print(f"  After:  {len(indistinguishable_sets)} indistinguishable sets ({len(non_abelian) - sum(len(s)-1 for s in indistinguishable_sets)} distinguishable groups, {100 * (len(non_abelian) - sum(len(s)-1 for s in indistinguishable_sets)) / len(non_abelian):.1f}%)")
print(f"  Improvement: {46 - len(indistinguishable_sets)} fewer indistinguishable sets")

if len(indistinguishable_sets) > 0:
    print(f"\n\nRemaining {len(indistinguishable_sets)} indistinguishable sets:")
    print("-" * 80)
    for i, group_set in enumerate(indistinguishable_sets[:20], 1):  # Show first 20
        group_ids = ', '.join([g['group_id'] for g in group_set])
        print(f"{i}. {group_ids}")
    if len(indistinguishable_sets) > 20:
        print(f"... and {len(indistinguishable_sets) - 20} more sets")
