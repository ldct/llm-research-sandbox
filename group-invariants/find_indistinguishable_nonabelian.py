#!/usr/bin/env python3
import json
from collections import defaultdict

# Read the existing data
with open('group_properties_21_functions_complete.json', 'r') as f:
    groups = json.load(f)

# Read the a²b = b²a data
a2b_data = {}
with open('a2b_eq_b2a_results.txt', 'r') as f:
    for line in f:
        if not ',' in line or line.startswith('#'):
            continue
        parts = line.strip().split(',')
        if len(parts) == 4:
            order, index, count, _ = map(int, parts)
            a2b_data[(order, index)] = count

# Add a²b=b²a as property 22
for group in groups:
    key = (group['order'], group['index'])
    group['num_pairs_a2b_eq_b2a'] = a2b_data.get(key, -1)

# Filter to non-abelian groups only
nonabelian_groups = [g for g in groups if g['is_abelian'] == 0]
print(f"Total non-abelian groups: {len(nonabelian_groups)}")

# O(n²) properties we have so far:
# - num_commuting_pairs (property 16)
# - num_pairs_a2b_eq_b2a (property 22)

o_n2_properties = [
    'num_commuting_pairs',
    'num_pairs_a2b_eq_b2a'
]

# Also include O(n) and O(1) properties that are fast:
fast_properties = [
    'order',  # needed to group
    'exponent',
    'center_size',
    'derived_subgroup_size',
    'num_conjugacy_classes',
    'num_elements_order_2',
    'nilpotency_class',
    'derived_length',
    'min_num_generators',
    'fitting_subgroup_size'
]

# Group non-abelian groups by order
by_order = defaultdict(list)
for group in nonabelian_groups:
    by_order[group['order']].append(group)

print(f"\nOrders with multiple non-abelian groups:")
for order in sorted(by_order.keys()):
    if len(by_order[order]) > 1:
        print(f"  Order {order}: {len(by_order[order])} non-abelian groups")

# Check which groups are indistinguishable with current O(n²) properties
print("\n" + "=" * 80)
print("Testing with O(n²) properties only:")
print("=" * 80)

indistinguishable_sets = []

for order, group_list in sorted(by_order.items()):
    if len(group_list) < 2:
        continue

    # Group by signature using O(n²) properties
    signatures = {}
    for group in group_list:
        sig = tuple(group[prop] for prop in o_n2_properties)
        if sig not in signatures:
            signatures[sig] = []
        signatures[sig].append(group)

    # Find signatures with multiple groups
    for sig, groups_with_sig in signatures.items():
        if len(groups_with_sig) > 1:
            indistinguishable_sets.append(groups_with_sig)

print(f"\nWith 2 O(n²) properties:")
print(f"  {len(indistinguishable_sets)} sets of indistinguishable non-abelian groups")

if len(indistinguishable_sets) > 0:
    print(f"\nIndistinguishable groups (showing first 10 sets):")
    for i, group_set in enumerate(indistinguishable_sets[:10], 1):
        print(f"\n  Set {i}: Order {group_set[0]['order']}, {len(group_set)} groups")
        for g in group_set:
            print(f"    {g['group_id']}")
        print(f"    Signature: commuting_pairs={group_set[0]['num_commuting_pairs']}, "
              f"a2b_eq_b2a={group_set[0]['num_pairs_a2b_eq_b2a']}")

# Now test with fast properties added
print("\n" + "=" * 80)
print("Testing with O(n²) + fast O(n) properties:")
print("=" * 80)

all_fast_props = o_n2_properties + fast_properties
indistinguishable_sets2 = []

for order, group_list in sorted(by_order.items()):
    if len(group_list) < 2:
        continue

    signatures = {}
    for group in group_list:
        sig = tuple(group.get(prop, -1) for prop in all_fast_props)
        if sig not in signatures:
            signatures[sig] = []
        signatures[sig].append(group)

    for sig, groups_with_sig in signatures.items():
        if len(groups_with_sig) > 1:
            indistinguishable_sets2.append(groups_with_sig)

print(f"\nWith 2 O(n²) + {len(fast_properties)} fast properties:")
print(f"  {len(indistinguishable_sets2)} sets of indistinguishable non-abelian groups")

if len(indistinguishable_sets2) > 0:
    print(f"\nRemaining indistinguishable groups:")
    for i, group_set in enumerate(indistinguishable_sets2, 1):
        print(f"\n  Set {i}: Order {group_set[0]['order']}, {len(group_set)} groups")
        for g in group_set:
            print(f"    {g['group_id']}")

    # Save these for further testing
    with open('indistinguishable_nonabelian.json', 'w') as f:
        json.dump(indistinguishable_sets2, f, indent=2)
    print(f"\nSaved indistinguishable sets to indistinguishable_nonabelian.json")

print("\n" + "=" * 80)
