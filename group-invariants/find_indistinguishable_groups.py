#!/usr/bin/env python3
import json
from collections import defaultdict

# Read the data
with open('group_properties_20_functions.json', 'r') as f:
    groups = json.load(f)

# Property names to compare (excluding order, index, group_id)
property_names = [
    "exponent",
    "center_size",
    "derived_subgroup_size",
    "num_conjugacy_classes",
    "num_subgroups",
    "num_normal_subgroups",
    "num_maximal_subgroups",
    "frattini_subgroup_size",
    "num_cyclic_subgroups",
    "num_abelian_subgroups",
    "nilpotency_class",
    "derived_length",
    "num_elements_order_2",
    "automorphism_group_size",
    "min_num_generators",
    "num_commuting_pairs",
    "num_triples_abc_eq_cab",
    "is_abelian",
    "is_cyclic",
    "fitting_subgroup_size"
]

# Group by order first, then by property signature
by_order = defaultdict(list)
for group in groups:
    by_order[group['order']].append(group)

# Find groups with identical properties
indistinguishable_pairs = []

for order, group_list in by_order.items():
    if len(group_list) < 2:
        continue

    # Create signature for each group (tuple of all properties)
    signatures = {}
    for group in group_list:
        sig = tuple(group[prop] for prop in property_names)
        if sig not in signatures:
            signatures[sig] = []
        signatures[sig].append(group)

    # Find signatures that have multiple groups
    for sig, groups_with_sig in signatures.items():
        if len(groups_with_sig) > 1:
            indistinguishable_pairs.append(groups_with_sig)

print(f"Total groups analyzed: {len(groups)}")
print(f"\nSearching for groups with identical property values...")
print("=" * 80)

if len(indistinguishable_pairs) == 0:
    print("\n✓ SUCCESS! All groups can be distinguished by these 20 properties!")
    print("\nThis means the 20 numerical functions we computed are sufficient")
    print("to distinguish all non-isomorphic groups of order ≤ 60.")
else:
    print(f"\n✗ Found {len(indistinguishable_pairs)} sets of indistinguishable groups:\n")

    for i, group_set in enumerate(indistinguishable_pairs, 1):
        print(f"\nSet {i}: {len(group_set)} groups with identical properties")
        print("-" * 60)
        for g in group_set:
            print(f"  {g['group_id']} (order {g['order']}, index {g['index']})")

        # Show the common property values
        print("\n  Common property values:")
        for prop in property_names:
            print(f"    {prop}: {group_set[0][prop]}")

print("\n" + "=" * 80)

# Additional statistics
total_distinguishable = len(groups) - sum(len(s) - 1 for s in indistinguishable_pairs)
print(f"\nStatistics:")
print(f"  Total groups: {len(groups)}")
if indistinguishable_pairs:
    print(f"  Groups that can be distinguished: {total_distinguishable}")
    print(f"  Groups in indistinguishable sets: {sum(len(s) for s in indistinguishable_pairs)}")
    print(f"  Percentage distinguishable: {100 * total_distinguishable / len(groups):.1f}%")
else:
    print(f"  All groups are distinguishable by these 20 properties!")
