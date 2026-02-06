#!/usr/bin/env python3
import json

# Property names for all 21 functions
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
    "fitting_subgroup_size",
    "num_characteristic_subgroups"  # NEW!
]

# Read existing data
with open('group_properties_20_functions.json', 'r') as f:
    groups = json.load(f)

# Read characteristic subgroups data
char_subgroups = {}
with open('characteristic_subgroups.txt', 'r') as f:
    for line in f:
        parts = line.strip().split(',')
        order, index, num_char = int(parts[0]), int(parts[1]), int(parts[2])
        char_subgroups[(order, index)] = num_char

# Add characteristic subgroups to each group
for group in groups:
    key = (group['order'], group['index'])
    group['num_characteristic_subgroups'] = char_subgroups[key]

# Write updated JSON file
with open('group_properties_21_functions.json', 'w') as f:
    json.dump(groups, f, indent=2)

print(f"Written {len(groups)} groups to group_properties_21_functions.json")

# Create markdown table with property descriptions
with open('group_properties_21_functions.md', 'w') as f:
    f.write("# 21 Numerical Functions on Groups of Order ≤ 60\n\n")

    f.write("## Property Descriptions\n\n")
    descriptions = [
        "1. **Exponent**: Smallest positive integer k such that g^k = e for all elements g",
        "2. **Center Size**: Number of elements that commute with all other elements",
        "3. **Derived Subgroup Size**: Size of the commutator subgroup [G,G]",
        "4. **Number of Conjugacy Classes**: Number of equivalence classes under conjugation",
        "5. **Number of Subgroups**: Total count of all subgroups",
        "6. **Number of Normal Subgroups**: Count of subgroups normal in G",
        "7. **Number of Maximal Subgroups**: Count of maximal proper subgroups",
        "8. **Frattini Subgroup Size**: Size of intersection of all maximal subgroups",
        "9. **Number of Cyclic Subgroups**: Count of subgroups that are cyclic",
        "10. **Number of Abelian Subgroups**: Count of subgroups that are abelian",
        "11. **Nilpotency Class**: Upper central series length (0 if not nilpotent)",
        "12. **Derived Length**: Derived series length (0 if not solvable)",
        "13. **Number of Elements of Order 2**: Count of involutions",
        "14. **Automorphism Group Size**: Size of Aut(G)",
        "15. **Minimum Number of Generators**: Size of minimal generating set",
        "16. **Number of Commuting Pairs**: Count of (a,b) pairs where ab = ba",
        "17. **Number of Triples abc = cab**: Count of (a,b,c) where abc = cab (only for order ≤ 20)",
        "18. **Is Abelian**: 1 if abelian, 0 otherwise",
        "19. **Is Cyclic**: 1 if cyclic, 0 otherwise",
        "20. **Fitting Subgroup Size**: Size of largest normal nilpotent subgroup",
        "21. **Number of Characteristic Subgroups**: Subgroups preserved by all automorphisms"
    ]

    for desc in descriptions:
        f.write(f"{desc}\n")

    f.write("\n## Data Table\n\n")
    f.write("Note: For property 17, -1 means not computed (only computed for order ≤ 20 due to computational cost).\n\n")

    # Create header
    header = "| Order | Index | Group ID |"
    separator = "|-------|-------|----------|"
    for prop in property_names:
        header += f" {prop} |"
        separator += "---------|"

    f.write(header + "\n")
    f.write(separator + "\n")

    # Write data rows
    for group in groups:
        row = f"| {group['order']} | {group['index']} | {group['group_id']} |"
        for prop_name in property_names:
            row += f" {group[prop_name]} |"
        f.write(row + "\n")

print(f"Written markdown table to group_properties_21_functions.md")

# Check if all groups are now distinguishable
from collections import defaultdict

by_order = defaultdict(list)
for group in groups:
    by_order[group['order']].append(group)

indistinguishable_pairs = []

for order, group_list in by_order.items():
    if len(group_list) < 2:
        continue

    signatures = {}
    for group in group_list:
        sig = tuple(group[prop] for prop in property_names)
        if sig not in signatures:
            signatures[sig] = []
        signatures[sig].append(group)

    for sig, groups_with_sig in signatures.items():
        if len(groups_with_sig) > 1:
            indistinguishable_pairs.append(groups_with_sig)

print("\n" + "=" * 80)
print("Checking if all groups are now distinguishable...")
print("=" * 80)

if len(indistinguishable_pairs) == 0:
    print("\n✓ SUCCESS! All 312 groups can now be distinguished by these 21 properties!")
    print("\nAdding 'num_characteristic_subgroups' as property 21 was sufficient")
    print("to distinguish SmallGroup(32,13) from SmallGroup(32,14).")
else:
    print(f"\n✗ Still found {len(indistinguishable_pairs)} sets of indistinguishable groups:\n")
    for i, group_set in enumerate(indistinguishable_pairs, 1):
        print(f"\nSet {i}: {len(group_set)} groups")
        for g in group_set:
            print(f"  {g['group_id']}")
