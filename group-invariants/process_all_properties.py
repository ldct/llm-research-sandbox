#!/usr/bin/env python3
import json

# Property names for the 20 functions
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

# Read the raw data (skip the first line which is the function definition)
with open('group_properties_raw.txt', 'r') as f:
    lines = f.readlines()[1:]  # Skip first line

# Parse the data
groups = []
for line in lines:
    parts = line.strip().split(',')
    if len(parts) < 22:  # 2 (order, index) + 20 properties
        continue

    order = int(parts[0])
    index = int(parts[1])
    properties = [int(x) for x in parts[2:]]

    group_data = {
        "order": order,
        "index": index,
        "group_id": f"SmallGroup({order},{index})"
    }

    # Add all properties
    for i, prop_name in enumerate(property_names):
        group_data[prop_name] = properties[i]

    groups.append(group_data)

# Write JSON file
with open('group_properties_20_functions.json', 'w') as f:
    json.dump(groups, f, indent=2)

print(f"Written {len(groups)} groups to group_properties_20_functions.json")

# Create markdown table with property descriptions
with open('group_properties_20_functions.md', 'w') as f:
    f.write("# 20 Numerical Functions on Groups of Order ≤ 60\n\n")

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
        "20. **Fitting Subgroup Size**: Size of largest normal nilpotent subgroup"
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

print(f"Written markdown table to group_properties_20_functions.md")

# Create a summary statistics file
with open('group_properties_summary.md', 'w') as f:
    f.write("# Summary Statistics for 20 Group Properties\n\n")

    f.write("## Sample Interesting Cases\n\n")

    # Find some interesting examples
    f.write("### Groups with largest center\n")
    sorted_by_center = sorted(groups, key=lambda x: x['center_size'], reverse=True)[:5]
    for g in sorted_by_center:
        f.write(f"- {g['group_id']}: center size = {g['center_size']}, order = {g['order']}\n")

    f.write("\n### Groups with most subgroups\n")
    sorted_by_subgroups = sorted(groups, key=lambda x: x['num_subgroups'], reverse=True)[:5]
    for g in sorted_by_subgroups:
        f.write(f"- {g['group_id']}: {g['num_subgroups']} subgroups\n")

    f.write("\n### Groups with largest automorphism groups\n")
    sorted_by_aut = sorted(groups, key=lambda x: x['automorphism_group_size'], reverse=True)[:5]
    for g in sorted_by_aut:
        f.write(f"- {g['group_id']}: |Aut(G)| = {g['automorphism_group_size']}\n")

    f.write("\n### Non-nilpotent groups (nilpotency_class = 0)\n")
    non_nilpotent = [g for g in groups if g['nilpotency_class'] == 0]
    f.write(f"Found {len(non_nilpotent)} non-nilpotent groups:\n")
    for g in non_nilpotent[:10]:
        f.write(f"- {g['group_id']}\n")

    f.write("\n### Groups with highest derived length\n")
    sorted_by_derived = sorted([g for g in groups if g['derived_length'] > 0],
                               key=lambda x: x['derived_length'], reverse=True)[:5]
    for g in sorted_by_derived:
        f.write(f"- {g['group_id']}: derived length = {g['derived_length']}\n")

print(f"Written summary to group_properties_summary.md")
print(f"\nTotal groups analyzed: {len(groups)}")
print(f"Property names: {', '.join(property_names)}")
